'use strict';
/*
 * Network Map — Server Hub app
 * Scans the local network(s), labels devices, spots double NAT / second routers,
 * tracks history, runs speed tests, surveys Wi-Fi and manages UPnP port forwards.
 * Pure Node (built-in modules + express). Uses only commands Windows already has:
 * ping, arp, route, tracert, netsh.
 */
const express = require('express');
const os = require('os');
const fs = require('fs');
const path = require('path');
const net = require('net');
const dgram = require('dgram');
const dns = require('dns');
const http = require('http');
const https = require('https');
const crypto = require('crypto');
const { execFile } = require('child_process');

const PORT = +process.env.PORT || 4380;
const IS_WIN = process.platform === 'win32';
const IS_MAC = process.platform === 'darwin';
const APP_DIR = __dirname;
const DATA_DIR = path.join(APP_DIR, 'data');
const OUI_FILE = path.join(APP_DIR, 'lib', 'oui.txt');
fs.mkdirSync(DATA_DIR, { recursive: true });

/* ------------------------------------------------------------------ storage */
function readJson(file, fallback) {
  try { return JSON.parse(fs.readFileSync(path.join(DATA_DIR, file), 'utf8')); }
  catch { return fallback; }
}
function writeJson(file, obj) {
  const p = path.join(DATA_DIR, file);
  const tmp = p + '.tmp';
  fs.writeFileSync(tmp, JSON.stringify(obj));
  fs.renameSync(tmp, p);
}

const DEFAULT_ROUTERS = [
  {
    id: 'den', name: 'Den router', model: 'Calix GigaCenter 844E-1', room: 'Den', ssid: 'lg2',
    lanIp: '192.168.1.1', mode: 'router', role: 'main', macHint: '44:65:7f:40:ce',
    notes: 'Fiber ONT + main router from HES/EnergyNet. Wi-Fi 5. Hands out 192.168.1.x.'
  },
  {
    id: 'rec', name: 'Rec room router', model: 'Calix GigaSpire BLAST u6.2 (GS4227E)', room: 'Rec room', ssid: 'lg',
    lanIp: '192.168.2.1', mode: 'ap', role: 'second', macHint: '04:bc:9f:02:d1',
    notes: 'Wi-Fi 6 (EXOS). Access point: DHCP off, den cable in a LAN port. Admin page stays at 192.168.2.1.'
  },
  {
    id: 'up', name: 'Upstairs router', model: 'TP-Link Archer BE230', room: 'Upstairs', ssid: 'lg',
    lanIp: '', mode: 'ap', role: 'second', macHint: '68:7f:f0:6e:7f',
    notes: 'Wi-Fi 7. Access point mode, uplink cable in its Internet port. Gets its own address from the den router.'
  },
  {
    id: 'office', name: "Mom's office router", model: 'TP-Link Archer BE230', room: "Mom's office", ssid: 'lg',
    lanIp: '', mode: 'ap', role: 'second', macHint: '68:7f:f0:52:ea',
    notes: 'Wi-Fi 7. Access point mode. Also runs "lg print" (2.4 GHz IoT network) for the HP printer.'
  }
];
const DEFAULT_SETTINGS = { autoScanMinutes: 30, extraSubnets: [], routers: DEFAULT_ROUTERS };

let settings = Object.assign({}, DEFAULT_SETTINGS, readJson('settings.json', {}));
if (!Array.isArray(settings.routers) || !settings.routers.length) settings.routers = DEFAULT_ROUTERS;
// v1.4: add the two TP-Link access points to setups saved before they existed
{
  let added = false;
  for (const r of DEFAULT_ROUTERS.filter(x => x.id === 'up' || x.id === 'office')) {
    if (settings.routers.some(x => x.id === r.id || (x.macHint && x.macHint.toLowerCase() === r.macHint))) continue;
    if (settings.routers.length >= 8) break;
    settings.routers.push({ ...r }); added = true;
  }
  if (added) writeJson('settings.json', settings);
}
let db = Object.assign({ devices: {}, aliases: {}, events: [], lastDoubleNat: null }, readJson('devices.json', {}));
let history = Object.assign({ scans: [], speed: [] }, readJson('history.json', {}));

const saveSettings = () => writeJson('settings.json', settings);
const saveDb = () => writeJson('devices.json', db);
const saveHistory = () => writeJson('history.json', history);

/* ------------------------------------------------------------------ helpers */
const ip2n = ip => ip.split('.').reduce((a, o) => a * 256 + (+o), 0);
const n2ip = n => [(n >>> 24) & 255, (n >>> 16) & 255, (n >>> 8) & 255, n & 255].join('.');
const prefixMask = p => (p === 0 ? 0 : (0xFFFFFFFF << (32 - p)) >>> 0);
const netOf = (ip, p) => n2ip((ip2n(ip) & prefixMask(p)) >>> 0);
function inSubnet(ip, cidr) {
  if (!ip || !cidr) return false;
  const [n, p] = cidr.split('/');
  return ((ip2n(ip) & prefixMask(+p)) >>> 0) === ip2n(n);
}
const isIPv4 = s => /^(\d{1,3})\.(\d{1,3})\.(\d{1,3})\.(\d{1,3})$/.test(s || '') && s.split('.').every(o => +o <= 255);
const isRfc1918 = ip => inSubnet(ip, '10.0.0.0/8') || inSubnet(ip, '172.16.0.0/12') || inSubnet(ip, '192.168.0.0/16');
const isCgnat = ip => inSubnet(ip, '100.64.0.0/10');
function maskToPrefix(mask) { return mask.split('.').reduce((a, o) => a + (+o).toString(2).split('1').length - 1, 0); }
function normMac(m) {
  const hex = (m || '').replace(/[^0-9a-f]/gi, '').toLowerCase();
  return hex.length === 12 && hex !== '000000000000' ? hex.match(/../g).join(':') : '';
}
function isRandomMac(mac) {
  const b = parseInt((mac || '').replace(/[^0-9a-f]/gi, '').slice(0, 2), 16);
  return !isNaN(b) && (b & 0x02) === 2;
}
function run(cmd, args, timeoutMs = 8000) {
  return new Promise(res => {
    try {
      execFile(cmd, args, { timeout: timeoutMs, windowsHide: true, maxBuffer: 8 * 1024 * 1024 },
        (err, stdout, stderr) => res(String(stdout || '') + (err && !stdout ? String(stderr || '') : '')));
    } catch { res(''); }
  });
}
async function pool(items, n, fn) {
  const out = new Array(items.length);
  let i = 0;
  await Promise.all(Array.from({ length: Math.min(n, items.length) }, async () => {
    while (i < items.length) {
      const k = i++;
      try { out[k] = await fn(items[k], k); } catch { out[k] = null; }
    }
  }));
  return out;
}
const withTimeout = (p, ms, fallback) => Promise.race([p, new Promise(r => setTimeout(() => r(fallback), ms))]);
const median = a => { if (!a.length) return null; const s = [...a].sort((x, y) => x - y); return s[Math.floor(s.length / 2)]; };
function decodeXml(s) {
  return (s || '').replace(/&lt;/g, '<').replace(/&gt;/g, '>').replace(/&quot;/g, '"').replace(/&apos;/g, "'").replace(/&amp;/g, '&').trim();
}
function xmlTag(xml, tag) {
  const m = new RegExp(`<(?:[\\w-]+:)?${tag}(?:\\s[^>]*)?>([\\s\\S]*?)</(?:[\\w-]+:)?${tag}>`, 'i').exec(xml || '');
  return m ? decodeXml(m[1]) : '';
}
const escXml = s => String(s).replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');

function httpRequest(url, { method = 'GET', headers = {}, body = null, timeout = 2500, agent, maxBytes = 2e6 } = {}) {
  return new Promise(res => {
    let u;
    try { u = new URL(url); } catch { return res(null); }
    const lib = u.protocol === 'https:' ? https : http;
    const req = lib.request(u, { method, headers, timeout, agent, rejectUnauthorized: false }, r => {
      const chunks = []; let size = 0;
      r.on('data', c => { size += c.length; if (size <= maxBytes) chunks.push(c); });
      r.on('end', () => res({ status: r.statusCode, headers: r.headers, body: Buffer.concat(chunks).toString('utf8') }));
      r.on('error', () => res(null));
    });
    req.on('timeout', () => req.destroy());
    req.on('error', () => res(null));
    if (body) req.write(body);
    req.end();
  });
}

/* ------------------------------------------------------------------ vendor lookup */
const OUI = new Map();
try {
  for (const line of fs.readFileSync(OUI_FILE, 'utf8').split('\n')) {
    const t = line.indexOf('\t');
    if (t > 0) OUI.set(line.slice(0, t), line.slice(t + 1).trim());
  }
} catch { console.warn('[network-map] lib/oui.txt missing — vendor names disabled'); }
function vendorOf(mac) {
  if (!mac || isRandomMac(mac)) return '';
  const hex = mac.replace(/[^0-9a-f]/gi, '').toUpperCase();
  return OUI.get(hex.slice(0, 9)) || OUI.get(hex.slice(0, 7)) || OUI.get(hex.slice(0, 6)) || '';
}
function shortVendor(v) {
  return (v || '').replace(/[,.]?\s+(inc|incorporated|corp|corporation|co|ltd|limited|llc|gmbh|s\.?a|ag|bv|plc|technologies|technology|electronics co)\.?$/i, '')
    .replace(/[,.]?\s+(inc|corp|co|ltd|llc)\.?$/i, '').trim();
}

/* ------------------------------------------------------------------ networks */
const VIRTUAL_RE = /vEthernet|VirtualBox|VMware|Hyper-V|WSL|Loopback|Tailscale|ZeroTier|Hamachi|docker|^br-|^veth|vboxnet|utun|Npcap|Bluetooth/i;

function parseRoutePrint(t) {
  const out = [];
  for (const line of t.split(/\r?\n/)) {
    const m = line.match(/^\s*0\.0\.0\.0\s+0\.0\.0\.0\s+(\d+\.\d+\.\d+\.\d+)\s+(\d+\.\d+\.\d+\.\d+)\s+(\d+)/);
    if (m) out.push({ gateway: m[1], ifaceIp: m[2], metric: +m[3] });
  }
  return out.sort((a, b) => a.metric - b.metric);
}
async function getGateways() {
  const out = [];
  if (IS_WIN) {
    out.push(...parseRoutePrint(await run('route', ['print', '-4'])));
  } else if (IS_MAC) {
    const t = await run('netstat', ['-rn', '-f', 'inet']);
    for (const line of t.split('\n')) {
      const m = line.match(/^default\s+(\d+\.\d+\.\d+\.\d+)\s+\S+\s+(\S+)/);
      if (m) out.push({ gateway: m[1], ifaceName: m[2] });
    }
  } else {
    const t = await run('ip', ['-4', 'route', 'show', 'default']);
    for (const line of t.split('\n')) {
      const m = line.match(/default via (\S+) dev (\S+)(?:.*metric (\d+))?/);
      if (m) out.push({ gateway: m[1], ifaceName: m[2], metric: m[3] ? +m[3] : 0 });
    }
  }
  return out;
}

async function getNetworks() {
  const gws = await getGateways();
  const nets = [];
  for (const [name, addrs] of Object.entries(os.networkInterfaces())) {
    for (const a of addrs || []) {
      if (!(a.family === 'IPv4' || a.family === 4) || a.internal || a.address.startsWith('169.254.')) continue;
      const prefix = a.cidr ? +a.cidr.split('/')[1] : maskToPrefix(a.netmask);
      const cidr = netOf(a.address, prefix) + '/' + prefix;
      const gw = gws.find(g => g.ifaceIp === a.address || g.ifaceName === name) || gws.find(g => inSubnet(g.gateway, cidr));
      nets.push({ iface: name, ip: a.address, mac: normMac(a.mac), prefix, cidr, gateway: gw ? gw.gateway : null, virtual: VIRTUAL_RE.test(name) });
    }
  }
  return nets;
}
const localIps = () => Object.values(os.networkInterfaces()).flat().filter(a => a && (a.family === 'IPv4' || a.family === 4)).map(a => a.address);

function hostsIn(sub) {
  // Never sweep more than a /24 — pick the /24 around this PC if the subnet is larger.
  let base, prefix = +sub.cidr.split('/')[1];
  if (prefix < 24) { base = ip2n(netOf(sub.hostIp || sub.cidr.split('/')[0], 24)); prefix = 24; }
  else base = ip2n(sub.cidr.split('/')[0]);
  const size = 2 ** (32 - prefix);
  const out = [];
  for (let i = 1; i < size - 1; i++) out.push(n2ip(base + i));
  return out;
}

/* ------------------------------------------------------------------ probes */
const PROBE_PORTS = [80, 443, 8060, 8008, 8009, 5555, 22, 445, 139, 62078, 8080, 7000, 1400, 554];

function tcpProbe(ip, port, ms = 700) {
  return new Promise(res => {
    const s = new net.Socket();
    let done = false;
    const fin = st => { if (done) return; done = true; s.destroy(); res(st); };
    s.setTimeout(ms);
    s.once('connect', () => fin('open'));
    s.once('timeout', () => fin('timeout'));
    s.once('error', e => fin(e.code === 'ECONNREFUSED' ? 'closed' : 'error'));
    try { s.connect(port, ip); } catch { fin('error'); }
  });
}
async function pingHost(ip) {
  const args = IS_WIN ? ['-n', '1', '-w', '800', ip] : IS_MAC ? ['-c', '1', '-t', '1', ip] : ['-c', '1', '-W', '1', ip];
  const t = await run('ping', args, 3000);
  const ttl = t.match(/ttl[=\s:]+(\d+)/i);
  const rtt = t.match(/time[=<]\s*([\d.]+)\s*ms/i);
  return { alive: !!ttl, ttl: ttl ? +ttl[1] : null, rtt: rtt ? +rtt[1] : null };
}
async function probeHost(ip) {
  const [p, ports] = await Promise.all([
    pingHost(ip),
    Promise.all(PROBE_PORTS.map(port => tcpProbe(ip, port).then(s => [port, s])))
  ]);
  const open = ports.filter(([, s]) => s === 'open').map(([port]) => port);
  const refused = ports.some(([, s]) => s === 'closed');
  return { ip, alive: p.alive || open.length > 0 || refused, ping: p.alive, rtt: p.rtt, ttl: p.ttl, open };
}

async function readArp() {
  let t;
  if (IS_WIN || IS_MAC) t = await run('arp', ['-a']);
  else { t = await run('ip', ['neigh']); if (!t.trim()) t = await run('arp', ['-an']); }
  return parseArp(t);
}
function parseArp(t) {
  const map = new Map();
  for (const line of t.split(/\r?\n/)) {
    if (/incomplete|FAILED/i.test(line)) continue;
    const ip = line.match(/(\d+\.\d+\.\d+\.\d+)/);
    const mac = line.match(/\b([0-9a-f]{1,2}[:-]){5}[0-9a-f]{1,2}\b/i);
    if (!ip || !mac) continue;
    const m = normMac(mac[0].split(/[:-]/).map(x => x.padStart(2, '0')).join(''));
    if (!m || m === 'ff:ff:ff:ff:ff:ff' || m.startsWith('01:00:5e')) continue;
    map.set(ip[1], m);
  }
  return map;
}

function reverseName(ip) {
  return withTimeout(new Promise(r => {
    try { dns.lookupService(ip, 80, (e, host) => r(e || !host || host === ip ? '' : host)); } catch { r(''); }
  }), 2500, '');
}
function reverseViaGateway(ip, gw) {
  try {
    const r = new dns.Resolver({ timeout: 1200, tries: 1 });
    r.setServers([gw]);
    return withTimeout(new Promise(res => r.reverse(ip, (e, names) => res(e || !names ? '' : names[0] || ''))), 1800, '');
  } catch { return Promise.resolve(''); }
}

/* ------------------------------------------------------------------ mDNS (Bonjour) */
const MDNS_SERVICES = ['_googlecast._tcp', '_androidtvremote2._tcp', '_amzn-wplay._tcp', '_airplay._tcp', '_raop._tcp',
  '_companion-link._tcp', '_spotify-connect._tcp', '_device-info._tcp', '_hap._tcp', '_ipp._tcp', '_printer._tcp',
  '_smb._tcp', '_sonos._tcp', '_http._tcp', '_workstation._tcp'];

function encName(name) {
  const parts = name.split('.').filter(Boolean).map(p => { const b = Buffer.from(p, 'utf8'); return Buffer.concat([Buffer.from([b.length]), b]); });
  return Buffer.concat([...parts, Buffer.from([0])]);
}
function buildDnsQuery(names, type = 12) {
  const h = Buffer.alloc(12);
  h.writeUInt16BE(0x1234, 0);
  h.writeUInt16BE(names.length, 4);
  const qs = names.map(n => { const t = Buffer.alloc(4); t.writeUInt16BE(type, 0); t.writeUInt16BE(1, 2); return Buffer.concat([encName(n), t]); });
  return Buffer.concat([h, ...qs]);
}
function readName(buf, off) {
  const labels = []; let jumped = false, end = off, guard = 0;
  while (guard++ < 128 && off < buf.length) {
    const len = buf[off];
    if (len === 0) { off++; break; }
    if ((len & 0xC0) === 0xC0) { if (!jumped) end = off + 2; jumped = true; off = ((len & 0x3F) << 8) | buf[off + 1]; continue; }
    labels.push(buf.toString('utf8', off + 1, off + 1 + len));
    off += 1 + len;
  }
  return { name: labels.join('.'), next: jumped ? end : off };
}
function parseDns(buf) {
  const qd = buf.readUInt16BE(4), total = buf.readUInt16BE(6) + buf.readUInt16BE(8) + buf.readUInt16BE(10);
  let off = 12;
  for (let i = 0; i < qd; i++) off = readName(buf, off).next + 4;
  const recs = [];
  for (let i = 0; i < total && off + 10 <= buf.length; i++) {
    const n = readName(buf, off); off = n.next;
    const type = buf.readUInt16BE(off), rdlen = buf.readUInt16BE(off + 8), rd = off + 10;
    let data = null;
    if (type === 1 && rdlen === 4) data = [buf[rd], buf[rd + 1], buf[rd + 2], buf[rd + 3]].join('.');
    else if (type === 12) data = readName(buf, rd).name;
    else if (type === 33) data = { port: buf.readUInt16BE(rd + 4), target: readName(buf, rd + 6).name };
    else if (type === 16) {
      data = {}; let p = rd;
      while (p < rd + rdlen) { const l = buf[p]; const s = buf.toString('utf8', p + 1, p + 1 + l); const eq = s.indexOf('='); if (eq > 0) data[s.slice(0, eq).toLowerCase()] = s.slice(eq + 1); p += 1 + l; }
    }
    recs.push({ name: n.name, type, data });
    off = rd + rdlen;
  }
  return recs;
}
function mdnsDiscover(ifaceIps, ms = 3500) {
  return new Promise(resolve => {
    const found = {}, socks = [];
    const q = buildDnsQuery(MDNS_SERVICES.map(s => s + '.local'));
    const entry = ip => found[ip] || (found[ip] = { hostnames: new Set(), services: new Set(), instances: new Set(), txt: {} });
    for (const ifip of ifaceIps) {
      try {
        const s = dgram.createSocket({ type: 'udp4', reuseAddr: true });
        s.on('error', () => {});
        s.on('message', (msg, rinfo) => {
          let recs; try { recs = parseDns(msg); } catch { return; }
          const e = entry(rinfo.address);
          const aMap = {};
          for (const r of recs) if (r.type === 1) aMap[r.name.toLowerCase()] = r.data;
          for (const r of recs) {
            if (r.type === 1 && r.data === rinfo.address) e.hostnames.add(r.name);
            if (r.type === 12) {
              const svc = MDNS_SERVICES.find(sv => r.name.toLowerCase().startsWith(sv));
              if (svc) { e.services.add(svc); const inst = String(r.data).split('._')[0]; if (inst) e.instances.add(inst); }
            }
            if (r.type === 16 && r.data) for (const k of ['fn', 'md', 'model', 'am', 'ty', 'n']) if (r.data[k] && !e.txt[k]) e.txt[k] = r.data[k];
            if (r.type === 33 && r.data && aMap[r.data.target.toLowerCase()] === rinfo.address) e.hostnames.add(r.data.target);
          }
        });
        s.bind(0, ifip, () => {
          try { s.setMulticastInterface(ifip); s.setMulticastTTL(255); } catch {}
          const send = () => { try { s.send(q, 5353, '224.0.0.251'); } catch {} };
          send(); setTimeout(send, 1000);
        });
        socks.push(s);
      } catch {}
    }
    setTimeout(() => {
      socks.forEach(s => { try { s.close(); } catch {} });
      const out = {};
      for (const [ip, e] of Object.entries(found)) out[ip] = { hostnames: [...e.hostnames], services: [...e.services], instances: [...e.instances], txt: e.txt };
      resolve(out);
    }, ms);
  });
}

/* ------------------------------------------------------------------ SSDP / UPnP */
function ssdpDiscover(ifaceIps, ms = 3500, st = 'ssdp:all') {
  return new Promise(resolve => {
    const found = {}, socks = [];
    const msg = Buffer.from(['M-SEARCH * HTTP/1.1', 'HOST: 239.255.255.250:1900', 'MAN: "ssdp:discover"', 'MX: 2', `ST: ${st}`, 'USER-AGENT: NetworkMap/1.0 UPnP/1.1', '', ''].join('\r\n'));
    for (const ifip of ifaceIps) {
      try {
        const s = dgram.createSocket({ type: 'udp4', reuseAddr: true });
        s.on('error', () => {});
        s.on('message', (buf, rinfo) => {
          const h = {};
          for (const line of buf.toString().split(/\r?\n/)) { const i = line.indexOf(':'); if (i > 0) h[line.slice(0, i).trim().toLowerCase()] = line.slice(i + 1).trim(); }
          const e = found[rinfo.address] || (found[rinfo.address] = { locations: new Set(), servers: new Set(), sts: new Set() });
          if (h.location) e.locations.add(h.location);
          if (h.server) e.servers.add(h.server);
          if (h.st) e.sts.add(h.st);
        });
        s.bind(0, ifip, () => {
          try { s.setMulticastInterface(ifip); } catch {}
          const send = () => { try { s.send(msg, 1900, '239.255.255.250'); } catch {} };
          send(); setTimeout(send, 800);
        });
        socks.push(s);
      } catch {}
    }
    setTimeout(() => {
      socks.forEach(s => { try { s.close(); } catch {} });
      const out = {};
      for (const [ip, e] of Object.entries(found)) out[ip] = { locations: [...e.locations], servers: [...e.servers], sts: [...e.sts] };
      resolve(out);
    }, ms);
  });
}
function parseDeviceDesc(xml, location) {
  const base = xmlTag(xml, 'URLBase') || location;
  const out = {
    location, friendlyName: xmlTag(xml, 'friendlyName'), manufacturer: xmlTag(xml, 'manufacturer'),
    modelName: xmlTag(xml, 'modelName'), modelNumber: xmlTag(xml, 'modelNumber'), deviceType: xmlTag(xml, 'deviceType'), igd: false
  };
  const svcRe = /<(?:\w+:)?service>([\s\S]*?)<\/(?:\w+:)?service>/g;
  let m;
  while ((m = svcRe.exec(xml))) {
    const st = xmlTag(m[1], 'serviceType'), cu = xmlTag(m[1], 'controlURL');
    if (/WAN(IP|PPP)Connection/.test(st) && cu) {
      try { out.controlURL = new URL(cu, base).href; out.serviceType = st; out.igd = true; break; } catch {}
    }
  }
  if (/InternetGatewayDevice/.test(out.deviceType)) out.igd = true;
  return out;
}
async function soap(controlURL, serviceType, action, args = {}) {
  const inner = Object.entries(args).map(([k, v]) => `<${k}>${escXml(v)}</${k}>`).join('');
  const body = `<?xml version="1.0"?><s:Envelope xmlns:s="http://schemas.xmlsoap.org/soap/envelope/" s:encodingStyle="http://schemas.xmlsoap.org/soap/encoding/"><s:Body><u:${action} xmlns:u="${serviceType}">${inner}</u:${action}></s:Body></s:Envelope>`;
  return httpRequest(controlURL, {
    method: 'POST', body, timeout: 4000,
    headers: { 'Content-Type': 'text/xml; charset="utf-8"', 'SOAPAction': `"${serviceType}#${action}"`, 'Content-Length': Buffer.byteLength(body) }
  });
}
let igdCache = { at: 0, igd: null };
async function findIgd(force = false) {
  if (!force && igdCache.igd && Date.now() - igdCache.at < 5 * 60000) return igdCache.igd;
  const nets = (await getNetworks()).filter(n => n.gateway && !n.virtual);
  if (!nets.length) return null;
  const gateways = nets.map(n => n.gateway);
  const [a, b] = await Promise.all([
    ssdpDiscover(nets.map(n => n.ip), 2500, 'urn:schemas-upnp-org:device:InternetGatewayDevice:1'),
    ssdpDiscover(nets.map(n => n.ip), 2500, 'urn:schemas-upnp-org:service:WANIPConnection:1')
  ]);
  const cands = {};
  for (const src of [a, b]) for (const [ip, e] of Object.entries(src)) (cands[ip] = cands[ip] || new Set()) && e.locations.forEach(l => cands[ip].add(l));
  const order = Object.keys(cands).sort((x, y) => (gateways.includes(y) ? 1 : 0) - (gateways.includes(x) ? 1 : 0));
  for (const ip of order) {
    for (const loc of cands[ip]) {
      const r = await httpRequest(loc, { timeout: 3000 });
      if (r && r.status === 200) {
        const d = parseDeviceDesc(r.body, loc);
        if (d.controlURL) { d.ip = ip; d.isGateway = gateways.includes(ip); igdCache = { at: Date.now(), igd: d }; return d; }
      }
    }
  }
  igdCache = { at: Date.now(), igd: null };
  return null;
}

/* ------------------------------------------------------------------ device-specific info */
async function rokuInfo(ip) {
  const r = await httpRequest(`http://${ip}:8060/query/device-info`, { timeout: 2000 });
  if (!r || r.status !== 200 || !r.body.includes('device-info')) return null;
  const x = r.body;
  return {
    name: xmlTag(x, 'user-device-name') || xmlTag(x, 'friendly-device-name'),
    model: xmlTag(x, 'friendly-model-name') || xmlTag(x, 'model-name'),
    isTv: xmlTag(x, 'is-tv') === 'true', location: xmlTag(x, 'user-device-location'),
    wifi: xmlTag(x, 'network-name'), connection: xmlTag(x, 'network-type')
  };
}
async function castInfo(ip) {
  for (const url of [`http://${ip}:8008/setup/eureka_info?params=name,device_info`, `https://${ip}:8443/setup/eureka_info?params=name,device_info`]) {
    const r = await httpRequest(url, { timeout: 2000 });
    if (r && r.status === 200) {
      try { const j = JSON.parse(r.body); return { name: j.name, model: j.device_info && (j.device_info.model_name || j.device_info.product_name), maker: j.device_info && j.device_info.manufacturer }; } catch {}
    }
  }
  return null;
}

/* ------------------------------------------------------------------ classification */
const NET_GEAR_RE = /calix|netgear|tp-link|tplink|asustek|linksys|arris|ubiquiti|eero|zyxel|sagemcom|technicolor|actiontec|mikrotik|d-link|belkin|plume|adtran|nokia shanghai/i;

function matchRouter(d) {
  const mac = (d.mac || '').toLowerCase();
  return settings.routers.find(r => r.macHint && mac && mac.startsWith(r.macHint.toLowerCase()))
    || (d.isGateway ? settings.routers.find(r => r.lanIp === d.ip) : null) || null;
}
function classify(d) {
  if (d.isSelf) return 'This PC';
  if (d.isGateway && d.upstream) return 'Router (upstream)';
  if (d.isGateway) return 'Router (gateway)';
  if (d.nestedRouter) return 'Router (runs its own network)';
  if (d.routerMatch) return 'Access point';
  if (d.roku) return d.roku.isTv ? 'Roku TV' : 'Roku';
  const s = d.services || [], v = (d.vendor || '').toLowerCase();
  if (s.includes('_amzn-wplay._tcp') || (v.includes('amazon') && d.open.includes(5555))) return 'Fire TV';
  if (s.includes('_androidtvremote2._tcp')) return 'Google TV / Android TV';
  if (d.cast || s.includes('_googlecast._tcp')) return d.cast && /speaker|home|nest|mini|audio/i.test(d.cast.model || '') ? 'Google speaker' : 'Chromecast / Google TV';
  if (d.open.includes(62078) || s.includes('_companion-link._tcp')) return 'Apple device';
  if (s.includes('_airplay._tcp')) return 'AirPlay device';
  if (s.includes('_ipp._tcp') || s.includes('_printer._tcp')) return 'Printer';
  if (s.includes('_sonos._tcp') || v.includes('sonos')) return 'Sonos speaker';
  if (v.includes('roku')) return 'Roku';
  if (v.includes('amazon')) return 'Amazon device';
  if (v.includes('apple')) return 'Apple device';
  if (v.includes('google')) return 'Google device';
  if (/nintendo/.test(v)) return 'Nintendo';
  if (/sony/.test(v)) return 'Sony / PlayStation';
  if (/microsoft/.test(v)) return 'Microsoft / Xbox';
  if (/samsung/.test(v)) return 'Samsung device';
  if (/tcl|hisense|vizio|lg electronics|funai/.test(v)) return 'Smart TV';
  if (/espressif|tuya|wyze|ring|ecobee|nest labs|lifi|signify|philips lighting|wiz/.test(v)) return 'Smart home device';
  if (NET_GEAR_RE.test(v)) return 'Network equipment';
  if (d.open.includes(445) || d.open.includes(139) || d.ttl === 128) return 'Windows PC';
  if (d.randomMac) return 'Phone / tablet (private address)';
  return 'Unknown';
}
function bestName(d) {
  const short = h => (h || '').replace(/\.(local|lan|home|localdomain|attlocal\.net)\.?$/i, '');
  return (d.roku && d.roku.name) || (d.cast && d.cast.name) || d.txt.fn || d.txt.n
    || (d.upnp.find(u => u.friendlyName) || {}).friendlyName
    || short(d.hostname) || short(d.mdnsNames[0]) || d.instances.find(i => !/^[0-9a-f-]{16,}$/i.test(i))
    || (d.vendor ? `${d.vendor} device` : '') || d.ip;
}

async function enrich(c, ctx) {
  const s = c.subnet;
  const isSelf = c.ip === s.hostIp;
  const mac = isSelf ? s.hostMac : (ctx.arp.get(c.ip) || '');
  const md = ctx.mdns[c.ip], sd = ctx.ssdp[c.ip], desc = ctx.descs[c.ip] || [];
  const d = {
    ip: c.ip, cidr: s.cidr, gateway: s.gateway, mac, vendor: shortVendor(vendorOf(mac)), randomMac: mac ? isRandomMac(mac) : false,
    responds: !!c.alive, ping: !!c.ping, rtt: c.rtt ?? null, ttl: c.ttl ?? null, open: c.open || [],
    isSelf, isGateway: c.ip === s.gateway, upstream: !!s.upstream,
    services: md ? md.services : [], mdnsNames: md ? md.hostnames : [], instances: md ? md.instances : [], txt: md ? md.txt : {},
    ssdpServer: sd ? (sd.servers[0] || '') : '',
    upnp: desc.map(x => ({ friendlyName: x.friendlyName, manufacturer: x.manufacturer, model: x.modelName, type: (x.deviceType || '').split(':').slice(-2, -1)[0] || '', igd: !!x.igd })),
    hostname: isSelf ? os.hostname() : ''
  };
  const tasks = [];
  if (!d.hostname) tasks.push(reverseName(c.ip).then(h => { if (h) d.hostname = h; }));
  if (d.open.includes(8060) || (sd && sd.sts.some(x => /roku/i.test(x)))) tasks.push(rokuInfo(c.ip).then(r => { if (r) d.roku = r; }));
  if (d.open.includes(8008) || d.open.includes(8009) || d.services.includes('_googlecast._tcp')) tasks.push(castInfo(c.ip).then(r => { if (r) d.cast = r; }));
  await Promise.all(tasks);
  if (!d.hostname && s.gateway) d.hostname = await reverseViaGateway(c.ip, s.gateway);
  if (!d.hostname && d.mdnsNames.length) d.hostname = d.mdnsNames[0];

  const r = matchRouter(d);
  d.routerMatch = r ? r.id : null;
  const igdHere = d.upnp.some(u => u.igd);
  d.nestedRouter = !d.isGateway && !d.isSelf && (igdHere || (r && r.mode !== 'ap'));
  d.possibleRouter = !d.isGateway && !d.isSelf && !d.nestedRouter && !r && NET_GEAR_RE.test(d.vendor) && (d.open.includes(80) || d.open.includes(443));
  d.kind = classify(d);
  d.autoName = bestName(d);
  return d;
}

/* ------------------------------------------------------------------ scan */
let scanState = { running: false, phase: 'idle', done: 0, total: 0, startedAt: null, finishedAt: null, error: null };

function resolveKey(k) { let g = 0; while (db.aliases[k] && g++ < 10) k = db.aliases[k]; return k; }

async function runScan(trigger = 'manual') {
  if (scanState.running) return;
  scanState = { running: true, phase: 'Finding networks', done: 0, total: 0, startedAt: Date.now(), finishedAt: null, error: null };
  try {
    const nets = await getNetworks();
    let targets = nets.filter(n => n.gateway && !n.virtual);
    if (!targets.length) targets = nets.filter(n => !n.virtual);
    const subnets = [];
    for (const n of targets) if (!subnets.find(s => s.cidr === n.cidr)) subnets.push({ cidr: n.cidr, gateway: n.gateway, iface: n.iface, hostIp: n.ip, hostMac: n.mac });
    for (const x of settings.extraSubnets || []) {
      const m = /^(\d+\.\d+\.\d+\.\d+)\/(\d+)$/.exec(x);
      if (m && isIPv4(m[1])) { const c = netOf(m[1], +m[2]) + '/' + m[2]; if (!subnets.find(s => s.cidr === c)) subnets.push({ cidr: c, gateway: null, iface: 'manual', extra: true }); }
    }
    const ifaceIps = [...new Set(subnets.filter(s => s.hostIp).map(s => s.hostIp))];

    scanState.phase = 'Sweeping addresses';
    const primaryGw = (subnets.find(s => s.gateway) || {}).gateway || null;
    const traceP = primaryGw ? traceroute('1.1.1.1', 3) : Promise.resolve([]);
    const discoP = Promise.all([mdnsDiscover(ifaceIps), ssdpDiscover(ifaceIps)]);
    const hostList = [];
    const myIps = new Set(localIps());
    for (const s of subnets) for (const ip of hostsIn(s)) if (ip !== s.hostIp && !myIps.has(ip)) hostList.push({ ip, subnet: s });
    scanState.total = hostList.length;
    const probes = await pool(hostList, 40, async h => { const r = await probeHost(h.ip); scanState.done++; return { ...r, subnet: h.subnet }; });

    // Is there another router above our gateway (double NAT)? Look at the 2nd traceroute hop.
    scanState.phase = 'Checking for a router upstream';
    const hops = await traceP;
    let upstream = null;
    const gi = hops.findIndex(h => h.ip === primaryGw);
    if (gi >= 0) {
      const nxt = hops.slice(gi + 1).find(h => h.ip);
      if (nxt && (inSubnet(nxt.ip, '192.168.0.0/16') || inSubnet(nxt.ip, '172.16.0.0/12')) && !subnets.some(s => inSubnet(nxt.ip, s.cidr)))
        upstream = { ip: nxt.ip, cidr: netOf(nxt.ip, 24) + '/24', via: primaryGw };
    }
    if (upstream && settings.scanUpstream !== false) {
      const us = { cidr: upstream.cidr, gateway: upstream.ip, iface: 'through ' + primaryGw, hostIp: null, hostMac: '', upstream: true };
      subnets.push(us);
      scanState.phase = 'Sweeping the network above your router';
      const list = hostsIn(us).map(ip => ({ ip, subnet: us }));
      scanState.total += list.length;
      probes.push(...await pool(list, 40, async h => { const r = await probeHost(h.ip); scanState.done++; return { ...r, subnet: h.subnet }; }));
    }
    scanState.phase = 'Listening for device announcements';
    const [mdns, ssdp] = await discoP;

    scanState.phase = 'Reading MAC addresses';
    const arp = await readArp();
    const cands = new Map();
    for (const p of probes) if (p && p.alive) cands.set(p.ip, p);
    for (const ip of myIps) if (!subnets.some(s => s.hostIp === ip)) arp.delete(ip);
    const subOf = ip => subnets.find(s => inSubnet(ip, s.cidr));
    for (const [ip] of arp) if (!cands.has(ip)) {
      const s = subOf(ip);
      if (s && hostsIn(s).includes(ip)) cands.set(ip, { ip, alive: false, open: [], subnet: s });
    }
    for (const ip of [...Object.keys(mdns), ...Object.keys(ssdp)]) if (!cands.has(ip) && !(myIps.has(ip) && !subnets.some(s => s.hostIp === ip))) { const s = subOf(ip); if (s) cands.set(ip, { ip, alive: true, open: [], subnet: s }); }
    for (const s of subnets) if (s.hostIp && !cands.has(s.hostIp)) cands.set(s.hostIp, { ip: s.hostIp, alive: true, open: [], subnet: s });

    scanState.phase = 'Identifying devices';
    const descs = {};
    await pool(Object.entries(ssdp).filter(([ip]) => cands.has(ip)), 8, async ([ip, e]) => {
      for (const loc of e.locations.slice(0, 3)) {
        const r = await httpRequest(loc, { timeout: 2500 });
        if (r && r.status === 200 && /<device/i.test(r.body)) (descs[ip] = descs[ip] || []).push(parseDeviceDesc(r.body, loc));
      }
    });
    const ctx = { arp, mdns, ssdp, descs };
    const devices = (await pool([...cands.values()], 16, c => enrich(c, ctx))).filter(Boolean);

    /* ---- merge into the device database + compute events ---- */
    const now = Date.now();
    const scanId = now.toString(36);
    const firstEver = history.scans.length === 0;
    const prev = history.scans[history.scans.length - 1];
    const prevKeys = new Set(prev ? prev.devices.map(x => x[0]) : []);
    const scanned = subnets.map(s => s.cidr);
    const events = [];
    const seen = new Set();
    for (const d of devices) {
      const k = resolveKey(d.mac ? 'mac:' + d.mac : 'ip:' + d.ip);
      d.key = k; seen.add(k);
      let rec = db.devices[k];
      if (!rec) {
        rec = db.devices[k] = { key: k, firstSeen: now, label: '', router: '', room: '', notes: '', seenCount: 0 };
        if (!firstEver) events.push({ type: 'new', key: k, ip: d.ip, cidr: d.cidr, at: now });
      } else {
        if (rec.cidr && rec.cidr !== d.cidr) {
          const mv = { type: 'moved', key: k, from: rec.cidr, to: d.cidr, fromIp: rec.ip, toIp: d.ip, at: now };
          events.push(mv); rec.moved = mv;
        } else if (rec.ip && rec.ip !== d.ip) events.push({ type: 'ip-changed', key: k, from: rec.ip, to: d.ip, at: now });
        if (prev && !prevKeys.has(k) && rec.online === false) events.push({ type: 'back', key: k, ip: d.ip, at: now });
        rec.missed = 0;
      }
      Object.assign(rec, {
        mac: d.mac || rec.mac || '', ip: d.ip, cidr: d.cidr, gateway: d.gateway,
        hostname: d.hostname || rec.hostname || '', vendor: d.vendor || rec.vendor || '', kind: d.kind, autoName: d.autoName,
        randomMac: d.randomMac, responds: d.responds, rtt: d.rtt, ttl: d.ttl, open: d.open, services: d.services, upnp: d.upnp,
        roku: d.roku || null, cast: d.cast || null, isSelf: d.isSelf, isGateway: d.isGateway, nestedRouter: d.nestedRouter,
        possibleRouter: d.possibleRouter, routerMatch: d.routerMatch, lastSeen: now, seenCount: (rec.seenCount || 0) + 1, online: true
      });
    }
    for (const rec of Object.values(db.devices)) {
      if (rec.manual || seen.has(rec.key)) continue;
      if (!scanned.includes(rec.cidr)) { rec.online = false; continue; } // network no longer exists
      rec.missed = (rec.missed || 0) + 1;
      if (rec.missed >= 2 && rec.online) { events.push({ type: 'gone', key: rec.key, ip: rec.ip, at: now }); rec.online = false; }
    }
    // tidy up: an IP-only record (seen across a router, no MAC) is replaced by the real device now seen at that IP
    for (const d of devices) {
      if (!d.mac) continue;
      const k = 'ip:' + d.ip;
      if (!db.devices[k] || k === d.key || !db.devices[d.key]) continue;
      const a = db.devices[k], b = db.devices[d.key];
      for (const f of ['label', 'router', 'room', 'notes', 'kindOverride']) if (!b[f] && a[f]) b[f] = a[f];
      b.firstSeen = Math.min(a.firstSeen || now, b.firstSeen || now);
      db.aliases[k] = d.key;
      delete db.devices[k];
    }
    history.scans.push({
      id: scanId, at: now, trigger, ms: now - scanState.startedAt,
      networks: subnets.map(s => ({ cidr: s.cidr, gateway: s.gateway, iface: s.iface, hostIp: s.hostIp, upstream: !!s.upstream })),
      upstream,
      nested: devices.filter(d => d.nestedRouter).map(d => ({ ip: d.ip, key: d.key, router: d.routerMatch })),
      devices: devices.map(d => [d.key, d.ip, d.cidr, d.responds ? 1 : 0]),
      events
    });
    if (history.scans.length > 3000) history.scans.splice(0, history.scans.length - 3000);
    db.events.push(...events.map(e => ({ ...e, scan: scanId })));
    if (db.events.length > 1500) db.events.splice(0, db.events.length - 1500);
    autoMaintain(subnets, upstream, devices);
    saveDb(); saveHistory();
  } catch (e) {
    scanState.error = String((e && e.stack) || e);
    console.error('[network-map] scan failed', e);
  } finally {
    scanState.running = false; scanState.finishedAt = Date.now(); scanState.phase = 'idle';
  }
}

/* ------------------------------------------------------------------ auto maintenance */
function autoMaintain(subnets, upstream, devices) {
  const mine = new Set(localIps());
  // records for this PC's other adapters (Wi-Fi etc.) are folded into the PC
  const self = Object.values(db.devices).find(d => d.isSelf && d.online);
  for (const d of Object.values(db.devices)) {
    if (d.isSelf || d.manual || !mine.has(d.ip)) continue;
    if (self) db.aliases[d.key] = self.key;
    delete db.devices[d.key];
  }
  // IP-only leftovers replaced by a real device at the same IP
  for (const a of Object.values(db.devices)) {
    if (!a.key.startsWith('ip:')) continue;
    const b = Object.values(db.devices).find(x => x.mac && x.ip === a.ip && x.key !== a.key && x.online);
    if (!b) continue;
    for (const f of ['label', 'router', 'room', 'notes', 'kindOverride']) if (!b[f] && a[f]) b[f] = a[f];
    db.aliases[a.key] = b.key; delete db.devices[a.key];
  }
  // if the main router is our gateway and no second router shows up anywhere, the other routers must be access points
  const gwRouter = settings.routers.find(r => subnets.some(s => s.gateway && s.gateway === r.lanIp));
  const nested = devices.some(d => d.nestedRouter);
  if (gwRouter && gwRouter.role === 'main' && !upstream && !nested) {
    let changed = false;
    for (const r of settings.routers) if (r !== gwRouter && r.mode !== 'ap') { r.mode = 'ap'; changed = true; }
    if (changed) saveSettings();
  }
  // remember extra adapters on this PC so the UI can mention them
  db.selfExtraIps = [...mine].filter(ip => ip !== '127.0.0.1' && !ip.startsWith('169.254.') && !subnets.some(s => s.hostIp === ip) && subnets.some(s => inSubnet(ip, s.cidr)));
}

/* ------------------------------------------------------------------ network analysis */
function analysis() {
  const last = history.scans[history.scans.length - 1];
  const devs = Object.values(db.devices);
  const networks = [];
  if (last) for (const n of last.networks) {
    const gwDev = devs.find(d => d.ip === n.gateway && d.cidr === n.cidr);
    const r = (gwDev && gwDev.routerMatch && settings.routers.find(x => x.id === gwDev.routerMatch)) || settings.routers.find(x => x.lanIp === n.gateway);
    networks.push({ cidr: n.cidr, gateway: n.gateway, iface: n.iface, hostIp: n.hostIp, router: r ? r.id : null, scannable: true, upstream: !!n.upstream });
  }
  let upstream = null;
  if (last && last.upstream) {
    const r = settings.routers.find(x => x.lanIp === last.upstream.ip);
    const below = networks.find(n => !n.upstream && n.gateway === last.upstream.via);
    upstream = { ...last.upstream, router: r ? r.id : null, belowRouter: below ? below.router : null, belowCidr: below ? below.cidr : null };
    if (!networks.find(n => n.cidr === last.upstream.cidr)) networks.push({ cidr: last.upstream.cidr, gateway: last.upstream.ip, router: upstream.router, scannable: false, upstream: true });
  }
  // networks hidden behind a second router
  const nested = devs.filter(d => d.nestedRouter && d.online);
  for (const d of nested) {
    const r = settings.routers.find(x => x.id === d.routerMatch);
    const lan = r && isIPv4(r.lanIp) ? netOf(r.lanIp, 24) + '/24' : null;
    if (lan && networks.find(n => n.cidr === lan && n.scannable)) continue;
    networks.push({ cidr: lan, gateway: r ? r.lanIp : null, router: r ? r.id : null, via: d.key, viaIp: d.ip, scannable: false });
  }
  // networks known only from manual entries
  for (const d of devs.filter(x => x.manual && x.cidr)) {
    if (!networks.find(n => n.cidr === d.cidr)) networks.push({ cidr: d.cidr, gateway: null, router: d.router || null, scannable: false, manualOnly: true });
  }
  const multi = networks.length > 1;
  const doubleNat = nested.length > 0 || !!upstream || !!(db.lastDoubleNat && db.lastDoubleNat.pcDoubleNat);
  const moved = devs.filter(d => d.moved && !d.moved.acked);
  return { selfExtraIps: db.selfExtraIps || [], networks, multi, doubleNat, upstream, nestedRouters: nested.map(d => ({ key: d.key, ip: d.ip, router: d.routerMatch })), movedCount: moved.length, possibleRouters: devs.filter(d => d.possibleRouter && d.online).map(d => d.key) };
}

/* ------------------------------------------------------------------ double NAT check */
async function traceroute(target = '1.1.1.1', maxHops = 6) {
  const t = IS_WIN ? await run('tracert', ['-d', '-h', String(maxHops), '-w', '800', target], 40000)
    : await run('traceroute', ['-n', '-m', String(maxHops), '-w', '1', '-q', '1', target], 30000);
  const hops = [];
  for (const line of t.split(/\r?\n/)) {
    const m = line.match(/^\s*(\d+)\s+(.*)$/);
    if (!m) continue;
    const ip = (m[2].match(/(\d+\.\d+\.\d+\.\d+)/) || [])[1] || null;
    const ms = (m[2].match(/<?(\d+)\s*ms/) || [])[1];
    hops.push({ hop: +m[1], ip, ms: ms ? +ms : null });
  }
  return hops;
}
async function doubleNatCheck() {
  const res = { at: Date.now() };
  const nets = (await getNetworks()).filter(n => n.gateway && !n.virtual);
  res.gateway = nets[0] ? nets[0].gateway : null;
  const [pub, igd, hops] = await Promise.all([
    httpRequest('https://api.ipify.org?format=json', { timeout: 5000 }),
    findIgd(true),
    traceroute()
  ]);
  try { res.publicIp = JSON.parse(pub.body).ip; } catch { res.publicIp = null; }
  if (igd) {
    res.igd = { ip: igd.ip, name: igd.friendlyName, model: igd.modelName, isGateway: igd.isGateway };
    const r = await soap(igd.controlURL, igd.serviceType, 'GetExternalIPAddress');
    res.routerWanIp = r && r.status === 200 ? xmlTag(r.body, 'NewExternalIPAddress') : null;
  }
  res.hops = hops;
  // count only the private hops at the start of the path (inside the home), stop at the first public hop
  const privHops = [];
  for (const h of hops) { if (!h.ip) continue; if (isRfc1918(h.ip)) privHops.push(h); else break; }
  res.privateHops = privHops.length;
  res.cgnat = hops.some(h => h.ip && isCgnat(h.ip)) || !!(res.routerWanIp && isCgnat(res.routerWanIp));
  res.pcDoubleNat = privHops.length >= 2 || !!(res.routerWanIp && isRfc1918(res.routerWanIp));
  res.nested = Object.values(db.devices).filter(d => d.nestedRouter && d.online).map(d => ({ ip: d.ip, router: d.routerMatch, name: d.label || d.autoName }));
  db.lastDoubleNat = res; saveDb();
  return res;
}

/* ------------------------------------------------------------------ UPnP port forwarding */
async function upnpList() {
  const igd = await findIgd(true);
  if (!igd) return { ok: false, reason: 'No router answered UPnP. UPnP is probably turned off on the den router, or it doesn’t support UPnP port mapping. Turn UPnP on in its admin page, or add forwards there by hand.' };
  const ext = await soap(igd.controlURL, igd.serviceType, 'GetExternalIPAddress');
  const mappings = [];
  for (let i = 0; i < 128; i++) {
    const r = await soap(igd.controlURL, igd.serviceType, 'GetGenericPortMappingEntry', { NewPortMappingIndex: i });
    if (!r || r.status !== 200) break;
    mappings.push({
      remoteHost: xmlTag(r.body, 'NewRemoteHost'), externalPort: +xmlTag(r.body, 'NewExternalPort'), protocol: xmlTag(r.body, 'NewProtocol'),
      internalPort: +xmlTag(r.body, 'NewInternalPort'), internalClient: xmlTag(r.body, 'NewInternalClient'),
      enabled: xmlTag(r.body, 'NewEnabled') !== '0', description: xmlTag(r.body, 'NewPortMappingDescription'), lease: +xmlTag(r.body, 'NewLeaseDuration') || 0
    });
  }
  return {
    ok: true, externalIp: ext && ext.status === 200 ? xmlTag(ext.body, 'NewExternalIPAddress') : null,
    igd: { ip: igd.ip, name: igd.friendlyName, model: igd.modelName, isGateway: igd.isGateway }, mappings
  };
}
function soapError(r) { return r ? (xmlTag(r.body, 'errorDescription') || `HTTP ${r.status}`) : 'No response from router'; }

/* ------------------------------------------------------------------ Wi-Fi survey (Windows) */
async function wifiSurvey() {
  if (!IS_WIN) return { ok: false, reason: 'The Wi-Fi survey only works when this app runs on Windows.' };
  const [iface, nets] = await Promise.all([run('netsh', ['wlan', 'show', 'interfaces']), run('netsh', ['wlan', 'show', 'networks', 'mode=bssid'], 12000)]);
  const both = iface + '\n' + nets;
  if (/no wireless interface|wlansvc.*not running|Wireless AutoConfig Service.*not running/i.test(both))
    return { ok: false, reason: 'This PC has no Wi-Fi adapter (or Wi-Fi is off), so it can’t see nearby channels. Use the Speed tab from your phone in each room instead.' };
  if (/location/i.test(nets) && !/SSID \d+\s*:/.test(nets))
    return { ok: false, reason: 'Windows is blocking Wi-Fi scanning. Turn on Location services (Settings → Privacy & security → Location, and allow desktop apps), then try again.' };
  const cur = {};
  for (const line of iface.split(/\r?\n/)) {
    let m;
    if ((m = line.match(/^\s*SSID\s+:\s*(.*)$/))) cur.ssid = m[1].trim();
    else if ((m = line.match(/^\s*Signal\s*:\s*(\d+)%/))) cur.signal = +m[1];
    else if ((m = line.match(/^\s*Channel\s*:\s*(\d+)/))) cur.channel = +m[1];
    else if ((m = line.match(/^\s*Radio type\s*:\s*(.+)$/))) cur.radio = m[1].trim();
    else if ((m = line.match(/^\s*Band\s*:\s*(.+)$/))) cur.band = m[1].trim();
    else if ((m = line.match(/Receive rate \(Mbps\)\s*:\s*([\d.]+)/))) cur.rx = +m[1];
    else if ((m = line.match(/Transmit rate \(Mbps\)\s*:\s*([\d.]+)/))) cur.tx = +m[1];
    else if ((m = line.match(/^\s*State\s*:\s*(.+)$/))) cur.state = m[1].trim();
  }
  const aps = []; let ssid = null, ap = null;
  for (const line of nets.split(/\r?\n/)) {
    let m;
    if ((m = line.match(/^SSID \d+\s*:\s*(.*)$/))) { ssid = m[1].trim(); ap = null; }
    else if ((m = line.match(/^\s*BSSID \d+\s*:\s*(\S+)/))) { ap = { ssid, bssid: m[1].toLowerCase(), signal: 0, channel: 0, band: '', radio: '' }; aps.push(ap); }
    else if (ap && (m = line.match(/^\s*Signal\s*:\s*(\d+)%/))) ap.signal = +m[1];
    else if (ap && (m = line.match(/^\s*Channel\s*:\s*(\d+)/))) ap.channel = +m[1];
    else if (ap && (m = line.match(/^\s*Band\s*:\s*(.+)$/))) ap.band = m[1].trim();
    else if (ap && (m = line.match(/^\s*Radio type\s*:\s*(.+)$/))) ap.radio = m[1].trim();
  }
  for (const a of aps) if (!a.band) a.band = a.channel && a.channel <= 14 ? '2.4 GHz' : '5 GHz';
  const mine = new Set(settings.routers.map(r => (r.ssid || '').toLowerCase()).filter(Boolean));
  const two = aps.filter(a => a.band.startsWith('2.4'));
  const score = (ch, excludeBssid) => two.filter(a => a.bssid !== excludeBssid).reduce((s, a) => {
    const d = Math.abs(a.channel - ch); return d < 5 ? s + (a.signal / 100) * (5 - d) / 5 : s;
  }, 0);
  const advice = [];
  const own = aps.filter(a => mine.has((a.ssid || '').toLowerCase()));
  for (const a of own.filter(x => x.band.startsWith('2.4'))) {
    const opts = [1, 6, 11].map(ch => ({ ch, score: score(ch, a.bssid) })).sort((x, y) => x.score - y.score);
    const curScore = score(a.channel, a.bssid);
    a.best = opts[0].ch;
    if (opts[0].ch !== a.channel && curScore - opts[0].score > 0.3) advice.push(`"${a.ssid}" 2.4 GHz is on channel ${a.channel}; channel ${opts[0].ch} is less crowded here.`);
  }
  const own24 = own.filter(x => x.band.startsWith('2.4'));
  for (let i = 0; i < own24.length; i++) for (let j = i + 1; j < own24.length; j++) {
    if (own24[i].ssid !== own24[j].ssid && Math.abs(own24[i].channel - own24[j].channel) < 5)
      advice.push(`"${own24[i].ssid}" and "${own24[j].ssid}" overlap on 2.4 GHz (channels ${own24[i].channel} and ${own24[j].channel}). Put one on 1 and the other on 11.`);
  }
  const own5 = own.filter(x => !x.band.startsWith('2.4'));
  for (let i = 0; i < own5.length; i++) for (let j = i + 1; j < own5.length; j++) {
    if (own5[i].ssid !== own5[j].ssid && own5[i].channel === own5[j].channel)
      advice.push(`"${own5[i].ssid}" and "${own5[j].ssid}" share 5 GHz channel ${own5[i].channel}. Move one (for example 36 and 149).`);
  }
  if (!own.length) advice.push('Neither of your Wi-Fi names showed up in the scan from this PC. Check the Wi-Fi names in the Routers tab.');
  return { ok: true, at: Date.now(), current: cur, aps: aps.sort((a, b) => b.signal - a.signal), advice, mine: [...mine] };
}

/* ------------------------------------------------------------------ internet speed (from this PC) */
const keepAgent = new https.Agent({ keepAlive: true, maxSockets: 8 });
function streamDown(url, deadline, counter) {
  return new Promise(res => {
    const req = https.get(url, { agent: keepAgent }, r => {
      r.on('data', c => { counter.bytes += c.length; if (Date.now() > deadline) req.destroy(); });
      r.on('end', res); r.on('error', res); r.on('close', res);
    });
    req.on('error', res);
    req.setTimeout(20000, () => req.destroy());
  });
}
function streamUp(url, bytes, deadline, counter) {
  return new Promise(res => {
    const req = https.request(url, { method: 'POST', agent: keepAgent, headers: { 'Content-Type': 'application/octet-stream', 'Content-Length': bytes } }, r => { r.resume(); r.on('end', res); r.on('error', res); });
    req.on('error', res);
    req.setTimeout(20000, () => req.destroy());
    const chunk = crypto.randomBytes(64 * 1024);
    let sent = 0;
    const pump = () => {
      while (sent < bytes) {
        if (Date.now() > deadline) { req.destroy(); return res(); }
        const n = Math.min(chunk.length, bytes - sent);
        sent += n; counter.bytes += n;
        if (!req.write(n === chunk.length ? chunk : chunk.subarray(0, n))) { req.once('drain', pump); return; }
      }
      req.end();
    };
    pump();
  });
}
async function internetSpeed() {
  const lat = [];
  await httpRequest('https://speed.cloudflare.com/__down?bytes=0', { timeout: 5000, agent: keepAgent });
  for (let i = 0; i < 6; i++) {
    const t = process.hrtime.bigint();
    const r = await httpRequest('https://speed.cloudflare.com/__down?bytes=0', { timeout: 4000, agent: keepAgent });
    if (r) lat.push(Number(process.hrtime.bigint() - t) / 1e6);
  }
  const dc = { bytes: 0 }; let t0 = Date.now();
  await Promise.all(Array.from({ length: 4 }, () => streamDown('https://speed.cloudflare.com/__down?bytes=50000000', t0 + 8000, dc)));
  const downSec = (Date.now() - t0) / 1000;
  const uc = { bytes: 0 }; t0 = Date.now();
  await Promise.all(Array.from({ length: 4 }, () => streamUp('https://speed.cloudflare.com/__up', 15e6, t0 + 8000, uc)));
  const upSec = (Date.now() - t0) / 1000;
  if (!lat.length && !dc.bytes) return { ok: false, reason: 'Couldn’t reach the speed test server.' };
  return {
    ok: true, ping: lat.length ? Math.round(median(lat)) : null,
    down: +(dc.bytes * 8 / downSec / 1e6).toFixed(1), up: +(uc.bytes * 8 / upSec / 1e6).toFixed(1)
  };
}

/* ------------------------------------------------------------------ who is asking */
async function whoIs(ipRaw) {
  let ip = (ipRaw || '').replace(/^::ffff:/, '');
  if (ip === '::1') ip = '127.0.0.1';
  const self = ip === '127.0.0.1' || localIps().includes(ip);
  const devs = Object.values(db.devices);
  let dev = devs.find(d => d.ip === ip && !d.manual && d.online !== false) || null;
  let viaRouter = null;
  if (!self) {
    let mac = dev && dev.mac;
    if (!mac) { const arp = await readArp(); mac = arp.get(ip) || ''; }
    const r = matchRouter({ mac, ip, isGateway: false });
    if (r && r.mode !== 'ap') viaRouter = r;
    else if (dev && dev.nestedRouter) viaRouter = settings.routers.find(x => x.id === dev.routerMatch) || { id: null, name: 'another router' };
  }
  const nets = await getNetworks();
  const netw = nets.find(n => inSubnet(ip, n.cidr));
  return {
    ip, self, network: netw ? netw.cidr : null,
    device: dev && !viaRouter ? { key: dev.key, name: dev.label || dev.autoName, kind: dev.kind } : null,
    viaRouter: viaRouter ? { id: viaRouter.id, name: viaRouter.name, ssid: viaRouter.ssid, lanIp: viaRouter.lanIp } : null
  };
}

/* ------------------------------------------------------------------ HTTP API */
const app = express();
app.disable('x-powered-by');
app.use(express.json({ limit: '2mb' }));
// App icons are kept here as text because Server Hub copies app files as text
const ICONS = {
  '/icon-192.png': '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',
  '/icon-512.png': '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'
};
for (const [route, b64] of Object.entries(ICONS)) {
  const buf = Buffer.from(b64, 'base64');
  app.get(route, (req, res) => { res.set({ 'Content-Type': 'image/png', 'Cache-Control': 'public, max-age=86400' }); res.end(buf); });
}
app.get('/favicon.ico', (req, res) => res.redirect(301, '/icon-192.png'));
app.use(express.static(path.join(APP_DIR, 'public'), { extensions: ['html'] }));

const publicDevice = d => d;
app.get('/api/state', async (req, res) => {
  const who = await whoIs(req.socket.remoteAddress);
  res.json({
    settings, scanState, who, analysis: analysis(), lastDoubleNat: db.lastDoubleNat,
    lastScan: history.scans.length ? (({ devices, ...rest }) => ({ ...rest, count: devices.length }))(history.scans[history.scans.length - 1]) : null,
    scanCount: history.scans.length,
    devices: Object.values(db.devices).map(publicDevice),
    events: db.events.slice(-150).reverse(),
    platform: process.platform, port: PORT,
    urls: localIps().filter(ip => ip !== '127.0.0.1' && !ip.startsWith('169.254.')).map(ip => `http://${ip}:${PORT}`)
  });
});
app.post('/api/scan', (req, res) => { if (!scanState.running) runScan('manual'); res.json(scanState); });
app.get('/api/scan/status', (req, res) => res.json(scanState));

app.patch('/api/devices/:key', (req, res) => {
  const rec = db.devices[resolveKey(req.params.key)];
  if (!rec) return res.status(404).json({ error: 'Unknown device' });
  for (const f of ['label', 'router', 'room', 'notes', 'kindOverride', 'hidden', 'ip', 'cidr', 'mac']) {
    if (f in req.body) {
      if ((f === 'ip' || f === 'cidr' || f === 'mac') && !rec.manual) continue;
      rec[f] = typeof req.body[f] === 'string' ? req.body[f].slice(0, 200) : req.body[f];
    }
  }
  if (rec.manual && rec.ip && isIPv4(rec.ip) && !req.body.cidr) rec.cidr = netOf(rec.ip, 24) + '/24';
  saveDb(); res.json(rec);
});
app.post('/api/devices/:key/ack', (req, res) => {
  const rec = db.devices[resolveKey(req.params.key)];
  if (rec && rec.moved) rec.moved.acked = true;
  saveDb(); res.json({ ok: true });
});
app.post('/api/moved/ack-all', (req, res) => {
  let n = 0;
  for (const d of Object.values(db.devices)) if (d.moved && !d.moved.acked) { d.moved.acked = true; n++; }
  saveDb(); res.json({ ok: true, count: n });
});
app.post('/api/cleanup', (req, res) => {
  const last = history.scans[history.scans.length - 1];
  const live = new Set(last ? last.networks.map(n => n.cidr) : []);
  let merged = 0, forgotten = 0;
  for (const a of Object.values(db.devices)) {
    if (!a.key.startsWith('ip:') || !db.devices[a.key]) continue;
    const b = Object.values(db.devices).find(x => x.mac && x.ip === a.ip && x.key !== a.key);
    if (b) {
      for (const f of ['label', 'router', 'room', 'notes', 'kindOverride']) if (!b[f] && a[f]) b[f] = a[f];
      db.aliases[a.key] = b.key; delete db.devices[a.key]; merged++;
    }
  }
  for (const d of Object.values(db.devices)) if (!d.manual && d.cidr && !live.has(d.cidr)) d.online = false;
  if (req.body && req.body.forgetOld) for (const d of Object.values(db.devices)) {
    if (!d.manual && !d.online && !d.label && d.cidr && !live.has(d.cidr)) { delete db.devices[d.key]; forgotten++; }
  }
  saveDb(); res.json({ ok: true, merged, forgotten });
});
app.post('/api/devices/:key/merge', (req, res) => {
  const from = resolveKey(req.params.key), into = resolveKey(req.body.into || '');
  if (!db.devices[from] || !db.devices[into] || from === into) return res.status(400).json({ error: 'Pick two different devices' });
  const a = db.devices[from], b = db.devices[into];
  for (const f of ['label', 'router', 'room', 'notes', 'kindOverride']) if (!b[f] && a[f]) b[f] = a[f];
  b.firstSeen = Math.min(a.firstSeen || Date.now(), b.firstSeen || Date.now());
  b.otherMacs = [...new Set([...(b.otherMacs || []), ...(a.otherMacs || []), a.mac].filter(Boolean))];
  db.aliases[from] = into;
  for (const [k, v] of Object.entries(db.aliases)) if (v === from) db.aliases[k] = into;
  delete db.devices[from];
  saveDb(); res.json(b);
});
app.delete('/api/devices/:key', (req, res) => {
  const k = resolveKey(req.params.key);
  delete db.devices[k];
  for (const [a, v] of Object.entries(db.aliases)) if (v === k) delete db.aliases[a];
  saveDb(); res.json({ ok: true });
});
app.post('/api/devices', (req, res) => {
  const b = req.body || {};
  if (!b.label) return res.status(400).json({ error: 'Give it a name' });
  if (b.ip && !isIPv4(b.ip)) return res.status(400).json({ error: 'That IP address doesn’t look right' });
  const key = 'manual:' + crypto.randomBytes(4).toString('hex');
  db.devices[key] = {
    key, manual: true, label: String(b.label).slice(0, 100), ip: b.ip || '', cidr: b.ip ? netOf(b.ip, 24) + '/24' : '',
    mac: normMac(b.mac), vendor: shortVendor(vendorOf(normMac(b.mac))), router: b.router || '', room: b.room || '', notes: b.notes || '',
    kind: b.kind || 'Added by hand', autoName: b.label, firstSeen: Date.now(), lastSeen: null, online: null, open: [], services: [], upnp: []
  };
  saveDb(); res.json(db.devices[key]);
});

app.get('/api/history', (req, res) => {
  const limit = Math.min(500, +req.query.limit || 150);
  res.json(history.scans.slice(-limit).reverse().map(s => {
    const per = {};
    for (const d of s.devices) per[d[2]] = (per[d[2]] || 0) + 1;
    return { id: s.id, at: s.at, trigger: s.trigger, ms: s.ms, networks: s.networks, nested: s.nested, perNetwork: per, total: s.devices.length, events: s.events };
  }));
});
app.get('/api/history/device/:key', (req, res) => {
  const k = resolveKey(req.params.key);
  const keys = new Set([k, ...Object.entries(db.aliases).filter(([, v]) => v === k).map(([a]) => a)]);
  const out = history.scans.slice(-(Math.min(1000, +req.query.limit || 96))).map(s => {
    const hit = s.devices.find(d => keys.has(d[0]));
    return hit ? { at: s.at, ip: hit[1], cidr: hit[2], responds: !!hit[3] } : { at: s.at, absent: true };
  });
  res.json(out);
});

app.get('/api/ping', (req, res) => res.json({ app: 'network-map', name: 'Network Map', version: require('./package.json').version }));

/* ---- which router is the phone app connected to (it sends the Wi-Fi BSSID it sees) ---- */
const macBytes = m => ((m || '').toLowerCase().match(/[0-9a-f]{2}/g) || []).map(h => parseInt(h, 16));
function matchBssid(bssid) {
  const b = normMac(bssid);
  if (!b || b === '02:00:00:00:00:00') return null;
  const exact = settings.routers.find(r => (r.bssids || []).includes(b));
  if (exact) return { router: exact, how: 'learned' };
  const bb = macBytes(b);
  for (const r of settings.routers) {
    const h = macBytes(r.macHint);
    if (h.length < 4) continue;
    // Wi-Fi radios use addresses next to the router's own MAC; the first byte may have the "local" bit set
    if ((h[0] & 0xfd) === (bb[0] & 0xfd) && h.slice(1).every((x, i) => x === bb[i + 1])) return { router: r, how: 'mac' };
  }
  return null;
}
function setDeviceRouter(ip, routerId, bssid) {
  const dev = Object.values(db.devices).find(d => d.ip === ip && !d.manual && d.online !== false);
  if (!dev) return null;
  dev.router = routerId;
  dev.routerAuto = { at: Date.now(), bssid, via: 'app' };
  saveDb();
  return dev.key;
}
app.post('/api/whereami', async (req, res) => {
  const b = req.body || {};
  const ip = (req.socket.remoteAddress || '').replace(/^::ffff:/, '');
  const bssid = normMac(b.bssid);
  const m = matchBssid(bssid);
  const deviceKey = m ? setDeviceRouter(ip, m.router.id, bssid) : null;
  res.json({ bssid, ssid: String(b.ssid || '').slice(0, 40), router: m ? m.router.id : null, how: m ? m.how : null, deviceKey });
});
app.post('/api/routers/:id/bssid', (req, res) => {
  const bssid = normMac((req.body || {}).bssid);
  const r = settings.routers.find(x => x.id === req.params.id);
  if (!r || !bssid) return res.status(400).json({ error: 'Unknown router or Wi-Fi address' });
  for (const x of settings.routers) x.bssids = (x.bssids || []).filter(v => v !== bssid);
  r.bssids = [...(r.bssids || []), bssid].slice(-16);
  saveSettings();
  const ip = (req.socket.remoteAddress || '').replace(/^::ffff:/, '');
  res.json({ ok: true, router: r.id, deviceKey: setDeviceRouter(ip, r.id, bssid) });
});

app.get('/api/settings', (req, res) => res.json(settings));
app.put('/api/settings', (req, res) => {
  const b = req.body || {};
  if ('scanUpstream' in b) settings.scanUpstream = !!b.scanUpstream;
  if ('autoScanMinutes' in b) settings.autoScanMinutes = Math.max(0, Math.min(1440, +b.autoScanMinutes || 0));
  if (Array.isArray(b.extraSubnets)) settings.extraSubnets = b.extraSubnets.map(String).filter(x => /^\d+\.\d+\.\d+\.\d+\/\d+$/.test(x)).slice(0, 8);
  const oldRouters = settings.routers;
  if (Array.isArray(b.routers)) settings.routers = b.routers.slice(0, 8).map((r, i) => ({
    bssids: (Array.isArray(r.bssids) ? r.bssids : ((oldRouters.find(o => o.id === r.id) || {}).bssids || [])).map(normMac).filter(Boolean).slice(0, 16),
    id: String(r.id || 'r' + i).slice(0, 30), name: String(r.name || 'Router').slice(0, 60), model: String(r.model || '').slice(0, 80),
    room: String(r.room || '').slice(0, 40), ssid: String(r.ssid || '').slice(0, 40), lanIp: isIPv4(r.lanIp) ? r.lanIp : '',
    mode: r.mode === 'ap' ? 'ap' : 'router', role: r.role === 'main' ? 'main' : 'second',
    macHint: String(r.macHint || '').toLowerCase().replace(/[^0-9a-f:]/g, '').slice(0, 17), notes: String(r.notes || '').slice(0, 300)
  }));
  saveSettings(); scheduleAuto();
  // re-evaluate router matching on stored devices
  for (const d of Object.values(db.devices)) {
    if (d.manual) continue;
    const r = matchRouter(d);
    d.routerMatch = r ? r.id : null;
    const igd = (d.upnp || []).some(u => u.igd);
    d.nestedRouter = !d.isGateway && !d.isSelf && (igd || !!(r && r.mode !== 'ap'));
  }
  saveDb();
  res.json(settings);
});

app.post('/api/doublenat', async (req, res) => res.json(await doubleNatCheck()));
app.get('/api/upnp', async (req, res) => res.json(await upnpList()));
app.post('/api/upnp/add', async (req, res) => {
  const b = req.body || {};
  const igd = await findIgd();
  if (!igd) return res.status(400).json({ error: 'No UPnP router found' });
  const ext = +b.externalPort, int = +b.internalPort || ext, proto = b.protocol === 'UDP' ? 'UDP' : 'TCP';
  if (!(ext > 0 && ext < 65536) || !(int > 0 && int < 65536) || !isIPv4(b.internalClient)) return res.status(400).json({ error: 'Check the ports and device IP' });
  const r = await soap(igd.controlURL, igd.serviceType, 'AddPortMapping', {
    NewRemoteHost: '', NewExternalPort: ext, NewProtocol: proto, NewInternalPort: int, NewInternalClient: b.internalClient,
    NewEnabled: 1, NewPortMappingDescription: String(b.description || 'Network Map').slice(0, 60), NewLeaseDuration: 0
  });
  if (!r || r.status !== 200) return res.status(400).json({ error: soapError(r) });
  res.json({ ok: true });
});
app.post('/api/upnp/delete', async (req, res) => {
  const b = req.body || {};
  const igd = await findIgd();
  if (!igd) return res.status(400).json({ error: 'No UPnP router found' });
  const r = await soap(igd.controlURL, igd.serviceType, 'DeletePortMapping', { NewRemoteHost: b.remoteHost || '', NewExternalPort: +b.externalPort, NewProtocol: b.protocol === 'UDP' ? 'UDP' : 'TCP' });
  if (!r || r.status !== 200) return res.status(400).json({ error: soapError(r) });
  res.json({ ok: true });
});

app.get('/api/wifi', async (req, res) => res.json(await wifiSurvey()));

const RAND = crypto.randomBytes(1 << 20);
app.get('/api/speed/ping', (req, res) => { res.set('Cache-Control', 'no-store'); res.end('ok'); });
app.get('/api/speed/down', (req, res) => {
  const mb = Math.min(500, Math.max(1, Math.floor(+req.query.mb || 50)));
  res.set({ 'Content-Type': 'application/octet-stream', 'Content-Length': mb * RAND.length, 'Cache-Control': 'no-store' });
  let sent = 0, closed = false;
  req.on('close', () => { closed = true; });
  const write = () => {
    while (sent < mb && !closed) { sent++; if (!res.write(RAND)) { res.once('drain', write); return; } }
    res.end();
  };
  write();
});
app.post('/api/speed/up', (req, res) => {
  let bytes = 0; const t = Date.now();
  req.on('data', c => { bytes += c.length; });
  req.on('end', () => res.json({ bytes, ms: Date.now() - t }));
});
app.post('/api/speed/internet', async (req, res) => {
  const r = await internetSpeed();
  if (r.ok) { history.speed.push({ at: Date.now(), kind: 'internet', where: 'This PC (wired)', ...r }); history.speed = history.speed.slice(-500); saveHistory(); }
  res.json(r);
});
app.post('/api/speed/results', async (req, res) => {
  const b = req.body || {};
  const who = await whoIs(req.socket.remoteAddress);
  const where = who.self ? 'This PC' : who.viaRouter ? `Through ${who.viaRouter.name}${who.viaRouter.ssid ? ` ("${who.viaRouter.ssid}")` : ''}` : `On ${who.network || 'main network'}`;
  const rec = { at: Date.now(), kind: 'lan', where, label: String(b.label || '').slice(0, 60), down: +b.down || 0, up: +b.up || 0, ping: +b.ping || 0, ip: who.ip };
  history.speed.push(rec); history.speed = history.speed.slice(-500); saveHistory();
  res.json(rec);
});
app.get('/api/speed/results', (req, res) => res.json(history.speed.slice(-200).reverse()));

app.get('/api/export', (req, res) => {
  res.set('Content-Disposition', `attachment; filename="network-map-${new Date().toISOString().slice(0, 10)}.json"`);
  res.json({ exportedAt: new Date().toISOString(), settings, devices: db.devices, aliases: db.aliases, events: db.events, history });
});

/* ------------------------------------------------------------------ auto-scan + start */
let autoTimer = null;
function scheduleAuto() {
  clearInterval(autoTimer);
  const m = +settings.autoScanMinutes || 0;
  if (m > 0) autoTimer = setInterval(() => runScan('auto'), m * 60000);
}

if (require.main === module) {
  app.listen(PORT, '0.0.0.0', () => {
    console.log(`[network-map] running on port ${PORT}`);
    for (const u of localIps().filter(ip => ip !== '127.0.0.1')) console.log(`  open http://${u}:${PORT}`);
    scheduleAuto();
    setTimeout(() => runScan('startup'), 4000);
  });
}
module.exports = { app, _test: { autoMaintain, getDb: () => db, getSettings: () => settings, parseRoutePrint, parseArp, parseDns, buildDnsQuery, readName, getGateways, readArp, hostsIn, netOf, inSubnet, vendorOf, shortVendor, classify, parseDeviceDesc, xmlTag, isRandomMac, runScan, analysis, getNetworks } };
