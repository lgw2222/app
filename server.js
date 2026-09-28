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
  }
];
const DEFAULT_SETTINGS = { autoScanMinutes: 30, extraSubnets: [], routers: DEFAULT_ROUTERS };

let settings = Object.assign({}, DEFAULT_SETTINGS, readJson('settings.json', {}));
if (!Array.isArray(settings.routers) || !settings.routers.length) settings.routers = DEFAULT_ROUTERS;
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

app.get('/api/settings', (req, res) => res.json(settings));
app.put('/api/settings', (req, res) => {
  const b = req.body || {};
  if ('scanUpstream' in b) settings.scanUpstream = !!b.scanUpstream;
  if ('autoScanMinutes' in b) settings.autoScanMinutes = Math.max(0, Math.min(1440, +b.autoScanMinutes || 0));
  if (Array.isArray(b.extraSubnets)) settings.extraSubnets = b.extraSubnets.map(String).filter(x => /^\d+\.\d+\.\d+\.\d+\/\d+$/.test(x)).slice(0, 8);
  if (Array.isArray(b.routers)) settings.routers = b.routers.slice(0, 8).map((r, i) => ({
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
