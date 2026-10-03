// Tag multiplayer server: static index.html + WebSocket room relay.
// Run: npm install && npm start
'use strict';
const http = require('http'), fs = require('fs'), path = require('path');
const zlib = require('zlib'), crypto = require('crypto');
const { WebSocketServer } = require('ws');

const PORT = process.env.PORT || 3000;
const MAX_ROOM = 5;
const FLUSH_MS = 20;          // position batches go out ~50x/s (clients send ~60x/s: smoother remote players, more precise tags)
const MAX_CONN_PER_IP = 12;
const rooms = new Map();

/* ---------------- static file (cached + gzipped; reloaded automatically if it changes on disk) ---------------- */
const FILE = path.join(__dirname, 'index.html');
let html = null, gz = null, etag = '', mtime = 0;
function loadHtml() {
  try {
    mtime = fs.statSync(FILE).mtimeMs;
    html = fs.readFileSync(FILE);
    gz = zlib.gzipSync(html, { level: 9 });
    etag = '"' + crypto.createHash('sha1').update(html).digest('hex').slice(0, 16) + '"';
  } catch (e) {
    html = null;
    console.error('index.html missing or unreadable:', e.message);
  }
}
loadHtml();

const server = http.createServer((req, res) => {
  const url = (req.url || '/').split('?')[0];

  // Health check (use as Render "Health Check Path" and for uptime pingers).
  if (url === '/healthz') {
    res.writeHead(200, { 'Content-Type': 'text/plain', 'Cache-Control': 'no-store' });
    return res.end('ok');
  }
  if (url === '/favicon.ico') { res.writeHead(204); return res.end(); }
  if (req.method !== 'GET' && req.method !== 'HEAD') { res.writeHead(405); return res.end(); }
  try { if (fs.statSync(FILE).mtimeMs !== mtime) loadHtml(); } catch {}
  if (!html) { res.writeHead(500); return res.end('index.html missing'); }

  const headers = {
    'Content-Type': 'text/html; charset=utf-8',
    'Cache-Control': 'no-cache',
    'ETag': etag,
    'Vary': 'Accept-Encoding',
    'X-Content-Type-Options': 'nosniff',
    'Referrer-Policy': 'no-referrer'
  };
  if (req.headers['if-none-match'] === etag) { res.writeHead(304, headers); return res.end(); }

  const useGz = /\bgzip\b/.test(req.headers['accept-encoding'] || '');
  const body = useGz ? gz : html;
  if (useGz) headers['Content-Encoding'] = 'gzip';
  headers['Content-Length'] = body.length;
  res.writeHead(200, headers);
  res.end(req.method === 'HEAD' ? undefined : body);
});

// Render's proxy keeps connections alive; make sure Node doesn't close them first (avoids sporadic 502s).
server.keepAliveTimeout = 65000;
server.headersTimeout = 66000;

const wss = new WebSocketServer({ server, maxPayload: 8192, perMessageDeflate: false });

/* ---------------- presence validation ---------------- */
const FAST = new Set(['x', 'y', 'vx', 'vy', 'f', 'g', 'ts']);               // high-rate keys, batched
const HOSTKEYS = new Set(['st', 'gm', 'rn', 'ord', 'first', 'loser', 'win', 'rt']); // only the room host may write
const NUM = new Set(['x', 'y', 'vx', 'vy', 'f', 'g', 't0', 'host', 'ci', 'rt', 'gm', 'rn', 'ts']);

function clean(k, v) {
  if (v === null) return null;
  if (NUM.has(k)) return typeof v === 'number' && isFinite(v) && Math.abs(v) < 1e13 ? v : undefined;
  switch (k) {
    case 'nm': return typeof v === 'string' ? v.replace(/[\u0000-\u001f\u007f]/g, '').slice(0, 12) : undefined;
    case 'st': return typeof v === 'string' && v.length <= 8 ? v : undefined;
    case 'first': case 'loser': case 'win':
      return typeof v === 'string' && v.length <= 16 ? v : undefined;
    case 'it': case 'alive':
      return typeof v === 'boolean' || v === 0 || v === 1 ? v : undefined;
    case 'ord':
      return Array.isArray(v) && v.length <= MAX_ROOM && v.every(s => typeof s === 'string' && s.length <= 16) ? v : undefined;
    case 'pn':
      return v && typeof v === 'object' && typeof v.to === 'string' && v.to.length <= 16 &&
        typeof v.n === 'number' && isFinite(v.n) ? { to: v.to, n: v.n } : undefined;
  }
  return undefined; // unknown key -> dropped
}

function send(ws, s, droppable) {
  if (ws.readyState !== 1) return;
  if (ws.bufferedAmount > 1048576) { ws.terminate(); return; }          // hopelessly backed up
  if (droppable && ws.bufferedAmount > 65536) return;                   // skip stale positions on slow links
  ws.send(s);
}

/* ---------------- batched position relay ---------------- */
const pendRooms = new Set();
setInterval(() => {
  for (const r of pendRooms) {
    if (!r.pend.size) continue;
    if (r.size > 1) {
      const u = [];
      for (const [pid, p] of r.pend) u.push([pid, p]);
      const out = JSON.stringify({ t: 'b', u });
      for (const c of r.values()) send(c.ws, out, true);
    }
    r.pend.clear();
  }
  pendRooms.clear();
}, FLUSH_MS);

/* ---------------- connections ---------------- */
const perIp = new Map();

wss.on('connection', (ws, req) => {
  try { req.socket.setNoDelay(true); } catch {}   // no Nagle: send small packets immediately

  const ip = String((req.headers['x-forwarded-for'] || req.socket.remoteAddress || '')).split(',')[0].trim();
  const n = (perIp.get(ip) || 0) + 1;
  if (n > MAX_CONN_PER_IP) { ws.close(); return; }
  perIp.set(ip, n);

  const id = Math.random().toString(36).slice(2, 10);
  ws.lastSeen = Date.now();
  ws.on('pong', () => { ws.lastSeen = Date.now(); });

  let room = null, count = 0, winStart = Date.now();

  const leave = () => {
    if (!room) return;
    room.delete(id);
    room.pend.delete(id);
    if (room.hostId === id) room.hostId = null;

    if (!room.size) {
      rooms.delete(room.name);
    } else {
      const out = JSON.stringify({ t: 'l', id });
      for (const c of room.values()) send(c.ws, out);
    }
    room = null;
  };

  ws.on('message', (raw, isBinary) => {
    const now = Date.now();
    ws.lastSeen = now;
    if (now - winStart >= 1000) { winStart = now; count = 0; }
    if (++count > 150 || isBinary) return;      // per-connection rate limit

    let m;
    try { m = JSON.parse(raw); } catch { return; }
    if (!m || typeof m !== 'object') return;

    if (m.t === 'hb') { if (ws.readyState === 1) ws.send('{"t":"hb"}'); return; }

    // ---- join ----
    if (m.t === 'join' && !room) {
      if (typeof m.room !== 'string' || !/^tag-[a-z0-9]{3,6}$/.test(m.room)) {
        send(ws, '{"t":"err","e":"bad"}'); return ws.close();
      }
      let r = rooms.get(m.room);
      if (!r) {
        r = new Map();
        r.name = m.room;
        r.pend = new Map();
        r.hostId = null;
        rooms.set(m.room, r);
      }
      if (r.size >= MAX_ROOM) {
        send(ws, '{"t":"err","e":"full"}'); return ws.close();
      }

      const others = [...r].map(([oid, c]) => ({ id: oid, p: c.pres }));
      const mine = { ws, pres: {} };
      r.set(id, mine);
      room = r;
      ws.send(JSON.stringify({ t: 'hello', id }));
      ws.send(JSON.stringify({ t: 'full', peers: others.concat({ id, p: mine.pres }) }));
      const j = JSON.stringify({ t: 'j', id, p: mine.pres });
      for (const [oid, c] of r) if (oid !== id) send(c.ws, j);
      return;
    }

    // ---- presence / state ----
    if (m.t === 'pres' && room && m.p && typeof m.p === 'object' && !Array.isArray(m.p)) {
      if (raw.length > 1500) return;
      const me = room.get(id);
      if (!me) return;

      // First client to claim host while the room has none becomes the host.
      if (m.p.host === 1 && room.hostId === null) room.hostId = id;
      const isHost = room.hostId === id;

      const patch = {};
      let slow = false, any = false;
      for (const k of Object.keys(m.p)) {
        if (k === 'host' && m.p.host === 1 && !isHost) continue;      // rejected host claim
        if (HOSTKEYS.has(k) && !isHost) continue;                      // only the host drives game state
        const v = clean(k, m.p[k]);
        if (v === undefined) continue;
        me.pres[k] = v;
        patch[k] = v;
        any = true;
        if (!FAST.has(k)) slow = true;
      }
      if (!any) return;

      if (!slow) {
        // Pure movement: merge into the next batch instead of relaying immediately.
        const prev = room.pend.get(id);
        room.pend.set(id, prev ? Object.assign(prev, patch) : patch);
        pendRooms.add(room);
        return;
      }

      // State change: send now (carrying any queued movement so ordering is preserved).
      const q = room.pend.get(id);
      if (q) { Object.assign(q, patch); room.pend.delete(id); Object.assign(patch, q); }
      const out = JSON.stringify({ t: 'u', id, p: patch });
      for (const c of room.values()) send(c.ws, out);
    }
  });

  ws.on('close', () => {
    const left = (perIp.get(ip) || 1) - 1;
    if (left <= 0) perIp.delete(ip); else perIp.set(ip, left);
    leave();
  });

  ws.on('error', () => {});
});

// Drop dead connections (closed browser, lost signal, frozen tab) so ghost players disappear.
setInterval(() => {
  const now = Date.now();
  for (const ws of wss.clients) {
    if (now - ws.lastSeen > 15000) { ws.terminate(); continue; }
    try { ws.ping(); } catch {}
  }
}, 5000);

/* ---------------- lifecycle ---------------- */
server.listen(PORT, '0.0.0.0', () => {
  console.log('Tag multiplayer server running on port ' + PORT);
});

function shutdown() {
  console.log('Shutting down...');
  for (const ws of wss.clients) { try { ws.close(1001); } catch {} }
  server.close(() => process.exit(0));
  setTimeout(() => process.exit(0), 3000).unref();
}
process.on('SIGTERM', shutdown);
process.on('SIGINT', shutdown);
process.on('uncaughtException', (e) => console.error('uncaught:', e));
process.on('unhandledRejection', (e) => console.error('unhandled:', e));