// Tag multiplayer server — FULLY SERVER-AUTHORITATIVE.
// The server owns: physics, positions, tagging, the round timer, eliminations, lobbies and matchmaking.
// Clients only send their key presses (inputs) and render what the server tells them.
// => a background tab / frozen phone / laggy host can never pause or alter the match for anyone else,
//    and nobody can teleport, speed-hack, fake a tag or touch the timer.
// Run: npm install && npm start
'use strict';
const http = require('http'), fs = require('fs'), path = require('path');
const zlib = require('zlib'), crypto = require('crypto');
const { performance } = require('perf_hooks');
const { WebSocketServer } = require('ws');

const PORT = process.env.PORT || 3000;

/* ---------------- tunables ---------------- */
const MAX_ROOM = 5;            // players per room
const PUB_SIZE = 5;            // public match starts when this many are waiting
const MAX_CONN_PER_IP = +process.env.MAX_CONN_PER_IP || 20;
const MAX_CLIENTS = 2000;       // hard caps so a flood can never exhaust memory
const MAX_ROOMS = 600;
const LOBBY_GRACE_MS = 10000;  // a dropped connection in a lobby / results screen is held this long (brief blips don't kick you)
const ALLOWED = (process.env.ALLOWED_ORIGINS || '').split(',').map(x => x.trim()).filter(Boolean);   // optional: restrict which sites may open a socket
const TICK_MS = 1000 / 60;     // simulation rate (must match the client's PHYS_HZ = 60)
const DT = 1 / 60;
let snapEvery = +process.env.TAG_SNAP_EVERY || 1;   // send a snapshot every N ticks (1 = 60/s, 2 = 30/s). Adapts automatically when the server is overloaded (see the tick loop).
const FIXED_SNAP = !!process.env.TAG_SNAP_EVERY;
const ROUND_S = +process.env.TAG_ROUND_S || 100;           // seconds per round
const CD_MS = 2200;            // 3-2-1-GO countdown before each round
const TAG_GRACE_MS = 300;      // nobody can be tagged right after GO
const BETWEEN_MS = 3200;       // pause after someone is eliminated
const LOBBY_GO_MS = 3000;      // public lobby full -> match starts after this
const LOCK_MS = 1200;          // the player who just passed the tag can't take it straight back
const GRACE_MS = 15000;        // a dropped connection keeps its character this long and may reconnect
const STALL_MS = 150;          // wait this long for a late input packet before treating the player as idle
const LOBBY_IDLE_MS = +process.env.TAG_LOBBY_IDLE_MS || 10 * 60 * 1000;   // a seat in a public lobby is held at most this long (no permanent idlers)
const QCAP = 12;               // max queued inputs per player (anti speed-hack: input rate is capped at 60/s)

const rooms = new Map();       // key -> room   (private: the room code, public: 'p-xxxx')

/* ---------------- static file (cached + gzipped; reloaded automatically if it changes on disk) ---------------- */
const FILE = path.join(__dirname, 'index.html');
let html = null, gz = null, br = null, etag = '', mtime = 0;
function loadHtml() {
  try {
    mtime = fs.statSync(FILE).mtimeMs;
    html = fs.readFileSync(FILE);
    gz = zlib.gzipSync(html, { level: 9 });
    try { br = zlib.brotliCompressSync(html, { params: { [zlib.constants.BROTLI_PARAM_QUALITY]: 11, [zlib.constants.BROTLI_PARAM_SIZE_HINT]: html.length } }); } catch { br = null; }
    etag = '"' + crypto.createHash('sha1').update(html).digest('hex').slice(0, 16) + '"';
  } catch (e) {
    html = null;
    console.error('index.html missing or unreadable:', e.message);
  }
}
loadHtml();

const server = http.createServer((req, res) => {
  const url = (req.url || '/').split('?')[0];

  if (url === '/healthz') {
    res.writeHead(200, { 'Content-Type': 'text/plain', 'Cache-Control': 'no-store' });
    return res.end('ok');
  }
  if (url === '/stats') {
    let waiting = 0;
    for (const r of rooms.values()) if (r.pub && r.st === 'lobby') waiting += r.players.size;
    res.writeHead(200, { 'Content-Type': 'application/json', 'Cache-Control': 'no-store' });
    return res.end(JSON.stringify({ online: wss.clients.size, waiting }));
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
    'Referrer-Policy': 'no-referrer',
    'X-Frame-Options': 'DENY',
    'Content-Security-Policy': "default-src 'self'; script-src 'self' 'unsafe-inline' https://cdnjs.cloudflare.com; style-src 'self' 'unsafe-inline' https://fonts.googleapis.com; font-src https://fonts.gstatic.com; img-src 'self' data: blob:; media-src 'self' data: blob:; connect-src 'self' ws: wss:; frame-ancestors 'none'"
  };
  if (req.headers['if-none-match'] === etag) { res.writeHead(304, headers); return res.end(); }

  const ae = req.headers['accept-encoding'] || '';
  const useBr = br && /\bbr\b/.test(ae), useGz = !useBr && /\bgzip\b/.test(ae);
  const body = useBr ? br : useGz ? gz : html;
  if (useBr) headers['Content-Encoding'] = 'br'; else if (useGz) headers['Content-Encoding'] = 'gzip';
  headers['Content-Length'] = body.length;
  res.writeHead(200, headers);
  res.end(req.method === 'HEAD' ? undefined : body);
});

server.keepAliveTimeout = 65000;
server.headersTimeout = 66000;

const wss = new WebSocketServer({ server, maxPayload: 2048, perMessageDeflate: false });

/* ---------------- world (identical to the client's copy) ---------------- */
const WW = 1600, WH = 836, PW = 30, PH = 34, LX = 22, RX = 1570;
const PL = [[22,304,133],[191,384,99],[48,451,100],[334,451,210],[22,536,358],[323,626,227],[106,707,183],[572,354,209],[764,277,209],[606,451,365],[538,536,482],[837,586,203],[956,354,332],[1154,284,201],[1455,399,73],[1161,512,273],[1148,622,195],[1046,712,446],[22,800,1548]].map(a => ({ x: a[0], y: a[1], w: a[2], h: a[1] == 800 ? 36 : 14 }));
const RAMP = [], CRATE = [{ x: 1383, y: 487, w: 26, h: 25 }, { x: 1409, y: 487, w: 26, h: 25 }, { x: 1409, y: 461, w: 26, h: 26 }];
[[555, 630, 20, 6.1], [1357, 287, 6, 5.9]].forEach(r => { for (let i = 0; i < r[2]; i++) RAMP.push({ x: r[0] + i * 10, y: r[1] + r[3] * (i + .5), w: 10, h: 14 }); });
const SOL = PL.concat(RAMP, CRATE);

/* One physics step. MUST stay numerically identical to the client's step() (the client uses it for prediction). */
function step(p, inp, dt) {
  const m = p.it ? 1.07 : 1, MAX = 340 * m;
  const ax = (inp.r ? 1 : 0) - (inp.l ? 1 : 0);
  if (ax) { const turn = Math.sign(p.vx) == -ax ? 1.8 : 1; p.vx += ax * (p.g ? 3000 : 2000) * turn * dt; p.vx = Math.max(-MAX, Math.min(MAX, p.vx)); p.face = ax; }
  else { const f = (p.g ? 2800 : 500) * dt; p.vx = Math.abs(p.vx) <= f ? 0 : p.vx - Math.sign(p.vx) * f; }
  const jp = inp.j && !p.pj; p.pj = !!inp.j; if (jp) p.buf = .13; else p.buf -= dt;
  p.coy = p.g ? .1 : p.coy - dt;
  if (p.buf > 0 && p.coy > 0) { p.vy = -840; p.buf = p.coy = 0; p.g = 0; p.cut = 0; }
  if (!inp.j && p.vy < -260 && !p.cut) { p.vy *= .45; p.cut = 1; }
  if (inp.d && p.g) p.drop = .22; p.drop -= dt;
  p.vy = Math.min(p.vy + (p.vy > 0 ? 3400 : 2300) * dt, 1150);
  const ov = q => p.x < q.x + q.w && p.x + PW > q.x && p.y < q.y + q.h && p.y + PH > q.y;
  const was = p.g; p.x += p.vx * dt;
  if (p.x < LX) { p.x = LX; p.vx = 0; } if (p.x > RX - PW) { p.x = RX - PW; p.vx = 0; }
  for (const q of SOL) if (ov(q)) { if (was && p.y + PH - q.y <= 9) p.y = q.y - PH; else { p.x = p.vx > 0 ? q.x - PW : p.vx < 0 ? q.x + q.w : (p.x + PW / 2 < q.x + q.w / 2 ? q.x - PW : q.x + q.w); p.vx = 0; } }
  p.g = 0; p.y += p.vy * dt;
  for (const q of SOL) if (ov(q)) {
    if (p.vy >= 0) { p.y = q.y - PH; p.vy = 0; p.g = 1; }
    else { const l = p.x + PW - q.x, r = q.x + q.w - p.x; if (Math.min(l, r) < 10) p.x += l < r ? -l : r; else { p.y = q.y + q.h; p.vy = 0; } }
  }
}
const hit = (a, b, pad) => a.x < b.x + PW - pad && a.x + PW > b.x + pad && a.y < b.y + PH - pad && a.y + PH > b.y + pad;

/* ---------------- helpers ---------------- */
const rnd = n => Math.random() * n | 0;
const r4 = v => Math.round(v * 1e4) / 1e4;
const r1 = v => Math.round(v * 10) / 10;
const ri = v => Math.round(v);
const hex = n => crypto.randomBytes(n).toString('hex');
const now = () => performance.now();

function cleanName(v) {
  const s = typeof v === 'string' ? v.replace(/[\u0000-\u001f\u007f<>]/g, '').trim().slice(0, 12) : '';
  return s || 'Player';
}

function send(ws, s, droppable) {
  if (!ws || ws.readyState !== 1) return;
  if (ws.bufferedAmount > 1048576) { ws.terminate(); return; }          // hopelessly backed up
  if (droppable && ws.bufferedAmount > 4096) return;                    // slow link: skip a stale snapshot (the next one is 16 ms away) instead of queueing latency
  ws.send(s);
}
const sendP = (p, s, drop) => { if (p.ws) send(p.ws, s, drop); };
const bcast = (r, s, drop) => { for (const p of r.players.values()) sendP(p, s, drop); };

/* ---------------- rooms ---------------- */
function mkRoom(key, pub) {
  const r = {
    key, pub: !!pub, players: new Map(), st: 'lobby', hostId: null,
    ord: [], rn: 0, gm: 0, practice: false, first: null,
    loser: null, ln: null, win: null, wn: null,
    lobbyGo: 0, cdEnd: 0, deadline: 0, tagFrom: 0, betweenEnd: 0, lk: null
  };
  return r;   // not registered yet: addPlayer() registers it together with its first player, so an empty room can never be left behind
}

const conn = r => { let n = 0; for (const p of r.players.values()) if (p.ws) n++; return n; };

function newPlayer(nm, ci) {
  return {
    id: hex(4), tk: hex(12), ws: null, nm, ci,
    q: [], lastIn: 0, lastSeq: 0, lastCmd: 0, dc: 0, gr: 0, credit: 0,
    alive: false, it: 0, rs: 0,
    x: 0, y: 0, vx: 0, vy: 0, g: 0, coy: 0, buf: 0, pj: false, cut: 0, drop: 0, face: 1
  };
}

function bcastRoom(r) {
  const t = now();
  bcast(r, JSON.stringify({
    t: 'room', code: r.pub ? '' : r.key, pub: r.pub ? 1 : 0, st: r.st, host: r.hostId,
    rn: r.rn, gm: r.gm, practice: r.practice ? 1 : 0, first: r.first,
    loser: r.loser, ln: r.ln, win: r.win, wn: r.wn,
    lc: r.lobbyGo ? Math.max(0, (r.lobbyGo - t) / 1000) : 0,
    pl: [...r.players.values()].filter(p => p.ws || r.st === 'play' || r.st === 'between').map(p => ({ id: p.id, nm: p.nm, ci: p.ci, al: p.alive ? 1 : 0 }))
  }));
}

function updateLobbyGo(r, t) {
  if (!r.pub || r.st !== 'lobby') return;
  if (conn(r) >= PUB_SIZE) { if (!r.lobbyGo) r.lobbyGo = t + LOBBY_GO_MS; }
  else r.lobbyGo = 0;
}

function spawn(p, k, t) {
  p.x = 690 + k * 45; p.y = 502; p.vx = p.vy = 0; p.g = 0; p.coy = p.buf = p.cut = p.drop = 0; p.pj = false; p.face = 1;
  p.rs++; p.q.length = 0; p.lastCmd = t;
}

function aliveIds(r) {
  return r.ord.filter(id => { const p = r.players.get(id); return p && p.alive; });
}

function startRound(r, ids, t) {
  r.rn++; r.st = 'play'; r.loser = r.ln = null; r.lk = null; r.ord = ids.slice();
  const first = ids[rnd(ids.length)]; r.first = first;
  ids.forEach((id, k) => { const p = r.players.get(id); if (!p) return; spawn(p, k, t); p.alive = true; p.it = id === first ? 1 : 0; });
  for (const p of r.players.values()) if (!ids.includes(p.id)) { p.alive = false; p.it = 0; }
  r.cdEnd = t + CD_MS; r.deadline = r.cdEnd + ROUND_S * 1000; r.tagFrom = r.cdEnd + TAG_GRACE_MS;
  bcastRoom(r);
}

function startMatch(r, t) {
  const ids = [...r.players.values()].filter(p => p.ws).map(p => p.id).slice(0, MAX_ROOM);   // only players who are actually connected
  if (!ids.length) return;
  r.gm = 1 + rnd(999999999); r.rn = 0; r.practice = ids.length === 1; r.win = r.wn = null; r.lobbyGo = 0;
  startRound(r, ids, t);
}

function finish(r, id) {
  const p = id && r.players.get(id);
  r.st = 'over'; r.win = id || null; r.wn = p ? p.nm : null; r.lobbyGo = 0;
  for (const q of r.players.values()) q.it = 0;
  bcastRoom(r);
}

function toLobby(r) {
  r.st = 'lobby'; r.ord = []; r.rn = 0; r.gm = 0; r.first = r.loser = r.win = r.ln = r.wn = null; r.lk = null; r.practice = false;
  for (const p of r.players.values()) { p.alive = false; p.it = 0; p.q.length = 0; }
  updateLobbyGo(r, now());
  bcastRoom(r);
}

function expire(r, t, holder) {
  r.loser = holder.id; r.ln = holder.nm; holder.alive = false; holder.it = 0;
  r.st = 'between'; r.betweenEnd = t + BETWEEN_MS;
  bcastRoom(r);
}

function removePlayer(r, p, t) {
  if (r.players.get(p.id) !== p) return;
  r.players.delete(p.id);
  if (!r.players.size) { rooms.delete(r.key); return; }
  if (r.hostId === p.id) {                                                          // oldest CONNECTED player becomes the host
    const nx = [...r.players.values()].find(q => q.ws) || r.players.values().next().value;
    r.hostId = r.pub ? null : (nx ? nx.id : null);
  }
  if (r.st === 'lobby') updateLobbyGo(r, t);
  else if (r.st === 'play' && p.alive) {
    const al = aliveIds(r);
    if (!r.practice && al.length < 2) { finish(r, al[0]); return; }
    if (p.it && al.length) { const nh = r.players.get(al[rnd(al.length)]); if (nh) { nh.it = 1; r.lk = null; } }
  }
  bcastRoom(r);
}

function kick(r, p, why) {
  const w = p.ws; p.ws = null;
  removePlayer(r, p, now());
  if (w) { send(w, JSON.stringify({ t: 'kick', e: why })); try { w.close(); } catch {} }
}
// A bug in one room must never take the other rooms (or the whole server) down with it.
function destroyRoom(r) {
  rooms.delete(r.key);
  for (const p of r.players.values()) if (p.ws) { const w = p.ws; p.ws = null; send(w, '{"t":"kick","e":"error"}'); try { w.close(); } catch {} }
  r.players.clear();
}

/* ---------------- simulation ---------------- */
// Returns the input bit-mask to apply this tick, or -1 = "wait, the next input packet is probably in flight".
function consume(p, t) {
  const c = p.q.shift();
  if (c) { p.lastSeq = c.s; p.lastCmd = t; return c.b; }
  if (t - p.lastCmd < STALL_MS) return -1;   // short wait keeps us in lock-step with the client's prediction
  return 0;                                    // client is silent (hidden tab / lost signal): stand still, but keep playing
}

function advance(p, b) {
  step(p, { l: b & 1, r: b & 2, j: b & 4, d: b & 8 }, DT);
  if (p.y > WH + 200 || !(p.x + p.y + p.vx + p.vy < 1e9 && p.x + p.y + p.vx + p.vy > -1e9)) { p.x = 300 + Math.random() * 600; p.y = -60; p.vx = p.vy = 0; p.rs++; }   // fell out of the world (or numeric glitch): respawn
}

function simRoom(r, t) {
  const cd = r.st === 'play' && t < r.cdEnd;
  for (const p of r.players.values()) {
    if (!p.alive) continue;
    let b = consume(p, t);
    if (b === -1) { p.credit = Math.min(8, p.credit + 1); continue; }   // a late packet: the player earns ONE catch-up step (never more than 1 per missed tick)
    advance(p, cd ? 0 : b);
    // after a lag spike a burst of inputs arrives: spend earned credit to catch up. A flooding cheater has no credit, so they can't go faster than 60 steps/s.
    while (p.credit > 0 && p.q.length > 1) { p.credit--; { const c2 = p.q.shift(); p.lastSeq = c2.s; advance(p, cd ? 0 : c2.b); } }
  }

  if (r.st === 'between') { if (t >= r.betweenEnd) { const al = aliveIds(r); if (al.length >= 2) startRound(r, al, t); else finish(r, al[0]); } return; }
  if (r.st !== 'play' || cd) return;

  let holder = null;
  for (const p of r.players.values()) if (p.alive && p.it) { holder = p; break; }
  if (!holder) {   // safety net: there must always be exactly one holder
    const al = aliveIds(r);
    if (al.length) { holder = r.players.get(al[rnd(al.length)]); holder.it = 1; }
  }
  if (!holder) return;

  // the passer can't take the tag straight back until they've separated (or 1.2 s passed)
  if (r.lk) {
    const a = r.players.get(r.lk.from), b = r.players.get(r.lk.to);
    if (!a || !b || t > r.lk.until || !hit(a, b, -8)) r.lk = null;
  }
  if (t >= r.tagFrom) {
    for (const q of r.players.values()) {
      if (!q.alive || q.it || q === holder) continue;
      if (!hit(holder, q, 3)) continue;                                   // real overlap only, never from a distance
      if (r.lk && r.lk.from === q.id && r.lk.to === holder.id) continue;
      holder.it = 0; q.it = 1;
      r.lk = { from: holder.id, to: q.id, until: t + LOCK_MS };
      bcast(r, JSON.stringify({ t: 'tag', a: q.id, b: holder.id }));
      holder = q;
      break;
    }
  }
  if (!r.practice && t >= r.deadline) expire(r, t, holder);
}

function snapshot(r, t, tt) {
  let arr = '';
  for (const p of r.players.values()) if (p.alive) arr += (arr ? ',' : '') + '["' + p.id + '",' + r1(p.x) + ',' + r1(p.y) + ',' + ri(p.vx) + ',' + ri(p.vy) + ',' + p.face + ',' + (p.g ? 1 : 0) + ',' + (p.it ? 1 : 0) + ']';
  const tl = r.practice ? 'null' : r.st === 'play' ? Math.min(ROUND_S, Math.max(0, (r.deadline - t) / 1000)).toFixed(2) : '0';
  const head = '{"t":"s","ts":' + tt.toFixed(1) + ',"tl":' + tl + ',"cd":' + Math.max(0, (r.cdEnd - t) / 1000).toFixed(2) + ',"p":[' + arr + ']';
  for (const p of r.players.values()) {
    if (!p.ws) continue;
    // full-precision state of the receiver, used for client-side prediction + reconciliation
    const a = p.alive ? ',"a":{"x":' + r4(p.x) + ',"y":' + r4(p.y) + ',"vx":' + r4(p.vx) + ',"vy":' + r4(p.vy) + ',"g":' + (p.g ? 1 : 0) + ',"coy":' + r4(p.coy) + ',"buf":' + r4(p.buf) + ',"pj":' + (p.pj ? 'true' : 'false') + ',"cut":' + (p.cut ? 1 : 0) + ',"drop":' + r4(p.drop) + ',"face":' + p.face + ',"it":' + (p.it ? 1 : 0) + ',"q":' + p.lastSeq + ',"rs":' + p.rs + '}' : '';
    send(p.ws, head + a + '}', true);
  }
}

let tickN = 0, nextTick = now();
function tickAll(t, tt) {
  tickN++;
  const sweep = tickN % 15 === 0;               // housekeeping 4x/s is plenty; keeps the 60 Hz path free of allocations
  for (const r of rooms.values()) {
    try {
      if (sweep) for (const p of [...r.players.values()]) if (p.dc && t - p.dc > p.gr) removePlayer(r, p, t);   // dropped and never came back
      if (!rooms.has(r.key)) continue;
      if (r.st === 'lobby') {
        if (sweep && r.pub) for (const p of [...r.players.values()]) if (p.ws && t - p.since > LOBBY_IDLE_MS) kick(r, p, 'idle');
        if (r.lobbyGo && t >= r.lobbyGo) { r.lobbyGo = 0; if (conn(r) >= PUB_SIZE) startMatch(r, t); else bcastRoom(r); }
      } else if (r.st === 'play' || r.st === 'between') {
        simRoom(r, t);
        if (rooms.has(r.key) && (r.st === 'play' || r.st === 'between') && tickN % snapEvery === 0 && conn(r)) snapshot(r, t, tt);
      }
    } catch (e) { console.error('room error, closing room ' + r.key + ':', e); destroyRoom(r); }
  }
}
let lagEma = 0, calmSince = 0;
setInterval(() => {
  const t = now();
  // Overload guard: if ticks keep running late (a busy / tiny shared CPU), halve the snapshot rate so the game logic stays on time
  // and every player keeps the same fair, steady 60 Hz simulation. It returns to 60 snapshots/s by itself when the load drops.
  const lag = Math.max(0, t - nextTick);
  lagEma += (lag - lagEma) * 0.05;
  if (!FIXED_SNAP) {
    if (snapEvery === 1 && lagEma > 6) { snapEvery = 2; calmSince = 0; console.log('high load: snapshots at 30/s'); }
    else if (snapEvery === 2) { if (lagEma < 1.5) { if (!calmSince) calmSince = t; else if (t - calmSince > 20000) { snapEvery = 1; calmSince = 0; console.log('load normal: snapshots at 60/s'); } } else calmSince = 0; }
  }
  let n = 0;
  while (nextTick <= t && n++ < 5) { tickAll(t, nextTick); nextTick += TICK_MS; }   // fixed 60 Hz, catches up after a hiccup
  if (nextTick < t - 100) nextTick = t;
}, 4);

/* ---------------- connections ---------------- */
const perIp = new Map();
const CODE_CHARS = 'ABCDEFGHJKLMNPQRSTUVWXYZ23456789';

wss.on('connection', (ws, req) => {
  try { req.socket.setNoDelay(true); } catch {}
  if (wss.clients.size > MAX_CLIENTS) { ws.close(); return; }
  if (ALLOWED.length) { const o = String(req.headers.origin || ''); if (!ALLOWED.some(a => o === a || o.endsWith('.' + a.replace(/^https?:\/\//, '')))) { ws.close(); return; } }

  const ip = String(req.headers['cf-connecting-ip'] || req.headers['true-client-ip'] || req.headers['x-forwarded-for'] || req.socket.remoteAddress || '').split(',')[0].trim();
  const n = (perIp.get(ip) || 0) + 1;
  if (n > MAX_CONN_PER_IP) { ws.close(); return; }
  perIp.set(ip, n);

  ws.lastSeen = ws.born = Date.now();
  ws.on('pong', () => { ws.lastSeen = Date.now(); });

  let r = null, p = null, cnt = 0, winStart = Date.now();
  const err = e => { send(ws, '{"t":"err","e":"' + e + '"}'); ws.close(); };

  const attach = (rr, pp) => {
    r = rr; p = pp; pp.ws = ws; pp.dc = 0; ws.joined = 1;
    send(ws, JSON.stringify({ t: 'hello', id: pp.id, tk: pp.tk, rk: rr.key, code: rr.pub ? '' : rr.key, pub: rr.pub ? 1 : 0 }));
  };
  const addPlayer = (rr, nm) => {
    if (rr.players.size >= MAX_ROOM && rr.st === 'lobby') {                  // a disconnected "ghost" never blocks a real player from a lobby
      for (const q of rr.players.values()) if (!q.ws) { rr.players.delete(q.id); break; }
    }
    if (rr.players.size >= MAX_ROOM) return err('full');                       // single choke point: no path can exceed the room limit
    if (rr.pub && rr.st !== 'lobby') return err('full');                       // public matches in progress are closed
    if (!rooms.has(rr.key)) rooms.set(rr.key, rr);
    const used = new Set([...rr.players.values()].map(q => q.ci)); let ci = 0; while (used.has(ci)) ci++;
    const pp = newPlayer(nm, ci); pp.since = now();
    rr.players.set(pp.id, pp);
    if (!rr.pub && !rr.hostId) rr.hostId = pp.id;
    attach(rr, pp);
    updateLobbyGo(rr, now());
    bcastRoom(rr);
  };

  ws.on('message', (raw, isBinary) => {
    const t = Date.now();
    ws.lastSeen = t;
    if (t - winStart >= 1000) { winStart = t; cnt = 0; }
    if (++cnt > 200 || isBinary) return;           // per-connection rate limit

    let m;
    try { m = JSON.parse(raw); } catch { return; }
    if (!m || typeof m !== 'object') return;

    /* ---- inputs: the ONLY thing a client controls ---- */
    if (m.t === 'in') {
      if (!p || !p.alive || !Array.isArray(m.c)) return;
      const c = m.c;
      for (let i = 0; i < c.length && i < 8; i++) {
        const e = c[i];
        if (!Array.isArray(e)) continue;
        const s = e[0], b = e[1];
        if (!Number.isInteger(s) || !Number.isInteger(b) || b < 0 || b > 15 || s <= p.lastIn) continue;
        p.lastIn = s;
        if (p.q.length < QCAP) p.q.push({ s, b });
      }
      return;
    }
    if (m.t === 'hb') { send(ws, '{"t":"hb"}'); return; }
    if (m.t === 'leave' && r && p) { removePlayer(r, p, now()); p.ws = null; r = null; p = null; return; }   // deliberate exit: no grace period

    /* ---- joining ---- */
    if (!r) {
      if (m.t === 'create') {
        if (rooms.size >= MAX_ROOMS) return err('busy');
        let code; do { code = Array.from({ length: 4 }, () => CODE_CHARS[rnd(32)]).join(''); } while (rooms.has(code));
        return addPlayer(mkRoom(code, false), cleanName(m.nm));
      }
      if (m.t === 'join') {
        const code = typeof m.code === 'string' ? m.code.toUpperCase() : '';
        if (!/^[A-Z0-9]{3,6}$/.test(code)) return err('bad');
        const rr = rooms.get(code);
        if (!rr || rr.pub) return err('nf');
        if (rr.players.size >= MAX_ROOM) return err('full');
        if (rr.practice && rr.st !== 'lobby') toLobby(rr);   // a solo practice game has no end: someone joining brings everybody back to the lobby
        return addPlayer(rr, cleanName(m.nm));          // joining a running match = spectate until the next game
      }
      if (m.t === 'quick') {
        let best = null;
        for (const rr of rooms.values()) {
          if (!rr.pub || rr.st !== 'lobby' || conn(rr) >= MAX_ROOM) continue;
          if (!best || conn(rr) > conn(best)) best = rr;   // fullest lobby first
        }
        if (!best && rooms.size >= MAX_ROOMS) return err('busy');
        if (!best) { let k; do { k = 'p-' + hex(3); } while (rooms.has(k)); best = mkRoom(k, true); }
        return addPlayer(best, cleanName(m.nm));
      }
      if (m.t === 'resume') {                           // reconnect after a dropped connection
        const rr = typeof m.rk === 'string' && m.rk.length <= 16 ? rooms.get(m.rk) : null;
        const pp = rr && typeof m.id === 'string' ? rr.players.get(m.id) : null;
        if (!pp || pp.tk !== m.tk) return err('gone');
        if (pp.ws && pp.ws !== ws) { const old = pp.ws; pp.ws = null; try { old.terminate(); } catch {} }
        attach(rr, pp);
        bcastRoom(rr);
      }
      return;
    }

    /* ---- room controls ---- */
    if (m.t === 'start' && r.st === 'lobby' && !r.pub && r.hostId === p.id) return startMatch(r, now());
    if (m.t === 'lobby' && r.st === 'over' && !r.pub && r.hostId === p.id) return toLobby(r);
  });

  ws.on('close', () => {
    const left = (perIp.get(ip) || 1) - 1;
    if (left <= 0) perIp.delete(ip); else perIp.set(ip, left);
    if (r && p && p.ws === ws) {
      p.ws = null; p.dc = now();                                  // keep the character for a while: the player may just be reconnecting
      p.gr = (r.st === 'play' || r.st === 'between') ? GRACE_MS : LOBBY_GRACE_MS;
      if (r.st === 'lobby') updateLobbyGo(r, now());              // a ghost never counts towards starting a match
      bcastRoom(r);
    }
  });

  ws.on('error', () => {});
});

// Drop dead sockets (closed browser, lost signal) and keep proxies from idling the connection out.
setInterval(() => {
  const t = Date.now();
  for (const ws of wss.clients) {
    if (t - ws.lastSeen > 15000 || (!ws.joined && t - ws.born > 120000)) { ws.terminate(); continue; }
    try { ws.ping(); } catch {}
    send(ws, '{"t":"hb"}');
  }
}, 5000);

/* ---------------- housekeeping ---------------- */
// Safety net: any room with nobody connected for a while is deleted, whatever state it is in.
setInterval(() => {
  const t = now();
  for (const r of rooms.values()) {
    if (!r.players.size) { rooms.delete(r.key); continue; }
    if (conn(r)) { r.idle = 0; continue; }
    if (!r.idle) r.idle = t;
    else if (t - r.idle > GRACE_MS + 5000) rooms.delete(r.key);
  }
}, 10000).unref();

// Render's free plan puts a service to sleep after ~15 min without traffic, which makes the next player wait ~1 min.
// Pinging our own public URL counts as traffic. Disable with KEEPALIVE=0.
if (process.env.RENDER_EXTERNAL_URL && process.env.KEEPALIVE !== '0' && typeof fetch === 'function') {
  setInterval(() => { fetch(process.env.RENDER_EXTERNAL_URL + '/healthz').catch(() => {}); }, 10 * 60 * 1000).unref();
}

/* ---------------- lifecycle ---------------- */
server.listen(PORT, '0.0.0.0', () => {
  console.log('Tag multiplayer server (authoritative) running on port ' + PORT);
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