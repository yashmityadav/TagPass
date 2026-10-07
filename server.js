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
const MAX_ROOM = 10;           // players per room
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
const ROUND_S = +process.env.TAG_ROUND_S || 180;           // seconds per round
const CD_MS = 2200;            // 3-2-1-GO countdown before each round
const TAG_GRACE_MS = 300;      // nobody can be tagged right after GO
const BETWEEN_MS = 3200;       // pause after someone is eliminated
const LOBBY_GO_MS = 3000;      // public lobby full -> match starts after this
const LOCK_MS = 1200;          // the player who just passed the tag can't take it straight back
const GRACE_MS = 15000;        // a dropped connection keeps its character this long and may reconnect
const STALL_MS = 150;          // wait this long for a late input packet before treating the player as idle
const LOBBY_IDLE_MS = +process.env.TAG_LOBBY_IDLE_MS || 10 * 60 * 1000;   // a seat in a public lobby is held at most this long (no permanent idlers)
const QCAP = 12;               // max queued inputs per player (anti speed-hack: input rate is capped at 60/s)

/* ---- abilities ---- */
const DASH_V = 1000, DASH_T = 0.16, DASH_CD = 15;   // dash (everyone): speed px/s, duration s, cooldown s
const AB_CD = 30;                                    // cooldown (s) of the ability each player picks before the match
const FAKE_T = 5, SMOKE_T = 5, TRAP_T = 5;           // how long each effect lasts (s)
const TRAP_W = 110, TRAP_IMM = 1;                    // trap width (px); its owner is immune for the first second so they can step off it
const SLOW_K = 0.4, JUMP_K = 0.8;                    // speed / jump multipliers while standing in a trap
/* ---- grab: hold the button next to a player to latch on and drag them along (Human-Fall-Flat style). Everyone has it. ---- */
const GRAB_REACH = 46, GRAB_REACH_T = 0.7;           // how far (px beyond the body) the hand reaches / how long (s) the hands stay out before it counts as a miss
const GRAB_MAX = 6, GRAB_MIN = 0.25;               // longest hold (s) / shortest hold (a tap or a lag blip can't drop the grip instantly)
const GRAB_CD = 8, GRAB_MISS_CD = 1.5;               // cooldown (s) after a hold / after a miss
const GRAB_ROPE = 70, GRAB_BREAK = 300, GRAB_IMM = 1.2;   // max distance between the two bodies (px) / the grip snaps beyond this / a freed player can't be re-grabbed for this long (s)
const HELD_K = 0.5, CARRY_K = 0.8;                   // speed multiplier of the player who is held / of the player who is carrying
const ABIL = new Set(['fake', 'smoke', 'trap']);
/* ---- lightning: random warning circle, strike after LT_WARN s, launches everyone inside (no damage) ---- */
const LT_R = 110, LT_WARN = 1, LT_FLASH = .35, LT_MIN = 3, LT_MAX = 6, LT_VY = 1500, LT_VX = 620;

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
let SX = null; const SOL = PL; SX = SOL;                                                             // solid rectangles: just the platforms, the arena is wide open

/* ---- MAP FEATURES (the client has an identical copy; both run inside step()) ----
   PADS : launch pads. vx=0 -> straight up; vx!=0 -> a cannon that also shoots you sideways.
   ZIPS : ziplines, completely optional. Tap JUMP in the air next to a cable to grab it and ride it (left/right picks the direction),
          tap JUMP again to hop off, or just ride to the end. Every cable must run left -> right (x1 < x2). */
const PADS = [
  { x: 1524, y: 800, w: 44, vy: 1500, vx: 0 },       // bottom-right corner of the floor: straight up (steer left in the air to land on the right-side decks)
  { x: 417, y: 451, w: 44, vy: 1300, vx: 0 }         // middle of the platform up-right of the left tower: straight up, right through the diagonal cable
];
const ZIPS = [
  { x1: 170, y1: 473, x2: 844, y2: 167 },      // LEFT DIAGONAL: from the left-side deck up to the top-centre platform
  { x1: 1181, y1: 457, x2: 1505, y2: 289 }     // RIGHT DIAGONAL: from the right-middle deck up to the far-right perch
].map(z => { const dx = z.x2 - z.x1, dy = z.y2 - z.y1, len = Math.hypot(dx, dy); return { x1: z.x1, y1: z.y1, x2: z.x2, y2: z.y2, len, ux: dx / len, uy: dy / len }; });
const BST_K = 1.5, PAD_BST = .9;
const ZIP_V = 640, ZIP_R = 44, ZIP_HANG = 8, ZIP_CD = .35, ZIP_HOP = 640, ZIP_OUT = 520;
const zh = { i: -1, s: 0 };
function zipFind(p) {                                                       // nearest cable point within reach of my hands (result in zh)
  const hx = p.x + PW / 2, hy = p.y + ZIP_HANG; let bi = -1, bd = ZIP_R, bs = 0;
  for (let i = 0; i < ZIPS.length; i++) {
    const z = ZIPS[i], s = Math.max(0, Math.min(z.len, (hx - z.x1) * z.ux + (hy - z.y1) * z.uy));
    const d = Math.hypot(hx - (z.x1 + z.ux * s), hy - (z.y1 + z.uy * s));
    if (d < bd) { bd = d; bi = i; bs = s; }
  }
  zh.i = bi; zh.s = bs; return bi;
}
function zipPose(p) {                                                       // hang from the cable at distance p.zs from its left end
  const z = ZIPS[p.zip];
  p.x = z.x1 + z.ux * p.zs - PW / 2; p.y = z.y1 + z.uy * p.zs - ZIP_HANG;
  p.vx = p.zd * ZIP_V * z.ux; p.vy = p.zd * ZIP_V * z.uy; p.g = 0;
  p.face = p.vx > 0 ? 1 : -1;
}

/* One physics step. MUST stay numerically identical to the client's step() (the client uses it for prediction). */
function step(p, inp, dt) {
  if (p.bst > 0) p.bst -= dt;
  if (p.zcd > 0) p.zcd -= dt;
  p.bv = 0;
  if (p.zip >= 0) {                                                           // riding a zipline: the cable owns my movement
    if (p.dcd > 0) p.dcd -= dt;
    p.ps = !!inp.s;
    const jp = inp.j && !p.pj; p.pj = !!inp.j;
    const ax = (inp.r ? 1 : 0) - (inp.l ? 1 : 0); if (ax) p.zd = ax;           // steer: hold left/right to ride that way (cables run left -> right, so +1 = toward the right end)
    const z = ZIPS[p.zip];
    p.zs += p.zd * ZIP_V * dt;
    const end = p.zs <= 0 || p.zs >= z.len;
    p.zs = Math.max(0, Math.min(z.len, p.zs));
    zipPose(p);
    if (jp || end || p.hb || p.gt || p.gk) {                                          // let go: hop off / end of the cable / somebody grabbed me
      p.zip = -1; p.zcd = ZIP_CD; p.buf = p.coy = 0; p.cut = 1; p.drop = 0;
      if (jp) { p.vx = Math.max(-ZIP_OUT, Math.min(ZIP_OUT, p.vx)); p.vy = -ZIP_HOP; }   // hop off: keep the speed and fly
      else { p.vx *= .3; p.vy *= .5; }                                        // cable end (or grabbed): drop off near the end, onto whatever is below
    }
    return;
  }
  const m = p.it ? 1.1 : 1, MAX = 340 * m * (p.slow ? SLOW_K : 1) * (p.hb ? HELD_K : 1) * ((p.gt || p.gk) ? CARRY_K : 1) * (p.bst > 0 ? BST_K : 1);
  const ax = (inp.r ? 1 : 0) - (inp.l ? 1 : 0);
  const ds = inp.s && !p.ps; p.ps = !!inp.s;                                  // dash = rising edge of the dash button
  if (p.dcd > 0) p.dcd -= dt;
  if (ds && p.dcd <= .001 && p.dash <= 0) { p.dash = DASH_T; p.dcd = DASH_CD; p.dd = ax || p.face; p.face = p.dd; }
  if (p.dash > 0) { p.dash -= dt; p.vx = p.dd * DASH_V; if (p.dash <= 0) { p.dash = 0; p.vx = p.dd * MAX; } }
  else if (ax) { const turn = Math.sign(p.vx) == -ax ? 1.8 : 1; p.vx += ax * (p.g ? 3000 : 2000) * turn * dt; p.vx = Math.max(-MAX, Math.min(MAX, p.vx)); p.face = ax; }
  else { const f = (p.g ? 2800 : 500) * dt; p.vx = Math.abs(p.vx) <= f ? 0 : p.vx - Math.sign(p.vx) * f; }
  const jp = inp.j && !p.pj; p.pj = !!inp.j; if (jp) p.buf = .13; else p.buf -= dt;
  p.coy = p.g ? .1 : p.coy - dt;
  if (p.buf > 0 && p.coy > 0) { p.vy = -840 * ((p.slow || p.hb) ? JUMP_K : 1); p.buf = p.coy = 0; p.g = 0; p.cut = 0; if (p.dash > 0) { p.dash = 0; p.vx = Math.max(-MAX, Math.min(MAX, p.vx)); } }
  if (p.zcd <= 0 && !p.g && p.buf > 0 && !p.hb && !p.gt && !p.gk && zipFind(p) >= 0) {   // tap JUMP in the air next to a cable = grab it (decoys have no zcd, so they never do)
    p.zip = zh.i; p.zs = zh.s; p.zd = ax || (zh.s < ZIPS[zh.i].len / 2 ? 1 : -1);
    p.buf = 0; p.dash = 0; p.cut = 1; p.drop = 0;
    zipPose(p); return;
  }
  if (!inp.j && p.vy < -260 && !p.cut) { p.vy *= .45; p.cut = 1; }
  if (inp.d && p.g) p.drop = .22; p.drop -= dt;
  if (p.dash > 0 && !p.g) p.vy = 0; else p.vy = Math.min(p.vy + (p.vy > 0 ? 3400 : 2300) * dt, 1150);   // air-dash: no gravity while dashing
  const ov = q => p.x < q.x + q.w && p.x + PW > q.x && p.y < q.y + q.h && p.y + PH > q.y;
  const was = p.g; p.x += p.vx * dt;
  if (p.x < LX) { p.x = LX; p.vx = 0; } if (p.x > RX - PW) { p.x = RX - PW; p.vx = 0; }
  for (const q of SX) if (ov(q)) { if (was && p.y + PH - q.y <= 9) p.y = q.y - PH; else { p.x = p.vx > 0 ? q.x - PW : p.vx < 0 ? q.x + q.w : (p.x + PW / 2 < q.x + q.w / 2 ? q.x - PW : q.x + q.w); p.vx = 0; } }
  p.g = 0; p.y += p.vy * dt;
  for (const q of SX) if (ov(q)) {
    if (p.vy >= 0) { p.y = q.y - PH; p.vy = 0; p.g = 1; }
    else { const l = p.x + PW - q.x, r = q.x + q.w - p.x; if (Math.min(l, r) < 10) p.x += l < r ? -l : r; else { p.y = q.y + q.h; p.vy = 0; } }
  }
  if (p.g) for (const q of PADS) if (Math.abs(p.y + PH - q.y) < 3 && p.x + PW > q.x + 4 && p.x < q.x + q.w - 4) {      // launch pad / cannon
    p.vy = -q.vy; p.g = 0; p.coy = 0; p.buf = 0; p.cut = 1; p.dash = 0;
    if (q.vx) { p.vx = q.vx; p.face = q.vx > 0 ? 1 : -1; p.bst = PAD_BST; }
    break;
  }
}
const hit = (a, b, pad) => a.x < b.x + PW - pad && a.x + PW > b.x + pad && a.y < b.y + PH - pad && a.y + PH > b.y + pad;

/* ---------------- crates: solid boxes; hold GRAB next to one to drag it ---------------- */
const CS = 40, CRATE_ROPE = 64, CRATE_BREAK = 220;
const CRATE_SP = [[300,760],[1250,760],[700,411],[1100,314],[120,496],[1300,672],[480,411]];
function initCrates(r) { r.cr = CRATE_SP.map((a, i) => ({ id: i + 1, x: a[0], y: a[1], w: CS, h: CS, sx: a[0], sy: a[1], vy: 0, hb: '' })); }
const crHit = (c, o) => c.x < o.x + o.w && c.x + c.w > o.x && c.y < o.y + o.h && c.y + c.h > o.y;
function crBlocked(r, c) {
  if (c.x < LX || c.x + c.w > RX) return true;
  for (const s of SOL) if (crHit(c, s)) return true;
  for (const o of r.cr) if (o !== c && crHit(c, o)) return true;
  for (const p of r.players.values()) if (p.alive && c.x < p.x + PW && c.x + c.w > p.x && c.y < p.y + PH && c.y + c.h > p.y) return true;
  return false;
}
function moveCrate(r, c, mx, my) {
  const ox = c.x, oy = c.y;
  c.x = ox + mx; c.y = oy + my; if (!crBlocked(r, c)) return;
  c.y = oy; if (!crBlocked(r, c)) return;
  c.x = ox; c.y = oy + my; if (!crBlocked(r, c)) return;
  c.x = ox; c.y = oy;
}
function grabCrate(r, p) {
  let best = null, bd = 1e9;
  for (const c of r.cr) {
    if (c.hb || !(p.x < c.x + c.w + GRAB_REACH && p.x + PW > c.x - GRAB_REACH && p.y < c.y + c.h + GRAB_REACH && p.y + PH > c.y - GRAB_REACH)) continue;
    const d = Math.abs(p.x + PW / 2 - c.x - c.w / 2) + Math.abs(p.y + PH / 2 - c.y - c.h / 2);
    if (d < bd) { bd = d; best = c; }
  }
  return best;
}
function crateTick(r) {
  for (const c of r.cr) {
    let h = c.hb ? r.players.get(c.hb) : null;
    if (c.hb && (!h || !h.alive || h.gk !== c.id)) { c.hb = ''; h = null; }
    if (h) {
      const dx = h.x + PW / 2 - c.x - c.w / 2, dy = h.y + PH / 2 - c.y - c.h / 2, d = Math.hypot(dx, dy);
      if (d > CRATE_BREAK) { ungrab(r, h, GRAB_CD); continue; }
      if (d > CRATE_ROPE) { const k = (d - CRATE_ROPE) / d; moveCrate(r, c, dx * k, dy * k); }
      c.vy = 0; continue;
    }
    c.vy = Math.min(1150, c.vy + 2300 * DT);
    let left = c.vy * DT;
    while (left > 0) { const st = Math.min(left, 1.5); c.y += st; if (crBlocked(r, c)) { c.y -= st; c.vy = 0; break; } left -= st; }
    if (c.y > WH + 100) { c.x = c.sx; c.y = c.sy; c.vy = 0; }
  }
}

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
let pubN = 0;
const roomMax = r => r.pub ? PUB_SIZE : MAX_ROOM;   // public matches 5 (alternate classic / infection), private rooms 10
function mkRoom(key, pub) {
  const r = {
    key, pub: !!pub, players: new Map(), st: 'lobby', hostId: null,
    ord: [], rn: 0, gm: 0, practice: false, first: null, inf: pub ? (pubN++ & 1) : 0,
    loser: null, ln: null, win: null, wn: null,
    lobbyGo: 0, cdEnd: 0, deadline: 0, tagFrom: 0, betweenEnd: 0, lk: null,
    dec: [], pj: [], sm: [], tr: [], lt: [], cr: [], ltNext: 2, fxn: 0      // ability effects: decoys, smoke grenades in flight, smoke clouds, traps
  };
  return r;   // not registered yet: addPlayer() registers it together with its first player, so an empty room can never be left behind
}

const conn = r => { let n = 0; for (const p of r.players.values()) if (p.ws) n++; return n; };

function newPlayer(nm, ci) {
  return {
    id: hex(4), tk: hex(12), ws: null, nm, ci,
    q: [], lastIn: 0, lastSeq: 0, lastCmd: 0, dc: 0, gr: 0, credit: 0,
    alive: false, it: 0, rs: 0,
    x: 0, y: 0, vx: 0, vy: 0, g: 0, coy: 0, buf: 0, pj: false, cut: 0, drop: 0, face: 1,
    ps: false, dash: 0, dd: 1, dcd: 0, slow: 0, ab: 'fake', acd: 0, pa: 0, bst: 0, pcd: 0, bv: 0, zip: -1, zd: 1, zs: 0, zcd: 0,     // dash / ability / map-feature state (zip* = zipline)
    gt: '', hb: '', gk: 0, gs: 0, gl: 0, gcd: 0, gimm: 0, pg: false, ge: 0, gin: 0   // grab: target id, held-by id, state (0 idle / 1 reaching / 2 holding), timer, cooldown, immunity, button edge
  };
}

function bcastRoom(r) {
  const t = now();
  bcast(r, JSON.stringify({
    t: 'room', code: r.pub ? '' : r.key, pub: r.pub ? 1 : 0, st: r.st, host: r.hostId,
    rn: r.rn, gm: r.gm, practice: r.practice ? 1 : 0, inf: r.inf ? 1 : 0, first: r.first,
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
  p.x = 580 + k * 42; p.y = 502; p.vx = p.vy = 0; p.g = 0; p.coy = p.buf = p.cut = p.drop = 0; p.pj = false; p.face = 1;
  p.rs++; p.q.length = 0; p.lastCmd = t;
  p.ps = false; p.dash = 0; p.dd = 1; p.dcd = 0; p.slow = 0; p.acd = 0; p.pa = 0; p.bst = p.pcd = p.bv = 0; p.zip = -1; p.zd = 1; p.zs = 0; p.zcd = 0; resetGrab(p);   // every round starts with dash + ability + grab ready
}

function aliveIds(r) {
  return r.ord.filter(id => { const p = r.players.get(id); return p && p.alive; });
}

function startRound(r, ids, t) {
  r.rn++; r.st = 'play'; r.loser = r.ln = null; r.lk = null; r.ord = ids.slice(); clearFx(r); initCrates(r);
  const first = ids[rnd(ids.length)]; r.first = first;
  ids.forEach((id, k) => { const p = r.players.get(id); if (!p) return; spawn(p, k, t); p.alive = true; p.it = id === first ? 1 : 0; });
  for (const p of r.players.values()) if (!ids.includes(p.id)) { p.alive = false; p.it = 0; }
  r.evK = -1; r.evF = rnd(2); r.cdEnd = t + CD_MS; r.deadline = r.cdEnd + ROUND_S * 1000; r.tagFrom = r.cdEnd + TAG_GRACE_MS;
  bcastRoom(r);
}

function startMatch(r, t) {
  const ids = [...r.players.values()].filter(p => p.ws).map(p => p.id).slice(0, roomMax(r));   // only players who are actually connected
  if (!ids.length) return;
  r.gm = 1 + rnd(999999999); r.rn = 0; r.practice = ids.length === 1; r.win = r.wn = null; r.lobbyGo = 0;
  startRound(r, ids, t);
}

function finish(r, id) {
  const p = id && r.players.get(id);
  r.st = 'over'; r.win = id || null; r.wn = p ? p.nm : null; r.lobbyGo = 0; clearFx(r);
  for (const q of r.players.values()) q.it = 0;
  bcastRoom(r);
}

function toLobby(r) {
  r.st = 'lobby'; clearFx(r); r.ord = []; r.rn = 0; r.gm = 0; r.first = r.loser = r.win = r.ln = r.wn = null; r.lk = null; r.practice = false;
  for (const p of r.players.values()) { p.alive = false; p.it = 0; p.q.length = 0; }
  updateLobbyGo(r, now());
  bcastRoom(r);
}

function expire(r, t, holder) {
  r.loser = holder.id; r.ln = holder.nm; holder.alive = false; holder.it = 0;
  r.st = 'between'; r.betweenEnd = t + BETWEEN_MS; clearFx(r);
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

/* ---------------- abilities ---------------- */
function clearFx(r) { r.lt.length = 0; r.ltNext = 2; r.dec.length = 0; r.pj.length = 0; r.sm.length = 0; r.tr.length = 0; for (const p of r.players.values()) resetGrab(p); }

// Is this (grounded) player standing in a trap? Must match the client's slowAt().
function inTrap(r, p) {
  if (!r.tr.length || !p.g) return 0;
  for (const t of r.tr) {
    if (t.o === p.id && TRAP_T - t.life < TRAP_IMM) continue;                       // the owner may step off their own trap
    if (p.x + PW > t.x - TRAP_W / 2 && p.x < t.x + TRAP_W / 2 && Math.abs(p.y + PH - t.y) < 36) return 1;
  }
  return 0;
}

// The chosen ability was pressed (rising edge). The server owns the cooldown, so it can't be skipped.
function useAbility(r, p) {
  if (r.st !== 'play' || p.acd > 0) return;
  const k = p.ab;
  if (k === 'fake') {
    r.dec.push({ id: 'd' + (++r.fxn), o: p.id, life: FAKE_T, x: p.x, y: p.y, vx: p.vx, vy: p.vy, g: p.g, coy: 0, buf: 0, pj: false, cut: 0, drop: 0, face: p.face,
      it: p.it, dir: p.face, stuck: 0, ps: false, dash: 0, dd: 1, dcd: 0, slow: 0, bst: 0, pcd: 0, bv: 0 });
  } else if (k === 'smoke') {
    r.pj.push({ x: p.x + PW / 2, y: p.y + 8, vx: p.face * 520 + p.vx * .4, vy: -420, t: 0 });
  } else if (k === 'trap') {
    if (!p.g) return;                                                               // a trap needs floor under your feet (no cooldown is spent)
    r.tr.push({ id: ++r.fxn, x: Math.round(p.x + PW / 2), y: Math.round(p.y + PH), o: p.id, life: TRAP_T });
  } else return;
  p.acd = AB_CD;
  bcast(r, JSON.stringify({ t: 'abu', o: p.id, k }));
}

// Moves decoys / grenades and ages every effect (called once per tick while a round is running).
function tickFx(r) {
  for (let i = r.dec.length - 1; i >= 0; i--) {
    const d = r.dec[i], o = r.players.get(d.o);
    d.life -= DT; d.it = o && o.it ? 1 : 0;
    step(d, { l: d.dir < 0 ? 1 : 0, r: d.dir > 0 ? 1 : 0, j: 0, d: 0, s: 0 }, DT);          // a decoy runs along using the real physics
    if (Math.abs(d.vx) < 25) { if (++d.stuck > 10) { d.dir = -d.dir; d.stuck = 0; } } else d.stuck = 0;   // hit a wall: turn around
    if (d.life <= 0 || d.y > WH + 100) r.dec.splice(i, 1);
  }
  for (let i = r.pj.length - 1; i >= 0; i--) {
    const j = r.pj[i]; j.t += DT;
    let boom = j.t > 1.4, hitSolid = false;
    for (let s = 0; s < 4 && !boom; s++) {                                          // sub-steps: a fast grenade can't tunnel through a thin platform
      const ox = j.x, oy = j.y, h = DT / 4;
      j.vy = Math.min(1000, j.vy + 1500 * h); j.x += j.vx * h; j.y += j.vy * h;
      if (j.x < LX || j.x > RX) { j.x = ox; j.vx = -j.vx * .4; }
      for (const q of SOL) if (j.x > q.x && j.x < q.x + q.w && j.y > q.y && j.y < q.y + q.h) { j.x = ox; j.y = oy; boom = true; hitSolid = j.vy > 0; break; }   // landed on a floor (not a ceiling / side)
      if (j.y > WH + 40) boom = true;
    }
    if (boom) {
      r.pj.splice(i, 1);
      r.sm.push({ id: ++r.fxn, x: j.x, y: Math.min(j.y, WH - 60) - (hitSolid ? 38 : 0), life: SMOKE_T });
    }
  }
  for (let i = r.sm.length - 1; i >= 0; i--) if ((r.sm[i].life -= DT) <= 0) r.sm.splice(i, 1);
  for (let i = r.tr.length - 1; i >= 0; i--) if ((r.tr[i].life -= DT) <= 0) r.tr.splice(i, 1);
  if ((r.ltNext -= DT) <= 0) {                                                      // new warning circle somewhere random
    r.ltNext = LT_MIN + Math.random() * (LT_MAX - LT_MIN);
    r.lt.push({ id: ++r.fxn, x: ri(LX + LT_R + Math.random() * (RX - LX - 2 * LT_R)), y: ri(150 + Math.random() * 640), age: 0, hit: 0 });
  }
  for (let i = r.lt.length - 1; i >= 0; i--) {
    const z = r.lt[i]; z.age += DT;
    if (!z.hit && z.age >= LT_WARN) {                                               // STRIKE: launch everyone inside the circle
      z.hit = 1;
      for (const p of r.players.values()) {
        if (!p.alive) continue;
        const dx = p.x + PW / 2 - z.x, dy = p.y + PH / 2 - z.y;
        if (dx * dx + dy * dy > LT_R * LT_R) continue;
        if (p.gt) ungrab(r, p, GRAB_CD);
        if (p.hb) { const h = r.players.get(p.hb); if (h) ungrab(r, h, GRAB_CD); }
        p.vx = (dx < 0 ? -1 : 1) * LT_VX; p.vy = -LT_VY; p.g = 0; p.coy = p.buf = 0; p.cut = 1; p.dash = 0; p.drop = 0; p.zip = -1; p.bst = .9; p.rs++;
      }
    }
    if (z.age >= LT_WARN + LT_FLASH) r.lt.splice(i, 1);
  }
}

/* ---------------- grab ---------------- */
function resetGrab(p) { p.gk = 0; p.gt = ''; p.hb = ''; p.gs = 0; p.gl = 0; p.gcd = 0; p.gimm = 0; p.pg = false; p.ge = 0; p.gin = 0; }

// p lets go of whoever they hold; cd = seconds before p may grab again. The freed player is briefly immune to being re-grabbed.
function ungrab(r, p, cd) {
  if (p.gk) { const c = r.cr.find(x => x.id === p.gk); if (c && c.hb === p.id) c.hb = ''; p.gk = 0; }
  const q = p.gt && r.players.get(p.gt);
  if (q && q.hb === p.id) { q.hb = ''; q.gimm = GRAB_IMM; }
  p.gt = ''; p.gs = 0; p.gl = 0; p.gcd = cd;
}

const inSolid = p => { for (const s of SX) if (p.x < s.x + s.w && p.x + PW > s.x && p.y < s.y + s.h && p.y + PH > s.y) return true; return false; };

// the nearest player inside p's reach that nobody is holding yet
function grabTarget(r, p) {
  let best = null, bd = 1e9;
  for (const q of r.players.values()) {
    if (q === p || !q.alive || q.hb || q.gimm > 0) continue;
    if (!hit(p, q, -GRAB_REACH)) continue;                       // negative pad = the hitbox grown by the reach
    const d = Math.abs(p.x - q.x) + Math.abs(p.y - q.y);
    if (d < bd) { bd = d; best = q; }
  }
  return best;
}

// Drag q by (mx,my) but never into a wall / floor: try the full move, then x only, then y only.
function dragBy(q, mx, my) {
  const ox = q.x, oy = q.y;
  q.x = Math.max(LX, Math.min(RX - PW, ox + mx)); q.y = oy + my;
  if (!inSolid(q)) return;
  q.y = oy; if (!inSolid(q)) return;
  q.x = ox; q.y = oy + my; if (!inSolid(q)) return;
  q.x = ox; q.y = oy;
}

// Runs once per tick while a round is live (after everybody moved).
function grabTick(r) {
  for (const p of r.players.values()) {
    if (p.gcd > 0) p.gcd -= DT;
    if (p.gimm > 0) p.gimm -= DT;
    // links go stale when someone leaves / is out; a held player who DASHES breaks free
    if (p.hb) { const h = r.players.get(p.hb); if (!h || !h.alive || h.gt !== p.id) p.hb = ''; else if (p.dash > 0) ungrab(r, h, GRAB_CD); }
    if (p.gt) { const q = r.players.get(p.gt); if (!p.alive || !q || !q.alive || q.hb !== p.id) { p.gt = ''; p.gs = 0; p.gl = 0; p.gcd = GRAB_CD; } }
    if (p.gk) { const c = r.cr.find(x => x.id === p.gk); if (!p.alive || !c || c.hb !== p.id) { if (c && c.hb === p.id) c.hb = ''; p.gk = 0; p.gs = 0; p.gl = 0; p.gcd = GRAB_CD; } }
    if (!p.alive) continue;

    if (p.gs === 0 && p.ge && p.gcd <= 0 && !p.hb) { p.gs = 1; p.gl = GRAB_REACH_T; }   // button pressed: hands out
    p.ge = 0;
    if (p.gs === 1) {
      const q = p.hb ? null : grabTarget(r, p);
      const cc = (q || p.hb) ? null : grabCrate(r, p);
      if (q) { p.gs = 2; p.gt = q.id; q.hb = p.id; p.gl = GRAB_MAX; bcast(r, JSON.stringify({ t: 'grab', a: p.id, b: q.id })); }
      else if (cc) { p.gs = 2; p.gk = cc.id; cc.hb = p.id; p.gl = GRAB_MAX; bcast(r, JSON.stringify({ t: 'grab', a: p.id, b: 'c' })); }
      else { p.gl -= DT; if (!p.gin || p.gl <= 0 || p.hb) { p.gs = 0; p.gl = 0; p.gcd = GRAB_MISS_CD; } }   // nobody in reach: a miss
    } else if (p.gs === 2) {
      p.gl -= DT;
      if (p.gl <= 0 || (!p.gin && GRAB_MAX - p.gl >= GRAB_MIN)) ungrab(r, p, GRAB_CD);            // time's up / button let go
    }
  }
  // the rope: whoever is held can't get further than GRAB_ROPE from the grabber, so they get dragged along
  for (const p of r.players.values()) {
    if (p.gs !== 2) continue;
    const q = r.players.get(p.gt); if (!q) continue;
    const dx = q.x - p.x, dy = q.y - p.y, d = Math.hypot(dx, dy);
    if (d > GRAB_BREAK) { ungrab(r, p, GRAB_CD); continue; }       // stretched too far (fell off the map, got stuck behind a wall): the grip snaps
    if (d <= GRAB_ROPE) continue;
    const k = (d - GRAB_ROPE) / d;
    dragBy(q, -dx * k, -dy * k);
    const ux = dx / d, uy = dy / d, vr = q.vx * ux + q.vy * uy;      // remove the part of q's velocity that points away from the grabber
    if (vr > 0) { q.vx -= vr * ux; q.vy -= vr * uy; }
  }
}

/* ---------------- simulation ---------------- */
// Returns the input bit-mask to apply this tick, or -1 = "wait, the next input packet is probably in flight".
function consume(p, t) {
  const c = p.q.shift();
  if (c) { p.lastSeq = c.s; p.lastCmd = t; return c.b; }
  if (t - p.lastCmd < STALL_MS) return -1;   // short wait keeps us in lock-step with the client's prediction
  return 0;                                    // client is silent (hidden tab / lost signal): stand still, but keep playing
}

function advance(r, p, b) {
  step(p, { l: b & 1, r: b & 2, j: b & 4, d: b & 8, s: b & 16 }, DT);
  const ab = (b & 32) ? 1 : 0;                                                       // ability button: acts on the rising edge only
  if (ab && !p.pa) useAbility(r, p);
  p.pa = ab;
  const gb = (b & 64) ? 1 : 0;                                                       // grab button: the rising edge starts a grab, holding keeps it
  if (gb && !p.pg) p.ge = 1;
  p.pg = gb; p.gin = gb;
  if (p.y > WH + 200 || !(p.x + p.y + p.vx + p.vy < 1e9 && p.x + p.y + p.vx + p.vy > -1e9)) { p.x = 300 + Math.random() * 600; p.y = -60; p.vx = p.vy = 0; p.dash = 0; p.bst = p.pcd = p.bv = 0; p.zip = -1; p.zcd = 0; p.rs++; }   // fell out of the world (or numeric glitch): respawn
}

// events: every 40 s of play = 30 s normal + 10 s of either blackout or lava (the lava platform is flagged 2 s before)
function evState(r, t) {
  const el = (t - r.cdEnd) / 1000; if (el < 0) return null;
  const k = Math.floor(el / 40), ph = el - k * 40;
  if (r.evK !== k) { r.evK = k; r.evT = (k + r.evF) % 2 ? 'b' : 'l'; r.evP = rnd(18); }
  if (r.evT === 'b') return ph >= 30 ? ['b', 1, 0, 40 - ph] : null;
  return ph >= 28 ? ['l', ph < 30 ? 0 : 1, r.evP, ph < 30 ? 30 - ph : 40 - ph] : null;
}

function simRoom(r, t) {
  SX = r.cr.length ? SOL.concat(r.cr) : SOL;
  const cd = r.st === 'play' && t < r.cdEnd;
  for (const p of r.players.values()) {
    if (!p.alive) continue;
    if (p.acd > 0) p.acd -= DT;                                           // ability cooldown
    p.slow = inTrap(r, p);                                                // standing in a trap?
    let b = consume(p, t);
    if (b === -1) { p.credit = Math.min(8, p.credit + 1); continue; }   // a late packet: the player earns ONE catch-up step (never more than 1 per missed tick)
    advance(r, p, cd ? 0 : b);
    // after a lag spike a burst of inputs arrives: spend earned credit to catch up. A flooding cheater has no credit, so they can't go faster than 60 steps/s.
    while (p.credit > 0 && p.q.length > 1) { p.credit--; { const c2 = p.q.shift(); p.lastSeq = c2.s; advance(r, p, cd ? 0 : c2.b); } }
  }

  if (r.st === 'between') { if (t >= r.betweenEnd) { const al = aliveIds(r); if (al.length >= 2) startRound(r, al, t); else finish(r, al[0]); } return; }
  if (r.st !== 'play' || cd) return;
  tickFx(r);
  const ev = evState(r, t);
  if (ev && ev[0] === 'l' && ev[1] === 1) {
    const q = PL[ev[2]];
    for (const p of r.players.values()) if (p.alive && p.g && Math.abs(p.y + PH - q.y) < 3 && p.x + PW > q.x && p.x < q.x + q.w) {   // standing on lava: burn, respawn on the ground
      p.x = 300 + Math.random() * 600; p.y = 800 - PH - 1; p.vx = p.vy = 0; p.g = 1; p.dash = 0; p.bst = p.pcd = p.bv = 0; p.zip = -1; p.zcd = 0; resetGrab(p); p.rs++;
    }
  }
  grabTick(r);
  crateTick(r);
  if (r.inf) {   // INFECTION: every infected player spreads it by touch; the last healthy player wins
    const al = aliveIds(r).map(id => r.players.get(id));
    if (!al.some(p => p.it) && al.length) al[rnd(al.length)].it = 1;
    if (t >= r.tagFrom) for (const q of al) if (!q.it) for (const h of al) if (h.it && hit(h, q, 3)) { q.it = 1; r.lastInf = q.id; break; }
    const hl = al.filter(p => !p.it);
    if (!r.practice && al.length > 1) { if (hl.length <= 1) finish(r, hl.length ? hl[0].id : r.lastInf); }
    return;
  }

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
      if (holder.gt === q.id) ungrab(r, holder, GRAB_CD); else if (q.gt === holder.id) ungrab(r, q, GRAB_CD);   // a tag ends the grip between the two
      r.lk = { from: holder.id, to: q.id, until: t + LOCK_MS };
      bcast(r, JSON.stringify({ t: 'tag', a: q.id, b: holder.id }));
      holder = q;
      break;
    }
  }
  // the arrow holder who runs into a decoy pops it (the holder's own decoys are ignored)
  for (let i = r.dec.length - 1; i >= 0; i--) if (r.dec[i].o !== holder.id && hit(holder, r.dec[i], 3)) r.dec.splice(i, 1);
  if (!r.practice && t >= r.deadline) expire(r, t, holder);
}

function snapshot(r, t, tt) {
  let arr = '';
  for (const p of r.players.values()) if (p.alive) arr += (arr ? ',' : '') + '["' + p.id + '",' + r1(p.x) + ',' + r1(p.y) + ',' + ri(p.vx + p.bv) + ',' + ri(p.vy) + ',' + p.face + ',' + (p.g ? 1 : 0) + ',' + (p.it ? 1 : 0) + ']';
  const tl = r.practice || r.inf ? 'null' : r.st === 'play' ? Math.min(ROUND_S, Math.max(0, (r.deadline - t) / 1000)).toFixed(2) : '0';
  let fx = '';                                                           // ability effects (only when something is active)
  if (r.dec.length) fx += ',"d":[' + r.dec.map(d => '["' + d.id + '",' + r1(d.x) + ',' + r1(d.y) + ',' + ri(d.vx + d.bv) + ',' + ri(d.vy) + ',' + d.face + ',' + (d.g ? 1 : 0) + ',0,"' + d.o + '"]').join(',') + ']';
  if (r.pj.length) fx += ',"j":[' + r.pj.map(j => '[' + ri(j.x) + ',' + ri(j.y) + ']').join(',') + ']';
  if (r.sm.length) fx += ',"s":[' + r.sm.map(s => '[' + s.id + ',' + ri(s.x) + ',' + ri(s.y) + ',' + r1(s.life) + ']').join(',') + ']';
  if (r.lt.length) fx += ',"lt":[' + r.lt.map(z => '[' + z.id + ',' + z.x + ',' + z.y + ',' + r1(z.age) + ']').join(',') + ']';
  if (r.tr.length) fx += ',"tr":[' + r.tr.map(x => '[' + x.id + ',' + x.x + ',' + x.y + ',' + r1(x.life) + ',"' + x.o + '"]').join(',') + ']';
  let gb = '', gr = '';                                                  // who is holding whom / who has their hands out
  for (const p of r.players.values()) { if (!p.alive) continue; if (p.gs === 2 && p.gt) gb += (gb ? ',' : '') + '["' + p.id + '","' + p.gt + '"]'; else if (p.gs === 1) gr += (gr ? ',' : '') + '"' + p.id + '"'; }
  if (r.cr.length) fx += ',"c":[' + r.cr.map(c => '[' + c.id + ',' + r1(c.x) + ',' + r1(c.y) + ',' + (c.hb ? '"' + c.hb + '"' : 0) + ']').join(',') + ']';
  if (gb) fx += ',"gb":[' + gb + ']'; if (gr) fx += ',"gr":[' + gr + ']';
  if (r.st === 'play') { const ev = evState(r, t); if (ev) fx += ',"ev":["' + ev[0] + '",' + ev[1] + ',' + ev[2] + ',' + r1(ev[3]) + ']'; }
  const head = '{"t":"s","ts":' + tt.toFixed(1) + ',"tl":' + tl + ',"cd":' + Math.max(0, (r.cdEnd - t) / 1000).toFixed(2) + ',"p":[' + arr + ']' + fx;
  for (const p of r.players.values()) {
    if (!p.ws) continue;
    // full-precision state of the receiver, used for client-side prediction + reconciliation
    const a = p.alive ? ',"a":{"x":' + r4(p.x) + ',"y":' + r4(p.y) + ',"vx":' + r4(p.vx) + ',"vy":' + r4(p.vy) + ',"g":' + (p.g ? 1 : 0) + ',"coy":' + r4(p.coy) + ',"buf":' + r4(p.buf) + ',"pj":' + (p.pj ? 'true' : 'false') + ',"cut":' + (p.cut ? 1 : 0) + ',"drop":' + r4(p.drop) + ',"face":' + p.face + ',"it":' + (p.it ? 1 : 0) + ',"dash":' + r4(p.dash) + ',"dd":' + p.dd + ',"dcd":' + r4(p.dcd) + ',"ps":' + (p.ps ? 'true' : 'false') + ',"ac":' + r1(Math.max(0, p.acd)) + ',"gs":' + p.gs + ',"gt":' + (p.gt ? 1 : 0) + ',"hb":' + (p.hb ? 1 : 0) + ',"gk":' + (p.gk ? 1 : 0) + ',"gc":' + r1(Math.max(0, p.gcd)) + ',"bs":' + r4(Math.max(0, p.bst)) + ',"pc":' + r4(Math.max(0, p.pcd)) + ',"z":' + p.zip + ',"zd":' + p.zd + ',"zs":' + r4(p.zs) + ',"zc":' + r4(Math.max(0, p.zcd)) + ',"q":' + p.lastSeq + ',"rs":' + p.rs + '}' : '';
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
    send(ws, JSON.stringify({ t: 'hello', id: pp.id, tk: pp.tk, rk: rr.key, code: rr.pub ? '' : rr.key, pub: rr.pub ? 1 : 0, ab: pp.ab }));
  };
  const addPlayer = (rr, nm) => {
    if (rr.players.size >= roomMax(rr) && rr.st === 'lobby') {                  // a disconnected "ghost" never blocks a real player from a lobby
      for (const q of rr.players.values()) if (!q.ws) { rr.players.delete(q.id); break; }
    }
    if (rr.players.size >= roomMax(rr)) return err('full');                       // single choke point: no path can exceed the room limit
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
        if (!Number.isInteger(s) || !Number.isInteger(b) || b < 0 || b > 127 || s <= p.lastIn) continue;
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
        if (rr.players.size >= roomMax(rr)) return err('full');
        if (rr.practice && rr.st !== 'lobby') toLobby(rr);   // a solo practice game has no end: someone joining brings everybody back to the lobby
        return addPlayer(rr, cleanName(m.nm));          // joining a running match = spectate until the next game
      }
      if (m.t === 'quick') {
        let best = null;
        for (const rr of rooms.values()) {
          if (!rr.pub || rr.st !== 'lobby' || conn(rr) >= PUB_SIZE) continue;
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

    /* ---- ability choice: in the lobby (spectators waiting for the next match may pick too) ---- */
    if (m.t === 'ab') { if (typeof m.k === 'string' && ABIL.has(m.k) && (r.st === 'lobby' || !p.alive)) p.ab = m.k; return; }

    /* ---- room controls ---- */
    if (m.t === 'mode' && r.st === 'lobby' && !r.pub && r.hostId === p.id) { r.inf = m.m ? 1 : 0; return bcastRoom(r); }
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