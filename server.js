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
const PUB_SIZE = 10;           // public match starts when this many are waiting
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
const classicS = n => Math.max(25, 70 - 6 * n);   // classic: seconds per elimination, shrinks as players grow (2p 58s, 3p 52s, 5p 40s, 8+p 25s)

const FREEZE_S = 300;          // freeze tag: always 300 s

const roundS = r => r.rs || (r.inf === 2 ? FREEZE_S : r.inf === 0 ? classicS(2) : ROUND_S);
const CD_MS = 2200;            // 3-2-1-GO countdown before each round
const TAG_GRACE_MS = 300;      // nobody can be tagged right after GO
const BETWEEN_MS = 3200;       // pause after someone is eliminated
const BOT_GAP_MS = 2000;       // public lobby not full: one bot joins every 2 s (a real player takes a bot's seat)
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

const parties = new Map();     // friends waiting together before entering a public lobby
const PARTY_MAX = 3;
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

/* ---------------- accounts: username + password, stats saved per account in Upstash Redis (free, external: survives Render restarts/redeploys) ---------------- */
const UP_URL = (process.env.UPSTASH_REDIS_REST_URL || '').replace(/\/$/, ''), UP_TOK = process.env.UPSTASH_REDIS_REST_TOKEN || '';
if (!UP_URL) console.warn('WARNING: UPSTASH_REDIS_REST_URL not set - accounts are kept in memory only and are LOST on restart!');
const MEM = new Map();   // fallback store for local testing
async function db(...cmds) {   // runs commands as one pipeline, returns the array of results
  if (!UP_URL) return cmds.map(([op, k, v, nx]) => op === 'GET' ? (MEM.has(k) ? MEM.get(k) : null) : op === 'DEL' ? (MEM.delete(k), 1) : (nx && MEM.has(k)) ? null : (MEM.set(k, v), 'OK'));
  const r = await fetch(UP_URL + '/pipeline', { method: 'POST', headers: { Authorization: 'Bearer ' + UP_TOK }, body: JSON.stringify(cmds) });
  if (!r.ok) throw new Error('db ' + r.status);
  return (await r.json()).map(x => { if (x.error) throw new Error(x.error); return x.result; });
}
const sha = s => crypto.createHash('sha256').update(s).digest('hex');
const ACC = new Map(), byTok = new Map(), dirty = new Set();   // in-memory caches of what the DB holds
let accT = 0;
async function getAcc(k) { let a = ACC.get(k); if (a) return a; const [v] = await db(['GET', 'acc:' + k]); if (!v) return null; a = ACC.get(k) || JSON.parse(v); ACC.set(k, a); return a; }
async function tokAcc(tk) {
  if (typeof tk !== 'string' || !tk || tk.length > 64) return null;
  const h = sha(tk); let a = byTok.get(h); if (a) return a;
  const [k] = await db(['GET', 'tok:' + h]); a = k ? await getAcc(k) : null; if (a) byTok.set(h, a); return a;
}
async function newTok(a) {
  const tk = hex(24), h = sha(tk), cmds = [['SET', 'tok:' + h, a.k]]; a.tk.push(h); byTok.set(h, a);
  while (a.tk.length > 5) { const o = a.tk.shift(); byTok.delete(o); cmds.push(['DEL', 'tok:' + o]); }
  cmds.push(['SET', 'acc:' + a.k, JSON.stringify(a)]); await db(...cmds); return tk;
}
function accSave(a) { dirty.add(a); if (!accT) accT = setTimeout(accFlush, 3000); }   // stats are batched into one request
async function accFlush() {
  accT = 0; if (!dirty.size) return;
  const l = [...dirty]; dirty.clear();
  try { await db(...l.map(a => ['SET', 'acc:' + a.k, JSON.stringify(a)])); }
  catch (e) { console.error('account save failed:', e.message); for (const a of l) dirty.add(a); if (!accT) accT = setTimeout(accFlush, 10000); }
}
const accOut = (a, tk) => ({ ok: 1, u: a.n, tk, st: { p: a.p, w: a.w, l: a.l } });
const LIVE = new WeakMap(), authIp = new Map(), socIp = new Map(), INV = new Map(); setInterval(() => { authIp.clear(); socIp.clear(); }, 60000).unref();
function authReq(req, res) {
  const out = (c, o) => { res.writeHead(c, { 'Content-Type': 'application/json', 'Cache-Control': 'no-store', 'Access-Control-Allow-Origin': '*' }); res.end(JSON.stringify(o)); };
  const ip = String(req.headers['cf-connecting-ip'] || req.headers['x-forwarded-for'] || req.socket.remoteAddress || '').split(',')[0].trim();
  let b = ''; req.on('data', d => { b += d; if (b.length > 1024) req.destroy(); });
  req.on('end', async () => {
    try {
      let m; try { m = JSON.parse(b); } catch { return out(400, { e: 'bad' }); }
      if (!m || typeof m !== 'object') return out(400, { e: 'bad' });
      const soc = m.m === 'soc', mp = soc ? socIp : authIp, n = (mp.get(ip) || 0) + 1; mp.set(ip, n);
      if (n > (soc ? 90 : 30)) return out(429, { e: 'rate' });
      if (m.m === 'soc') {   // friends: poll + add / accept / decline / remove / invite
        const me = await tokAcc(m.tk); if (!me) return out(401, { e: 'tk' });
        me.f = me.f || []; me.rq = me.rq || [];
        const a = m.a, nm = String(m.n || '').toLowerCase(), T = /^[a-z0-9_]{3,12}$/.test(nm) ? await getAcc(nm) : null;
        if (T) { T.f = T.f || []; T.rq = T.rq || []; }
        if (a === 'add') {
          if (!T) return out(404, { e: 'nf' }); if (T.k === me.k) return out(400, { e: 'self' });
          if (me.f.includes(T.k)) return out(400, { e: 'dup' });
          if (me.rq.includes(T.k)) { me.rq = me.rq.filter(x => x !== T.k); me.f.push(T.k); T.f.push(me.k); accSave(T); }   // they already asked me: instant friends
          else if (!T.rq.includes(me.k) && T.rq.length < 30) { T.rq.push(me.k); accSave(T); }
          accSave(me);
        } else if ((a === 'acc' || a === 'dec') && T && me.rq.includes(T.k)) {
          me.rq = me.rq.filter(x => x !== T.k);
          if (a === 'acc' && me.f.length < 50) { if (!me.f.includes(T.k)) me.f.push(T.k); if (!T.f.includes(me.k)) T.f.push(me.k); accSave(T); }
          accSave(me);
        } else if (a === 'rm' && T) {
          me.f = me.f.filter(x => x !== T.k); T.f = T.f.filter(x => x !== me.k); accSave(T); accSave(me);
        } else if (a === 'inv') {
          const c = String(m.c || '').toUpperCase(), P = parties.get(c), R = !P && rooms.get(c);
          const ok = P ? (P.mem.size < PARTY_MAX && [...P.mem.values()].some(q => q.ws && q.ws.acct === me)) : !!(R && !R.pub && R.st === 'lobby' && R.players.size < roomMax(R) && [...R.players.values()].some(q => q.acct === me));
          if (!T || !me.f.includes(T.k) || !ok) return out(400, { e: 'nop' });
          const l = (INV.get(T.k) || []).filter(x => x.n !== me.n && Date.now() - x.t < 120000); l.push({ n: me.n, c, t: Date.now(), r: P ? 0 : 1 }); INV.set(T.k, l);
        } else if (a === 'idis' && T) INV.set(me.k, (INV.get(me.k) || []).filter(x => x.n !== T.n));
        const on = new Set(); for (const w of wss.clients) if (w.acct && w.readyState === 1) on.add(w.acct.k);
        const fl = [], rq = [];
        for (const k of me.f) { const f = await getAcc(k); if (f) fl.push({ n: f.n, on: on.has(f.k) ? 1 : 0, p: f.p, w: f.w, l: f.l }); }
        for (const k of me.rq) { const f = await getAcc(k); if (f) rq.push(f.n); }
        const inv = (INV.get(me.k) || []).filter(x => Date.now() - x.t < 120000 && (parties.has(x.c) || rooms.has(x.c))).map(x => ({ n: x.n, c: x.c, r: x.r ? 1 : 0 }));
        return out(200, { ok: 1, f: fl, rq, inv });
      }
      if (m.m === 'tk') { const a = await tokAcc(m.tk); return a ? out(200, accOut(a, m.tk)) : out(401, { e: 'tk' }); }
      const u = String(m.u || ''), pw = String(m.p || ''), k = u.toLowerCase();
      if (!/^[A-Za-z0-9_]{3,12}$/.test(u) || pw.length < 4 || pw.length > 64) return out(400, { e: 'bad' });
      const scr = salt => new Promise((ok, no) => crypto.scrypt(pw, salt, 32, (e, d) => e ? no(e) : ok(d)));
      if (m.m === 'reg') {
        if (await getAcc(k)) return out(409, { e: 'taken' });
        const salt = hex(16), a = { k, n: u, s: salt, h: (await scr(salt)).toString('hex'), p: 0, w: 0, l: 0, tk: [] };
        const [ok] = await db(['SET', 'acc:' + k, JSON.stringify(a), 'NX']);   // NX: two people can never grab the same name
        if (!ok) return out(409, { e: 'taken' });
        ACC.set(k, a); return out(200, accOut(a, await newTok(a)));
      }
      if (m.m === 'login') {
        const a = await getAcc(k); if (!a) return out(401, { e: 'cred' });
        if (!crypto.timingSafeEqual(await scr(a.s), Buffer.from(a.h, 'hex'))) return out(401, { e: 'cred' });
        return out(200, accOut(a, await newTok(a)));
      }
      out(400, { e: 'bad' });
    } catch (e) { console.error('auth error:', e.message); try { out(503, { e: 'busy' }); } catch {} }
  });
}
function rec(p, win) {   // one finished (or abandoned) match -> played +1, won/lost +1
  if (!p.rec || !p.acct) return; p.rec = 0;
  const a = p.acct; a.p++; if (win) a.w++; else a.l++; accSave(a);
  sendP(p, JSON.stringify({ t: 'st', p: a.p, w: a.w, l: a.l }));
}

const server = http.createServer((req, res) => {
  const url = (req.url || '/').split('?')[0];

  if (url === '/healthz') {
    res.writeHead(200, { 'Content-Type': 'text/plain', 'Cache-Control': 'no-store' });
    return res.end('ok');
  }
  if (url === '/stats') {
    let waiting = 0; const wm = [0, 0, 0];

    for (const r of rooms.values()) if (r.pub && r.st === 'lobby') { waiting += r.players.size; wm[r.inf] += conn(r); }
    res.writeHead(200, { 'Content-Type': 'application/json', 'Cache-Control': 'no-store' });
    return res.end(JSON.stringify({ online: wss.clients.size, waiting, wm }));
  }
  if (url === '/auth') {
    if (req.method === 'OPTIONS') { res.writeHead(204, { 'Access-Control-Allow-Origin': '*', 'Access-Control-Allow-Methods': 'POST', 'Access-Control-Allow-Headers': 'Content-Type' }); return res.end(); }
    if (req.method === 'POST') return authReq(req, res);
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
let PL = [[22,304,133],[191,384,99],[48,451,100],[334,451,210],[22,536,358],[323,626,227],[106,707,183],[572,354,209],[764,277,209],[606,451,365],[538,536,482],[837,586,203],[956,354,332],[1154,284,201],[1455,399,73],[1161,512,273],[1148,622,195],[1046,712,446],[22,800,1548]].map(a => ({ x: a[0], y: a[1], w: a[2], h: a[1] == 800 ? 36 : 14 }));
let SX = null, SOL = PL, SL = []; SX = SOL;                                                             // solid rectangles: just the platforms, the arena is wide open

/* ---- MAP FEATURES (the client has an identical copy; both run inside step()) ----
   PADS : launch pads. vx=0 -> straight up; vx!=0 -> a cannon that also shoots you sideways.
   ZIPS : ziplines, completely optional. Tap JUMP in the air next to a cable to grab it and ride it (left/right picks the direction),
          tap JUMP again to hop off, or just ride to the end. Every cable must run left -> right (x1 < x2). */
let PADS = [
  { x: 1524, y: 800, w: 44, vy: 1500, vx: 0 },       // bottom-right corner of the floor: straight up (steer left in the air to land on the right-side decks)
  { x: 417, y: 451, w: 44, vy: 1300, vx: 0 }         // middle of the platform up-right of the left tower: straight up, right through the diagonal cable
];
let ZIPS = [
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
  const was = p.g, fy0 = p.y + PH, px0 = p.x; p.x += p.vx * dt;
  if (p.x < LX) { p.x = LX; p.vx = 0; } if (p.x > RX - PW) { p.x = RX - PW; p.vx = 0; }
  for (const q of SX) if (ov(q)) { if (was && p.y + PH - q.y <= 9) p.y = q.y - PH; else { p.x = p.vx > 0 ? q.x - PW : p.vx < 0 ? q.x + q.w : (p.x + PW / 2 < q.x + q.w / 2 ? q.x - PW : q.x + q.w); p.vx = 0; } }
  p.g = 0; p.y += p.vy * dt;
  for (const q of SX) if (ov(q)) {
    if (p.vy >= 0) { p.y = q.y - PH; p.vy = 0; p.g = 1; }
    else { const l = p.x + PW - q.x, r = q.x + q.w - p.x; if (Math.min(l, r) < 10) p.x += l < r ? -l : r; else { p.y = q.y + q.h; p.vy = 0; } }
  }
  if (SL.length) { const mx = p.x + PW / 2, f = p.y + PH; for (const q of SL) { if (mx < q.x || mx > q.x + q.w) continue; const s = q.y + (mx - q.x) / q.w * q.dy, b = s + q.hv;
    if (p.vy >= 0 && (was ? (fy0 >= s - 26 && fy0 <= s + 20) : (fy0 <= s + 2 && f >= s - 1))) { p.y = s - PH; p.vy = 0; p.g = 1; break; }
    if (f > s + 2 && p.y < b) { if (p.y + PH / 2 > s + q.hv / 2) { if (was && p.g) { p.x = px0; p.vx = 0; } else { p.y = b; if (p.vy < 0) p.vy = 0; } } else { p.y = s - PH; p.vy = 0; p.g = 1; } break; } } }
  if (p.g) for (const q of PADS) if (Math.abs(p.y + PH - q.y) < 3 && p.x + PW > q.x + 4 && p.x < q.x + q.w - 4) {      // launch pad / cannon
    p.vy = -q.vy; p.g = 0; p.coy = 0; p.buf = 0; p.cut = 1; p.dash = 0;
    if (q.vx) { p.vx = q.vx; p.face = q.vx > 0 ? 1 : -1; p.bst = PAD_BST; }
    break;
  }
}
const onQ = (q, p) => q.dy ? (p.x + PW / 2 >= q.x && p.x + PW / 2 <= q.x + q.w && Math.abs(p.y + PH - (q.y + (p.x + PW / 2 - q.x) / q.w * q.dy)) < 4) : (Math.abs(p.y + PH - q.y) < 3 && p.x + PW > q.x && p.x < q.x + q.w);
const hit = (a, b, pad) => a.x < b.x + PW - pad && a.x + PW > b.x + pad && a.y < b.y + PH - pad && a.y + PH > b.y + pad;
/* Lag compensation: the player who tags sees the others ~RTT+interp-delay in the past (and himself predicted in the present), so contact is judged on HIS screen:
   his current position against the other player's position from that many ticks ago. A bot holder has no screen -> the human runner's screen decides. */
const LAGC_MAX = 10, LAGC_EXTRA = 55;
const lagK = p => Math.min(LAGC_MAX, Math.round((((p.ws && p.ws.rtt) || 0) + LAGC_EXTRA) / TICK_MS));
const hitRew = (a, b, k) => { const i = (b.hi - k) & 31, x = b.hx[i], y = b.hy[i]; return a.x < x + PW - 3 && a.x + PW > x + 3 && a.y < y + PH - 3 && a.y + PH > y + 3; };
function tagHit(h, q) {
  if (!h.bot && h.ws) return hitRew(h, q, lagK(h));
  if (!q.bot && q.ws) return hitRew(q, h, lagK(q));
  return hit(h, q, 3);
}

/* ---------------- crates: solid boxes; hold GRAB next to one to drag it ---------------- */
const CS = 40, CRATE_ROPE = 64, CRATE_BREAK = 220;
/* ---- MAPS: pl = [x,y,w] platforms (floor y=800 last), pads, zips (x1<x2), cr = crate spots (top-left, 40x40, resting on a platform), sp = spawn of player 0 (+42 px per player) ---- */
const mkZ = z => { const dx = z.x2 - z.x1, dy = z.y2 - z.y1, len = Math.hypot(dx, dy); return { x1: z.x1, y1: z.y1, x2: z.x2, y2: z.y2, len, ux: dx / len, uy: dy / len }; };
const mkP = a => a.map(v => ({ x: v[0], y: v[1], w: v[2], h: v[1] == 800 ? 36 : 14, dy: v[3] || 0, hv: 14 * (v[3] ? Math.sqrt(1 + (v[3] / v[2]) ** 2) : 1) }));
const MAPS = [
  { pl: PL.map(q => [q.x, q.y, q.w]), pads: PADS, zips: ZIPS.map(z => ({ x1: z.x1, y1: z.y1, x2: z.x2, y2: z.y2 })), cr: [[300,760],[1250,760],[700,411],[1100,314],[120,496],[1300,672],[480,411]], sp: [580, 502] },   // 0 classic
  { pl: [[435,408,380],[1203,325,196],[887,487,176],[171,547,468],[22,659,167],[605,653,198],[366,721,224],[73,409,137,-138],[946,716,336,-265],[1250,583,256,-222],[22,800,1548]],
    pads: [{"x":284,"y":547,"w":44,"vy":1250,"vx":0},{"x":1518,"y":800,"w":44,"vy":1400,"vx":0}], zips: [{"x1":350,"y1":691,"x2":1273,"y2":177}], cr: [[610,368],[1282,285],[967,447],[417,507],[468,681],[702,613],[700,760],[1200,760]], sp: [50, 600] },   // 1 frozen peaks
  { pl: [[628,238,230],[1357,277,192],[83,367,119],[1138,388,285],[106,518,423],[977,507,237],[22,620,81],[1180,618,279],[66,715,131],[1372,725,198],[465,300,260,200],[805,500,260,-200],[22,800,1548]],
    pads: [{"x":743,"y":800,"w":44,"vy":1700,"vx":0}], zips: [{"x1":136,"y1":247,"x2":663,"y2":114},{"x1":781,"y1":107,"x2":1456,"y2":211}], cr: [[733,198],[1435,237],[1231,348],[264,478],[1079,467],[1282,578],[400,760]], sp: [50, 570] }   // 2 desert ruins
];
for (const m of MAPS) m.raw = { pl: m.pl, pads: m.pads, zips: m.zips };
const COMP = MAPS.map(m => ({ PL: mkP(m.pl), PADS: m.pads, ZIPS: m.zips.map(mkZ) }));
let CURMAP = 0;
function setMap(i) { const c = COMP[i]; PL = c.PL; SOL = PL.filter(q => !q.dy); SL = PL.filter(q => q.dy); PADS = c.PADS; ZIPS = c.ZIPS; CURMAP = i; }
function initCrates(r) { r.cr = MAPS[r.mp].cr.map((a, i) => ({ id: i + 1, x: a[0], y: a[1], w: CS, h: CS, sx: a[0], sy: a[1], vy: 0, hb: '' })); }
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
  if (droppable && ws.bufferedAmount > 16384) return;                    // slow link: skip a stale snapshot (the next one is 16 ms away) instead of queueing latency
  ws.send(s);
}
const sendP = (p, s, drop) => { if (p.ws) send(p.ws, s, drop); };
const bcast = (r, s, drop) => { for (const p of r.players.values()) sendP(p, s, drop); };

/* ---------------- rooms ---------------- */
let pubN = 0;
const roomMax = r => r.pub ? PUB_SIZE : MAX_ROOM;   // public matches 10 (alternate classic / infection), private rooms 10
function mkRoom(key, pub, md) {
  const r = {
    key, pub: !!pub, players: new Map(), st: 'lobby', hostId: null,
    ord: [], rn: 0, gm: 0, mp: 0, practice: false, first: null, inf: pub ? (md | 0) % 3 : 0, sel: 0,
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
    rdy: 0, q: [], lastIn: 0, lastSeq: 0, lastCmd: 0, dc: 0, gr: 0, credit: 0, lastB: 0, starve: 0, debt: 0, hx: new Float32Array(32), hy: new Float32Array(32), hi: 0, hrs: -1,
    alive: false, it: 0, rs: 0,
    x: 0, y: 0, vx: 0, vy: 0, g: 0, coy: 0, buf: 0, pj: false, cut: 0, drop: 0, face: 1,
    ps: false, dash: 0, dd: 1, dcd: 0, slow: 0, ab: 'fake', acd: 0, pa: 0, bst: 0, pcd: 0, bv: 0, zip: -1, zd: 1, zs: 0, zcd: 0,     // dash / ability / map-feature state (zip* = zipline)
    gt: '', hb: '', gk: 0, fz: 0, lv: 0, fimm: 0, gs: 0, gl: 0, gcd: 0, gimm: 0, pg: false, ge: 0, gin: 0   // grab: target id, held-by id, state (0 idle / 1 reaching / 2 holding), timer, cooldown, immunity, button edge
  };
}

function bcastRoom(r) {
  const t = now();
  bcast(r, JSON.stringify({
    t: 'room', code: r.pub ? '' : r.key, pub: r.pub ? 1 : 0, st: r.st, host: r.hostId,
    rn: r.rn, gm: r.gm, mp: r.mp, md: r.st === 'lobby' ? 0 : MAPS[r.mp].raw, practice: r.practice ? 1 : 0, inf: r.inf, sl: r.sel, first: r.first,
    loser: r.loser, ln: r.ln, win: r.win, wn: r.wn, wt: r.wt | 0,
    lc: r.lobbyGo ? Math.max(0, (r.lobbyGo - t) / 1000) : 0,
    pl: [...r.players.values()].filter(p => p.ws || p.bot || r.st === 'play' || r.st === 'between').map(p => ({ id: p.id, nm: p.nm, ci: p.ci, al: p.alive ? 1 : 0, rd: p.rdy ? 1 : 0 }))
  }));
}

const tot = r => { let n = 0; for (const p of r.players.values()) if (p.ws || p.bot) n++; return n; };   // humans + bots
function updateLobbyGo(r, t) {
  if (!r.pub || r.st !== 'lobby') return;
  while (tot(r) > PUB_SIZE) { const b = [...r.players.values()].find(p => p.bot); if (!b) break; r.players.delete(b.id); }   // a real player takes a bot's seat
  if (tot(r) >= PUB_SIZE) { if (!r.lobbyGo) r.lobbyGo = t + LOBBY_GO_MS; }
  else r.lobbyGo = 0;
  r.botNext = conn(r) >= 1 && tot(r) < PUB_SIZE ? (r.botNext || t + BOT_GAP_MS) : 0;   // bots join one by one while people are waiting
}

const BOT_NAMES = ['Zed', 'Mika', 'Rex', 'Nova', 'Kai', 'Luna', 'Jax', 'Pixel', 'Turbo', 'Echo', 'Blaze', 'Milo'];
function addBots(r, cnt) {
  const used = new Set([...r.players.values()].map(p => p.ci)), nm = new Set([...r.players.values()].map(p => p.nm));
  for (let need = cnt; need > 0; need--) {
    let ci = 0; while (used.has(ci)) ci++; used.add(ci); ci %= 10;
    let n; do { n = BOT_NAMES[rnd(BOT_NAMES.length)]; } while (nm.has(n)); nm.add(n);
    const b = newPlayer(n, ci); b.bot = true; b.since = now(); b.btk = 0; b.bst2 = 0; b.stk = 0; b.tc = 0; b.tid = ''; b.tx = b.ty = 0; b.sx = 0; b.sy = 0; b.pl = null;
    r.players.set(b.id, b);
  }
}

/* ---- bots: every 8 ticks they try 12 short plans on a copy of their own body (same physics as the real game), look ~0.5 s ahead and pick the best one ---- */
function botInput(r, p, t) {
  if (p.fz || t < r.cdEnd) return 0;
  if (p.btk-- <= 0) { p.btk = 12; botPlan(r, p); p.k = 0; }
  const pl = p.pl; if (!pl) return 0;
  const k = p.k++;
  return (pl.d < 0 ? 1 : pl.d > 0 ? 2 : 0) | (k < pl.j ? 4 : 0) | (pl.s && k === 0 ? 16 : 0);
}
function botPlan(r, p) {
  let near = null, nd = 1e9, rescue = null, rd = 1e9, thr = null, td = 1e9;
  for (const q of r.players.values()) {
    if (q === p || !q.alive) continue;
    const d = Math.hypot(q.x - p.x, (q.y - p.y) * 1.2);
    if (p.it) { if (!q.it && !q.fz && d < nd) { nd = d; near = q; } }
    else if (q.it) { if (d < td) { td = d; thr = q; } }
    else if (r.inf === 2 && q.fz && d < rd) { rd = d; rescue = q; }
  }
  let tg = null, chase = true;
  if (p.it) tg = near;
  else if (rescue && td > 320) tg = rescue;
  else { tg = thr; chase = false; }
  if (!tg) { p.pl = { d: 0, j: 0, s: 0 }; return; }
  if (Math.hypot(p.x - p.sx, p.y - p.sy) < 6 && ++p.stk > 12 && chase) { p.stk = 0; p.pl = { d: rnd(3) - 1, j: 14, s: 0 }; p.btk = 14; return; }   // stuck under a ledge: shake loose
  if (Math.hypot(p.x - p.sx, p.y - p.sy) >= 6) p.stk = 0;
  p.sx = p.x; p.sy = p.y;
  if (p.tid !== tg.id || --p.tc <= 0) { p.tid = tg.id; p.tc = 2; p.tx = tg.x + (Math.random() - .5) * 140; p.ty = tg.y + (Math.random() - .5) * 60; }   // human-like reaction: stale, slightly off view of the target
  const tx = p.tx, ty = p.ty;
  let best = null, bc = 1e12; const all = [];
  for (let d = -1; d <= 1; d++) for (let j = 0; j <= 14; j += 14) for (let ds = 0; ds < 2; ds++) {
    if (ds && (p.dcd > 0 || !d || Math.random() > .25)) continue;
    const s = Object.assign({}, p); let c = 0, dead = false, mn = 1e9;
    for (let k = 0; k < 30; k++) {
      step(s, { l: d < 0, r: d > 0, j: k < j, d: 0, s: ds && !k }, DT);
      if (s.y > WH - 30 || s.x < LX - 30 || s.x > RX + 30) { dead = true; break; }
      if (k % 5 === 4) { const dd = Math.hypot(s.x - tx, (s.y - ty) * 1.2); c += chase ? dd : -Math.min(dd, 700); if (dd < mn) mn = dd; }
    }
    if (dead) c = chase ? c + 4000 : 1e6;
    else if (chase && mn < 40) c -= 300;
    else if (!chase && s.g) c -= 40;
    c += Math.random() * 3;
    if (!dead) all.push({ d, j, s: ds });
    if (c < bc) { bc = c; best = { d, j, s: ds }; }
  }
  p.pl = Math.random() < .2 && all.length ? all[rnd(all.length)] : best || { d: 0, j: 0, s: 0 };   // 1 in 5 plans is a deliberate mistake
}

function spawn(p, k, t, sp) {
  p.x = sp[0] + k * 42; p.y = sp[1]; p.vx = p.vy = 0; p.g = 0; p.coy = p.buf = p.cut = p.drop = 0; p.pj = false; p.face = 1;
  p.rs++; p.q.length = 0; p.lastCmd = t; p.lastB = 0; p.starve = 0; p.debt = 0;
  p.ps = false; p.dash = 0; p.dd = 1; p.dcd = 0; p.slow = 0; p.lv = 0; p.acd = 0; p.pa = 0; p.bst = p.pcd = p.bv = 0; p.zip = -1; p.zd = 1; p.zs = 0; p.zcd = 0; resetGrab(p); p.fz = 0; p.fimm = 0;   // every round starts with dash + ability + grab ready
}

function aliveIds(r) {
  return r.ord.filter(id => { const p = r.players.get(id); return p && p.alive; });
}

function spots(r, n) {   // classic: tight group on the middle-most platform; other modes: random, well separated spots
  if (CURMAP !== r.mp) setMap(r.mp);
  const P = SOL.filter(q => q.w >= 90);
  if (!r.inf) {
    let b = P[0]; for (const q of P) if (Math.abs(q.x + q.w / 2 - WW / 2) + Math.abs(q.y - WH / 2) * .3 < Math.abs(b.x + b.w / 2 - WW / 2) + Math.abs(b.y - WH / 2) * .3) b = q;
    const g = Math.min(42, (b.w - 50) / Math.max(1, n)), x0 = Math.max(b.x, Math.min(WW / 2, b.x + b.w) - g * (n - 1) / 2 - PW / 2);
    return Array.from({ length: n }, (_, k) => [x0 + k * g, b.y - PH - 2]);
  }
  for (let md = 480; ; md -= 60) {
    const out = [];
    for (let tries = 0; tries < 300 && out.length < n; tries++) {
      const q = P[rnd(P.length)], x = q.x + 15 + Math.random() * (q.w - 60), y = q.y - PH - 2;
      if (x < LX || x > RX - PW) continue;
      if (out.every(o => Math.hypot(o[0] - x, o[1] - y) >= md)) out.push([x, y]);
    }
    if (out.length === n || md <= 0) { while (out.length < n) out.push([300 + Math.random() * 900, -60]); return out; }
  }
}
function zoneSpots(r, n, right) {   // infection / freeze: one team per map edge
  if (CURMAP !== r.mp) setMap(r.mp);
  const P = SOL.filter(q => q.w >= 90), a = right ? RX - PW - WW * .3 : LX, b = right ? RX - PW : LX + WW * .3;
  for (let md = 300; ; md -= 40) {
    const out = [];
    for (let tries = 0; tries < 400 && out.length < n; tries++) {
      const q = P[rnd(P.length)], x0 = Math.max(q.x + 15, a), x1 = Math.min(q.x + q.w - 45, b);
      if (x1 < x0) continue;
      const x = x0 + Math.random() * (x1 - x0), y = q.y - PH - 2;
      if (out.every(o => Math.hypot(o[0] - x, o[1] - y) >= md)) out.push([x, y]);
    }
    if (out.length === n || md <= 0) { while (out.length < n) out.push([a + Math.random() * (b - a), -60]); return out; }
  }
}
function startRound(r, ids, t) {
  r.rn++; r.st = 'play'; r.loser = r.ln = null; r.lk = null; r.ord = ids.slice(); clearFx(r); initCrates(r);
  let pts = r.inf ? null : spots(r, ids.length);
  const first = ids[rnd(ids.length)]; r.first = first;
  const frs = new Set(r.inf === 2 ? ids.slice().sort(() => Math.random() - .5).slice(0, Math.max(1, ids.length >> 1)) : [first]);   // freeze tag: 50% of the players are freezers
  if (r.inf) { const d = ids.filter(i => !frs.has(i)), a = ids.filter(i => frs.has(i)), L = zoneSpots(r, d.length, 0), R = zoneSpots(r, a.length, 1), m = {}; d.forEach((i, k) => m[i] = L[k]); a.forEach((i, k) => m[i] = R[k]); pts = ids.map(i => m[i]); }   // defenders left, attackers right
  ids.forEach((id, k) => { const p = r.players.get(id); if (!p) return; spawn(p, 0, t, pts[k]); p.alive = true; p.it = frs.has(id) ? 1 : 0; });
  for (const p of r.players.values()) if (!ids.includes(p.id)) { p.alive = false; p.it = 0; }
  r.rs = r.inf === 0 ? classicS(ids.length) : r.inf === 2 ? FREEZE_S : ROUND_S;

  r.evK = -1; r.evF = rnd(2); r.cdEnd = t + CD_MS; r.deadline = r.cdEnd + roundS(r) * 1000; r.tagFrom = r.cdEnd + TAG_GRACE_MS;
  bcastRoom(r);
}

function startMatch(r, t) {
  const ids = [...r.players.values()].filter(p => p.ws || p.bot).map(p => p.id).slice(0, roomMax(r));   // only players who are actually connected
  if (!ids.length) return;
  r.gm = 1 + rnd(999999999); r.mp = !r.pub && r.sel > 0 ? r.sel - 1 : rnd(MAPS.length); r.rn = 0; for (const q of r.players.values()) q.rdy = 0; r.practice = ids.length === 1; r.win = r.wn = null; r.lobbyGo = 0; r.botNext = 0;
  for (const q of r.players.values()) q.rec = (r.pub && !r.practice && q.acct && ids.includes(q.id)) ? 1 : 0;   // only public lobbies (incl. party joins) count; private rooms and solo practice never do
  startRound(r, ids, t);
}

function finish(r, id, wt) {
  const p = id && r.players.get(id);
  r.st = 'over'; r.win = id || null; r.wn = p ? p.nm : null; r.wt = wt || 0; r.lobbyGo = 0; clearFx(r);
  for (const q of r.players.values()) { q.it = 0; rec(q, q.id === id); }
  bcastRoom(r);
}

function toLobby(r) {
  r.st = 'lobby'; clearFx(r); r.ord = []; r.rn = 0; r.gm = 0; r.first = r.loser = r.win = r.ln = r.wn = null; r.lk = null; r.practice = false;
  for (const p of [...r.players.values()]) { if (p.bot) { r.players.delete(p.id); continue; } p.alive = false; p.it = 0; p.q.length = 0; p.rdy = 0; p.rec = 0; }
  updateLobbyGo(r, now());
  bcastRoom(r);
}

function resumeClassic(r, t, al) {   // classic: keep positions, new random tag, fresh 30 s
  for (const q of r.players.values()) q.it = 0;
  const h = r.players.get(al[rnd(al.length)]); if (h) h.it = 1;
  r.st = 'play'; r.loser = r.ln = null; r.lk = null; r.rs = classicS(al.length); r.deadline = t + r.rs * 1000; r.tagFrom = t + TAG_GRACE_MS;
  bcastRoom(r);
}

function expire(r, t, holder) {
  r.loser = holder.id; r.ln = holder.nm; holder.alive = false; holder.it = 0;
  r.st = 'between'; r.betweenEnd = t + BETWEEN_MS; clearFx(r);
  bcastRoom(r);
}

function removePlayer(r, p, t) {
  if (r.players.get(p.id) !== p) return;
  if (r.st !== 'lobby' && r.st !== 'over') rec(p, 0);   // leaving a running match = a loss
  r.players.delete(p.id);
  if (![...r.players.values()].some(q => !q.bot)) { rooms.delete(r.key); return; }   // only bots left -> close the room
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
const REPEAT_MAX = 9, QTRIM = 4;   // ticks a silent player keeps moving on their last input / longest input backlog kept
function consume(p) {
  if (!p.q.length) {                                   // input is late: keep moving on the last input instead of freezing (a freeze looks like a teleport on everyone else's screen)
    if (p.starve < REPEAT_MAX) { p.starve++; p.debt++; return p.lastB; }
    p.debt = 0; return p.lastB = 0;                    // really silent (hidden tab / lost signal): stand still
  }
  p.starve = 0;
  let c = p.q.shift(), b = c.b;
  while (p.q.length && (p.debt > 0 || p.q.length > QTRIM)) {   // repay the repeated ticks (or trim a backlog) by dropping the oldest input - its button presses are merged into the next one so no jump/dash is lost
    if (p.debt > 0) p.debt--;
    const press = b & ~p.lastB & 116;
    c = p.q.shift(); b = c.b | press;
  }
  p.lastSeq = c.s; p.lastB = b; return b;
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
  if (r.evK !== k) { r.evK = k; r.evT = (k + r.evF) % 2 ? 'b' : 'l'; r.evP = rnd(PL.length - 1); }
  if (r.evT === 'b') return ph >= 30 ? ['b', 1, 0, 40 - ph] : null;
  return ph >= 28 ? ['l', ph < 30 ? 0 : 1, r.evP, ph < 30 ? 30 - ph : 40 - ph] : null;
}

function simRoom(r, t) {
  if (CURMAP !== r.mp) setMap(r.mp);
  SX = r.cr.length ? SOL.concat(r.cr) : SOL;
  const cd = r.st === 'play' && t < r.cdEnd;
  for (const p of r.players.values()) {
    if (!p.alive) continue;
    if (p.acd > 0) p.acd -= DT; if (p.lv > 0) p.lv -= DT;                                           // ability cooldown
    p.slow = inTrap(r, p) || p.lv > 0;                                                // standing in a trap?
    let b = p.bot ? botInput(r, p, t) : consume(p);
    advance(r, p, (cd || p.fz) ? 0 : b);
    if (p.hrs !== p.rs) { p.hx.fill(p.x); p.hy.fill(p.y); p.hrs = p.rs; }                 // position history (lag compensation)
    p.hi = (p.hi + 1) & 31; p.hx[p.hi] = p.x; p.hy[p.hi] = p.y;
  }

  if (r.st === 'between') { if (t >= r.betweenEnd) { const al = aliveIds(r); if (al.length >= 2) { if (r.inf === 0) resumeClassic(r, t, al); else startRound(r, al, t); } else finish(r, al[0]); } return; }
  if (r.st !== 'play' || cd) return;
  tickFx(r);
  const ev = evState(r, t);
  if (ev && ev[0] === 'l' && ev[1] === 1) {
    const q = PL[ev[2]];
    for (const p of r.players.values()) if (p.alive && p.g && onQ(q, p)) p.lv = 15;   // standing on lava: slowed for 15 s
  }
  grabTick(r);
  crateTick(r);
  if (r.inf === 2) {   // FREEZE TAG: half the players are freezers (they freeze runners by touch), free runners unfreeze frozen ones by touch. All runners frozen = freezers win; time out = runners win.
    const al = aliveIds(r).map(id => r.players.get(id));
    if (!al.length) return;
    if (!al.some(p => p.it)) al[rnd(al.length)].it = 1;
    const its = al.filter(p => p.it), run = al.filter(p => !p.it);
    for (const p of its) p.fz = 0;
    for (const q of run) if (q.fimm > 0) q.fimm -= DT;
    if (t >= r.tagFrom) for (const q of run) {
      if (q.fz) { for (const h of run) if (h !== q && !h.fz && tagHit(h, q)) { q.fz = 0; q.fimm = 1.2; bcast(r, JSON.stringify({ t: 'fz', a: q.id, f: 0 })); break; } }
      else if (q.fimm <= 0) {
        const f = its.find(h => tagHit(h, q));
        if (!f) continue;
        q.fz = 1; q.vx = 0; q.dash = 0; q.zip = -1; r.lastInf = f.id;
        if (q.gt || q.gk) ungrab(r, q, GRAB_CD);
        if (q.hb) { const g = r.players.get(q.hb); if (g) ungrab(r, g, GRAB_CD); }
        bcast(r, JSON.stringify({ t: 'fz', a: q.id, f: 1 }));
      }
    }
    if (!r.practice && run.length) {
      if (run.every(p => p.fz)) finish(r, r.players.has(r.lastInf) ? r.lastInf : its[0].id, 1);
      else if (t >= r.deadline) finish(r, run.find(p => !p.fz).id, 2);
    }
    return;
  }
  if (r.inf === 1) {   // INFECTION: every infected player spreads it by touch; the last healthy player wins
    const al = aliveIds(r).map(id => r.players.get(id));
    if (!al.some(p => p.it) && al.length) al[rnd(al.length)].it = 1;
    if (t >= r.tagFrom) for (const q of al) if (!q.it) for (const h of al) if (h.it && tagHit(h, q)) { q.it = 1; r.lastInf = q.id; break; }
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
      if (!tagHit(holder, q)) continue;                                   // real overlap only, never from a distance
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
  for (const p of r.players.values()) if (p.alive) arr += (arr ? ',' : '') + '["' + p.id + '",' + r1(p.x) + ',' + r1(p.y) + ',' + ri(p.vx + p.bv) + ',' + ri(p.vy) + ',' + p.face + ',' + (p.g ? 1 : 0) + ',' + (p.it ? 1 : 0) + ',' + (p.fz ? 1 : 0) + ']';
  const tl = r.practice || r.inf === 1 ? 'null' : r.st === 'play' ? Math.min(roundS(r), Math.max(0, (r.deadline - t) / 1000)).toFixed(2) : '0';
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
    const a = p.alive ? ',"a":{"x":' + r4(p.x) + ',"y":' + r4(p.y) + ',"vx":' + r4(p.vx) + ',"vy":' + r4(p.vy) + ',"g":' + (p.g ? 1 : 0) + ',"coy":' + r4(p.coy) + ',"buf":' + r4(p.buf) + ',"pj":' + (p.pj ? 'true' : 'false') + ',"cut":' + (p.cut ? 1 : 0) + ',"drop":' + r4(p.drop) + ',"face":' + p.face + ',"it":' + (p.it ? 1 : 0) + ',"dash":' + r4(p.dash) + ',"dd":' + p.dd + ',"dcd":' + r4(p.dcd) + ',"ps":' + (p.ps ? 'true' : 'false') + ',"ac":' + r1(Math.max(0, p.acd)) + ',"gs":' + p.gs + ',"gt":' + (p.gt ? 1 : 0) + ',"hb":' + (p.hb ? 1 : 0) + ',"gk":' + (p.gk ? 1 : 0) + ',"lv":' + r1(Math.max(0, p.lv || 0)) + ',"fz":' + (p.fz ? 1 : 0) + ',"gc":' + r1(Math.max(0, p.gcd)) + ',"bs":' + r4(Math.max(0, p.bst)) + ',"pc":' + r4(Math.max(0, p.pcd)) + ',"z":' + p.zip + ',"zd":' + p.zd + ',"zs":' + r4(p.zs) + ',"zc":' + r4(Math.max(0, p.zcd)) + ',"q":' + p.lastSeq + ',"rs":' + p.rs + '}' : '';
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
        if (r.botNext && t >= r.botNext) { r.botNext = 0; if (conn(r) >= 1 && tot(r) < PUB_SIZE) { addBots(r, 1); updateLobbyGo(r, t); bcastRoom(r); } }
        if (r.lobbyGo && t >= r.lobbyGo) { r.lobbyGo = 0; if (tot(r) >= PUB_SIZE) startMatch(r, t); else bcastRoom(r); }
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
  setTimeout(() => { if (!ws.acct) try { ws.close(); } catch {} }, 15000);   // never logged in -> dropped
  ws.on('pong', () => { const n = Date.now(); ws.lastSeen = n; if (ws.pingAt) { const m = n - ws.pingAt; ws.rtt = ws.rtt ? ws.rtt * .7 + m * .3 : m; } });

  let r = null, p = null, cnt = 0, winStart = Date.now();
  const pid = hex(4); let pt = null;     // party membership (before a room exists)
  const pbc = P => { const mem = [...P.mem.values()]; const lst = mem.map(x => ({ id: x.id, nm: x.nm, rd: x.rd })); for (const q of mem) send(q.ws, JSON.stringify({ t: 'party', code: P.code, you: q.id, lead: P.lead, md: P.md, mem: lst })); };
  const pdrop = () => { if (!pt) return; const P = pt; pt = null; P.mem.delete(pid); if (!P.mem.size) { parties.delete(P.code); return; } if (P.lead === pid) P.lead = P.mem.keys().next().value; for (const q of P.mem.values()) q.rd = 0; pbc(P); };
  const err = e => { send(ws, '{"t":"err","e":"' + e + '"}'); ws.close(); };

  const attach = (rr, pp) => {
    r = rr; p = pp; pp.ws = ws; pp.dc = 0; ws.joined = 1;
    const o = LIVE.get(ws.acct); if (o && o !== ws && o.readyState === 1) { try { o.terminate(); } catch {} }   // one live session per account
    LIVE.set(ws.acct, ws);
    send(ws, JSON.stringify({ t: 'hello', id: pp.id, tk: pp.tk, rk: rr.key, code: rr.pub ? '' : rr.key, pub: rr.pub ? 1 : 0, ab: pp.ab }));
  };
  const addPlayer = (rr, nm) => {
    if (rr.players.size >= roomMax(rr) && rr.st === 'lobby') {                  // a disconnected "ghost" never blocks a real player from a lobby
      for (const q of rr.players.values()) if (!q.ws) { rr.players.delete(q.id); break; }
    }
    if (rr.players.size >= roomMax(rr)) return err('full');                       // single choke point: no path can exceed the room limit
    if (rr.pub && rr.st !== 'lobby') return err('full');                       // public matches in progress are closed
    if (!rooms.has(rr.key)) rooms.set(rr.key, rr);
    const used = new Set([...rr.players.values()].map(q => q.ci)); let ci = 0; while (used.has(ci)) ci++; ci %= 10;
    const pp = newPlayer(nm, ci); pp.since = now(); pp.acct = ws.acct; pp.rec = 0;
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

    /* ---- login gate: nothing else is processed until the socket proves it belongs to an account ---- */
    if (!ws.acct) {
      if (m.t === 'auth' && !ws.pend) {
        ws.pend = [];   // messages that arrive while the token is being checked wait here
        tokAcc(m.tk).then(a => {
          const q = ws.pend; ws.pend = null;
          if (!a) return err('auth');
          ws.acct = a; send(ws, JSON.stringify({ t: 'st', p: a.p, w: a.w, l: a.l }));
          for (const x of q) ws.emit('message', x[0], x[1]);
        }, () => { ws.pend = null; err('busy'); });
      }
      else if (m.t === 'hb') send(ws, '{"t":"hb"}');
      else if (ws.pend && ws.pend.length < 8) ws.pend.push([raw, isBinary]);
      return;
    }

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
    if (m.t === 'hb') { ws.pres = t; send(ws, '{"t":"hb"}'); return; }
    if (m.t === 'leave' && r && p) { removePlayer(r, p, now()); p.ws = null; r = null; p = null; return; }   // deliberate exit: no grace period

    /* ---- joining ---- */
    if (!r) {
      /* ---- party: leader makes a code, friends join, all ready, leader picks mode + starts -> everyone enters the same public lobby ---- */
      if (m.t === 'pcreate' || m.t === 'pjoin') {
        if (pt) return;
        let P;
        if (m.t === 'pcreate') {
          if (parties.size >= MAX_ROOMS) return err('busy');
          let c; do { c = Array.from({ length: 4 }, () => CODE_CHARS[rnd(32)]).join(''); } while (parties.has(c) || rooms.has(c));
          P = { code: c, lead: pid, md: 0, mem: new Map() }; parties.set(c, P);
        } else {
          const c = typeof m.code === 'string' ? m.code.toUpperCase() : '';
          if (!/^[A-Z0-9]{3,6}$/.test(c)) return err('bad');
          P = parties.get(c); if (!P) return err('nf');
          if (P.mem.size >= PARTY_MAX) return err('full');
        }
        for (const q of P.mem.values()) q.rd = 0;                 // someone new arrived: everybody readies up again
        const nm = ws.acct.n;
        P.mem.set(pid, { id: pid, ws, nm, rd: 0, go: rr => { pt = null; addPlayer(rr, nm); } });
        pt = P; ws.joined = 1;
        return pbc(P);
      }
      if (pt) {
        const P = pt;
        if (m.t === 'prdy') { P.mem.get(pid).rd = m.v ? 1 : 0; return pbc(P); }
        if (m.t === 'pmode' && P.lead === pid) { P.md = Math.max(0, Math.min(2, m.m | 0)); return pbc(P); }
        if (m.t === 'pstart' && P.lead === pid) {
          const mem = [...P.mem.values()], n = mem.length;
          if (mem.some(q => !q.rd)) return;
          let best = null;
          for (const rr of rooms.values()) {                      // a lobby with room for the WHOLE party, fullest first
            if (!rr.pub || rr.inf !== P.md || rr.st !== 'lobby' || conn(rr) + n > PUB_SIZE) continue;
            if (!best || conn(rr) > conn(best)) best = rr;
          }
          if (!best && rooms.size >= MAX_ROOMS) return err('busy');
          if (!best) { let k; do { k = 'p-' + hex(3); } while (rooms.has(k)); best = mkRoom(k, true, P.md); }   // no space for all -> fresh lobby
          while (best.players.size + n > PUB_SIZE) { const b = [...best.players.values()].find(q => q.bot || !q.ws); if (!b) break; best.players.delete(b.id); }
          parties.delete(P.code);
          for (const q of mem) q.go(best);
          return;
        }
        return;
      }
      if (m.t === 'create') {
        if (rooms.size >= MAX_ROOMS) return err('busy');
        let code; do { code = Array.from({ length: 4 }, () => CODE_CHARS[rnd(32)]).join(''); } while (rooms.has(code));
        return addPlayer(mkRoom(code, false), ws.acct.n);
      }
      if (m.t === 'join') {
        const code = typeof m.code === 'string' ? m.code.toUpperCase() : '';
        if (!/^[A-Z0-9]{3,6}$/.test(code)) return err('bad');
        const rr = rooms.get(code);
        if (!rr || rr.pub) return err('nf');
        if (rr.players.size >= roomMax(rr)) return err('full');
        if (rr.practice && rr.st !== 'lobby') toLobby(rr);   // a solo practice game has no end: someone joining brings everybody back to the lobby
        return addPlayer(rr, ws.acct.n);          // joining a running match = spectate until the next game
      }
      if (m.t === 'quick') {

        const md = Math.max(0, Math.min(2, m.m | 0));

        let best = null;
        for (const rr of rooms.values()) {
          if (!rr.pub || rr.inf !== md || rr.st !== 'lobby' || conn(rr) >= PUB_SIZE) continue;
          if (!best || conn(rr) > conn(best)) best = rr;   // fullest lobby first
        }
        if (!best && rooms.size >= MAX_ROOMS) return err('busy');
        if (!best) { let k; do { k = 'p-' + hex(3); } while (rooms.has(k)); best = mkRoom(k, true, md); }
        return addPlayer(best, ws.acct.n);
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
    if (m.t === 'ready' && r.st === 'lobby' && !r.pub) { p.rdy = m.v ? 1 : 0; return bcastRoom(r); }
    if (m.t === 'map' && r.st === 'lobby' && !r.pub && r.hostId === p.id) { r.sel = Math.max(0, Math.min(MAPS.length, m.m | 0)); return bcastRoom(r); }
    if (m.t === 'mode' && r.st === 'lobby' && !r.pub && r.hostId === p.id) { r.inf = Math.max(0, Math.min(2, m.m | 0)); return bcastRoom(r); }
    if (m.t === 'start' && r.st === 'lobby' && !r.pub && r.hostId === p.id) { if (conn(r) < (r.inf === 1 ? 4 : r.inf === 2 ? 3 : 1)) return; if ([...r.players.values()].some(q => q.ws && !q.rdy)) return; return startMatch(r, now()); }   // infection needs 4+ players, freeze tag 3+
    if (m.t === 'lobby' && r.st === 'over' && !r.pub && r.hostId === p.id) return toLobby(r);
  });

  ws.on('close', () => {
    pdrop();
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
    if (t - ws.lastSeen > 15000 || (!ws.joined && t - (ws.pres || ws.born) > 120000)) { ws.terminate(); continue; }
    try { ws.pingAt = Date.now(); ws.ping(); } catch {}
    send(ws, '{"t":"hb"}');
  }
}, 2000);

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
  accFlush().finally(() => server.close(() => process.exit(0)));
  setTimeout(() => process.exit(0), 4000).unref();
}
process.on('SIGTERM', shutdown);
process.on('SIGINT', shutdown);
process.on('uncaughtException', (e) => console.error('uncaught:', e));
process.on('unhandledRejection', (e) => console.error('unhandled:', e));