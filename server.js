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
const SNAP_BASE = 1;                                  // 30 snapshots/s: the client interpolates with velocities (Hermite), so it looks as smooth as 60/s but costs half the CPU/bandwidth
let snapEvery = +process.env.TAG_SNAP_EVERY || SNAP_BASE;   // send a snapshot every N ticks (2 = 30/s, 3 = 20/s). Drops to 3 by itself when the server is starved of CPU (see the tick loop).
const FIXED_SNAP = !!process.env.TAG_SNAP_EVERY;
const ROUND_S = +process.env.TAG_ROUND_S || 180;           // seconds per round
const classicS = n => Math.max(25, 70 - 6 * n);   // classic: seconds per elimination, shrinks as players grow (2p 58s, 3p 52s, 5p 40s, 8+p 25s)

const FREEZE_S = 100;          // freeze tag: always 100 s

const roundS = r => r.rs || (r.inf === 2 ? FREEZE_S : r.inf === 0 ? classicS(2) : ROUND_S);
const CD_MS = 2200;            // 3-2-1-GO countdown before each round
const TAG_GRACE_MS = 300;      // nobody can be tagged right after GO
const BETWEEN_MS = 3200;       // pause after someone is eliminated
const BOT_GAP_MS = 2000;       // public lobby not full: one bot joins every 2 s (a real player takes a bot's seat)
const LOBBY_GO_MS = 3000;      // public lobby full -> match starts after this
const LOCK_MS = 800;          // the player who just passed the tag can't take it straight back
const GRACE_MS = 15000;        // a dropped connection keeps its character this long and may reconnect
const STALL_MS = 80;          // wait this long for a late input packet before treating the player as idle
const LOBBY_IDLE_MS = +process.env.TAG_LOBBY_IDLE_MS || 10 * 60 * 1000;   // a seat in a public lobby is held at most this long (no permanent idlers)
const QCAP = 24;               // max queued inputs per player (anti speed-hack: input rate is capped at 60/s)

/* ---- abilities ---- */
const DASH_V = 1000, DASH_T = 0.16, DASH_CD = 15;   // dash (everyone): speed px/s, duration s, cooldown s
const AB_CD = 30;                                    // cooldown (s) of the ability each player picks before the match
const FAKE_T = 8, SMOKE_T = 8, TRAP_T = 8;           // how long each effect lasts (s)
const TRAP_W = 180, TRAP_IMM = 1;                    // trap width (px); its owner is immune for the first second so they can step off it
const SLOW_K = 0.4, JUMP_K = 0.8;                    // speed / jump multipliers while standing in a trap
/* ---- grab: hold the button next to a player to latch on and drag them along (Human-Fall-Flat style). Everyone has it. ---- */
const GRAB_REACH = 110, GRAB_REACH_T = 0.7;           // how far (px beyond the body) the hand reaches / how long (s) the hands stay out before it counts as a miss
const GRAB_MAX = 6, GRAB_MIN = 0.25;               // longest hold (s) / shortest hold (a tap or a lag blip can't drop the grip instantly)
const GRAB_CD = 8, GRAB_MISS_CD = 1.5;               // cooldown (s) after a hold / after a miss
const GRAB_ROPE = 70, GRAB_BREAK = 300, GRAB_IMM = 1.2;   // max distance between the two bodies (px) / the grip snaps beyond this / a freed player can't be re-grabbed for this long (s)
const HELD_K = 0.5, CARRY_K = 0.8;                   // speed multiplier of the player who is held / of the player who is carrying
const ABIL = new Set(['fake', 'smoke', 'trap', 'spring', 'rocket', 'uppercut', 'recharge', 'shock', 'magnet', 'shield', 'swap', 'clones', 'zap']);
const ABCD = { fake: 30, smoke: 30, trap: 30, spring: 20, rocket: 20, uppercut: 20, recharge: 25, shock: 30, magnet: 30, shield: 30, swap: 30, clones: 30, zap: 35 };   // per-ability cooldown (s); anything not listed uses AB_CD
const ZAP_CD = 7;                                    // ghost lightning: eliminated players can call a strike every ZAP_CD s
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
    gz = zlib.gzipSync(html, { level: 6 });
    try { br = zlib.brotliCompressSync(html, { params: { [zlib.constants.BROTLI_PARAM_QUALITY]: 7, [zlib.constants.BROTLI_PARAM_SIZE_HINT]: html.length } }); } catch { br = null; }
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
const RQ_TTL = 7 * 864e5;   // friend requests expire after 7 days
function rqPrune(a) { a.rq = a.rq || []; a.rqt = a.rqt || {}; const n = Date.now(); let c = 0; a.rq = a.rq.filter(k => { if (!a.rqt[k]) { a.rqt[k] = n; c = 1; return true } if (n - a.rqt[k] > RQ_TTL) { delete a.rqt[k]; c = 1; return false } return true }); for (const k in a.rqt) if (!a.rq.includes(k)) { delete a.rqt[k]; c = 1 } return c }
async function tokAcc(tk) {
  if (typeof tk !== 'string' || !tk || tk.length > 64) return null;
  const h = sha(tk); let a = byTok.get(h);
  if (!a) { const [k] = await db(['GET', 'tok:' + h]); a = k ? await getAcc(k) : null; if (a) byTok.set(h, a); }
  return a && !a.ban ? a : null;   // banned accounts are locked out
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
const accOut = (a, tk) => ({ ok: 1, u: a.n, tk, st: { p: a.p, w: a.w, l: a.l }, pr: prog(a) });
const msIp = new Map(); setInterval(() => msIp.clear(), 60000).unref();
const LIVE = new WeakMap(), authIp = new Map(), socIp = new Map(), INV = new Map(); setInterval(() => { authIp.clear(); socIp.clear(); }, 60000).unref();
function authReq(req, res) {
  const out = (c, o) => { res.writeHead(c, { 'Content-Type': 'application/json', 'Cache-Control': 'no-store', 'Access-Control-Allow-Origin': '*' }); res.end(JSON.stringify(o)); };
  const ip = String(req.headers['cf-connecting-ip'] || req.headers['x-forwarded-for'] || req.socket.remoteAddress || '').split(',')[0].trim();
  let b = ''; req.on('data', d => { b += d; if (b.length > 2048) req.destroy(); });
  req.on('end', async () => {
    try {
      let m; try { m = JSON.parse(b); } catch { return out(400, { e: 'bad' }); }
      if (!m || typeof m !== 'object') return out(400, { e: 'bad' });
      const soc = m.m === 'soc' || m.m === 'lb', mp = soc ? socIp : authIp, n = (mp.get(ip) || 0) + 1; mp.set(ip, n);
      if (n > (soc ? 90 : 30)) return out(429, { e: 'rate' });
      if (m.m === 'lb') {   // leaderboard by wins
        const me = await tokAcc(m.tk); if (!me) return out(401, { e: 'tk' }); lbSeed(me);
        const t = Math.max(0, Math.min(2, m.t | 0)), L = lbRows(t), i = L.findIndex(x => x[2] === me.k);
        return out(200, { ok: 1, rows: L.slice(0, 50).map(x => [x[0], x[1]]), me: i < 0 ? null : { r: i + 1, w: L[i][1] } });
      }
      if (m.m === 'soc') {   // friends: poll + add / accept / decline / remove / invite
        const me = await tokAcc(m.tk); if (!me) return out(401, { e: 'tk' });
        me.f = me.f || []; me.rq = me.rq || [];
        let rs = ''; if (rqPrune(me)) accSave(me);
        const a = m.a, nm = String(m.n || '').toLowerCase(), T = /^[a-z0-9_]{3,12}$/.test(nm) ? await getAcc(nm) : null;
        if (T) { T.f = T.f || []; T.rq = T.rq || []; if (rqPrune(T)) accSave(T); }
        if (a === 'add') {
          if (!T) return out(404, { e: 'nf' }); if (T.k === me.k) return out(400, { e: 'self' });
          if (me.f.includes(T.k)) return out(400, { e: 'dup' });
          if (me.rq.includes(T.k)) {   // they already asked me: instant friends
            me.rq = me.rq.filter(x => x !== T.k); delete me.rqt[T.k]; me.f.push(T.k); if (!T.f.includes(me.k)) T.f.push(me.k); accSave(T); rs = 'friends';
          } else if (T.rq.includes(me.k)) rs = 'already';   // my request is still pending (expires after 7 days)
          else { if (T.rq.length >= 30) return out(400, { e: 'full' }); T.rq.push(me.k); T.rqt[me.k] = Date.now(); accSave(T); rs = 'sent'; }
          accSave(me);
        } else if ((a === 'acc' || a === 'dec') && T && me.rq.includes(T.k)) {
          me.rq = me.rq.filter(x => x !== T.k); delete me.rqt[T.k];
          if (a === 'acc') { if (!me.f.includes(T.k)) me.f.push(T.k); if (!T.f.includes(me.k)) T.f.push(me.k); T.rq = T.rq.filter(x => x !== me.k); delete T.rqt[me.k]; accSave(T); }
          accSave(me);
        } else if (a === 'acc' || a === 'dec') {
          rs = 'gone';   // expired or already handled
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
        return out(200, { ok: 1, f: fl, rq, inv, r: rs });
      }
      if (m.m === 'pr') {   // every reward, purchase and claim is decided here, never by the browser
        const n = (msIp.get(ip) || 0) + 1; msIp.set(ip, n); if (n > 90) return out(429, { e: 'rate' });
        const a = await tokAcc(m.tk); if (!a) return out(401, { e: 'tk' });
        const e = progAct(a, m); if (e) return out(200, { ok: 0, e });
        if (m.a !== 'get') accSave(a);
        return out(200, { ok: 1, pr: prog(a) });
      }
      if (m.m === 'shop') {   // start a real-money checkout
        const a = await tokAcc(m.tk); if (!a) return out(401, { e: 'tk' });
        const r = await shopReq(a, m); return r.o ? out(200, { ok: 1, o: r.o, a: r.a, k: r.k, n: r.n }) : out(200, { ok: 0, e: r.e });
      }
      if (m.m === 'shopv') {   // the popup finished: verify the signature, credit, return the fresh balance
        const a = await tokAcc(m.tk); if (!a) return out(401, { e: 'tk' });
        return (await rzpVerify(a, m)) ? out(200, { ok: 1, pr: prog(a) }) : out(200, { ok: 0, e: 'pay' });
      }
      if (m.m === 'tk') { const a = await tokAcc(m.tk); if (a) lbSeed(a); return a ? out(200, accOut(a, m.tk)) : out(401, { e: 'tk' }); }
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
        if (a.ban) return out(403, { e: 'ban' });
        return out(200, accOut(a, await newTok(a)));
      }
      out(400, { e: 'bad' });
    } catch (e) { console.error('auth error:', e.message); try { out(503, { e: 'busy' }); } catch {} }
  });
}
const LB = new Map(); let lbT = 0;   // real leaderboard: account key -> [name, wins, dayId, dayWins, weekId, weekWins] (saved in Redis under "lbd")
const lbDay = () => Math.floor(Date.now() / 864e5), lbWeek = () => Math.floor((Date.now() / 864e5 + 3) / 7);
async function lbRebuild() {   // at startup: pull every account that has wins into the leaderboard, so nobody has to log in first
  try {
    let keys = [];
    if (!UP_URL) keys = [...MEM.keys()].filter(k => k.startsWith('acc:'));
    else { let c = '0'; do { const [r] = await db(['SCAN', c, 'MATCH', 'acc:*', 'COUNT', '500']); c = String(r[0]); keys.push(...r[1]); } while (c !== '0' && keys.length < 20000); }
    for (let i = 0; i < keys.length; i += 100) {
      for (const v of await db(...keys.slice(i, i + 100).map(k => ['GET', k]))) {
        if (!v) continue; const a = JSON.parse(v), c = ACC.get(a.k) || a;
        if (c.w > 0) { const e = LB.get(a.k); if (e) { e[0] = c.n; e[1] = c.w; } else LB.set(a.k, [c.n, c.w, 0, 0, 0, 0]); }
      }
    }
    while (LB.size > 500) { let lo = null; for (const [k, v] of LB) if (!lo || v[1] < LB.get(lo)[1]) lo = k; LB.delete(lo); }
    lbSave();
  } catch (e) { console.error('leaderboard rebuild failed:', e.message); }
}
db(['GET', 'lbd']).then(([v]) => { if (v) for (const [k, e] of JSON.parse(v)) if (!LB.has(k)) LB.set(k, e); }).catch(() => {}).then(lbRebuild);
function lbSave() { if (lbT) return; lbT = setTimeout(async () => { lbT = 0; try { await db(['SET', 'lbd', JSON.stringify([...LB])]); } catch (e) { console.error('leaderboard save failed:', e.message); } }, 5000); }
function lbSeed(a) { if (a.w > 0 && !LB.has(a.k)) { LB.set(a.k, [a.n, a.w, 0, 0, 0, 0]); lbSave(); } }
function lbWin(a) {
  const e = LB.get(a.k) || [a.n, 0, 0, 0, 0, 0], d = lbDay(), w = lbWeek();
  e[0] = a.n; e[1] = a.w; if (e[2] !== d) { e[2] = d; e[3] = 0; } if (e[4] !== w) { e[4] = w; e[5] = 0; } e[3]++; e[5]++;
  LB.set(a.k, e);
  if (LB.size > 500) { let lo = null; for (const [k, v] of LB) if (!lo || v[1] < LB.get(lo)[1]) lo = k; LB.delete(lo); }
  lbSave();
}
function lbRows(t) { const d = lbDay(), w = lbWeek(), L = []; for (const [k, e] of LB) { const v = t === 0 ? (e[2] === d ? e[3] : 0) : t === 1 ? (e[4] === w ? e[5] : 0) : e[1]; if (v > 0) L.push([e[0], v, k]); } return L.sort((a, b) => b[1] - a[1]); }
/* ---- server-authoritative progress: tokens, gems, xp, cosmetics, quests, stats ---- */
const PRICE = { sk: [0, 0, 200, 200, 350, 800, 100, 150, 250, 250, 300, 350, 400, 450, 500, 550, 600, 650, 700, 750, 900, 1000, 1200, 1400, 1600, 1800, 2200, 2500, 3000, 4000], ac: [0, 0, 0, 0, 150, 150, 150, 150, 150, 150, ...[100, 100, 120, 120, 120, 150, 150, 200, 250, 250, 300, 300, 350, 350, 400, 400, 450, 500, 700, 900]], hat: [0, 0, 250, 300, 350, 900, 150, 300, 200, 450, 250, 500, 350, 450, 600, 400, 350, 300, 400, 700, 700, 250, 500, 800, 600, 400, 550, 650, 1200, 1800], fc: [0, 150, 200, 0, 100, 120, 150, 150, 200, 200, 200, 250, 250, 300, 300, 350, 400, 400, 450, 500, 500, 550, 600, 700, 700, 800, 900, 1000, 1400, 1800], tr: [0, 250, 400, 300, 700, 150, 200, 200, 300, 300, 350, 350, 400, 450, 500, 500, 550, 600, 600, 700, 700, 800, 900, 1100, 1300, 1500, 1700, 2000, 2400, 2800], cl: [0, 3000, 3500, 4000, 5000, 6000, 7000, 8000, 10000, 12000, 15000, 20000, 30000], em: [0, 0, 0, 0, 150, 150, 250, 100, 100, 150, 100, 100, 400, 500, 250, 150, 250, 400, 800, 100, 100, 100, 150, 150, 200, 200, 300, 300, 300, 100] };
const ABP = { fake: 0, smoke: 300, trap: 500, spring: 200, rocket: 250, uppercut: 300, recharge: 350, shock: 400, magnet: 450, shield: 500, swap: 600, clones: 700, zap: 800 }, EQK = ['sk', 'ac', 'hat', 'fc', 'tr', 'cl'], DAILY = [100, 150, 200, 250, 300, 400, 500];
/* ---- economy: every token price x PM; top-tier items cost gems instead (gem price = old token price / GD) ---- */
const LAD=[5000,7000,10000,15000,20000,30000,40000,50000,60000,75000,100000],tp=p=>LAD[Math.max(0,Math.min(10,Math.round(Math.log(p/100)/Math.log(40)*10)))],gp=p=>Math.max(100,Math.round(p/50)*10);
const PM = 3, GD = 20, GEM_MIN = { sk: 1800, ac: 700, hat: 900, fc: 1000, tr: 1700, em: 800, cl: 1 }, GEM_AB = new Set(['swap', 'clones', 'zap']), GEMI = {}, ABG = {};
for (const k in PRICE) { const L = PRICE[k]; GEMI[k] = L.map(p => !!p && p >= GEM_MIN[k]); PRICE[k] = L.map((p, i) => !p ? 0 : GEMI[k][i] ? gp(p) : tp(p)); }
for (const k in ABP) { if (!ABP[k]) continue; if (GEM_AB.has(k)) { ABG[k] = 1; ABP[k] = gp(ABP[k]); } else ABP[k] = tp(ABP[k]); }
const needXp = l => 100 + (l - 1) * 40;
function lvlOf(x) { let l = 1; while (x >= needXp(l)) { x -= needXp(l); l++; } return l; }
const LRW = n => n == 4 ? { k: 'hat', i: 6 } : n == 8 ? { k: 'tr', i: 5 } : n == 12 ? { k: 'sk', i: 6 } : n == 16 ? { k: 'hat', i: 8 } : n % 5 == 0 ? { g: n % 10 == 0 ? 20 : 10 } : { t: Math.min(10 + n * 2, 50) * 10 };
const dayKey = t => new Date(t).toISOString().slice(0, 10);
function prog(a) {
  if (!a.pr) a.pr = { tok: 0, gem: 0, xp: 0, streak: 0, last: '', own: {}, lr: {}, em: [0, 1, 2, 3], eq: { sk: 0, ac: 0, hat: 0, fc: 0, tr: 0, cl: 0 }, ws: 0, bws: 0,
    q: [], qd: '',
    sx: { tg: 0, tt: 0, sv: 0, sn: 0, pt: 0, md: [0, 0, 0], rc: [] } };
  const td = dayKey(Date.now()); if (a.pr.qd !== td) { a.pr.qd = td; a.pr.q = genQ(a.k, td, lvlOf(a.pr.xp || 0)); }   // a fresh set of quests every UTC day, forever (yesterday's unclaimed ones expire)
  return a.pr;
}
function genQ(k, day, L) {   // deterministic per account + day, so reloading / reconnecting can never re-roll them
  let s = 2166136261; for (const c of k + day) s = Math.imul(s ^ c.charCodeAt(0), 16777619) >>> 0;
  const R = (lo, hi) => { s = (Math.imul(s, 1664525) + 1013904223) >>> 0; return lo + (s >>> 8) % (hi - lo + 1); }, sc = 1 + Math.min(L, 60) / 60;
  const mk = (k, t, n, u) => { const r = Math.round(n * u * sc / 5) * 5; return { k, t, p: 0, n, r, x: Math.round(r * .6) }; };
  const a = R(2, 5), b = R(1, 2), c = R(8, 16), d = R(4, 10) * 30;
  return [mk('play', 'Play ' + a + ' matches', a, 30), mk('win', 'Win ' + b + (b > 1 ? ' matches' : ' match'), b, 150), mk('tag', 'Tag ' + c + ' players', c, 12), mk('sv', 'Survive ' + d + ' seconds in matches', d, .5)];
}
function csClean(a, v) {   // a player can only show cosmetics they own
  const X = prog(a), p = String(v || '').split(',').map(Number);
  return EQK.map((k, j) => { let i = p[j] | 0; if (i < 0 || i >= PRICE[k].length || (PRICE[k][i] && !X.own[k + i])) i = 0; return i; }).join(',');
}
function progAct(a, m) {
  const X = prog(a), act = String(m.a);
  if (act === 'get') return '';
  if (act === 'sab') { const k = m.i; if (typeof k === 'string' && ABIL.has(k) && (ABP[k] === 0 || X.own['ab_' + k])) X.sab = k; return ''; }   // remembered ability choice
  if (act === 'buy') {
    let key, price, gem = false;
    if (m.k === 'ab') { if (typeof m.i !== 'string' || !Object.hasOwn(ABP, m.i)) return 'bad'; key = 'ab_' + m.i; price = ABP[m.i]; gem = !!ABG[m.i]; }
    else { const L = PRICE[m.k]; if (!L || !Number.isInteger(m.i) || m.i < 0 || m.i >= L.length) return 'bad'; key = m.k + m.i; price = L[m.i]; gem = !!GEMI[m.k][m.i]; }
    if (X.own[key] || !price) return '';
    if (gem) { if (X.gem < price) return 'gems'; X.gem -= price; }
    else { if (X.tok < price) return 'funds'; X.tok -= price; }
    X.own[key] = 1; return '';
  }
  if (act === 'eq') {
    const L = PRICE[m.k]; if (!L || !Number.isInteger(m.i) || m.i < 0 || m.i >= L.length) return 'bad';
    if (L[m.i] && !X.own[m.k + m.i]) return 'locked';
    if (m.k === 'em') { const s = m.s | 0; if (s < 0 || s > 3) return 'bad'; const j = X.em.indexOf(m.i); if (j >= 0) X.em[j] = X.em[s]; X.em[s] = m.i; }
    else X.eq[m.k] = m.i;
    return '';
  }
  if (act === 'daily') {
    const today = dayKey(Date.now()); if (X.last === today) return 'done';
    const cont = X.last === dayKey(Date.now() - 864e5), i = cont ? X.streak % 7 : 0;
    X.streak = cont ? X.streak + 1 : 1; X.last = today; const w = Math.min(Math.floor((X.streak - 1) / 7), 10); X.tok += DAILY[i]; if (i === 6) X.gem += 20; return '';
  }
  if (act === 'lr') {
    const n = m.n; if (!Number.isInteger(n) || n < 1 || n > 500) return 'bad';
    if (X.lr[n]) return 'done'; if (lvlOf(X.xp) < n) return 'locked';
    const r = LRW(n); X.lr[n] = 1; if (r.t) X.tok += r.t; if (r.g) X.gem += r.g; if (r.k) X.own[r.k + r.i] = 1; return '';
  }
  if (act === 'qc') {
    const q = Number.isInteger(m.i) ? X.q[m.i] : null; if (!q || q.d || q.p < q.n) return 'bad';
    q.d = 1; X.tok += q.r; X.xp += q.x; return '';
  }
  return 'bad';
}
function sxOf(X) { const S = X.sx || (X.sx = {}); S.tg |= 0; S.tt |= 0; S.sv = +S.sv || 0; S.sn |= 0; S.pt = +S.pt || 0; if (!Array.isArray(S.md)) S.md = [0, 0, 0]; if (!Array.isArray(S.rc)) S.rc = []; return S; }
function rec(p, win, fin) {   // one finished (or abandoned) match -> played +1, won/lost +1, plus the rewards
  if (!p.rec || !p.acct) return; const so = p.rec === 2; p.rec = 0;   // so: private match = stats only, no tokens / xp / quests / leaderboard
  const a = p.acct; a.p++; if (win) { a.w++; if (!so) lbWin(a); } else a.l++;
  const X = prog(a); let g = null;
  {   // profile analytics are recorded for every counted match, including ones the player quit
    const du0 = Math.max(0, (now() - (p.mt0 || now())) / 1000), sv0 = win || !p.outAt ? du0 : Math.max(0, (p.outAt - (p.mt0 || p.outAt)) / 1000), S0 = sxOf(X);
    S0.tg += p.tg | 0; S0.tt += p.tt | 0; S0.pt += du0; S0.sv += Math.min(sv0, du0); S0.sn++; S0.md[p.mdi | 0] = (S0.md[p.mdi | 0] | 0) + 1; S0.rc.unshift([win ? 1 : 0, p.mdi | 0, p.mpi | 0, Math.round(du0)]); S0.rc.length = Math.min(S0.rc.length, 10); AN.match(a, p, win, du0, fin);
  }
  if (win) { X.ws++; if (X.ws > X.bws) X.bws = X.ws; } else X.ws = 0;
  if (fin) {   // rewards only for matches played to the end, never for quitting
    const gx = win ? 90 : 35, gt = win ? 150 : 45, du = Math.max(0, (now() - (p.mt0 || now())) / 1000), sv = win || !p.outAt ? du : Math.max(0, (p.outAt - (p.mt0 || p.outAt)) / 1000);
    if (!so) { X.xp += gx; X.tok += gt; g = { x: gx, t: gt }; }
    if (!so && du >= 20) for (const q of X.q) { if (q.d) continue; const v = q.k === 'play' ? 1 : q.k === 'win' ? (win ? 1 : 0) : q.k === 'tag' ? Math.min(p.tg | 0, 8) : q.k === 'sv' ? Math.round(Math.min(sv, du)) : 0; q.p = Math.min(q.n, q.p + v); }   // only server-counted, finished public matches (>= 20 s) count; tags capped per match
    if (p.bonus && !so) { X.tok += p.bonus; g.bk = 1; p.bonus = 0; }
  }
  accSave(a);
  sendP(p, JSON.stringify({ t: 'st', p: a.p, w: a.w, l: a.l }));
  sendP(p, JSON.stringify({ t: 'pr', pr: X, g }));
}

/* ---- real-money store (Razorpay). env: RAZORPAY_KEY_ID, RAZORPAY_KEY_SECRET, RAZORPAY_WEBHOOK_SECRET. Amounts are decided HERE, never by the browser. ---- */
const RZP_ID = process.env.RAZORPAY_KEY_ID || '', RZP_SEC = process.env.RAZORPAY_KEY_SECRET || '', RZP_WH = process.env.RAZORPAY_WEBHOOK_SECRET || '';
const RZP_AUTH = 'Basic ' + Buffer.from(RZP_ID + ':' + RZP_SEC).toString('base64');
const PACKS = {   // c = price in paise (INR x 100). Amounts are fixed here; the browser only ever sends a pack id
  t1: { n: '2,000 Tokens', c: 34900, t: 2000 }, t2: { n: '6,000 Tokens', c: 84900, t: 6000 }, t3: { n: '15,000 Tokens', c: 169900, t: 15000 }, t4: { n: '40,000 Tokens', c: 399900, t: 40000 },
  g1: { n: '50 Gems', c: 34900, g: 50 }, g2: { n: '130 Gems', c: 84900, g: 130 }, g3: { n: '280 Gems', c: 169900, g: 280 }, g4: { n: '600 Gems', c: 349900, g: 600 } };
function payDay(a) { if (!a.pay || typeof a.pay !== 'object') a.pay = { ids: [] }; if (!Array.isArray(a.pay.ids)) a.pay.ids = []; return a.pay; }   // ids = paid order ids, so nothing can pay out twice
const hmacHex = (k, d) => crypto.createHmac('sha256', k).update(d).digest('hex');
const sameHex = (x, y) => typeof x === 'string' && x.length === y.length && /^[0-9a-f]+$/.test(x) && crypto.timingSafeEqual(Buffer.from(x), Buffer.from(y));
async function shopReq(a, m) {   // creates a Razorpay order -> { o: orderId, a: paise, k: keyId, n: name } or { e }
  const pk = typeof m.pk === 'string' && Object.hasOwn(PACKS, m.pk) ? PACKS[m.pk] : null; if (!pk) return { e: 'bad' };
  if (!RZP_ID || !RZP_SEC) return { e: 'off' };
  try {
    const r = await fetch('https://api.razorpay.com/v1/orders', { method: 'POST', headers: { Authorization: RZP_AUTH, 'Content-Type': 'application/json' },
      body: JSON.stringify({ amount: pk.c, currency: 'INR', receipt: 't' + Date.now().toString(36), notes: { acct: a.k, pack: m.pk } }) });
    const d = await r.json(); return r.ok && d.id ? { o: d.id, a: pk.c, k: RZP_ID, n: pk.n } : { e: 'pay' };
  } catch { return { e: 'pay' }; }
}
async function rzpSettle(id, who) {   // asks Razorpay itself whether the order is paid, then credits it exactly once
  if (typeof id !== 'string' || !/^order_[A-Za-z0-9]+$/.test(id)) return false;
  const r = await fetch('https://api.razorpay.com/v1/orders/' + id, { headers: { Authorization: RZP_AUTH } }); if (!r.ok) return false;
  const o = await r.json(), pk = o.notes && Object.hasOwn(PACKS, o.notes.pack) ? PACKS[o.notes.pack] : null, a = pk ? await getAcc(String(o.notes.acct || '')) : null;
  if (!pk || !a || (who && who !== a) || o.status !== 'paid' || o.amount !== pk.c || o.currency !== 'INR') return false;
  const P = payDay(a);
  if (!P.ids.includes(o.id)) { const X = prog(a); X.tok += pk.t || 0; X.gem += pk.g || 0; P.ids.push(o.id); if (P.ids.length > 100) P.ids.shift(); accSave(a); console.log('purchase', a.k, o.notes.pack); AN.purchase(pk, o.notes.pack); }
  return true;
}
async function rzpVerify(a, m) {   // the checkout popup hands the browser a signature; only Razorpay's secret can make a valid one
  if (!RZP_SEC || typeof m.o !== 'string' || typeof m.p !== 'string' || typeof m.s !== 'string' || m.o.length > 60 || m.p.length > 60) return false;
  if (!sameHex(m.s, hmacHex(RZP_SEC, m.o + '|' + m.p))) return false;
  return rzpSettle(m.o, a);
}
function rzpHook(req, res) {   // Razorpay -> server backup (e.g. the player closed the tab right after paying)
  const ch = []; let len = 0;
  req.on('data', d => { len += d.length; if (len > 65536) req.destroy(); else ch.push(d); });
  req.on('end', async () => {
    try {
      if (!RZP_WH) { res.writeHead(503); return res.end(); }
      const raw = Buffer.concat(ch).toString('utf8');
      if (!sameHex(String(req.headers['x-razorpay-signature'] || ''), hmacHex(RZP_WH, raw))) { res.writeHead(400); return res.end(); }
      const ev = JSON.parse(raw), pl = ev && ev.payload || {};
      const id = ev.event === 'order.paid' ? pl.order && pl.order.entity && pl.order.entity.id : ev.event === 'payment.captured' ? pl.payment && pl.payment.entity && pl.payment.entity.order_id : null;
      if (id) await rzpSettle(id, null);
      res.writeHead(200, { 'Content-Type': 'application/json' }); res.end('{"ok":true}');
    } catch (e) { console.error('razorpay hook', e.message); res.writeHead(500); res.end(); }
  });
}

const server = http.createServer((req, res) => {
  const url = (req.url || '/').split('?')[0];

  if (url === '/admin' || url.startsWith('/admin/')) return AN.http(req, res, url);
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
  if (url === '/razorpay' && req.method === 'POST') return rzpHook(req, res);
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
    'Content-Security-Policy': "default-src 'self'; script-src 'self' 'unsafe-inline' https://cdnjs.cloudflare.com https://checkout.razorpay.com; frame-src https://api.razorpay.com https://checkout.razorpay.com; style-src 'self' 'unsafe-inline' https://fonts.googleapis.com; font-src https://fonts.gstatic.com; img-src 'self' data: blob: https://*.razorpay.com; media-src 'self' data: blob:; connect-src 'self' ws: wss: https://api.razorpay.com https://lumberjack.razorpay.com https://lumberjack-cx.razorpay.com; frame-ancestors 'none'"
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
const kickAcc = a => { const w = LIVE.get(a); if (w) try { w.close(); } catch {} };
const pushPr = a => { const w = LIVE.get(a); if (w && w.readyState === 1) try { w.send(JSON.stringify({ t: 'pr', pr: prog(a) })); } catch {} };   // live balance update
async function delAcc(a) { kickAcc(a); const c = [['DEL', 'acc:' + a.k]]; for (const h of a.tk || []) { byTok.delete(h); c.push(['DEL', 'tok:' + h]); } ACC.delete(a.k); dirty.delete(a); LB.delete(a.k); lbSave(); await db(...c); }
const AN = require('./analytics')({ db, wss, ACC, rooms, MEM, UP: UP_URL, getAcc, accSave, prog, kickAcc, pushPr, delAcc, LB, lbSave });   // private analytics dashboard (/admin)

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
  const m = p.it ? 1.1 : 1, MAX = 360 * m * (p.slow ? SLOW_K : 1) * (p.hb ? HELD_K : 1) * ((p.gt || p.gk) ? CARRY_K : 1) * (p.bst > 0 ? BST_K : 1);
  const ax = (inp.r ? 1 : 0) - (inp.l ? 1 : 0);
  const ds = inp.s && !p.ps; p.ps = !!inp.s;                                  // dash = rising edge of the dash button
  if (p.dcd > 0) p.dcd -= dt;
  if (ds && p.dcd <= .001 && p.dash <= 0) { p.dash = DASH_T; p.dcd = DASH_CD; p.dd = ax || p.face; p.face = p.dd; }
  if (p.dash > 0) { p.dash -= dt; p.vx = p.dd * DASH_V; if (p.dash <= 0) { p.dash = 0; p.vx = p.dd * MAX; } }
  else if (ax) { const turn = Math.sign(p.vx) == -ax ? 1.8 : 1; p.vx += ax * (p.g ? 4200 : 2600) * turn * dt; p.vx = Math.max(-MAX, Math.min(MAX, p.vx)); p.face = ax; }
  else { const f = (p.g ? 3800 : 700) * dt; p.vx = Math.abs(p.vx) <= f ? 0 : p.vx - Math.sign(p.vx) * f; }
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
const LAGC_MAX = 8, LAGC_EXTRA = 55;   // rewind cap (ticks) / default render delay until the client reports its real one
const lagK = p => Math.min(LAGC_MAX, Math.round((((p.ws && p.ws.rtt) || 0) + (p.rd ? p.rd + 8 : LAGC_EXTRA)) / TICK_MS));
const hitRew = (a, b, k) => { const i = (b.hi - k) & 31, x = b.hx[i], y = b.hy[i]; return a.x < x + PW - 3 && a.x + PW > x + 3 && a.y < y + PH - 3 && a.y + PH > y + 3; };
function tagHit(h, q) {
  if (hit(h, q, -2)) return true;      // real contact on the server always tags
  if (!hit(h, q, -20)) return false;   // lag compensation only helps within 20 px: never a tag from a distance
  if (!h.bot && h.ws) return hitRew(h, q, lagK(h));
  if (!q.bot && q.ws) return hitRew(q, h, lagK(q));
  return false;
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
    rdy: 0, q: [], lastIn: 0, lastSeq: 0, lastCmd: 0, dc: 0, gr: 0, credit: 0, lastB: 0, starve: 0, debt: 0, hx: new Float32Array(32), hy: new Float32Array(32), hi: 0, hrs: -1, rd: 0,
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
    res: r.st === 'over' ? r.res : undefined, loser: r.loser, ln: r.ln, win: r.win, wn: r.wn, wt: r.wt | 0,
    lc: r.lobbyGo ? Math.max(0, (r.lobbyGo - t) / 1000) : 0,
    pl: [...r.players.values()].filter(p => p.ws || p.bot || r.st === 'play' || r.st === 'between').map(p => ({ id: p.id, nm: p.nm, ci: p.ci, al: p.alive ? 1 : 0, rd: p.rdy ? 1 : 0, cs: p.cs || '' }))
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

const BAB = ['fake', 'trap', 'spring', 'rocket', 'uppercut', 'recharge', 'shock', 'magnet', 'shield', 'swap'];
const BOT_NAMES = ['Zed', 'Mika', 'Rex', 'Nova', 'Kai', 'Luna', 'Jax', 'Pixel', 'Turbo', 'Echo', 'Blaze', 'Milo'];
function addBots(r, cnt) {
  const used = new Set([...r.players.values()].map(p => p.ci)), nm = new Set([...r.players.values()].map(p => p.nm));
  for (let need = cnt; need > 0; need--) {
    let ci = 0; while (used.has(ci)) ci++; used.add(ci); ci %= 10;
    let n; do { n = BOT_NAMES[rnd(BOT_NAMES.length)]; } while (nm.has(n)); nm.add(n);
    const b = newPlayer(n, ci); b.bot = true; b.since = now(); b.cs = [rnd(30), rnd(30), rnd(30), rnd(30), rnd(30), rnd(13)].join(','); b.emoNx = 0; /* bots wear a random look and use emotes */ b.sk = .93 + Math.random() * .07; b.ab = BAB[rnd(BAB.length)]; b.hop = null; b.wp = null; b.wpT = 0; b.btk = rnd(12); b.bst2 = 0; b.stk = 0; b.tc = 0; b.tid = ''; b.tx = b.ty = 0; b.sx = 0; b.sy = 0; b.pl = null;
    r.players.set(b.id, b);
  }
}

/* ---- bots: every ~0.25 s they simulate up to 18 short plans on a copy of their own body (same physics as the real game), look 0.5 s ahead and pick the best one.
   Runners flee while avoiding walls / crowds, idle runners wander between platforms, the holder chases; everyone uses dash, grab and their ability. ---- */
/* ---- LIGHT bots: no physics simulation. Every ~0.1 s one cheap decision (O(players)), using the precomputed platform-hop graph (NAV) to climb/route.
   Chase = path-nearest runner, flee = run away from the holder (avoids walls), wander = hop between platforms. Dash/grab used; no smoke/clones (those hid everyone). ---- */
function botInput(r, p, t) {
  if (p.fz || t < r.cdEnd) return 0;
  if (--p.btk <= 0) { p.btk = 6 + rnd(3); botPlan(r, p); p.k = 0; }
  const h = p.hop;
  if (h && p.g && Math.abs(p.x - h.x) < 9) { p.pl = { d: h.d, j: h.J, s: h.ds, a: 0, g: 0 }; p.k = 0; p.btk = Math.max(h.J, 6) + 4; p.hop = null; }   // exact launch spot reached: fire the precomputed hop
  const pl = p.pl; if (!pl) return 0;
  const k = p.k++;
  return (pl.d < 0 ? 1 : pl.d > 0 ? 2 : 0) | (k < pl.j ? 4 : 0) | (pl.s && k === 0 ? 16 : 0) | (pl.a && k === 1 ? 32 : 0) | (k < pl.g ? 64 : 0);
}
function botWp() {   // a random spot on a random platform, away from the map edges
  const P = SOL.filter(q => q.w >= 90 && q.x + q.w > LX + 100 && q.x < RX - 100);
  if (!P.length) return [WW / 2, 300];
  const q = P[rnd(P.length)];
  return [Math.max(LX + 120, Math.min(RX - 120, q.x + 30 + Math.random() * Math.max(1, q.w - 60))), q.y - PH - 2, SOL.indexOf(q)];
}
const NAV = {};
function pfOf(s) { if (!s.g) return -1; for (let i = 0; i < SOL.length; i++) if (onQ(SOL[i], s)) return i; return -1; }
function navBuild() {   // which platform reaches which (real physics: walking off, jumps, dashes, pads) -> hop counts between every pair of platforms
  const n = SOL.length, E = [], D = [], B = newPlayer('n', 0), sx0 = SX; SX = SOL;
  for (let i = 0; i < n; i++) { E.push([]); D.push(new Array(n).fill(99)); D[i][i] = 0; }
  const run = (i, x, d, v0, J, ds, pad) => {
    const s = Object.assign({}, B); s.x = x; s.y = SOL[i].y - PH; s.g = 1; s.vx = v0; let air = 0;
    for (let k = 0; k < 150; k++) {
      step(s, { l: d < 0, r: d > 0, j: k < J, d: 0, s: ds && !k }, DT);
      if (s.y > WH + 40) return;
      if (!s.g) air = 1; else if (air) { const l = pfOf(s); if (l >= 0 && l !== i && !E[i].some(e => e.j === l)) E[i].push({ j: l, x, y: SOL[i].y - PH, pad, d, J, ds }); return; }
    }
  };
  for (const mid of [0, 1]) for (let i = 0; i < n; i++) {
    const q = SOL[i], L = q.x + 2, R = Math.max(L, q.x + q.w - PW - 2), M = (L + R) / 2;
    for (const J of [0, 4, 8, 14, 24]) for (const ds of [0, 1]) { if (mid) { run(i, M, -1, 0, J, ds); run(i, M, 1, 0, J, ds); } else { run(i, L, -1, -300, J, ds); run(i, R, 1, 300, J, ds); } }
  }
  for (const pd of PADS) { const i = SOL.findIndex(q => Math.abs(q.y - pd.y) < 3 && pd.x + 4 >= q.x && pd.x < q.x + q.w); if (i >= 0) for (const d of [-1, 0, 1]) run(i, pd.x + 4, d, 0, 0, 0, 1); }
  for (let i = 0; i < n; i++) for (const e of E[i]) D[i][e.j] = 1;
  for (let k = 0; k < n; k++) for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) if (D[i][k] + D[k][j] < D[i][j]) D[i][j] = D[i][k] + D[k][j];
  SX = sx0; return { E, D };
}
function botAhead(p, d) {   // what is right in front of me? 0 free, 1 low obstacle (crate / ledge: jump it), 2 high wall or arena edge
  if (!d) return 0;
  if (d > 0 ? p.x > RX - PW - 24 : p.x < LX + 24) return 2;
  const x0 = d > 0 ? p.x + PW : p.x - 44, x1 = x0 + 44, y0 = p.y + 4, y1 = p.y + PH - 4; let o = 0;
  for (const q of SX) if (x0 < q.x + q.w && x1 > q.x && y0 < q.y + q.h && y1 > q.y) { if (p.y + PH - q.y > 120) return 2; o = 1; }   // SX = platforms + crates (set by simRoom)
  return o;
}
function botPlan(r, p) {
  const NV = NAV[CURMAP] || (NAV[CURMAP] = navBuild()), pf = q => { if (q.g) { const f = pfOf(q); if (f >= 0) q.lp = f; } return q.lp >= 0 ? q.lp : -1; };
  const cur = pf(p); let near = null, bs = 1e9, thr = null, td = 1e9, resc = null, rd = 1e9, sep = 0;
  for (const q of r.players.values()) {
    if (q === p || !q.alive) continue;
    const dx = q.x - p.x, dy = q.y - p.y, d = Math.abs(dx) + Math.abs(dy) * 1.5;
    if (!sep && Math.abs(dx) < 30 && Math.abs(dy) < 36) sep = dx > 0 || (dx === 0 && q.id > p.id) ? -1 : 1;   // someone is standing on top of me: step apart
    if (p.it) { if (!q.it && !q.fz) { const qp = q.g ? pf(q) : q.lp, sc = d + (cur >= 0 && qp >= 0 ? Math.min(NV.D[cur][qp], 8) * 260 : 0); if (sc < bs) { bs = sc; near = q; } } }
    else if (q.it) { if (d < td) { td = d; thr = q; } }
    else if (r.inf === 2 && q.fz && d < rd) { rd = d; resc = q; }
  }
  p.hop = null;
  if (p.hb) { const h = r.players.get(p.hb); p.pl = { d: h && h.x > p.x ? -1 : 1, j: 0, s: p.dcd <= 0 ? 1 : 0, a: 0, g: 0 }; return; }   // held: dash away to break free
  let tg = null, mode = 2;   // 0 chase, 1 flee, 2 wander
  if (p.it) { if (near) { tg = near; mode = 0; } }
  else if (thr && td < 520) { tg = thr; mode = 1; }
  else if (resc && td > 400) { tg = resc; mode = 0; }
  // universal unstick (walls, crates, corners, anything): not moving although I wanted to -> full jump + dash, then turn around
  const mv = Math.abs(p.x - p.sx) + Math.abs(p.y - p.sy); p.sx = p.x; p.sy = p.y;
  if (p.ld && mv < 6 && p.g) p.stk++; else p.stk = 0;
  if (p.stk >= 2) { const hard = p.stk >= 4; if (hard) { p.stk = 0; p.wp = null; } p.pl = { d: hard ? -p.ld : p.ld, j: 24, s: p.dcd <= 0 ? 1 : 0, a: 0, g: 0 }; p.ld = p.pl.d; p.btk = 26; return; }
  let d = 0, j = 0, s = 0, tp = -1, tx = p.x, nf = 0;
  if (mode === 1 && td >= 230 && cur >= 0) {   // threat not on top of me: run to the platform that is the most hops away from the holder (not into a corner)
    const tpT = pf(tg);
    if (tpT >= 0) {
      let bi = cur, bsc = -1e9;
      for (let i = 0; i < SOL.length; i++) { if (SOL[i].w < 70 || NV.D[cur][i] > 3) continue; const sc = NV.D[tpT][i] * 100 - NV.D[cur][i] * 35 + Math.random() * 25; if (sc > bsc) { bsc = sc; bi = i; } }
      const q = SOL[bi]; tx = Math.max(LX + 60, Math.min(RX - 60, tg.x < q.x + q.w / 2 ? q.x + q.w - 50 : q.x + 30)); tp = bi; nf = 1;
    }
  }
  if (mode === 1 && !nf) {   // close threat: run away from the holder, never into a wall, hop over him if cornered
    d = p.x >= tg.x ? 1 : -1;
    const ed = Math.min(p.x - LX, RX - PW - p.x);
    if (ed < 150) { const c = p.x < (LX + RX) / 2 ? 1 : -1; if (c !== d && p.g && td < 220) j = 22; d = c; }
    else if (td < 140 && p.g && Math.random() < .3) j = 14;
    if (td < 230 && p.dcd <= 0 && p.dash <= 0 && Math.random() < .6) s = 1;
  } else {
    if (mode === 0) { tx = tg.x + tg.vx * .2; tp = tg.g ? pf(tg) : tg.lp; }
    else if (!nf) {   // wander: pick the spot (of 3) that is farthest from other bots' spots; leave a slowing lava platform
      if (!p.wp || Math.abs(p.x - p.wp[0]) < 40 && Math.abs(p.y - p.wp[1]) < 60 || --p.wpT <= 0) {
        if (p.wp && Math.random() < .3) { p.wp = null; p.ld = 0; p.pl = { d: 0, j: 0, s: 0, a: 0, g: 0 }; return; }   // short human pause
        let bw = null, bm = -2;
        for (let i = 0; i < 3; i++) { const w = botWp(); let m = 1e9; for (const q of r.players.values()) if (q !== p && q.bot && q.wp) m = Math.min(m, Math.abs(q.wp[0] - w[0]) + Math.abs(q.wp[1] - w[1]) * .5); if (p.lv > 0 && w[2] === cur) m = -1; if (m > bm) { bm = m; bw = w; } }
        p.wp = bw; p.wpT = 40 + rnd(30);
      }
      tx = p.wp[0]; tp = p.wp[2];
    }
    d = Math.abs(tx - p.x) < 12 ? 0 : tx > p.x ? 1 : -1;
    if (cur >= 0 && tp >= 0 && cur !== tp && NV.D[cur][tp] < 99) {   // route: walk to the launch spot of the next hop towards the target platform
      let be = null, bd = 1e9; const dc = NV.D[cur][tp];
      for (const e of NV.E[cur]) { if (NV.D[e.j][tp] >= dc) continue; const dd = Math.abs(p.x - e.x); if (dd < bd) { bd = dd; be = e; } }
      if (be) { p.hop = be; d = be.x > p.x ? 1 : -1; if (bd < 9 && p.g) { p.pl = { d: be.d, j: be.J, s: be.ds, a: 0, g: 0 }; p.ld = be.d; p.btk = Math.max(be.J, 6) + 4; p.hop = null; return; } }
    } else if (mode === 0 && p.dcd <= 0 && p.dash <= 0 && Math.abs(tg.x - p.x) < 260 && Math.abs(tg.y - p.y) < 60) s = 1;   // dash at a runner on the same level
    if (mode === 0 && p.it && Math.abs(tg.x - p.x) < 150 && tg.y < p.y - 50 && p.g && !p.hop) j = 14;
    if (mode === 2 && sep && !p.hop) { d = sep; s = 0; }   // don't pile up on another bot
  }
  if (p.g && d) {   // obstacle right ahead: hop crates / ledges, turn around at high walls
    const bl = botAhead(p, d);
    if (bl === 1 && !j) j = 18; else if (bl === 2) { if (mode === 2 && !p.hop) { p.wp = null; d = -d; } else if (mode !== 1) j = 24; }
  }
  if (Math.random() > p.sk + .05) d = 0;   // rare human-like hesitation (tutorial bots, sk=.5, are much slower)
  const DD = mode === 0 ? bs : td, pl = { d, j, s, a: 0, g: 0 };
  if (r.st === 'play' && !r.tut && p.acd <= 0 && DD < 260 && Math.random() < .3) pl.a = 1;   // ability (never smoke/clones)
  if (p.gs > 0 && (p.gt || p.gk)) pl.g = 14; else if (p.it && mode === 0 && Math.abs(tg.x - p.x) + Math.abs(tg.y - p.y) < 70 && p.gcd <= 0 && Math.random() < .9) pl.g = 14;   // grab a runner in reach
  if (j || pl.g) p.btk = Math.max(j, pl.g) + 2;
  p.ld = d; p.pl = pl;
}

function spawn(p, k, t, sp) {
  p.x = sp[0] + k * 42; p.y = sp[1]; p.vx = p.vy = 0; p.g = 0; p.coy = p.buf = p.cut = p.drop = 0; p.pj = false; p.face = 1;
  p.rs++; p.q.length = 0; p.lastCmd = t; p.lastB = 0; p.starve = 0; p.debt = 0; p.credit = 2;
  p.ps = false; p.dash = 0; p.dd = 1; p.dcd = 0; p.slow = 0; p.lv = 0; p.acd = 0; p.pa = 0; p.bst = p.pcd = p.bv = 0; p.zip = -1; p.zd = 1; p.zs = 0; p.zcd = 0; resetGrab(p); p.fz = 0; p.fimm = 0; p.shd = 0;   // every round starts with dash + ability + grab ready
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
  r.rn++; r.st = 'play'; r.loser = r.ln = null; r.lk = null; r.ord = ids.slice(); for (const q of r.players.values()) q.outAt = 0; clearFx(r); initCrates(r);
  let pts = r.inf ? null : spots(r, ids.length);
  const first = r.tut ? (ids.find(i => { const z = r.players.get(i); return z && !z.bot; }) || ids[rnd(ids.length)]) : ids[rnd(ids.length)]; r.first = first;
  const frs = new Set(r.inf === 2 ? ids.slice().sort(() => Math.random() - .5).slice(0, Math.max(1, ids.length >> 1)) : [first]);   // freeze tag: 50% of the players are freezers
  if (r.inf) { const d = ids.filter(i => !frs.has(i)), a = ids.filter(i => frs.has(i)), L = zoneSpots(r, d.length, 0), R = zoneSpots(r, a.length, 1), m = {}; d.forEach((i, k) => m[i] = L[k]); a.forEach((i, k) => m[i] = R[k]); pts = ids.map(i => m[i]); }   // defenders left, attackers right
  ids.forEach((id, k) => { const p = r.players.get(id); if (!p) return; spawn(p, 0, t, pts[k]); p.alive = true; p.it = frs.has(id) ? 1 : 0; });
  for (const p of r.players.values()) if (!ids.includes(p.id)) { p.alive = false; p.it = 0; }
  r.rs = r.tut ? 15 : r.inf === 0 ? classicS(ids.length) : r.inf === 2 ? FREEZE_S : ROUND_S;

  r.evK = -1; r.evF = rnd(2); r.cdEnd = t + CD_MS; r.deadline = r.cdEnd + roundS(r) * 1000; r.tagFrom = r.cdEnd + TAG_GRACE_MS;
  bcastRoom(r);
}

function startMatch(r, t) {
  const ids = [...r.players.values()].filter(p => p.ws || p.bot).map(p => p.id).slice(0, roomMax(r));   // only players who are actually connected
  if (!ids.length) return;
  r.gm = 1 + rnd(999999999); r.mp = !r.pub && r.sel > 0 ? r.sel - 1 : rnd(MAPS.length); r.rn = 0; for (const q of r.players.values()) q.rdy = 0; r.practice = ids.length === 1; r.gone = {}; r.win = r.wn = null; r.lobbyGo = 0; r.botNext = 0;
  for (const q of r.players.values()) { q.mt0 = now(); q.tg = q.tt = 0; q.bk = null; q.bonus = 0; q.mdi = r.inf | 0; q.mpi = r.mp | 0; }
  for (const q of r.players.values()) q.rec = (q.acct && !r.practice && !r.prac && ids.includes(q.id)) ? (r.pub ? 1 : (ids.filter(i => { const z = r.players.get(i); return z && !z.bot; }).length >= 2 ? 2 : 0)) : 0;   // only public lobbies (incl. party joins) count; private rooms and solo practice never do
  startRound(r, ids, t);
}

function finish(r, id, wt) {
  const p = id && r.players.get(id);
  r.st = 'over'; r.win = id || null; r.wn = p ? p.nm : null; r.wt = wt || 0; r.lobbyGo = 0; clearFx(r);
  const W = new Set(); for (const q of r.players.values()) if (wt === 1 ? q.it : wt === 2 ? !q.it : q.id === id) W.add(q.id);   // freeze tag: the whole winning team (freezers or runners) gets the win
  for (const q of r.players.values()) if (q.bk != null && id && String(q.bk) === String(id) && q.id !== id && q.rec) q.bonus = 100;   // spectator who backed the winner
  for (const q of r.players.values()) { q.it = 0; if (r.inf === 1 && q.id === r.first && !W.has(q.id)) { q.rec = 0; continue; } rec(q, W.has(q.id), 1); }   // infection: the starting IT can't win by design, so it is not counted as a loss
  r.res = r.ord.map(id => r.players.get(id) || (r.gone && r.gone[id])).filter(Boolean).map(q => ({ id: q.id, nm: q.nm, b: q.bot ? 1 : 0, w: W.has(q.id) ? 1 : 0, o: q.outAt || 0, tw: q.acct ? q.acct.w : 0 })).sort((a, b) => b.w - a.w || b.o - a.o).map(x => ({ id: x.id, nm: x.nm, b: x.b, w: x.w, tw: x.tw }));   // this match's standings (winners first, then whoever lasted longest)
  if (r.tut) bcast(r, '{"t":"tutdone"}');
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
  r.st = 'play'; r.loser = r.ln = null; r.lk = null; r.rs = r.tut ? 15 : classicS(al.length); r.deadline = t + r.rs * 1000; r.tagFrom = t + TAG_GRACE_MS;
  bcastRoom(r);
}

function expire(r, t, holder) {
  r.loser = holder.id; r.ln = holder.nm; holder.alive = false; holder.it = 0; holder.outAt = now();
  r.st = 'between'; r.betweenEnd = t + BETWEEN_MS; clearFx(r);
  bcastRoom(r);
}

function removePlayer(r, p, t) {
  if (r.players.get(p.id) !== p) return;
  if (r.st !== 'lobby' && r.st !== 'over') rec(p, 0);   // leaving a running match = a loss
  if (r.st !== 'lobby' && r.st !== 'over' && r.ord.includes(p.id)) { p.outAt = p.outAt || now(); (r.gone || (r.gone = {}))[p.id] = p; }   // someone who leaves mid-match (even dead) still appears in the final results
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
function nearOthers(r, p, rad) {   // other living, unfrozen players within rad px, nearest first
  const o = [];
  for (const q of r.players.values()) { if (q === p || !q.alive || q.fz) continue; const d = Math.hypot(q.x - p.x, q.y - p.y); if (d < rad) o.push([d, q]); }
  return o.sort((a, b) => a[0] - b[0]);
}
function shove(q, vx, vy) { if (q.hb || q.gt || q.gk) return; q.vx = vx; q.vy = vy; q.g = 0; q.coy = q.buf = 0; q.cut = 1; q.dash = 0; q.zip = -1; q.bst = PAD_BST; q.rs++; }

/* ---- TUTORIAL room: 5 easy bots, you start as IT, rounds are 15 s, and if the bomb is still on you at 0 it is passed to a bot (you can't be eliminated) ---- */
function tutHint(r, t) {
  const h = [...r.players.values()].find(q => !q.bot && q.ws); if (!h) return;
  const bots = [...r.players.values()].filter(q => q.bot && q.alive).length;
  let k;
  if (r.st === 'between') k = 'out';
  else if (t < r.cdEnd) k = 'cd';
  else if (h.it) { k = (r.deadline - t) / 1000 <= 6 ? 'pass' : 'it'; }
  else k = 'run';
  if (r.tutHold > t) return;
  const key = k + bots; if (key === r.tutK) return; r.tutK = key;
  sendP(h, JSON.stringify({ t: 'tut', k, n: bots }));
}
function useAbility(r, p) {
  if (r.st !== 'play' || p.acd > 0) return;
  const k = p.ab;
  if (k === 'fake' || k === 'clones') {
    for (const dr of k === 'fake' ? [p.face] : [-1, 1]) r.dec.push({ id: 'd' + (++r.fxn), o: p.id, life: FAKE_T, x: p.x, y: p.y, vx: p.vx, vy: p.vy, g: p.g, coy: 0, buf: 0, pj: false, cut: 0, drop: 0, face: p.face,
      it: p.it, dir: dr, stuck: 0, ps: false, dash: 0, dd: 1, dcd: 0, slow: 0, bst: 0, pcd: 0, bv: 0 });
  } else if (k === 'smoke') {
    r.pj.push({ x: p.x + PW / 2, y: p.y + 8, vx: p.face * 520 + p.vx * .4, vy: -420, t: 0 });
  } else if (k === 'trap') {
    if (!p.g) return;                                                               // a trap needs floor under your feet (no cooldown is spent)
    r.tr.push({ id: ++r.fxn, x: Math.round(p.x + PW / 2), y: Math.round(p.y + PH), o: p.id, life: TRAP_T });
  } else if (k === 'spring') {
    if (p.hb) return;
    p.vy = -1450; p.g = 0; p.coy = p.buf = 0; p.cut = 1; p.dash = 0; p.zip = -1; p.rs++;
  } else if (k === 'rocket') {
    if (p.hb) return;
    p.vx = p.face * 1700; p.dash = 0; p.zip = -1; p.bst = PAD_BST; p.rs++;
  } else if (k === 'uppercut') {
    const o = nearOthers(r, p, 450); if (!o.length) return;
    shove(o[0][1], o[0][1].vx * .3, -1500);
  } else if (k === 'recharge') {
    p.dcd = 0; p.gcd = 0;
  } else if (k === 'shock' || k === 'magnet') {
    const o = nearOthers(r, p, 700); if (!o.length) return;
    for (const [, q] of o) { const sg = Math.sign(q.x - p.x) || 1, dist = Math.abs(q.x - p.x); if (k === 'shock') shove(q, sg * 1500, -700); else shove(q, -sg * Math.min(1500, 350 + dist * 3), -350); }
  } else if (k === 'shield') {
    if (p.it) return;                                                               // an IT with a shield would be pointless
    p.shd = 5;
  } else if (k === 'swap') {
    const o = nearOthers(r, p, 1800); if (!o.length || p.hb || p.gt || p.gk || p.zip >= 0) return;
    const q = o[0][1]; if (q.hb || q.gt || q.gk || q.zip >= 0) return;
    const x = p.x, y = p.y; p.x = q.x; p.y = q.y; q.x = x; q.y = y; p.g = q.g = 0; p.rs++; q.rs++;
  } else if (k === 'zap') {
    const o = nearOthers(r, p, 1800); if (!o.length) return;
    const q = o[0][1]; r.lt.push({ id: ++r.fxn, x: Math.round(q.x + PW / 2), y: Math.round(q.y + PH / 2), age: 0, hit: 0 });
  } else return;
  p.acd = ABCD[k] || AB_CD;
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

const inSolid = p => { for (const s of SX) if (p.x < s.x + s.w && p.x + PW > s.x && p.y < s.y + s.h && p.y + PH > s.y) return true; const mx = p.x + PW / 2; for (const q of SL) { if (mx < q.x || mx > q.x + q.w) continue; const s = q.y + (mx - q.x) / q.w * q.dy; if (p.y + PH > s + 6 && p.y < s + q.hv) return true; } return false; };

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
function dragBy(q, mx, my) {   // moves in 3 px sub-steps and stops at the first wall: a long drag can never tunnel through a platform
  const n = Math.max(1, Math.ceil(Math.max(Math.abs(mx), Math.abs(my)) / 3)), sx = mx / n, sy = my / n;
  for (let i = 0; i < n; i++) {
    const ox = q.x, oy = q.y;
    q.x = Math.max(LX, Math.min(RX - PW, ox + sx)); q.y = oy + sy;
    if (!inSolid(q)) continue;
    q.y = oy; if (!inSolid(q)) continue;
    q.x = ox; q.y = oy + sy; if (!inSolid(q)) continue;
    q.x = ox; q.y = oy; break;
  }
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

// Every input the client sent is simulated exactly once, in order (never repeated, never dropped), so the client's prediction always equals the server state.
// A late packet just waits; a burst is caught up with a time budget (credit), so nobody can speed-hack by flooding inputs.
function runHuman(r, p, cd) {
  p.credit = Math.min(4, p.credit + 1);
  let did = 0;
  while (p.credit >= 1) {
    if (!p.q.length) {
      if (did || ++p.starve <= REPEAT_MAX) break;
      p.lastB = 0; p.credit--; advance(r, p, 0); break;   // really silent (hidden tab / lost signal): stand still
    }
    p.starve = 0;
    const c = p.q.shift(); p.lastSeq = c.s; p.lastB = c.b; p.credit--; did++;
    advance(r, p, (cd || p.fz) ? 0 : c.b);
  }
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
  r.pb = 2;   // at most 2 bot plans per tick
  for (const p of r.players.values()) {
    if (!p.alive) continue;
    if (p.acd > 0) p.acd -= DT; if (p.shd > 0) p.shd -= DT; if (p.lv > 0) p.lv -= DT;                                           // ability cooldown
    p.slow = inTrap(r, p) || p.lv > 0;                                                // standing in a trap?
    if (p.bot) advance(r, p, (cd || p.fz) ? 0 : botInput(r, p, t)); else runHuman(r, p, cd);
    if (p.bot && r.st === 'play' && !cd) { if (!p.emoNx) p.emoNx = t + 25000 + rnd(35000); else if (t >= p.emoNx) { p.emoNx = t + 30000 + rnd(60000); if (Math.random() < .4) bcast(r, JSON.stringify({ t: 'emo', o: p.id, k: rnd(30) })); } }   // random bot emote every 4-13 s
    if (p.hrs !== p.rs) { p.hx.fill(p.x); p.hy.fill(p.y); p.hrs = p.rs; }                 // position history (lag compensation)
    p.hi = (p.hi + 1) & 31; p.hx[p.hi] = p.x; p.hy[p.hi] = p.y;
  }

  if (r.tut && (r.st === 'play' || r.st === 'between')) tutHint(r, t);
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
      else if (q.fimm <= 0 && !(q.shd > 0)) {
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
    if (t >= r.tagFrom) for (const q of al) if (!q.it && !(q.shd > 0)) for (const h of al) if (h.it && tagHit(h, q)) { q.it = 1; r.lastInf = q.id; break; }
    const hl = al.filter(p => !p.it);
    if (!r.practice && al.length > 1) { if (hl.length <= 1) finish(r, hl.length ? hl[0].id : null); }   // only a still-healthy survivor can win; if nobody is left healthy (e.g. the last one quit) nobody gets a win
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
    if (!a || !b || t > r.lk.until || (t > r.lk.min && !hit(a, b, -24))) r.lk = null;   // released once truly apart (24px) AND the lag-comp rewind window has passed   // lock lasts the FULL time (old code released it the moment they separated 8px -> instant re-tag)
  }
  if (t >= r.tagFrom) {
    for (const q of r.players.values()) {
      if (!q.alive || q.it || q === holder || q.shd > 0) continue;
      if (!tagHit(holder, q)) continue;                                   // real overlap only, never from a distance
      if (r.lk && r.lk.from === q.id && r.lk.to === holder.id) continue;
      holder.it = 0; q.it = 1; holder.tg = (holder.tg | 0) + 1; q.tt = (q.tt | 0) + 1;
      if (holder.gt === q.id) ungrab(r, holder, GRAB_CD); else if (q.gt === holder.id) ungrab(r, q, GRAB_CD);   // a tag ends the grip between the two
      r.lk = { from: holder.id, to: q.id, until: t + LOCK_MS, min: t + 250 };
      bcast(r, JSON.stringify({ t: 'tag', a: q.id, b: holder.id }));
      holder = q;
      break;
    }
  }
  // the arrow holder who runs into a decoy pops it (the holder's own decoys are ignored)
  for (let i = r.dec.length - 1; i >= 0; i--) if (r.dec[i].o !== holder.id && hit(holder, r.dec[i], 3)) r.dec.splice(i, 1);
  if (!r.practice && t >= r.deadline) {
    if (r.tut && !holder.bot) {   // tutorial mercy: the human is never eliminated, the bomb jumps to the nearest bot
      const o = nearOthers(r, holder, 1e5)[0];
      if (o) { const q = o[1]; holder.it = 0; q.it = 1; r.lk = { from: holder.id, to: q.id, until: t + LOCK_MS, min: t + 250 }; r.deadline = t + r.rs * 1000; r.tutHold = t + 3000; r.tutK = ''; bcast(r, JSON.stringify({ t: 'tag', a: q.id, b: holder.id })); sendP(holder, '{"t":"tut","k":"saved","n":0}'); return; }
    }
    expire(r, t, holder);
  }
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
let snapDue = false;
function tickAll(t, tt, last) {
  tickN++;
  if (tickN % snapEvery === 0) snapDue = true;      // a snapshot is owed ...
  const doSnap = last && snapDue;                   // ... but it is only sent after the last tick of a catch-up burst (stale in-between ones just cost CPU and arrive in a clump)
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
        if (rooms.has(r.key) && (r.st === 'play' || r.st === 'between') && doSnap && conn(r)) snapshot(r, t, tt);
      }
    } catch (e) { console.error('room error, closing room ' + r.key + ':', e); destroyRoom(r); }
  }
  if (doSnap) snapDue = false;
}
let lagEma = 0, calmSince = 0;
function loopBody() {
  const t = now();
  // Overload guard: if ticks keep running late (a busy / tiny shared CPU), halve the snapshot rate so the game logic stays on time
  // and every player keeps the same fair, steady 60 Hz simulation. It returns to 60 snapshots/s by itself when the load drops.
  const lag = Math.max(0, t - nextTick);
  lagEma += (lag - lagEma) * 0.05;
  if (!FIXED_SNAP) {
    if (snapEvery === SNAP_BASE && lagEma > 10) { snapEvery = SNAP_BASE + 1; calmSince = 0; console.log('high load: snapshots at 20/s'); }
    else if (snapEvery > SNAP_BASE) { if (lagEma < 1.5) { if (!calmSince) calmSince = t; else if (t - calmSince > 6000) { snapEvery = SNAP_BASE; calmSince = 0; console.log('load normal: snapshots at 30/s'); } } else calmSince = 0; }
  }
  let due = 0; for (let nt = nextTick; nt <= t && due < 5; nt += TICK_MS) due++;
  for (let i = 0; i < due; i++) { tickAll(t, nextTick, i === due - 1); nextTick += TICK_MS; }   // fixed 60 Hz, catches up after a hiccup
  if (nextTick < t - 100) nextTick = t;
}
// one wake-up per tick (60/s) instead of 250/s, aimed at the exact tick time: less CPU on a shared free-tier core and steadier snapshot timing
function loop() { try { loopBody(); } catch (e) { console.error('tick loop error:', e); } setTimeout(loop, Math.max(1, nextTick - now())); }
setTimeout(loop, 1);

try { for (let i = 0; i < MAPS.length; i++) { setMap(i); NAV[i] = navBuild(); } setMap(0); } catch (e) { console.error('nav prebuild failed:', e.message); }   // no lag spike on the first match

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
  const lt = setTimeout(() => { if (!ws.acct) try { ws.close(); } catch {} }, 15000); ws.on('close', () => clearTimeout(lt));   // never logged in -> dropped
  ws.on('pong', () => { const n = Date.now(); ws.lastSeen = n; if (ws.pingAt) { const m = n - ws.pingAt; ws.rtt = ws.rtt ? ws.rtt * .7 + m * .3 : m; } });

  let r = null, p = null, cnt = 0, winStart = Date.now();
  const pid = hex(4); let pt = null;     // party membership (before a room exists)
  const eff = P => { const L = P.mem.get(P.lead); if (L && !L.inr) return P.lead; const a = [...P.mem.values()].find(x => !x.inr); return a ? a.id : P.lead; };   // who can press start/mode right now (the real leader keeps the crown even while away in a match)
  const pbc = P => { const act = [...P.mem.values()].filter(x => !x.inr); if (!act.length) return; if (!P.mem.has(P.lead)) P.lead = act[0].id; const ef = eff(P), lst = act.map(x => ({ id: x.id, nm: x.nm, rd: x.rd, cs: x.cs || '' })); for (const q of act) send(q.ws, JSON.stringify({ t: 'party', code: P.code, you: q.id, lead: P.lead, can: ef === q.id ? 1 : 0, md: P.md, mem: lst })); };   // members still inside a match are hidden until they come back
  let hp = null;   // the party I belong to while I'm inside a match (the party survives the match so friends stay together)
  const pdrop = () => { const P = pt || hp; if (!P) return; pt = hp = null; P.mem.delete(pid); if (!P.mem.size) { P.kill = setTimeout(() => { if (!P.mem.size) parties.delete(P.code); }, 60000); return; } if (P.lead === pid) { P.olead = ws.acct; clearTimeout(P.olt); P.olt = setTimeout(() => { P.olead = null; }, 30000); P.lead = ([...P.mem.values()].find(x => !x.inr) || P.mem.values().next().value).id; } for (const q of P.mem.values()) q.rd = 0; pbc(P); };
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
    const pp = newPlayer(nm, ci); pp.since = now(); pp.acct = ws.acct; pp.rec = 0; { const X = prog(ws.acct); if (X.sab && ABIL.has(X.sab) && (ABP[X.sab] === 0 || X.own['ab_' + X.sab])) pp.ab = X.sab; }
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
          ws.acct = a; send(ws, JSON.stringify({ t: 'st', p: a.p, w: a.w, l: a.l })); AN.open(ws, a, req);
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
      if (typeof m.d === 'number' && m.d >= 0) p.rd = Math.min(240, m.d | 0);   // how far behind (ms) this client draws other players: tags are judged against that view
      return;
    }
    if (m.t === 'hb') { ws.pres = t; send(ws, '{"t":"hb"}'); return; }
    if (m.t === 'leave' && r && p) { if (hp && r.pub && r.st === 'lobby' && hp.lead === pid) for (const q of hp.mem.values()) if (q.inr && q.id !== pid) send(q.ws, '{"t":"pret"}');   // leader cancels the search: the whole party goes back to the party screen
      removePlayer(r, p, now()); p.ws = null; r = null; p = null; return; }   // deliberate exit: no grace period

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
          for (const [k, q] of [...P.mem]) if (q.ws !== ws && q.ws && q.ws.acct === ws.acct) P.mem.delete(k);   // same account coming back from a match: replace the stale entry
          if (P.mem.size >= PARTY_MAX) return err('full');
        }
        for (const q of P.mem.values()) q.rd = 0;                 // someone new arrived: everybody readies up again
        const nm = ws.acct.n;
        if (P.kill) { clearTimeout(P.kill); P.kill = 0; }
        if (P.olead && P.olead === ws.acct) { P.lead = pid; P.olead = null; }   // the real leader coming back gets the crown back
        if (!P.mem.has(P.lead)) P.lead = pid;                                   // everyone else never takes it
        const cs = typeof m.cs === 'string' && /^[0-9,]{1,24}$/.test(m.cs) ? csClean(ws.acct, m.cs) : '';
        P.mem.set(pid, { id: pid, ws, nm, cs, rd: 0, inr: 0, go: rr => { hp = pt; pt = null; const me = P.mem.get(pid); if (me) me.inr = 1; addPlayer(rr, nm); } });
        pt = P; ws.joined = 1;
        return pbc(P);
      }
      if (pt) {
        const P = pt;
        if (m.t === 'prdy') { P.mem.get(pid).rd = m.v ? 1 : 0; return pbc(P); }
        if (m.t === 'pcos') { if (typeof m.v === 'string' && /^[0-9,]{1,24}$/.test(m.v)) { P.mem.get(pid).cs = csClean(ws.acct, m.v); pbc(P); } return; }
        if (m.t === 'pmode' && eff(P) === pid) { P.md = Math.max(0, Math.min(2, m.m | 0)); return pbc(P); }
        if (m.t === 'pstart' && eff(P) === pid) {
          const mem = [...P.mem.values()].filter(q => !q.inr), n = mem.length;
          if (mem.some(q => !q.rd)) return;
          let best = null;
          for (const rr of rooms.values()) {                      // a lobby with room for the WHOLE party, fullest first
            if (!rr.pub || rr.inf !== P.md || rr.st !== 'lobby' || conn(rr) + n > PUB_SIZE) continue;
            if (!best || conn(rr) > conn(best)) best = rr;
          }
          if (!best && rooms.size >= MAX_ROOMS) return err('busy');
          if (!best) { let k; do { k = 'p-' + hex(3); } while (rooms.has(k)); best = mkRoom(k, true, P.md); }   // no space for all -> fresh lobby
          while (best.players.size + n > PUB_SIZE) { const b = [...best.players.values()].find(q => q.bot || !q.ws); if (!b) break; best.players.delete(b.id); }
          for (const q of mem) { q.rd = 0; q.go(best); }   // the party stays alive on the server: everybody rejoins it after the match
          return;
        }
        return;
      }
      if (m.t === 'tut') {   // first-time tutorial: private room, 5 easy bots, nothing counted
        if (rooms.size >= MAX_ROOMS) return err('busy');
        let code; do { code = Array.from({ length: 4 }, () => CODE_CHARS[rnd(32)]).join(''); } while (rooms.has(code));
        const nr = mkRoom(code, false); nr.tut = 1; nr.sel = 1; nr.inf = 0;
        addPlayer(nr, ws.acct.n); if (!r) return;
        addBots(nr, 5); for (const b of nr.players.values()) if (b.bot) b.sk = .5;
        return startMatch(nr, now());
      }
      if (m.t === 'create') {
        if (rooms.size >= MAX_ROOMS) return err('busy');
        let code; do { code = Array.from({ length: 4 }, () => CODE_CHARS[rnd(32)]).join(''); } while (rooms.has(code));
        const nr = mkRoom(code, false); nr.prac = m.pr ? 1 : 0;   // practice room: host picks mode + map, every match gets 4 bots, nothing is counted
        return addPlayer(nr, ws.acct.n);
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

    if (m.t === 'cos') { if (typeof m.v === 'string' && /^[0-9,]{1,24}$/.test(m.v)) { p.cs = csClean(ws.acct, m.v); bcastRoom(r); } return; }
    if (m.t === 'bk') { if (!p.alive && r.st !== 'lobby') p.bk = m.k == null ? null : String(m.k).slice(0, 24); return; }
    if (m.t === 'emo') { const k = m.k | 0, tn = Date.now(); if (k >= 0 && k < 30 && prog(ws.acct).em.includes(k) && tn - (p.emoAt || 0) > 1500) { p.emoAt = tn; bcast(r, JSON.stringify({ t: 'emo', o: p.id, k })); } return; }
    /* ---- ghost zap: an eliminated player calls a lightning strike anywhere (same strike as the random ones, server-side cooldown) ---- */
    if (m.t === 'zap') { const tn = now(), zx = +m.x, zy = +m.y; if (r.st === 'play' && !p.alive && tn >= r.cdEnd && tn - (p.zapAt || -1e9) > ZAP_CD * 1000 && r.lt.length < 6 && isFinite(zx) && isFinite(zy)) { p.zapAt = tn; r.lt.push({ id: ++r.fxn, x: ri(Math.max(LX + LT_R, Math.min(RX - LT_R, zx))), y: ri(Math.max(120, Math.min(WH - 40, zy))), age: 0, hit: 0 }); sendP(p, '{"t":"zap","cd":' + ZAP_CD + '}'); } return; }
    /* ---- ability choice: in the lobby (spectators waiting for the next match may pick too) ---- */
    if (m.t === 'ab') { if (typeof m.k === 'string' && ABIL.has(m.k) && (ABP[m.k] === 0 || prog(ws.acct).own['ab_' + m.k]) && (r.st === 'lobby' || !p.alive)) p.ab = m.k; return; }

    /* ---- room controls ---- */
    if (m.t === 'ready' && r.st === 'lobby' && !r.pub) { p.rdy = m.v ? 1 : 0; return bcastRoom(r); }
    if (m.t === 'map' && r.st === 'lobby' && !r.pub && r.hostId === p.id) { r.sel = Math.max(0, Math.min(MAPS.length, m.m | 0)); return bcastRoom(r); }
    if (m.t === 'mode' && r.st === 'lobby' && !r.pub && r.hostId === p.id) { r.inf = Math.max(0, Math.min(2, m.m | 0)); return bcastRoom(r); }
    if (m.t === 'start' && r.st === 'lobby' && !r.pub && r.hostId === p.id) { if (r.prac) { for (const b of [...r.players.values()]) if (b.bot) r.players.delete(b.id); addBots(r, 4); return startMatch(r, now()); } if (conn(r) < (r.inf === 1 ? 4 : r.inf === 2 ? 3 : 1)) return; if ([...r.players.values()].some(q => q.ws && !q.rdy)) return; return startMatch(r, now()); }   // infection needs 4+ players, freeze tag 3+
    if (m.t === 'lobby' && r.st === 'over' && !r.pub && r.hostId === p.id) return toLobby(r);
  });

  ws.on('close', () => {
    pdrop();
    AN.close(ws); const left = (perIp.get(ip) || 1) - 1;
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
  Promise.all([accFlush(), AN.flush()]).finally(() => server.close(() => process.exit(0)));
  setTimeout(() => process.exit(0), 4000).unref();
}
process.on('SIGTERM', shutdown);
process.on('SIGINT', shutdown);
process.on('uncaughtException', (e) => console.error('uncaught:', e));
process.on('unhandledRejection', (e) => console.error('unhandled:', e));