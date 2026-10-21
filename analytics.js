// Private analytics for the Tag game. Plugs into server.js (see the 7 hook lines there).
// Dashboard: https://YOUR-SITE/admin   (needs env var ADMIN_KEY; without it the page does not exist)
'use strict';
const crypto = require('crypto'), fs = require('fs'), path = require('path');
const KEY = process.env.ADMIN_KEY || '';
const DAY = 864e5, day = (t = Date.now()) => Math.floor(t / DAY);
const SESS_GAP = 90000;   // a reconnect within 90 s belongs to the same visit (menu <-> match reconnects don't inflate sessions)

module.exports = function ({ db, wss, ACC, rooms, MEM, UP, getAcc, accSave, prog, kickAcc, pushPr, delAcc }) {
  const idx = new Map(), sm = a => ({ k: a.k, n: a.n, p: a.p | 0, w: a.w | 0, t: (a.pr && a.pr.tok) | 0, g: (a.pr && a.pr.gem) | 0, b: a.ban ? 1 : 0 });   // light index of every account
  const days = {}, packs = {}, users = new Map(), dirty = new Set(), sess = new Map(), live = [];
  let dDirty = false, ready = false, bad = false, pend = [], snap = null, snapAt = 0, scanning = false, cache = null, cacheAt = 0;
  const shard = k => { let h = 0; for (let i = 0; i < k.length; i++) h = (h * 31 + k.charCodeAt(i)) & 7; return h; };
  const D = d => days[d] || (dDirty = true, days[d] = { s: 0, ss: 0, ns: 0, m: 0, q: 0, ms: 0, tg: 0, md: [0, 0, 0], mp: [0, 0, 0], dv: [0, 0], sb: [0, 0, 0, 0, 0, 0], rv: 0, pu: 0, pk: 0, h: new Array(48).fill(0) });

  /* ---------- tracking hooks ---------- */
  function touch(k) {   // user = [firstDay (0 = existed before tracking), ...active days ascending]
    const t = day(); let u = users.get(k);
    if (!u) { users.set(k, [t, t]); D(t).ns++; dDirty = true; }
    else if (u[u.length - 1] !== t) { u.push(t); if (u.length > 121) u.splice(1, 1); }
    else return;
    dirty.add(shard(k));
  }
  function open(ws, a, req) {   // socket proved it belongs to an account
    ws.anK = a.k; const t = Date.now(); let s = sess.get(a.k);
    if (s && (s.n > 0 || t - s.end < SESS_GAP)) s.n++;
    else {
      sess.set(a.k, { start: t, end: 0, n: 1 });
      const ua = String((req && req.headers['user-agent']) || ''), d = D(day(t));
      d.s++; d.dv[/Mobi|Android|iPhone|iPad/i.test(ua) ? 0 : 1]++; dDirty = true;
    }
    if (ready) touch(a.k); else pend.push(a.k);
  }
  function close(ws) {
    if (!ws.anK) return; const s = sess.get(ws.anK); ws.anK = null;
    if (s && --s.n <= 0) { s.n = 0; s.end = Date.now(); }
  }
  function match(a, p, win, du, fin) {   // one counted match for one player
    const d = D(day()); d.m++; d.ms += Math.max(0, du) || 0; d.tg += p.tg | 0; if (!fin) d.q++;
    const mi = p.mdi | 0, mp = p.mpi | 0; if (mi >= 0 && mi < 3) d.md[mi]++; if (mp >= 0 && mp < 3) d.mp[mp]++; dDirty = true;
  }
  function purchase(pk, id) { const d = D(day()); d.rv += pk.c || 0; d.pu++; packs[id] = (packs[id] || 0) + 1; dDirty = true; }

  const online = () => { let n = 0; for (const s of sess.values()) if (s.n > 0) n++; return n; };
  let tick = 0;
  setInterval(() => {   // every 5 s: concurrent users + close finished visits
    const t = Date.now(), c = online(), d = D(day(t)), b = Math.floor((t % DAY) / 1800000);
    if (c > d.h[b]) { d.h[b] = c; dDirty = true; } if (c > d.pk) d.pk = c;
    if (++tick % 12 === 0) { live.push([t, c]); if (live.length > 180) live.shift(); }   // chart history: 1 point / min
    for (const [k, s] of sess) if (s.n === 0 && t - s.end >= SESS_GAP) {
      const sec = Math.max(0, (s.end - s.start) / 1000), e = D(day(s.end)); e.ss += sec;
      e.sb[sec < 60 ? 0 : sec < 300 ? 1 : sec < 900 ? 2 : sec < 1800 ? 3 : sec < 3600 ? 4 : 5]++; sess.delete(k); dDirty = true;
    }
  }, 5000).unref();

  /* ---------- persistence (Upstash, same DB as the accounts) ---------- */
  async function flush() {
    if (bad || !ready) return; const c = [], sh = [...dirty]; dirty.clear();
    if (dDirty) { dDirty = false; const ks = Object.keys(days).map(Number).sort((a, b) => a - b); while (ks.length > 400) delete days[ks.shift()]; c.push(['SET', 'an:days', JSON.stringify({ d: days, p: packs })]); }
    for (const i of sh) { const o = {}; for (const [k, u] of users) if (shard(k) === i) o[k] = u; c.push(['SET', 'an:u:' + i, JSON.stringify(o)]); }
    if (!c.length) return;
    try { await db(...c); } catch (e) { console.error('analytics save failed:', e.message); dDirty = true; for (const i of sh) dirty.add(i); }
  }
  setInterval(flush, 120000).unref();

  async function scan() {   // counts every account that exists (also those who never logged in since tracking began) + lifetime stats
    if (scanning) return; scanning = true;
    try {
      let keys = [];
      if (!UP) keys = [...MEM.keys()].filter(k => k.startsWith('acc:'));
      else { let c = '0'; do { const [r] = await db(['SCAN', c, 'MATCH', 'acc:*', 'COUNT', '500']); c = String(r[0]); keys.push(...r[1]); } while (c !== '0' && keys.length < 50000); }
      const accs = [], need = [];
      for (const k of keys) { const c = ACC.get(k.slice(4)); c ? accs.push(c) : need.push(k); }
      for (let i = 0; i < need.length; i += 100) for (const v of await db(...need.slice(i, i + 100).map(k => ['GET', k]))) if (v) { try { accs.push(JSON.parse(v)); } catch {} }
      if (keys.length < 50000 && accs.length === keys.length) {   // drop deleted accounts from the user history + index
        const ex = new Set(accs.map(a => a.k));
        for (const k of [...users.keys()]) if (!ex.has(k)) { users.delete(k); dirty.add(shard(k)); }
        for (const k of [...idx.keys()]) if (!ex.has(k)) idx.delete(k);
      }
      const S = { total: accs.length, p1: 0, p5: 0, p20: 0, payers: 0, matches: 0, wins: 0, top: [] };
      for (const a of accs) {
        idx.set(a.k, sm(a)); if (!users.has(a.k)) { users.set(a.k, [0]); dirty.add(shard(a.k)); }
        const p = a.p | 0; S.matches += p; S.wins += a.w | 0; if (p >= 1) S.p1++; if (p >= 5) S.p5++; if (p >= 20) S.p20++;
        if (a.pay && a.pay.ids && a.pay.ids.length) S.payers++;
      }
      S.top = accs.sort((x, y) => (y.p | 0) - (x.p | 0)).slice(0, 15).map(a => [a.n, a.p | 0, a.w | 0]);
      snap = S; snapAt = Date.now();
    } catch (e) { console.error('analytics scan failed:', e.message); }
    scanning = false;
  }
  (async () => {
    try {
      const r = await db(['GET', 'an:days'], ...[0, 1, 2, 3, 4, 5, 6, 7].map(i => ['GET', 'an:u:' + i]));
      if (r[0]) { const o = JSON.parse(r[0]); Object.assign(days, o.d); Object.assign(packs, o.p || {}); }
      for (let i = 0; i < 8; i++) if (r[i + 1]) for (const [k, u] of Object.entries(JSON.parse(r[i + 1]))) users.set(k, u);
    } catch (e) { bad = true; console.error('analytics load failed (saving disabled so nothing is overwritten):', e.message); }
    await scan(); ready = true; for (const k of pend) touch(k); pend = [];
  })();

  /* ---------- dashboard data ---------- */
  function build() {
    const t = day(), N = 90, from = t - N + 1, dau = new Array(N).fill(0), wau = new Array(N).fill(0), mau = new Array(N).fill(0), nu = new Array(N).fill(0);
    const ret = { 1: [0, 0], 3: [0, 0], 7: [0, 0], 14: [0, 0], 30: [0, 0] }, coh = {}; let lapsed = 0, dormant = 0, known = 0;
    for (const u of users.values()) {
      const f = u[0], set = new Set(u.slice(1)); let cw = -1, cm = -1;
      for (let i = 1; i < u.length; i++) {
        const x = u[i]; if (x >= from) dau[x - from]++;
        for (const [w, arr, ref] of [[7, wau, 0], [30, mau, 1]]) {
          const cov = ref ? cm : cw; let s = Math.max(x, cov + 1); const e = Math.min(x + w - 1, t);
          for (let d = s; d <= e; d++) if (d >= from) arr[d - from]++;
          if (x + w - 1 > cov) { if (ref) cm = x + w - 1; else cw = x + w - 1; }
        }
      }
      const last = u.length > 1 ? u[u.length - 1] : 0;
      if (last) { known++; if (last < t - 29) dormant++; else if (last < t - 6) lapsed++; }
      if (f > 0) {
        if (f >= from) nu[f - from]++;
        for (const n of [1, 3, 7, 14, 30]) if (f + n <= t && f >= t - 60) { ret[n][1]++; if (set.has(f + n)) ret[n][0]++; }
        if (f >= t - 13) { const c = coh[f] || (coh[f] = { d: f, n: 0, r: {} }); c.n++; for (const n of [1, 3, 7]) if (f + n <= t && set.has(f + n)) c.r[n] = (c.r[n] || 0) + 1; }
      }
    }
    const total = Math.max(snap ? snap.total : 0, users.size); let cum = total; const cumA = new Array(N);
    for (let i = N - 1; i >= 0; i--) { cumA[i] = cum; cum -= nu[i]; }
    const rows = []; for (let i = 0; i < N; i++) { const d = from + i, r = days[d] || {}; rows.push(Object.assign({ d, dau: dau[i], wau: wau[i], mau: mau[i], nu: nu[i], cum: cumA[i] }, r)); }
    let inM = 0, lob = 0, rm = 0; for (const r of rooms.values()) { rm++; let h = 0; for (const p of r.players.values()) if (p.ws && !p.bot) h++; if (r.st === 'play' || r.st === 'between') inM += h; else if (r.pub) lob += h; }
    const ks = Object.keys(days).map(Number);
    return {
      now: Date.now(), today: t, since: ks.length ? Math.min(...ks) : t, rows, packs, tracked: known, lapsed, dormant, snap, snapAt,
      ret: Object.fromEntries(Object.entries(ret).map(([n, v]) => [n, v[1] ? [Math.round(v[0] / v[1] * 1000) / 10, v[1]] : null])),
      coh: Object.values(coh).sort((a, b) => a.d - b.d),
      live: { online: online(), inMatch: inM, lobby: lob, rooms: rm, series: live }
    };
  }

  const liveNow = () => {   // computed fresh on every request = real time
    let inM = 0, lob = 0, rm = 0; for (const r of rooms.values()) { rm++; let h = 0; for (const p of r.players.values()) if (p.ws && !p.bot) h++; if (r.st === 'play' || r.st === 'between') inM += h; else if (r.pub) lob += h; }
    const c = online(), t = Date.now(); return { online: c, inMatch: inM, lobby: lob, rooms: rm, series: live.concat([[t, c]]) };
  };
  function players(q) {   // fresh on every request: live accounts override the scanned index
    for (const a of ACC.values()) idx.set(a.k, sm(a));
    q = String(q || '').toLowerCase().slice(0, 20); const all = [], on = [];
    for (const [k, v] of idx) { if (q && !String(v.n).toLowerCase().includes(q)) continue; const o = sess.has(k) && sess.get(k).n > 0 ? 1 : 0; const x = Object.assign({ o }, v); all.push(x); if (o) on.push(x); }
    const srt = (a, b) => b.p - a.p; all.sort((a, b) => b.o - a.o || srt(a, b)); on.sort(srt);
    return { all: all.slice(0, 100), on: on.slice(0, 200), total: all.length };
  }
  async function adminAct(m) {
    const k = String(m.k || '').toLowerCase(); if (!/^[a-z0-9_]{3,12}$/.test(k)) return;
    const a = await getAcc(k); if (!a) return;
    if (m.act === 'ban') { a.ban = 1; accSave(a); kickAcc(a); }
    else if (m.act === 'unban') { delete a.ban; accSave(a); }
    else if (m.act === 'remove') { await delAcc(a); idx.delete(k); if (users.delete(k)) dirty.add(shard(k)); if (snap && snap.total > 0) snap.total--; cache = null; return; }
    else if (m.act === 'set') { const X = prog(a), t = Math.floor(+m.tok), g = Math.floor(+m.gem); if (isFinite(t) && t >= 0 && t <= 1e9) X.tok = t; if (isFinite(g) && g >= 0 && g <= 1e9) X.gem = g; accSave(a); pushPr(a); }
    idx.set(k, sm(a));
  }
  /* ---------- http: /admin and /admin/api ---------- */
  const hs = s => crypto.createHash('sha256').update(String(s)).digest(), bad401 = new Map(); setInterval(() => bad401.clear(), 60000).unref();
  function http(req, res, url) {
    const H = { 'Cache-Control': 'no-store', 'X-Robots-Tag': 'noindex', 'X-Content-Type-Options': 'nosniff', 'Referrer-Policy': 'no-referrer', 'X-Frame-Options': 'DENY' };
    if (!KEY) { res.writeHead(404); return res.end(); }
    if (url === '/admin' && req.method === 'GET') {
      let page; try { page = fs.readFileSync(path.join(__dirname, 'admin.html')); } catch { res.writeHead(500); return res.end('admin.html missing'); }
      res.writeHead(200, { ...H, 'Content-Type': 'text/html; charset=utf-8', 'Content-Security-Policy': "default-src 'none'; script-src 'unsafe-inline' https://cdnjs.cloudflare.com; style-src 'unsafe-inline'; connect-src 'self'; img-src data:" });
      return res.end(page);
    }
    if (url === '/admin/api' && req.method === 'POST') {
      const ip = String(req.headers['x-forwarded-for'] || req.socket.remoteAddress || '').split(',')[0].trim();
      if ((bad401.get(ip) || 0) >= 10) { res.writeHead(429, H); return res.end('{}'); }
      let b = ''; req.on('data', d => { b += d; if (b.length > 1024) req.destroy(); });
      req.on('end', async () => {
        const out = (c, o) => { res.writeHead(c, { ...H, 'Content-Type': 'application/json' }); res.end(JSON.stringify(o)); };
        try {
          if (!crypto.timingSafeEqual(hs(req.headers['x-admin-key'] || ''), hs(KEY))) { bad401.set(ip, (bad401.get(ip) || 0) + 1); return out(401, { e: 'key' }); }
          let m = {}; try { m = JSON.parse(b || '{}'); } catch {}
          if (m.act) await adminAct(m);
          if (m.r && Date.now() - snapAt > 300000) { await scan(); cache = null; }   // "refresh accounts" button: at most once per 5 min (it reads the DB)
          if (!cache || Date.now() - cacheAt > 2000) { cache = build(); cacheAt = Date.now(); }
          out(200, Object.assign({}, cache, { now: Date.now(), live: liveNow(), pl: players(m.q) }));
        } catch (e) { console.error('admin api:', e.message); out(500, { e: 'err' }); }
      });
      return;
    }
    res.writeHead(404); res.end();
  }
  return { open, close, match, purchase, flush, http };
};
