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
const MAX_ROOM = 5;
const PUB_SIZE = 5;
const MAX_CONN_PER_IP = +process.env.MAX_CONN_PER_IP || 20;
const MAX_CLIENTS = 2000;
const MAX_ROOMS = 600;
const LOBBY_GRACE_MS = 10000;
const ALLOWED = (process.env.ALLOWED_ORIGINS || '').split(',').map(x => x.trim()).filter(Boolean);
const TICK_MS = 1000 / 60;
const DT = 1 / 60;
let snapEvery = +process.env.TAG_SNAP_EVERY || 1;
const FIXED_SNAP = !!process.env.TAG_SNAP_EVERY;
const ROUND_S = +process.env.TAG_ROUND_S || 100;
const CD_MS = 2200;
const TAG_GRACE_MS = 300;
const BETWEEN_MS = 3200;
const LOBBY_GO_MS = 3000;
const LOCK_MS = 1200;
const GRACE_MS = 15000;
const STALL_MS = 150;
const LOBBY_IDLE_MS = +process.env.TAG_LOBBY_IDLE_MS || 10 * 60 * 1000;
const QCAP = 12;

/* ---- abilities ---- */
const DASH_V = 1000, DASH_T = 0.16, DASH_CD = 15;
const AB_CD = 30;
const FAKE_T = 5, SMOKE_T = 5, TRAP_T = 5;
const TRAP_W = 110, TRAP_IMM = 1;
const SLOW_K = 0.4, JUMP_K = 0.8;

/* ---- grab ---- */
const GRAB_REACH = 46, GRAB_REACH_T = 0.7;
const GRAB_MAX = 2.5, GRAB_MIN = 0.25;
const GRAB_CD = 8, GRAB_MISS_CD = 1.5;
const GRAB_ROPE = 70, GRAB_BREAK = 300, GRAB_IMM = 1.2;
const HELD_K = 0.5, CARRY_K = 0.8;
const ABIL = new Set(['fake', 'smoke', 'trap']);

const rooms = new Map();

/* ---------------- static file ---------------- */
const FILE = path.join(__dirname, 'index.html');
let html = null, gz = null, br = null, etag = '', mtime = 0;

function loadHtml() {
  try {
    mtime = fs.statSync(FILE).mtimeMs;
    html = fs.readFileSync(FILE);
    gz = zlib.gzipSync(html, { level: 9 });
    try {
      br = zlib.brotliCompressSync(html, {
        params: {
          [zlib.constants.BROTLI_PARAM_QUALITY]: 11,
          [zlib.constants.BROTLI_PARAM_SIZE_HINT]: html.length
        }
      });
    } catch {
      br = null;
    }
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
    res.writeHead(200, {
      'Content-Type': 'text/plain',
      'Cache-Control': 'no-store'
    });
    return res.end('ok');
  }

  if (url === '/stats') {
    let waiting = 0;
    for (const r of rooms.values()) {
      if (r.pub && r.st === 'lobby') waiting += r.players.size;
    }

    res.writeHead(200, {
      'Content-Type': 'application/json',
      'Cache-Control': 'no-store'
    });

    return res.end(JSON.stringify({
      online: wss.clients.size,
      waiting
    }));
  }

  if (url === '/favicon.ico') {
    res.writeHead(204);
    return res.end();
  }

  if (req.method !== 'GET' && req.method !== 'HEAD') {
    res.writeHead(405);
    return res.end();
  }

  try {
    if (fs.statSync(FILE).mtimeMs !== mtime) loadHtml();
  } catch {}

  if (!html) {
    res.writeHead(500);
    return res.end('index.html missing');
  }

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

  if (req.headers['if-none-match'] === etag) {
    res.writeHead(304, headers);
    return res.end();
  }

  const ae = req.headers['accept-encoding'] || '';
  const useBr = br && /\bbr\b/.test(ae);
  const useGz = !useBr && /\bgzip\b/.test(ae);
  const body = useBr ? br : useGz ? gz : html;

  if (useBr) headers['Content-Encoding'] = 'br';
  else if (useGz) headers['Content-Encoding'] = 'gzip';

  headers['Content-Length'] = body.length;

  res.writeHead(200, headers);
  res.end(req.method === 'HEAD' ? undefined : body);
});

server.keepAliveTimeout = 65000;
server.headersTimeout = 66000;

const wss = new WebSocketServer({
  server,
  maxPayload: 2048,
  perMessageDeflate: false
});

/* ---------------- world ---------------- */
const WW = 1600, WH = 836, PW = 30, PH = 34, LX = 22, RX = 1570;

const PL = [
  [22,304,133],
  [191,384,99],
  [48,451,100],
  [334,451,210],
  [22,536,358],
  [323,626,227],
  [106,707,183],
  [572,354,209],
  [764,277,209],
  [606,451,365],
  [538,536,482],
  [837,586,203],
  [956,354,332],
  [1154,284,201],
  [1455,399,73],
  [1161,512,273],
  [1148,622,195],
  [1046,712,446],
  [22,800,1548]
].map(a => ({
  x: a[0],
  y: a[1],
  w: a[2],
  h: a[1] == 800 ? 36 : 14
}));

const RAMP = [];

const CRATE = [
  { x: 1383, y: 487, w: 26, h: 25 },
  { x: 1409, y: 487, w: 26, h: 25 },
  { x: 1409, y: 461, w: 26, h: 26 }
];

[
  [555, 630, 20, 6.1],
  [1357, 287, 6, 5.9]
].forEach(r => {
  for (let i = 0; i < r[2]; i++) {
    RAMP.push({
      x: r[0] + i * 10,
      y: r[1] + r[3] * (i + .5),
      w: 10,
      h: 14
    });
  }
});

const SOL = PL.concat(RAMP, CRATE);

/* ---- MAP FEATURES ---- */
/* Only two simple vertical jump pads + one temporary portal. */

const PADS = [
  { x: 1500, y: 800, w: 44, vy: 1050, vx: 0 },
  { x: 450, y: 451, w: 44, vy: 1050, vx: 0 }
];

const PAD_BST = .9;

const TP_W = 38;
const TP_H = 64;
const TP_LIFE = 4.5;

const TP_GAP_MIN = 7;
const TP_GAP_MAX = 11;

const TP_FIRST_MIN = 8;
const TP_FIRST_MAX = 14;

/* ---------------- physics ---------------- */

function step(p, inp, dt) {
  if (p.bst > 0) p.bst -= dt;

  let bv = 0;
  p.bv = bv;

  const m = p.it ? 1.07 : 1;

  const MAX =
    340 *
    m *
    (p.slow ? SLOW_K : 1) *
    (p.hb ? HELD_K : 1) *
    (p.gt ? CARRY_K : 1) *
    (p.bst > 0 ? BST_K : 1);

  const ax = (inp.r ? 1 : 0) - (inp.l ? 1 : 0);

  const ds = inp.s && !p.ps;
  p.ps = !!inp.s;

  if (p.dcd > 0) p.dcd -= dt;

  if (ds && p.dcd <= .001 && p.dash <= 0) {
    p.dash = DASH_T;
    p.dcd = DASH_CD;
    p.dd = ax || p.face;
    p.face = p.dd;
  }

  if (p.dash > 0) {
    p.dash -= dt;
    p.vx = p.dd * DASH_V;

    if (p.dash <= 0) {
      p.dash = 0;
      p.vx = p.dd * MAX;
    }
  } else if (ax) {
    const turn = Math.sign(p.vx) == -ax ? 1.8 : 1;

    p.vx += ax * (p.g ? 3000 : 2000) * turn * dt;
    p.vx = Math.max(-MAX, Math.min(MAX, p.vx));
    p.face = ax;
  } else {
    const f = (p.g ? 2800 : 500) * dt;
    p.vx =
      Math.abs(p.vx) <= f
        ? 0
        : p.vx - Math.sign(p.vx) * f;
  }

  const jp = inp.j && !p.pj;
  p.pj = !!inp.j;

  if (jp) p.buf = .13;
  else p.buf -= dt;

  p.coy = p.g ? .1 : p.coy - dt;

  if (p.buf > 0 && p.coy > 0) {
    p.vy = -840 * ((p.slow || p.hb) ? JUMP_K : 1);
    p.buf = p.coy = 0;
    p.g = 0;
    p.cut = 0;

    if (p.dash > 0) {
      p.dash = 0;
      p.vx = Math.max(-MAX, Math.min(MAX, p.vx));
    }
  }

  if (!inp.j && p.vy < -260 && !p.cut) {
    p.vy *= .45;
    p.cut = 1;
  }

  if (inp.d && p.g) p.drop = .22;
  p.drop -= dt;

  const gz = 1;

  if (p.dash > 0 && !p.g) {
    p.vy = 0;
  } else {
    p.vy = Math.min(
      p.vy + (p.vy > 0 ? 3400 : 2300) * dt * gz,
      gz < 1 ? 690 : 1150
    );
  }

  const ov = q =>
    p.x < q.x + q.w &&
    p.x + PW > q.x &&
    p.y < q.y + q.h &&
    p.y + PH > q.y;

  const was = p.g;

  p.x += (p.vx + bv) * dt;

  if (p.x < LX) {
    p.x = LX;
    p.vx = 0;
  }

  if (p.x > RX - PW) {
    p.x = RX - PW;
    p.vx = 0;
  }

  for (const q of SOL) {
    if (ov(q)) {
      if (was && p.y + PH - q.y <= 9) {
        p.y = q.y - PH;
      } else {
        p.x =
          p.vx > 0
            ? q.x - PW
            : p.vx < 0
              ? q.x + q.w
              : (p.x + PW / 2 < q.x + q.w / 2
                ? q.x - PW
                : q.x + q.w);

        p.vx = 0;
      }
    }
  }

  p.g = 0;
  p.y += p.vy * dt;

  for (const q of SOL) {
    if (ov(q)) {
      if (p.vy >= 0) {
        p.y = q.y - PH;
        p.vy = 0;
        p.g = 1;
      } else {
        const l = p.x + PW - q.x;
        const r = q.x + q.w - p.x;

        if (Math.min(l, r) < 10) {
          p.x += l < r ? -l : r;
        } else {
          p.y = q.y + q.h;
          p.vy = 0;
        }
      }
    }
  }

  if (p.g) {
    for (const q of PADS) {
      if (
        Math.abs(p.y + PH - q.y) < 3 &&
        p.x + PW > q.x + 4 &&
        p.x < q.x + q.w - 4
      ) {
        p.vy = -q.vy;
        p.g = 0;
        p.coy = 0;
        p.buf = 0;
        p.cut = 1;
        p.dash = 0;
        break;
      }
    }
  }
}

const hit = (a, b, pad) =>
  a.x < b.x + PW - pad &&
  a.x + PW > b.x + pad &&
  a.y < b.y + PH - pad &&
  a.y + PH > b.y;

/* ---------------- helpers ---------------- */

const rnd = n => Math.random() * n | 0;
const r4 = v => Math.round(v * 1e4) / 1e4;
const r1 = v => Math.round(v * 10) / 10;
const ri = v => Math.round(v);
const hex = n => crypto.randomBytes(n).toString('hex');
const now = () => performance.now();

function cleanName(v) {
  const s =
    typeof v === 'string'
      ? v.replace(/[\u0000-\u001f\u007f<>]/g, '').trim().slice(0, 12)
      : '';

  return s || 'Player';
}

function send(ws, s, droppable) {
  if (!ws || ws.readyState !== 1) return;

  if (ws.bufferedAmount > 1048576) {
    ws.terminate();
    return;
  }

  if (droppable && ws.bufferedAmount > 4096) return;

  ws.send(s);
}

const sendP = (p, s, drop) => {
  if (p.ws) send(p.ws, s, drop);
};

const bcast = (r, s, drop) => {
  for (const p of r.players.values()) {
    sendP(p, s, drop);
  }
};

/* ---------------- rooms ---------------- */

function mkRoom(key, pub) {
  const r = {
    key,
    pub: !!pub,
    players: new Map(),
    st: 'lobby',
    hostId: null,

    ord: [],
    rn: 0,
    gm: 0,
    practice: false,
    first: null,

    loser: null,
    ln: null,
    win: null,
    wn: null,

    lobbyGo: 0,
    cdEnd: 0,
    deadline: 0,
    tagFrom: 0,
    betweenEnd: 0,
    lk: null,

    tp: null,
    tpNext: 0,

    dec: [],
    pj: [],
    sm: [],
    tr: [],
    fxn: 0
  };

  return r;
}

const conn = r => {
  let n = 0;

  for (const p of r.players.values()) {
    if (p.ws) n++;
  }

  return n;
};

function newPlayer(nm, ci) {
  return {
    id: hex(4),
    tk: hex(12),
    ws: null,
    nm,
    ci,

    q: [],
    lastIn: 0,
    lastSeq: 0,
    lastCmd: 0,
    dc: 0,
    gr: 0,
    credit: 0,

    alive: false,
    it: 0,
    rs: 0,

    x: 0,
    y: 0,
    vx: 0,
    vy: 0,
    g: 0,
    coy: 0,
    buf: 0,
    pj: false,
    cut: 0,
    drop: 0,
    face: 1,

    ps: false,
    dash: 0,
    dd: 1,
    dcd: 0,
    slow: 0,
    ab: 'fake',
    acd: 0,
    pa: 0,
    bst: 0,
    pcd: 0,
    bv: 0,

    gt: '',
    hb: '',
    gs: 0,
    gl: 0,
    gcd: 0,
    gimm: 0,
    pg: false,
    ge: 0,
    gin: 0
  };
}

function bcastRoom(r) {
  const t = now();

  bcast(
    r,
    JSON.stringify({
      t: 'room',
      code: r.pub ? '' : r.key,
      pub: r.pub ? 1 : 0,
      st: r.st,
      host: r.hostId,
      rn: r.rn,
      gm: r.gm,
      practice: r.practice ? 1 : 0,
      first: r.first,
      loser: r.loser,
      ln: r.ln,
      win: r.win,
      wn: r.wn,
      lc: r.lobbyGo
        ? Math.max(0, (r.lobbyGo - t) / 1000)
        : 0,
      pl: [...r.players.values()]
        .filter(p => p.ws || r.st === 'play' || r.st === 'between')
        .map(p => ({
          id: p.id,
          nm: p.nm,
          ci: p.ci,
          al: p.alive ? 1 : 0
        }))
    })
  );
}

function updateLobbyGo(r, t) {
  if (!r.pub || r.st !== 'lobby') return;

  if (conn(r) >= PUB_SIZE) {
    if (!r.lobbyGo) r.lobbyGo = t + LOBBY_GO_MS;
  } else {
    r.lobbyGo = 0;
  }
}

function spawn(p, k, t) {
  p.x = 690 + k * 45;
  p.y = 502;

  p.vx = p.vy = 0;
  p.g = 0;
  p.coy = p.buf = p.cut = p.drop = 0;
  p.pj = false;
  p.face = 1;

  p.rs++;
  p.q.length = 0;
  p.lastCmd = t;

  p.ps = false;
  p.dash = 0;
  p.dd = 1;
  p.dcd = 0;
  p.slow = 0;
  p.acd = 0;
  p.pa = 0;
  p.bst = p.pcd = p.bv = 0;

  resetGrab(p);
}

function aliveIds(r) {
  return r.ord.filter(id => {
    const p = r.players.get(id);
    return p && p.alive;
  });
}

function startRound(r, ids, t) {
  r.rn++;
  r.st = 'play';
  r.loser = r.ln = null;
  r.lk = null;
  r.ord = ids.slice();

  clearFx(r);

  r.tpNext = t + tpDelay(true) * 1000;

  const first = ids[rnd(ids.length)];
  r.first = first;

  ids.forEach((id, k) => {
    const p = r.players.get(id);
    if (!p) return;

    spawn(p, k, t);
    p.alive = true;
    p.it = id === first ? 1 : 0;
  });

  for (const p of r.players.values()) {
    if (!ids.includes(p.id)) {
      p.alive = false;
      p.it = 0;
    }
  }

  r.cdEnd = t + CD_MS;
  r.deadline = r.cdEnd + ROUND_S * 1000;
  r.tagFrom = r.cdEnd + TAG_GRACE_MS;

  bcastRoom(r);
}

function startMatch(r, t) {
  const ids = [...r.players.values()]
    .filter(p => p.ws)
    .map(p => p.id)
    .slice(0, MAX_ROOM);

  if (!ids.length) return;

  r.gm = 1 + rnd(999999999);
  r.rn = 0;
  r.practice = ids.length === 1;
  r.win = r.wn = null;
  r.lobbyGo = 0;

  startRound(r, ids, t);
}

function finish(r, id) {
  const p = id && r.players.get(id);

  r.st = 'over';
  r.win = id || null;
  r.wn = p ? p.nm : null;
  r.lobbyGo = 0;

  clearFx(r);

  for (const q of r.players.values()) {
    q.it = 0;
  }

  bcastRoom(r);
}

function toLobby(r) {
  r.st = 'lobby';

  clearFx(r);

  r.ord = [];
  r.rn = 0;
  r.gm = 0;

  r.first =
    r.loser =
    r.win =
    r.ln =
    r.wn =
    null;

  r.lk = null;
  r.practice = false;

  for (const p of r.players.values()) {
    p.alive = false;
    p.it = 0;
    p.q.length = 0;
  }

  updateLobbyGo(r, now());
  bcastRoom(r);
}

function expire(r, t, holder) {
  r.loser = holder.id;
  r.ln = holder.nm;

  holder.alive = false;
  holder.it = 0;

  r.st = 'between';
  r.betweenEnd = t + BETWEEN_MS;

  clearFx(r);

  bcastRoom(r);
}

function removePlayer(r, p, t) {
  if (r.players.get(p.id) !== p) return;

  r.players.delete(p.id);

  if (!r.players.size) {
    rooms.delete(r.key);
    return;
  }

  if (r.hostId === p.id) {
    const nx =
      [...r.players.values()].find(q => q.ws) ||
      r.players.values().next().value;

    r.hostId =
      r.pub
        ? null
        : (nx ? nx.id : null);
  }

  if (r.st === 'lobby') {
    updateLobbyGo(r, t);
  } else if (r.st === 'play' && p.alive) {
    const al = aliveIds(r);

    if (!r.practice && al.length < 2) {
      finish(r, al[0]);
      return;
    }

    if (p.it && al.length) {
      const nh = r.players.get(al[rnd(al.length)]);

      if (nh) {
        nh.it = 1;
        r.lk = null;
      }
    }
  }

  bcastRoom(r);
}

function kick(r, p, why) {
  const w = p.ws;

  p.ws = null;

  removePlayer(r, p, now());

  if (w) {
    send(w, JSON.stringify({ t: 'kick', e: why }));

    try {
      w.close();
    } catch {}
  }
}

function destroyRoom(r) {
  rooms.delete(r.key);

  for (const p of r.players.values()) {
    if (p.ws) {
      const w = p.ws;
      p.ws = null;

      send(w, '{"t":"kick","e":"error"}');

      try {
        w.close();
      } catch {}
    }
  }

  r.players.clear();
}

/* ---------------- abilities ---------------- */

function clearFx(r) {
  r.dec.length = 0;
  r.pj.length = 0;
  r.sm.length = 0;
  r.tr.length = 0;

  r.tp = null;
  r.tpNext = 0;

  for (const p of r.players.values()) {
    resetGrab(p);
  }
}

function inTrap(r, p) {
  if (!r.tr.length || !p.g) return 0;

  for (const t of r.tr) {
    if (
      t.o === p.id &&
      TRAP_T - t.life < TRAP_IMM
    ) continue;

    if (
      p.x + PW > t.x - TRAP_W / 2 &&
      p.x < t.x + TRAP_W / 2 &&
      Math.abs(p.y + PH - t.y) < 36
    ) {
      return 1;
    }
  }

  return 0;
}

function useAbility(r, p) {
  if (r.st !== 'play' || p.acd > 0) return;

  const k = p.ab;

  if (k === 'fake') {
    r.dec.push({
      id: 'd' + (++r.fxn),
      o: p.id,
      life: FAKE_T,
      x: p.x,
      y: p.y,
      vx: p.vx,
      vy: p.vy,
      g: p.g,
      coy: 0,
      buf: 0,
      pj: false,
      cut: 0,
      drop: 0,
      face: p.face,
      it: p.it,
      dir: p.face,
      stuck: 0,
      ps: false,
      dash: 0,
      dd: 1,
      dcd: 0,
      slow: 0,
      bst: 0,
      pcd: 0,
      bv: 0
    });
  } else if (k === 'smoke') {
    r.pj.push({
      x: p.x + PW / 2,
      y: p.y + 8,
      vx: p.face * 520 + p.vx * .4,
      vy: -420,
      t: 0
    });
  } else if (k === 'trap') {
    if (!p.g) return;

    r.tr.push({
      id: ++r.fxn,
      x: Math.round(p.x + PW / 2),
      y: Math.round(p.y + PH),
      o: p.id,
      life: TRAP_T
    });
  } else {
    return;
  }

  p.acd = AB_CD;

  bcast(
    r,
    JSON.stringify({
      t: 'abu',
      o: p.id,
      k
    })
  );
}

function tickFx(r) {
  for (let i = r.dec.length - 1; i >= 0; i--) {
    const d = r.dec[i];
    const o = r.players.get(d.o);

    d.life -= DT;
    d.it = o && o.it ? 1 : 0;

    step(
      d,
      {
        l: d.dir < 0 ? 1 : 0,
        r: d.dir > 0 ? 1 : 0,
        j: 0,
        d: 0,
        s: 0
      },
      DT
    );

    if (Math.abs(d.vx) < 25) {
      if (++d.stuck > 10) {
        d.dir = -d.dir;
        d.stuck = 0;
      }
    } else {
      d.stuck = 0;
    }

    if (d.life <= 0 || d.y > WH + 100) {
      r.dec.splice(i, 1);
    }
  }

  for (let i = r.pj.length - 1; i >= 0; i--) {
    const j = r.pj[i];

    j.t += DT;

    let boom = j.t > 1.4;
    let hitSolid = false;

    for (let s = 0; s < 4 && !boom; s++) {
      const ox = j.x;
      const oy = j.y;
      const h = DT / 4;

      j.vy = Math.min(1000, j.vy + 1500 * h);
      j.x += j.vx * h;
      j.y += j.vy * h;

      if (j.x < LX || j.x > RX) {
        j.x = ox;
        j.vx = -j.vx * .4;
      }

      for (const q of SOL) {
        if (
          j.x > q.x &&
          j.x < q.x + q.w &&
          j.y > q.y &&
          j.y < q.y + q.h
        ) {
          j.x = ox;
          j.y = oy;
          boom = true;
          hitSolid = j.vy > 0;
          break;
        }
      }

      if (j.y > WH + 40) boom = true;
    }

    if (boom) {
      r.pj.splice(i, 1);

      r.sm.push({
        id: ++r.fxn,
        x: j.x,
        y: Math.min(j.y, WH - 60) - (hitSolid ? 38 : 0),
        life: SMOKE_T
      });
    }
  }

  for (let i = r.sm.length - 1; i >= 0; i--) {
    if ((r.sm[i].life -= DT) <= 0) {
      r.sm.splice(i, 1);
    }
  }

  for (let i = r.tr.length - 1; i >= 0; i--) {
    if ((r.tr[i].life -= DT) <= 0) {
      r.tr.splice(i, 1);
    }
  }
}

/* ---------------- grab ---------------- */

function resetGrab(p) {
  p.gt = '';
  p.hb = '';
  p.gs = 0;
  p.gl = 0;
  p.gcd = 0;
  p.gimm = 0;
  p.pg = false;
  p.ge = 0;
  p.gin = 0;
}

function ungrab(r, p, cd) {
  const q = p.gt && r.players.get(p.gt);

  if (q && q.hb === p.id) {
    q.hb = '';
    q.gimm = GRAB_IMM;
  }

  p.gt = '';
  p.gs = 0;
  p.gl = 0;
  p.gcd = cd;
}

const inSolid = p => {
  for (const s of SOL) {
    if (
      p.x < s.x + s.w &&
      p.x + PW > s.x &&
      p.y < s.y + s.h &&
      p.y + PH > s.y
    ) {
      return true;
    }
  }

  return false;
};

function grabTarget(r, p) {
  let best = null;
  let bd = 1e9;

  for (const q of r.players.values()) {
    if (q === p || !q.alive || q.hb || q.gimm > 0) continue;

    if (!hit(p, q, -GRAB_REACH)) continue;

    const d =
      Math.abs(p.x - q.x) +
      Math.abs(p.y - q.y);

    if (d < bd) {
      bd = d;
      best = q;
    }
  }

  return best;
}

function dragBy(q, mx, my) {
  const ox = q.x;
  const oy = q.y;

  q.x = Math.max(
    LX,
    Math.min(RX - PW, ox + mx)
  );

  q.y = oy + my;

  if (!inSolid(q)) return;

  q.y = oy;

  if (!inSolid(q)) return;

  q.x = ox;
  q.y = oy + my;

  if (!inSolid(q)) return;

  q.x = ox;
  q.y = oy;
}

function grabTick(r) {
  for (const p of r.players.values()) {
    if (p.gcd > 0) p.gcd -= DT;
    if (p.gimm > 0) p.gimm -= DT;

    if (p.hb) {
      const h = r.players.get(p.hb);

      if (!h || !h.alive || h.gt !== p.id) {
        p.hb = '';
      } else if (p.dash > 0) {
        ungrab(r, h, GRAB_CD);
      }
    }

    if (p.gt) {
      const q = r.players.get(p.gt);

      if (
        !p.alive ||
        !q ||
        !q.alive ||
        q.hb !== p.id
      ) {
        p.gt = '';
        p.gs = 0;
        p.gl = 0;
        p.gcd = GRAB_CD;
      }
    }

    if (!p.alive) continue;

    if (
      p.gs === 0 &&
      p.ge &&
      p.gcd <= 0 &&
      !p.hb
    ) {
      p.gs = 1;
      p.gl = GRAB_REACH_T;
    }

    p.ge = 0;

    if (p.gs === 1) {
      const q = p.hb ? null : grabTarget(r, p);

      if (q) {
        p.gs = 2;
        p.gt = q.id;
        q.hb = p.id;
        p.gl = GRAB_MAX;

        bcast(
          r,
          JSON.stringify({
            t: 'grab',
            a: p.id,
            b: q.id
          })
        );
      } else {
        p.gl -= DT;

        if (!p.gin || p.gl <= 0 || p.hb) {
          p.gs = 0;
          p.gl = 0;
          p.gcd = GRAB_MISS_CD;
        }
      }
    } else if (p.gs === 2) {
      p.gl -= DT;

      if (
        p.gl <= 0 ||
        (!p.gin && GRAB_MAX - p.gl >= GRAB_MIN)
      ) {
        ungrab(r, p, GRAB_CD);
      }
    }
  }

  for (const p of r.players.values()) {
    if (p.gs !== 2) continue;

    const q = r.players.get(p.gt);
    if (!q) continue;

    const dx = q.x - p.x;
    const dy = q.y - p.y;
    const d = Math.hypot(dx, dy);

    if (d > GRAB_BREAK) {
      ungrab(r, p, GRAB_CD);
      continue;
    }

    if (d <= GRAB_ROPE) continue;

    const k = (d - GRAB_ROPE) / d;

    dragBy(
      q,
      -dx * k,
      -dy * k
    );

    const ux = dx / d;
    const uy = dy / d;
    const vr = q.vx * ux + q.vy * uy;

    if (vr > 0) {
      q.vx -= vr * ux;
      q.vy -= vr * uy;
    }
  }
}

/* ---------------- temporary teleport portal ---------------- */

function tpDelay(first) {
  const lo = first
    ? TP_FIRST_MIN
    : TP_GAP_MIN;

  const hi = first
    ? TP_FIRST_MAX
    : TP_GAP_MAX;

  return lo + Math.random() * (hi - lo);
}

function randomPortalSpot() {
  const candidates = SOL.filter(
    q => q.w >= TP_W + 20 && q.y < WH
  );

  const q = candidates[rnd(candidates.length)];

  const x =
    q.x +
    10 +
    Math.random() *
    Math.max(1, q.w - TP_W - 20);

  return {
    x,
    y: q.y - TP_H,
    w: TP_W,
    h: TP_H
  };
}

function startPortal(r, t) {
  if (r.tp || r.st !== 'play') return;

  const s = randomPortalSpot();

  r.tp = {
    x: s.x,
    y: s.y,
    w: s.w,
    h: s.h,
    life: TP_LIFE
  };
}

function touchPortal(r, p, t) {
  const q = r.tp;

  if (!q || !p.alive) return false;

  if (
    p.x + PW <= q.x + 4 ||
    p.x >= q.x + q.w - 4 ||
    p.y + PH <= q.y + 4 ||
    p.y >= q.y + q.h
  ) {
    return false;
  }

  const candidates = SOL.filter(
    b =>
      b.w >= PW + 20 &&
      b.y < WH &&
      Math.abs(b.y - (q.y + TP_H)) > 40
  );

  const d =
    candidates[rnd(candidates.length)];

  p.x =
    d.x +
    10 +
    Math.random() *
    Math.max(1, d.w - PW - 20);

  p.y = d.y - PH;

  p.vx = 0;
  p.vy = 0;
  p.g = 1;
  p.coy = .1;
  p.buf = 0;
  p.cut = 0;
  p.pcd = 0;

  r.tp = null;
  r.tpNext =
    t +
    tpDelay(false) * 1000;

  return true;
}

function tickPortal(r, t) {
  if (r.st !== 'play') return;

  if (r.tp) {
    r.tp.life -= DT;

    if (r.tp.life <= 0) {
      r.tp = null;
      r.tpNext =
        t +
        tpDelay(false) * 1000;
    }
  } else if (
    r.tpNext &&
    t >= r.tpNext
  ) {
    startPortal(r, t);
  }

  if (!r.tp) return;

  for (const p of r.players.values()) {
    if (touchPortal(r, p, t)) break;
  }
}

/* ---------------- simulation ---------------- */

function consume(p, t) {
  const c = p.q.shift();

  if (c) {
    p.lastSeq = c.s;
    p.lastCmd = t;
    return c.b;
  }

  if (t - p.lastCmd < STALL_MS) {
    return -1;
  }

  return 0;
}

function advance(r, p, b) {
  step(
    p,
    {
      l: b & 1,
      r: b & 2,
      j: b & 4,
      d: b & 8,
      s: b & 16
    },
    DT
  );

  const ab = (b & 32) ? 1 : 0;

  if (ab && !p.pa) {
    useAbility(r, p);
  }

  p.pa = ab;

  const gb = (b & 64) ? 1 : 0;

  if (gb && !p.pg) {
    p.ge = 1;
  }

  p.pg = gb;
  p.gin = gb;

  if (
    p.y > WH + 200 ||
    !(
      p.x + p.y + p.vx + p.vy < 1e9 &&
      p.x + p.y + p.vx + p.vy > -1e9
    )
  ) {
    p.x = 300 + Math.random() * 600;
    p.y = -60;
    p.vx = p.vy = 0;
    p.dash = 0;
    p.bst = p.pcd = p.bv = 0;
    p.rs++;
  }
}

function simRoom(r, t) {
  const cd =
    r.st === 'play' &&
    t < r.cdEnd;

  for (const p of r.players.values()) {
    if (!p.alive) continue;

    if (p.acd > 0) {
      p.acd -= DT;
    }

    p.slow = inTrap(r, p);

    let b = consume(p, t);

    if (b === -1) {
      p.credit =
        Math.min(8, p.credit + 1);
      continue;
    }

    advance(r, p, cd ? 0 : b);

    while (
      p.credit > 0 &&
      p.q.length > 1
    ) {
      p.credit--;

      {
        const c2 = p.q.shift();

        p.lastSeq = c2.s;

        advance(
          r,
          p,
          cd ? 0 : c2.b
        );
      }
    }
  }

  if (r.st === 'between') {
    if (t >= r.betweenEnd) {
      const al = aliveIds(r);

      if (al.length >= 2) {
        startRound(r, al, t);
      } else {
        finish(r, al[0]);
      }
    }

    return;
  }

  if (r.st !== 'play' || cd) return;

  tickFx(r);
  grabTick(r);
  tickPortal(r, t);

  let holder = null;

  for (const p of r.players.values()) {
    if (p.alive && p.it) {
      holder = p;
      break;
    }
  }

  if (!holder) {
    const al = aliveIds(r);

    if (al.length) {
      holder =
        r.players.get(
          al[rnd(al.length)]
        );

      holder.it = 1;
    }
  }

  if (!holder) return;

  if (r.lk) {
    const a = r.players.get(r.lk.from);
    const b = r.players.get(r.lk.to);

    if (
      !a ||
      !b ||
      t > r.lk.until ||
      !hit(a, b, -8)
    ) {
      r.lk = null;
    }
  }

  if (t >= r.tagFrom) {
    for (const q of r.players.values()) {
      if (!q.alive || q.it || q === holder) continue;

      if (!hit(holder, q, 3)) continue;

      if (
        r.lk &&
        r.lk.from === q.id &&
        r.lk.to === holder.id
      ) {
        continue;
      }

      holder.it = 0;
      q.it = 1;

      if (holder.gt === q.id) {
        ungrab(r, holder, GRAB_CD);
      } else if (q.gt === holder.id) {
        ungrab(r, q, GRAB_CD);
      }

      r.lk = {
        from: holder.id,
        to: q.id,
        until: t + LOCK_MS
      };

      bcast(
        r,
        JSON.stringify({
          t: 'tag',
          a: q.id,
          b: holder.id
        })
      );

      holder = q;
      break;
    }
  }

  for (
    let i = r.dec.length - 1;
    i >= 0;
    i--
  ) {
    if (
      r.dec[i].o !== holder.id &&
      hit(holder, r.dec[i], 3)
    ) {
      r.dec.splice(i, 1);
    }
  }

  if (
    !r.practice &&
    t >= r.deadline
  ) {
    expire(r, t, holder);
  }
}

/* ---------------- snapshots ---------------- */

function snapshot(r, t, tt) {
  let arr = '';

  for (const p of r.players.values()) {
    if (!p.alive) continue;

    arr +=
      (arr ? ',' : '') +
      '["' +
      p.id +
      '",' +
      r1(p.x) +
      ',' +
      r1(p.y) +
      ',' +
      ri(p.vx + p.bv) +
      ',' +
      ri(p.vy) +
      ',' +
      p.face +
      ',' +
      (p.g ? 1 : 0) +
      ',' +
      (p.it ? 1 : 0) +
      ']';
  }

  const tl =
    r.practice
      ? 'null'
      : r.st === 'play'
        ? Math.min(
            ROUND_S,
            Math.max(
              0,
              (r.deadline - t) / 1000
            )
          ).toFixed(2)
        : '0';

  let fx = '';

  if (r.dec.length) {
    fx +=
      ',"d":[' +
      r.dec
        .map(
          d =>
            '["' +
            d.id +
            '",' +
            r1(d.x) +
            ',' +
            r1(d.y) +
            ',' +
            ri(d.vx + d.bv) +
            ',' +
            ri(d.vy) +
            ',' +
            d.face +
            ',' +
            (d.g ? 1 : 0) +
            ',0,"' +
            d.o +
            '"]'
        )
        .join(',') +
      ']';
  }

  if (r.pj.length) {
    fx +=
      ',"j":[' +
      r.pj
        .map(
          j =>
            '[' +
            ri(j.x) +
            ',' +
            ri(j.y) +
            ']'
        )
        .join(',') +
      ']';
  }

  if (r.sm.length) {
    fx +=
      ',"s":[' +
      r.sm
        .map(
          s =>
            '[' +
            s.id +
            ',' +
            ri(s.x) +
            ',' +
            ri(s.y) +
            ',' +
            r1(s.life) +
            ']'
        )
        .join(',') +
      ']';
  }

  if (r.tr.length) {
    fx +=
      ',"tr":[' +
      r.tr
        .map(
          x =>
            '[' +
            x.id +
            ',' +
            x.x +
            ',' +
            x.y +
            ',' +
            r1(x.life) +
            ',"' +
            x.o +
            '"]'
        )
        .join(',') +
      ']';
  }

  if (r.tp) {
    fx +=
      ',"tp":{"x":' +
      r1(r.tp.x) +
      ',"y":' +
      r1(r.tp.y) +
      ',"w":' +
      r.tp.w +
      ',"h":' +
      r.tp.h +
      ',"life":' +
      r1(Math.max(0, r.tp.life)) +
      '}';
  }

  let gb = '';
  let gr = '';

  for (const p of r.players.values()) {
    if (!p.alive) continue;

    if (p.gs === 2 && p.gt) {
      gb +=
        (gb ? ',' : '') +
        '["' +
        p.id +
        '","' +
        p.gt +
        '"]';
    } else if (p.gs === 1) {
      gr +=
        (gr ? ',' : '') +
        '"' +
        p.id +
        '"';
    }
  }

  if (gb) fx += ',"gb":[' + gb + ']';
  if (gr) fx += ',"gr":[' + gr + ']';

  const head =
    '{"t":"s","ts":' +
    tt.toFixed(1) +
    ',"tl":' +
    tl +
    ',"cd":' +
    Math.max(
      0,
      (r.cdEnd - t) / 1000
    ).toFixed(2) +
    ',"p":[' +
    arr +
    ']' +
    fx;

  for (const p of r.players.values()) {
    if (!p.ws) continue;

    const a =
      p.alive
        ? ',"a":{"x":' +
          r4(p.x) +
          ',"y":' +
          r4(p.y) +
          ',"vx":' +
          r4(p.vx) +
          ',"vy":' +
          r4(p.vy) +
          ',"g":' +
          (p.g ? 1 : 0) +
          ',"coy":' +
          r4(p.coy) +
          ',"buf":' +
          r4(p.buf) +
          ',"pj":' +
          (p.pj ? 'true' : 'false') +
          ',"cut":' +
          (p.cut ? 1 : 0) +
          ',"drop":' +
          r4(p.drop) +
          ',"face":' +
          p.face +
          ',"it":' +
          (p.it ? 1 : 0) +
          ',"dash":' +
          r4(p.dash) +
          ',"dd":' +
          p.dd +
          ',"dcd":' +
          r4(p.dcd) +
          ',"ps":' +
          (p.ps ? 'true' : 'false') +
          ',"ac":' +
          r1(Math.max(0, p.acd)) +
          ',"gs":' +
          p.gs +
          ',"gt":' +
          (p.gt ? 1 : 0) +
          ',"hb":' +
          (p.hb ? 1 : 0) +
          ',"gc":' +
          r1(Math.max(0, p.gcd)) +
          ',"bs":' +
          r4(Math.max(0, p.bst)) +
          ',"pc":' +
          r4(Math.max(0, p.pcd)) +
          ',"q":' +
          p.lastSeq +
          ',"rs":' +
          p.rs +
          '}'
        : '';

    send(
      p.ws,
      head + a + '}',
      true
    );
  }
}

let tickN = 0;
let nextTick = now();

function tickAll(t, tt) {
  tickN++;

  const sweep = tickN % 15 === 0;

  for (const r of rooms.values()) {
    try {
      if (sweep) {
        for (const p of [...r.players.values()]) {
          if (
            p.dc &&
            t - p.dc > p.gr
          ) {
            removePlayer(r, p, t);
          }
        }
      }

      if (!rooms.has(r.key)) continue;

      if (r.st === 'lobby') {
        if (sweep && r.pub) {
          for (const p of [...r.players.values()]) {
            if (
              p.ws &&
              t - p.since > LOBBY_IDLE_MS
            ) {
              kick(r, p, 'idle');
            }
          }
        }

        if (
          r.lobbyGo &&
          t >= r.lobbyGo
        ) {
          r.lobbyGo = 0;

          if (conn(r) >= PUB_SIZE) {
            startMatch(r, t);
          } else {
            bcastRoom(r);
          }
        }
      } else if (
        r.st === 'play' ||
        r.st === 'between'
      ) {
        simRoom(r, t);

        if (
          rooms.has(r.key) &&
          (
            r.st === 'play' ||
            r.st === 'between'
          ) &&
          tickN % snapEvery === 0 &&
          conn(r)
        ) {
          snapshot(r, t, tt);
        }
      }
    } catch (e) {
      console.error(
        'room error, closing room ' +
        r.key +
        ':',
        e
      );

      destroyRoom(r);
    }
  }
}

let lagEma = 0;
let calmSince = 0;

setInterval(() => {
  const t = now();

  const lag =
    Math.max(0, t - nextTick);

  lagEma +=
    (lag - lagEma) * 0.05;

  if (!FIXED_SNAP) {
    if (
      snapEvery === 1 &&
      lagEma > 6
    ) {
      snapEvery = 2;
      calmSince = 0;
      console.log(
        'high load: snapshots at 30/s'
      );
    } else if (snapEvery === 2) {
      if (lagEma < 1.5) {
        if (!calmSince) {
          calmSince = t;
        } else if (
          t - calmSince > 20000
        ) {
          snapEvery = 1;
          calmSince = 0;

          console.log(
            'load normal: snapshots at 60/s'
          );
        }
      } else {
        calmSince = 0;
      }
    }
  }

  let n = 0;

  while (
    nextTick <= t &&
    n++ < 5
  ) {
    tickAll(t, nextTick);
    nextTick += TICK_MS;
  }

  if (nextTick < t - 100) {
    nextTick = t;
  }
}, 4);

/* ---------------- connections ---------------- */

const perIp = new Map();
const CODE_CHARS =
  'ABCDEFGHJKLMNPQRSTUVWXYZ23456789';

wss.on('connection', (ws, req) => {
  try {
    req.socket.setNoDelay(true);
  } catch {}

  if (
    wss.clients.size > MAX_CLIENTS
  ) {
    ws.close();
    return;
  }

  if (ALLOWED.length) {
    const o = String(
      req.headers.origin || ''
    );

    if (
      !ALLOWED.some(
        a =>
          o === a ||
          o.endsWith(
            '.' +
            a.replace(
              /^https?:\/\//,
              ''
            )
          )
      )
    ) {
      ws.close();
      return;
    }
  }

  const ip =
    String(
      req.headers['cf-connecting-ip'] ||
      req.headers['true-client-ip'] ||
      req.headers['x-forwarded-for'] ||
      req.socket.remoteAddress ||
      ''
    )
      .split(',')[0]
      .trim();

  const n =
    (perIp.get(ip) || 0) + 1;

  if (n > MAX_CONN_PER_IP) {
    ws.close();
    return;
  }

  perIp.set(ip, n);

  ws.lastSeen =
    ws.born =
    Date.now();

  ws.on('pong', () => {
    ws.lastSeen = Date.now();
  });

  let r = null;
  let p = null;
  let cnt = 0;
  let winStart = Date.now();

  const err = e => {
    send(
      ws,
      '{"t":"err","e":"' +
      e +
      '"}'
    );

    ws.close();
  };

  const attach = (rr, pp) => {
    r = rr;
    p = pp;

    pp.ws = ws;
    pp.dc = 0;
    ws.joined = 1;

    send(
      ws,
      JSON.stringify({
        t: 'hello',
        id: pp.id,
        tk: pp.tk,
        rk: rr.key,
        code: rr.pub ? '' : rr.key,
        pub: rr.pub ? 1 : 0,
        ab: pp.ab
      })
    );
  };

  const addPlayer = (rr, nm) => {
    if (
      rr.players.size >= MAX_ROOM &&
      rr.st === 'lobby'
    ) {
      for (const q of rr.players.values()) {
        if (!q.ws) {
          rr.players.delete(q.id);
          break;
        }
      }
    }

    if (rr.players.size >= MAX_ROOM) {
      return err('full');
    }

    if (
      rr.pub &&
      rr.st !== 'lobby'
    ) {
      return err('full');
    }

    if (!rooms.has(rr.key)) {
      rooms.set(rr.key, rr);
    }

    const used = new Set(
      [...rr.players.values()]
        .map(q => q.ci)
    );

    let ci = 0;

    while (used.has(ci)) ci++;

    const pp =
      newPlayer(nm, ci);

    pp.since = now();

    rr.players.set(
      pp.id,
      pp
    );

    if (
      !rr.pub &&
      !rr.hostId
    ) {
      rr.hostId = pp.id;
    }

    attach(rr, pp);
    updateLobbyGo(rr, now());
    bcastRoom(rr);
  };

  ws.on('message', (raw, isBinary) => {
    const t = Date.now();

    ws.lastSeen = t;

    if (
      t - winStart >= 1000
    ) {
      winStart = t;
      cnt = 0;
    }

    if (
      ++cnt > 200 ||
      isBinary
    ) {
      return;
    }

    let m;

    try {
      m = JSON.parse(raw);
    } catch {
      return;
    }

    if (
      !m ||
      typeof m !== 'object'
    ) {
      return;
    }

    /* ---- inputs ---- */

    if (m.t === 'in') {
      if (
        !p ||
        !p.alive ||
        !Array.isArray(m.c)
      ) {
        return;
      }

      const c = m.c;

      for (
        let i = 0;
        i < c.length && i < 8;
        i++
      ) {
        const e = c[i];

        if (!Array.isArray(e)) continue;

        const s = e[0];
        const b = e[1];

        if (
          !Number.isInteger(s) ||
          !Number.isInteger(b) ||
          b < 0 ||
          b > 127 ||
          s <= p.lastIn
        ) {
          continue;
        }

        p.lastIn = s;

        if (p.q.length < QCAP) {
          p.q.push({
            s,
            b
          });
        }
      }

      return;
    }

    if (m.t === 'hb') {
      send(ws, '{"t":"hb"}');
      return;
    }

    if (
      m.t === 'leave' &&
      r &&
      p
    ) {
      removePlayer(
        r,
        p,
        now()
      );

      p.ws = null;
      r = null;
      p = null;

      return;
    }

    /* ---- joining ---- */

    if (!r) {
      if (m.t === 'create') {
        if (
          rooms.size >= MAX_ROOMS
        ) {
          return err('busy');
        }

        let code;

        do {
          code = Array.from(
            { length: 4 },
            () =>
              CODE_CHARS[
                rnd(32)
              ]
          ).join('');
        } while (
          rooms.has(code)
        );

        return addPlayer(
          mkRoom(
            code,
            false
          ),
          cleanName(m.nm)
        );
      }

      if (m.t === 'join') {
        const code =
          typeof m.code === 'string'
            ? m.code.toUpperCase()
            : '';

        if (
          !/^[A-Z0-9]{3,6}$/.test(
            code
          )
        ) {
          return err('bad');
        }

        const rr =
          rooms.get(code);

        if (
          !rr ||
          rr.pub
        ) {
          return err('nf');
        }

        if (
          rr.players.size >= MAX_ROOM
        ) {
          return err('full');
        }

        if (
          rr.practice &&
          rr.st !== 'lobby'
        ) {
          toLobby(rr);
        }

        return addPlayer(
          rr,
          cleanName(m.nm)
        );
      }

      if (m.t === 'quick') {
        let best = null;

        for (const rr of rooms.values()) {
          if (
            !rr.pub ||
            rr.st !== 'lobby' ||
            conn(rr) >= MAX_ROOM
          ) {
            continue;
          }

          if (
            !best ||
            conn(rr) > conn(best)
          ) {
            best = rr;
          }
        }

        if (
          !best &&
          rooms.size >= MAX_ROOMS
        ) {
          return err('busy');
        }

        if (!best) {
          let k;

          do {
            k = 'p-' + hex(3);
          } while (
            rooms.has(k)
          );

          best =
            mkRoom(k, true);
        }

        return addPlayer(
          best,
          cleanName(m.nm)
        );
      }

      if (m.t === 'resume') {
        const rr =
          typeof m.rk === 'string' &&
          m.rk.length <= 16
            ? rooms.get(m.rk)
            : null;

        const pp =
          rr &&
          typeof m.id === 'string'
            ? rr.players.get(m.id)
            : null;

        if (
          !pp ||
          pp.tk !== m.tk
        ) {
          return err('gone');
        }

        if (
          pp.ws &&
          pp.ws !== ws
        ) {
          const old = pp.ws;
          pp.ws = null;

          try {
            old.terminate();
          } catch {}
        }

        attach(rr, pp);
        bcastRoom(rr);
      }

      return;
    }

    /* ---- ability choice ---- */

    if (m.t === 'ab') {
      if (
        typeof m.k === 'string' &&
        ABIL.has(m.k) &&
        (
          r.st === 'lobby' ||
          !p.alive
        )
      ) {
        p.ab = m.k;
      }

      return;
    }

    /* ---- room controls ---- */

    if (
      m.t === 'start' &&
      r.st === 'lobby' &&
      !r.pub &&
      r.hostId === p.id
    ) {
      return startMatch(
        r,
        now()
      );
    }

    if (
      m.t === 'lobby' &&
      r.st === 'over' &&
      !r.pub &&
      r.hostId === p.id
    ) {
      return toLobby(r);
    }
  });

  ws.on('close', () => {
    const left =
      (perIp.get(ip) || 1) - 1;

    if (left <= 0) {
      perIp.delete(ip);
    } else {
      perIp.set(ip, left);
    }

    if (
      r &&
      p &&
      p.ws === ws
    ) {
      p.ws = null;
      p.dc = now();

      p.gr =
        (
          r.st === 'play' ||
          r.st === 'between'
        )
          ? GRACE_MS
          : LOBBY_GRACE_MS;

      if (
        r.st === 'lobby'
      ) {
        updateLobbyGo(
          r,
          now()
        );
      }

      bcastRoom(r);
    }
  });

  ws.on('error', () => {});
});

/* ---------------- socket housekeeping ---------------- */

setInterval(() => {
  const t = Date.now();

  for (const ws of wss.clients) {
    if (
      t - ws.lastSeen > 15000 ||
      (
        !ws.joined &&
        t - ws.born > 120000
      )
    ) {
      ws.terminate();
      continue;
    }

    try {
      ws.ping();
    } catch {}

    send(
      ws,
      '{"t":"hb"}'
    );
  }
}, 5000);

/* ---------------- housekeeping ---------------- */

setInterval(() => {
  const t = now();

  for (const r of rooms.values()) {
    if (!r.players.size) {
      rooms.delete(r.key);
      continue;
    }

    if (conn(r)) {
      r.idle = 0;
      continue;
    }

    if (!r.idle) {
      r.idle = t;
    } else if (
      t - r.idle >
      GRACE_MS + 5000
    ) {
      rooms.delete(r.key);
    }
  }
}, 10000).unref();

/* ---------------- Render keepalive ---------------- */

if (
  process.env.RENDER_EXTERNAL_URL &&
  process.env.KEEPALIVE !== '0' &&
  typeof fetch === 'function'
) {
  setInterval(() => {
    fetch(
      process.env.RENDER_EXTERNAL_URL +
      '/healthz'
    ).catch(() => {});
  }, 10 * 60 * 1000).unref();
}

/* ---------------- lifecycle ---------------- */

server.listen(
  PORT,
  '0.0.0.0',
  () => {
    console.log(
      'Tag multiplayer server (authoritative) running on port ' +
      PORT
    );
  }
);

function shutdown() {
  console.log('Shutting down...');

  for (const ws of wss.clients) {
    try {
      ws.close(1001);
    } catch {}
  }

  server.close(
    () => process.exit(0)
  );

  setTimeout(
    () => process.exit(0),
    3000
  ).unref();
}

process.on(
  'SIGTERM',
  shutdown
);

process.on(
  'SIGINT',
  shutdown
);

process.on(
  'uncaughtException',
  e => console.error(
    'uncaught:',
    e
  )
);

process.on(
  'unhandledRejection',
  e => console.error(
    'unhandled:',
    e
  )
);