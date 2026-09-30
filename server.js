// Tag multiplayer server: static index.html + WebSocket room relay.
// Run: npm install && npm start
const http = require('http'), fs = require('fs'), path = require('path');
const { WebSocketServer } = require('ws');

const PORT = process.env.PORT || 3000;
const MAX_ROOM = 5;
const rooms = new Map();

const server = http.createServer((req, res) => {
  fs.readFile(path.join(__dirname, 'index.html'), (err, data) => {
    if (err) {
      res.writeHead(500);
      return res.end('index.html missing');
    }

    res.writeHead(200, {
      'Content-Type': 'text/html; charset=utf-8'
    });

    res.end(data);
  });
});

const wss = new WebSocketServer({
  server,
  maxPayload: 8192
});

wss.on('connection', (ws) => {
  const id = Math.random().toString(36).slice(2, 10);
  ws.lastSeen = Date.now();
  ws.on('pong', () => { ws.lastSeen = Date.now(); });

  let room = null;
  let count = 0;

  // Per-connection message rate limiter.
  const timer = setInterval(() => {
    count = 0;
  }, 1000);

  const leave = () => {
    if (!room) return;

    room.delete(id);

    if (!room.size) {
      rooms.delete(room.name);
    } else {
      const out = JSON.stringify({ t: 'l', id });
      for (const c of room.values()) if (c.ws.readyState === 1) c.ws.send(out);
    }

    room = null;
  };

  ws.on('message', (raw) => {
    // Protect the server from excessive messages.
    ws.lastSeen = Date.now();
    if (++count > 150) return;

    let m;

    try {
      m = JSON.parse(raw);
    } catch {
      return;
    }

    if (m && m.t === 'hb') { if (ws.readyState === 1) ws.send('{"t":"hb"}'); return; }

    // Join room.
    if (m.t === 'join' && !room) {
      if (
        typeof m.room !== 'string' ||
        !/^tag-[a-z0-9]{3,6}$/.test(m.room)
      ) {
        return ws.close();
      }

      let r = rooms.get(m.room);

      if (!r) {
        r = new Map();
        r.name = m.room;
        rooms.set(m.room, r);
      }

      if (r.size >= MAX_ROOM) {
        return ws.close();
      }

      const others = [...r].map(([oid, c]) => ({ id: oid, p: c.pres }));
      const mine = { ws, pres: {} };
      r.set(id, mine);
      room = r;
      ws.send(JSON.stringify({ t: 'hello', id }));
      ws.send(JSON.stringify({ t: 'full', peers: others.concat({ id, p: mine.pres }) }));
      for (const [oid, c] of r) if (oid !== id && c.ws.readyState === 1) c.ws.send(JSON.stringify({ t: 'j', id, p: mine.pres }));
      return;
    }

    // Receive player presence/state.
    if (
      m.t === 'pres' &&
      room &&
      m.p &&
      typeof m.p === 'object'
    ) {
      // Prevent oversized presence packets.
      if (JSON.stringify(m.p).length > 1500) return;

      const me = room.get(id);
      if (!me) return;

      // Only accept normal keys.
      const patch = {};
      for (const k of Object.keys(m.p)) {
        if (k !== '__proto__' && k.length < 16) { me.pres[k] = m.p[k]; patch[k] = m.p[k]; }
      }
      const out = JSON.stringify({ t: 'u', id, p: patch });
      for (const c of room.values()) if (c.ws.readyState === 1) c.ws.send(out);
    }
  });

  ws.on('close', () => {
    clearInterval(timer);
    leave();
  });

  ws.on('error', () => {});
});

// Drop dead connections (closed browser, lost signal, frozen tab) so ghost players disappear.
setInterval(() => {
  for (const ws of wss.clients) {
    if (Date.now() - ws.lastSeen > 12000) { ws.terminate(); continue; }
    try { ws.ping(); } catch {}
  }
}, 4000);

server.listen(PORT, () => {
  console.log(
    'Tag multiplayer server running on port ' + PORT
  );
});