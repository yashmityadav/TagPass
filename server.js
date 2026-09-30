// Tag multiplayer server: static index.html + WebSocket room relay.
// Run: npm install && npm start
const http = require('http'), fs = require('fs'), path = require('path');
const { WebSocketServer } = require('ws');
const PORT = process.env.PORT || 3000, MAX_ROOM = 5, rooms = new Map();

const server = http.createServer((req, res) => {
  fs.readFile(path.join(__dirname, 'index.html'), (err, data) => {
    if (err) { res.writeHead(500); return res.end('index.html missing'); }
    res.writeHead(200, { 'Content-Type': 'text/html; charset=utf-8' });
    res.end(data);
  });
});
const wss = new WebSocketServer({ server, maxPayload: 8192 });

wss.on('connection', (ws) => {
  const id = Math.random().toString(36).slice(2, 10);
  let room = null, count = 0;
  const timer = setInterval(() => (count = 0), 1000);
  const leave = () => {
    if (!room) return;
    room.delete(id);
    if (!room.size) rooms.delete(room.name); else room.dirty = true;
    room = null;
  };
  ws.on('message', (raw) => {
    if (++count > 100) return; // rate limit
    let m; try { m = JSON.parse(raw); } catch { return; }
    if (m.t === 'join' && !room) {
      if (typeof m.room !== 'string' || !/^tag-[a-z0-9]{3,6}$/.test(m.room)) return ws.close();
      let r = rooms.get(m.room);
      if (!r) { r = new Map(); r.name = m.room; rooms.set(m.room, r); }
      if (r.size >= MAX_ROOM) return ws.close();
      r.set(id, { ws, pres: {} }); room = r; r.dirty = true;
      ws.send(JSON.stringify({ t: 'hello', id }));
    } else if (m.t === 'pres' && room && m.p && typeof m.p === 'object') {
      if (JSON.stringify(m.p).length > 1500) return;
      const me = room.get(id);
      for (const k of Object.keys(m.p)) if (k !== '__proto__' && k.length < 16) me.pres[k] = m.p[k];
      room.dirty = true;
    }
  });
  ws.on('close', () => { clearInterval(timer); leave(); });
  ws.on('error', () => {});
});

// Broadcast room snapshots ~30 times a second when changes occur
setInterval(() => {
  for (const r of rooms.values()) {
    if (!r.dirty) continue; r.dirty = false;
    const msg = JSON.stringify({ t: 'peers', peers: [...r].map(([id, c]) => ({ id, p: c.pres })) });
    for (const c of r.values()) if (c.ws.readyState === 1) c.ws.send(msg);
  }
}, 33);

server.listen(PORT, () => console.log('Tag multiplayer server running on port ' + PORT));