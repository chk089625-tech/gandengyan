'use strict';
/* 干瞪眼联机测试版服务器：不依赖任何第三方包。
   网页用 POST 发动作，用 SSE（/api/events）收自己视角的牌桌状态；手牌只发给本人。 */
const http = require('http'), fs = require('fs'), path = require('path');
const L = require('./logic.js');

const PORT = process.env.PORT || 3000;
const STATIC = {
  '/': ['index.html', 'text/html; charset=utf-8'],
  '/index.html': ['index.html', 'text/html; charset=utf-8'],
  '/logic.js': ['logic.js', 'application/javascript; charset=utf-8'],
};
const BOT_NAMES = ['老张', '阿梅', '小六'];
const TURN_MS = 30000, OFFLINE_PLAY_MS = 5000, OFFLINE_LOBBY_MS = 120000, ROOM_IDLE_MS = 30 * 60000;
const MAX_MEMBERS = 8, MAX_ROOMS = 500;
const rooms = new Map();

class Oops extends Error {}
const validPid = p => typeof p === 'string' && /^[a-z0-9]{8,40}$/.test(p);
const cleanName = s => String(s || '').replace(/[\u0000-\u001f<>]/g, '').trim().slice(0, 12) || '无名牌友';
const online = (r, pid) => !!(r.conns.get(pid) && r.conns.get(pid).size);

function newRoom() {
  if (rooms.size >= MAX_ROOMS) throw new Oops('房间太多了，稍后再试');
  let code; do { code = String(Math.floor(1000 + Math.random() * 9000)); } while (rooms.has(code));
  const r = { code, v: 0, seq: 0, members: [], fill: true, scores: {}, conns: new Map(), offTimers: new Map(), timer: null, deadline: 0, touched: Date.now() };
  resetTable(r);
  rooms.set(code, r);
  return r;
}
function resetTable(r) {
  Object.assign(r, { phase: 'lobby', players: [], hands: [], played: [], deck: [], turn: 0, dealer: 0, last: null, mult: 1, show: [], trickEnd: false, over: null, msg: null, fresh: null });
}
function join(r, pid, name) {
  const m = r.members.find(m => m.pid === pid);
  if (m) { m.name = name; const p = r.players.find(p => p.pid === pid); if (p) p.name = name; return; }
  if (r.members.length >= MAX_MEMBERS) throw new Oops('这个房间人满了');
  r.members.push({ pid, name });
}
function leave(r, pid) {
  r.members = r.members.filter(m => m.pid !== pid);
  const i = r.players.findIndex(p => p.pid === pid);
  if (i >= 0) { const p = r.players[i]; p.pid = null; p.ai = true; p.name += '（已离开）'; }
  const set = r.conns.get(pid);
  if (set) { set.forEach(res => { try { res.end(); } catch (e) {} }); r.conns.delete(pid); }
  if (r.phase === 'play') sync(r); else { r.v++; broadcast(r); }
}

/* ---------- 牌局 ---------- */
function buildPlayers(r) {
  const ps = r.members.slice(0, 4).map(m => ({ key: m.pid, pid: m.pid, name: m.name, ai: false, auto: false }));
  if (r.fill) for (let k = 0; ps.length < 4; k++) ps.push({ key: 'bot' + k, pid: null, name: BOT_NAMES[k], ai: true, auto: false });
  return ps;
}
function deal(r, dealer) {
  const n = r.players.length, deck = L.shuffle(L.makeDeck()), hands = Array.from({ length: n }, () => []);
  for (let k = 0; k < 5; k++) hands.forEach(h => h.push(deck.pop()));
  hands[dealer].push(deck.pop());
  hands.forEach(L.sortHand);
  Object.assign(r, { phase: 'play', hands, played: Array(n).fill(false), deck, turn: dealer, dealer, last: null, mult: 1,
    show: Array(n).fill(null), trickEnd: false, over: null, fresh: null, msg: { k: 'deal', i: dealer, n: ++r.seq } });
  sync(r);
}
function minOpp(r, i) { return Math.min(...r.hands.filter((_, j) => j !== i).map(h => h.length)); }
function doPlay(r, i, cards, combo) {
  const ids = new Set(cards.map(c => c.id));
  r.hands[i] = r.hands[i].filter(c => !ids.has(c.id));
  r.played[i] = true;
  r.last = { by: i, cards, combo };
  r.show[i] = cards;
  if (combo.type === 'bomb') r.mult *= 2;
  if (r.fresh && r.fresh.i === i) r.fresh = null;
  r.msg = { k: 'play', i, combo, n: ++r.seq };
  if (!r.hands[i].length) return finish(r, i);
  advance(r);
}
function doPass(r, i) { r.show[i] = 'pass'; r.msg = { k: 'pass', i, n: ++r.seq }; advance(r); }
function advance(r) {
  r.turn = (r.turn + 1) % r.players.length;
  if (r.last && r.turn === r.last.by) r.trickEnd = true;
  sync(r);
}
function endTrick(r) {
  const i = r.turn;
  r.trickEnd = false; r.last = null; r.show = Array(r.players.length).fill(null);
  let c = null;
  if (r.deck.length) { c = r.deck.pop(); r.hands[i].push(c); L.sortHand(r.hands[i]); }
  r.fresh = c ? { i, id: c.id } : null;
  r.msg = { k: 'draw', i, c, n: ++r.seq };
  sync(r);
}
function finish(r, w) {
  const rows = r.hands.map((h, i) => i === w ? { gain: 0 } : { gain: -(h.length * r.mult * (r.played[i] ? 1 : 2)), shut: !r.played[i] });
  rows[w].gain = -rows.reduce((a, x) => a + x.gain, 0);
  rows.forEach((x, i) => { const k = r.players[i].key; r.scores[k] = (r.scores[k] || 0) + x.gain; });
  r.over = { winner: w, rows };
  r.phase = 'over';
  sync(r);
}
function aiTurn(r) {
  const i = r.turn;
  const pick = L.aiChoose(r.hands[i], r.last ? r.last.combo : null, minOpp(r, i));
  if (pick) doPlay(r, i, pick.cards, pick.combo); else doPass(r, i);
}
function schedule(r) {
  clearTimeout(r.timer); r.deadline = 0;
  if (r.phase !== 'play') return;
  const p = r.players[r.turn];
  if (r.trickEnd) r.timer = setTimeout(() => endTrick(r), 1100);
  else if (p.ai || p.auto) r.timer = setTimeout(() => aiTurn(r), 950);
  else {
    r.deadline = Date.now() + TURN_MS;
    r.timer = setTimeout(() => { p.auto = true; aiTurn(r); }, TURN_MS);
  }
}
function sync(r) { r.v++; r.touched = Date.now(); schedule(r); broadcast(r); }

/* ---------- 每个人看到的牌桌 ---------- */
function view(r, pid) {
  const you = r.players.findIndex(p => p.pid === pid);
  let msg = r.msg;
  if (msg && msg.k === 'draw' && msg.i !== you) msg = { k: 'draw', i: msg.i, c: msg.c ? true : null, n: msg.n };
  return {
    code: r.code, v: r.v, phase: r.phase, you, host: !!r.members[0] && r.members[0].pid === pid, fill: r.fill,
    members: r.members.map(m => ({ name: m.name, online: online(r, m.pid), you: m.pid === pid })),
    players: r.players.map((p, i) => ({ name: p.name, ai: p.ai, auto: !!p.auto, count: r.hands[i].length, score: r.scores[p.key] || 0 })),
    hand: you >= 0 ? r.hands[you] : [], deckN: r.deck.length, turn: r.turn, dealer: r.dealer, last: r.last, mult: r.mult,
    show: r.show, trickEnd: r.trickEnd, over: r.over ? { winner: r.over.winner, rows: r.over.rows, hands: r.hands } : null,
    msg, fresh: r.fresh && r.fresh.i === you ? r.fresh.id : null,
    left: r.deadline ? Math.max(0, Math.round((r.deadline - Date.now()) / 1000)) : 0,
  };
}
function broadcast(r) {
  r.conns.forEach((set, pid) => {
    if (!set.size) return;
    const data = 'data: ' + JSON.stringify(view(r, pid)) + '\n\n';
    set.forEach(res => { try { res.write(data); } catch (e) {} });
  });
}

/* ---------- 动作 ---------- */
function act(r, pid, b) {
  if (!r.members.some(m => m.pid === pid)) throw new Oops('你不在这个房间里，请重新加入');
  const host = r.members[0].pid === pid, you = r.players.findIndex(p => p.pid === pid);
  switch (b.type) {
    case 'fill':
      if (!host || r.phase !== 'lobby') throw new Oops('只有房主能改这个设置');
      r.fill = !!b.on; r.v++; broadcast(r); return;
    case 'start': {
      if (!host) throw new Oops('等房主开局');
      if (r.phase === 'play') throw new Oops('这一局还没打完');
      const winKey = r.over ? r.players[r.over.winner].key : null;
      const ps = buildPlayers(r);
      if (ps.length < 2) throw new Oops('至少要两个人，或者勾上电脑补位');
      r.players = ps;
      const w = ps.findIndex(p => p.key === winKey);
      return deal(r, w >= 0 ? w : Math.floor(Math.random() * ps.length));
    }
    case 'lobby':
      if (!host || r.phase !== 'over') throw new Oops('只有房主能在一局结束后回房间');
      resetTable(r); return sync(r);
    case 'play': {
      if (r.phase !== 'play' || you !== r.turn || r.trickEnd) throw new Oops('还没轮到你');
      const ids = new Set(Array.isArray(b.cards) ? b.cards.filter(Number.isInteger) : []);
      const cards = r.hands[you].filter(c => ids.has(c.id));
      if (!cards.length || cards.length !== ids.size) throw new Oops('选的牌不在你手里');
      const combo = L.resolve(cards, r.last ? r.last.combo : null, r.hands[you].length);
      if (!combo) throw new Oops('这手牌出不了');
      r.players[you].auto = false;
      return doPlay(r, you, cards, combo);
    }
    case 'pass':
      if (r.phase !== 'play' || you !== r.turn || r.trickEnd) throw new Oops('还没轮到你');
      if (!r.last) throw new Oops('你领出，不能不要');
      r.players[you].auto = false;
      return doPass(r, you);
    case 'unauto':
      if (you >= 0 && r.players[you].auto) {
        r.players[you].auto = false;
        if (r.phase === 'play' && r.turn === you && !r.trickEnd) schedule(r);
        r.v++; broadcast(r);
      }
      return;
    case 'leave': return leave(r, pid);
    default: throw new Oops('不认识的动作');
  }
}

/* ---------- 连接 ---------- */
function attach(r, pid, res) {
  clearTimeout(r.offTimers.get(pid)); r.offTimers.delete(pid);
  if (!r.conns.has(pid)) r.conns.set(pid, new Set());
  r.conns.get(pid).add(res);
  r.touched = Date.now();
  const i = r.players.findIndex(p => p.pid === pid);
  if (i >= 0 && r.players[i].auto) {
    r.players[i].auto = false;
    if (r.phase === 'play' && r.turn === i && !r.trickEnd) schedule(r);
  }
  r.v++; broadcast(r);
}
function detach(r, pid, res) {
  const set = r.conns.get(pid);
  if (!set) return;
  set.delete(res);
  if (set.size) return;
  r.v++; broadcast(r);
  clearTimeout(r.offTimers.get(pid));
  r.offTimers.set(pid, setTimeout(() => {
    r.offTimers.delete(pid);
    if (online(r, pid) || !rooms.has(r.code)) return;
    const i = r.players.findIndex(p => p.pid === pid);
    if (r.phase === 'play' && i >= 0) {
      r.players[i].auto = true;
      if (r.turn === i && !r.trickEnd) schedule(r);
      r.v++; broadcast(r);
    } else if (r.phase !== 'play') {
      r.members = r.members.filter(m => m.pid !== pid);
      r.v++; broadcast(r);
    }
  }, r.phase === 'play' ? OFFLINE_PLAY_MS : OFFLINE_LOBBY_MS));
}
setInterval(() => rooms.forEach(r => r.conns.forEach(set => set.forEach(res => { try { res.write(': ping\n\n'); } catch (e) {} }))), 20000).unref();
setInterval(() => {
  const now = Date.now();
  rooms.forEach(r => {
    const anyone = [...r.conns.values()].some(s => s.size);
    if (!anyone && now - r.touched > ROOM_IDLE_MS) { clearTimeout(r.timer); r.offTimers.forEach(clearTimeout); rooms.delete(r.code); }
  });
}, 5 * 60000).unref();

/* ---------- HTTP ---------- */
function send(res, code, obj) {
  res.writeHead(code, { 'Content-Type': 'application/json; charset=utf-8', 'Cache-Control': 'no-store' });
  res.end(JSON.stringify(obj));
}
function readBody(req) {
  return new Promise((ok, bad) => {
    let s = '', n = 0;
    req.on('data', d => { n += d.length; if (n > 10000) { bad(new Oops('请求太大')); req.destroy(); } else s += d; });
    req.on('end', () => { try { ok(s ? JSON.parse(s) : {}); } catch (e) { bad(new Oops('请求格式不对')); } });
    req.on('error', bad);
  });
}
function getRoom(code) {
  const r = rooms.get(String(code || ''));
  if (!r) throw new Oops('房间不存在，可能已经解散了');
  return r;
}
const server = http.createServer(async (req, res) => {
  try {
    const u = new URL(req.url, 'http://x');
    if (req.method === 'GET' && STATIC[u.pathname]) {
      const [file, type] = STATIC[u.pathname];
      res.writeHead(200, { 'Content-Type': type, 'Cache-Control': 'no-cache' });
      return fs.createReadStream(path.join(__dirname, file)).pipe(res);
    }
    if (req.method === 'GET' && u.pathname === '/healthz') return send(res, 200, { ok: true, rooms: rooms.size });
    if (req.method === 'GET' && u.pathname === '/api/events') {
      const pid = u.searchParams.get('pid');
      if (!validPid(pid)) throw new Oops('身份无效');
      const r = getRoom(u.searchParams.get('room'));
      join(r, pid, cleanName(u.searchParams.get('name')));
      res.writeHead(200, { 'Content-Type': 'text/event-stream; charset=utf-8', 'Cache-Control': 'no-cache, no-transform', 'Connection': 'keep-alive', 'X-Accel-Buffering': 'no' });
      res.write('retry: 2000\n\n');
      attach(r, pid, res);
      req.on('close', () => detach(r, pid, res));
      return;
    }
    if (req.method === 'POST' && u.pathname.startsWith('/api/')) {
      const b = await readBody(req);
      if (!validPid(b.pid)) throw new Oops('身份无效');
      if (u.pathname === '/api/create') { const r = newRoom(); join(r, b.pid, cleanName(b.name)); return send(res, 200, { room: r.code }); }
      if (u.pathname === '/api/join') { const r = getRoom(b.room); join(r, b.pid, cleanName(b.name)); return send(res, 200, { room: r.code }); }
      if (u.pathname === '/api/act') { act(getRoom(b.room), b.pid, b); return send(res, 200, { ok: true }); }
      if (u.pathname === '/api/ping') { const r = rooms.get(String(b.room || '')); if (r) r.touched = Date.now(); return send(res, 200, { ok: true }); }
    }
    send(res, 404, { error: '没有这个地址' });
  } catch (e) {
    if (e instanceof Oops) return send(res, 400, { error: e.message });
    console.error(e);
    if (!res.headersSent) send(res, 500, { error: '服务器出错了' });
  }
});
server.listen(PORT, () => console.log('干瞪眼服务器已启动，端口 ' + PORT));
