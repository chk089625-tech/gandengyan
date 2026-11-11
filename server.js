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
const avSeed = () => Math.floor(Math.random() * 4294967295) + 1;   // 国风头像的随机种子，网页按种子画头像
const VOICE_FILE = /^[A-Za-z0-9]+(-\d+)?\.(mp3|m4a|wav)$/;
/* GDY_TIME_SCALE 只给自动测试用，把所有计时按比例缩短；线上不设置，等于 1 */
const SCALE = Number(process.env.GDY_TIME_SCALE) > 0 ? Number(process.env.GDY_TIME_SCALE) : 1;
const TURN_MS = 30000 * SCALE, OFFLINE_PLAY_MS = 5000 * SCALE, OFFLINE_LOBBY_MS = 120000 * SCALE, ROOM_IDLE_MS = 30 * 60000 * SCALE, EMPTY_ROOM_MS = 2 * 60000 * SCALE;
const HOST_GRACE_MS = 20000 * SCALE;            // 房主掉线超过 20 秒，房主身份转给在线的人
const MAX_MEMBERS = 8, MAX_ROOMS = 500;
const CREATE_PER_IP = 6, CREATE_WINDOW_MS = 10 * 60000, ROOMS_PER_HOST = 3;
const CONNS_PER_PLAYER = 3, CONNS_PER_IP = 60;
const createLog = new Map(), ipConns = new Map();
const rooms = new Map();

class Oops extends Error {}
const validPid = p => typeof p === 'string' && /^[a-z0-9]{8,40}$/.test(p);
const cleanName = s => String(s || '').replace(/[\u0000-\u001f<>]/g, '').trim().slice(0, 12) || '无名牌友';
const online = (r, pid) => !!(r.conns.get(pid) && r.conns.get(pid).size);
/* 在线，或者刚掉线还在宽限期内（比如刷新页面） */
const present = (r, pid, grace) => online(r, pid) || Date.now() - (r.offSince.get(pid) || Date.now()) < grace;
/* 上桌顺序：在场的人按进房先后排在前面，离开太久的排到后面；前 4 个上桌 */
function seatQueue(r) {
  const here = r.members.filter(m => present(r, m.pid, HOST_GRACE_MS));
  return here.concat(r.members.filter(m => !here.includes(m)));
}
const seatable = r => r.members.filter(m => present(r, m.pid, HOST_GRACE_MS)).slice(0, 4);
/* 房主不在了就转给在线的人；原房主回来还是普通玩家，座位按身份保留 */
function ensureHost(r) {
  if (r.host && r.members.some(m => m.pid === r.host) && present(r, r.host, HOST_GRACE_MS)) return false;
  const next = r.members.find(m => online(r, m.pid)) || r.members.find(m => m.pid === r.host) || r.members[0];
  const nh = next ? next.pid : null;
  if (nh === r.host) return false;
  r.host = nh;
  return true;
}

function newRoom() {
  if (rooms.size >= MAX_ROOMS) throw new Oops('房间太多了，稍后再试');
  let code; do { code = String(Math.floor(1000 + Math.random() * 9000)); } while (rooms.has(code));
  const r = { code, v: 0, seq: 0, members: [], host: null, nextDealer: null, fill: true, scores: {}, conns: new Map(), offTimers: new Map(), offSince: new Map(), timer: null, deadline: 0, touched: Date.now() };
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
  r.members.push({ pid, name, av: avSeed() });
  if (!online(r, pid)) r.offSince.set(pid, Date.now());
  ensureHost(r);
}
function leave(r, pid) {
  r.members = r.members.filter(m => m.pid !== pid);
  const i = r.players.findIndex(p => p.pid === pid);
  if (i >= 0) { const p = r.players[i]; p.pid = null; p.ai = true; p.name += '（已离开）'; }
  const set = r.conns.get(pid);
  if (set) { set.forEach(res => { try { res.end(); } catch (e) {} }); r.conns.delete(pid); }
  r.offSince.delete(pid);
  ensureHost(r);
  if (r.phase === 'play') sync(r); else { r.v++; broadcast(r); }
}

/* ---------- 牌局 ---------- */
function buildPlayers(r) {
  const ps = seatable(r).map(m => ({ key: m.pid, pid: m.pid, name: m.name, av: m.av, ai: false, auto: false }));
  if (r.fill) for (let k = 0; ps.length < 4; k++) ps.push({ key: 'bot' + k, pid: null, name: BOT_NAMES[k], av: avSeed(), ai: true, auto: false });
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
  r.nextDealer = r.players[w].key;
  r.phase = 'over';
  ensureHost(r);
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
  if (r.trickEnd) r.timer = setTimeout(() => endTrick(r), 1100 * SCALE);
  else if (p.ai || p.auto) r.timer = setTimeout(() => aiTurn(r), 950 * SCALE);
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
    code: r.code, v: r.v, phase: r.phase, you, host: r.host === pid, fill: r.fill,
    members: seatQueue(r).map((m, i) => ({ name: m.name, av: m.av, online: online(r, m.pid), you: m.pid === pid, host: m.pid === r.host,
      seat: i < 4 && present(r, m.pid, HOST_GRACE_MS) })),
    players: r.players.map((p, i) => ({ name: p.name, av: p.av, ai: p.ai, auto: !!p.auto, count: r.hands[i].length, score: r.scores[p.key] || 0 })),
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
  ensureHost(r);
  const host = r.host === pid, you = r.players.findIndex(p => p.pid === pid);
  switch (b.type) {
    case 'fill':
      if (!host || r.phase !== 'lobby') throw new Oops('只有房主能改这个设置');
      r.fill = !!b.on; r.v++; broadcast(r); return;
    case 'start': {
      if (!host) throw new Oops('等房主开局');
      if (r.phase === 'play') throw new Oops('这一局还没打完');
      const ps = buildPlayers(r);
      if (ps.length < 2) throw new Oops('至少要两个人，或者勾上电脑补位');
      r.players = ps;
      /* 上局赢家坐庄；赢家已经离桌就随机 */
      const w = ps.findIndex(p => p.key === r.nextDealer);
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
      /* 玩家选了出法就按那个出法校验；牌型对象一律用服务器自己算出来的，不信客户端 */
      const opts = L.resolveAll(cards, r.last ? r.last.combo : null, r.hands[you].length);
      const want = b.combo && typeof b.combo === 'object' ? b.combo : null;
      const combo = want ? opts.find(o => L.sameCombo(o, want)) : opts[0];
      if (!combo) throw new Oops(want ? '这手牌不能按这个出法出' : '这手牌出不了');
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
    case 'avatar': {
      if (r.phase === 'play') throw new Oops('打完这局再换头像');
      r.members.find(m => m.pid === pid).av = avSeed();
      r.v++; broadcast(r); return;
    }
    case 'leave': return leave(r, pid);
    default: throw new Oops('不认识的动作');
  }
}

/* ---------- 连接 ---------- */
function attach(r, pid, res) {
  clearTimeout(r.offTimers.get(pid)); r.offTimers.delete(pid);
  r.offSince.delete(pid);
  if (!r.conns.has(pid)) r.conns.set(pid, new Set());
  r.conns.get(pid).add(res);
  r.touched = Date.now();
  ensureHost(r);
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
  r.offSince.set(pid, Date.now());
  r.v++; broadcast(r);
  /* 宽限期过了：房主可能要转交，座位排队也会变，都要通知大家 */
  setTimeout(() => { if (rooms.has(r.code) && !online(r, pid)) { ensureHost(r); r.v++; broadcast(r); } }, HOST_GRACE_MS + 200);
  clearTimeout(r.offTimers.get(pid));
  r.offTimers.set(pid, setTimeout(() => {
    r.offTimers.delete(pid);
    if (online(r, pid) || !rooms.has(r.code)) return;
    const i = r.players.findIndex(p => p.pid === pid);
    if (r.phase === 'play' && i >= 0) {
      r.players[i].auto = true;
      if (r.turn === i && !r.trickEnd) schedule(r);
      r.v++; broadcast(r);
    }
  }, OFFLINE_PLAY_MS));
}
setInterval(() => rooms.forEach(r => r.conns.forEach(set => set.forEach(res => { try { res.write(': ping\n\n'); } catch (e) {} }))), 20000).unref();
setInterval(() => {
  const now = Date.now();
  rooms.forEach(r => {
    let changed = false;
    if (r.phase !== 'play') {
      const keep = r.members.filter(m => present(r, m.pid, OFFLINE_LOBBY_MS));
      if (keep.length !== r.members.length) { r.members.filter(m => !keep.includes(m)).forEach(m => r.offSince.delete(m.pid)); r.members = keep; changed = true; }
    }
    if (ensureHost(r)) changed = true;
    if (changed) { r.v++; broadcast(r); }
    const anyone = [...r.conns.values()].some(s => s.size);
    if (!anyone && now - r.touched > (r.members.length ? ROOM_IDLE_MS : EMPTY_ROOM_MS)) { clearTimeout(r.timer); r.offTimers.forEach(clearTimeout); rooms.delete(r.code); }
  });
}, 15000 * SCALE).unref();

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
function clientIp(req) {
  return String(req.headers['x-forwarded-for'] || '').split(',')[0].trim() || req.socket.remoteAddress || '?';
}
setInterval(() => { const now = Date.now(); createLog.forEach((v, k) => { const keep = v.filter(t => now - t < CREATE_WINDOW_MS); if (keep.length) createLog.set(k, keep); else createLog.delete(k); }); }, 60000).unref();
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
    if (req.method === 'GET' && u.pathname === '/voice/list.json') {
      let list = [];
      try { list = fs.readdirSync(path.join(__dirname, 'voice')).filter(f => VOICE_FILE.test(f)); } catch (e) {}
      res.writeHead(200, { 'Content-Type': 'application/json; charset=utf-8', 'Cache-Control': 'no-cache' });
      return res.end(JSON.stringify(list));
    }
    if (req.method === 'GET' && u.pathname.startsWith('/voice/')) {
      const f = u.pathname.slice(7);
      if (!VOICE_FILE.test(f)) return send(res, 404, { error: '没有这个文件' });
      const fp = path.join(__dirname, 'voice', f);
      if (!fs.existsSync(fp)) return send(res, 404, { error: '没有这个文件' });
      const ext = f.split('.').pop();
      res.writeHead(200, { 'Content-Type': { mp3: 'audio/mpeg', m4a: 'audio/mp4', wav: 'audio/wav' }[ext], 'Cache-Control': 'public, max-age=86400' });
      return fs.createReadStream(fp).pipe(res);
    }
    if (req.method === 'GET' && u.pathname === '/healthz') return send(res, 200, { ok: true, rooms: rooms.size });
    if (req.method === 'GET' && u.pathname === '/api/events') {
      const pid = u.searchParams.get('pid');
      if (!validPid(pid)) throw new Oops('身份无效');
      const r = getRoom(u.searchParams.get('room'));
      const ip = clientIp(req);
      if ((r.conns.get(pid) || new Set()).size >= CONNS_PER_PLAYER) throw new Oops('你在太多窗口打开了这个房间，关掉几个再试');
      if ((ipConns.get(ip) || 0) >= CONNS_PER_IP) throw new Oops('当前网络连接太多，稍后再试');
      join(r, pid, cleanName(u.searchParams.get('name')));
      ipConns.set(ip, (ipConns.get(ip) || 0) + 1);
      req.on('close', () => { const n = (ipConns.get(ip) || 1) - 1; if (n > 0) ipConns.set(ip, n); else ipConns.delete(ip); });
      res.writeHead(200, { 'Content-Type': 'text/event-stream; charset=utf-8', 'Cache-Control': 'no-cache, no-transform', 'Connection': 'keep-alive', 'X-Accel-Buffering': 'no' });
      res.write('retry: 2000\n\n');
      attach(r, pid, res);
      req.on('close', () => detach(r, pid, res));
      return;
    }
    if (req.method === 'POST' && u.pathname.startsWith('/api/')) {
      const b = await readBody(req);
      if (!validPid(b.pid)) throw new Oops('身份无效');
      if (u.pathname === '/api/create') {
        const ip = clientIp(req), now = Date.now();
        const log = (createLog.get(ip) || []).filter(t => now - t < CREATE_WINDOW_MS);
        if (log.length >= CREATE_PER_IP) throw new Oops('建房太频繁了，过几分钟再试');
        let mine = 0; rooms.forEach(x => { if (x.host === b.pid && x.members.length) mine++; });
        if (mine >= ROOMS_PER_HOST) throw new Oops('你已经开了 ' + ROOMS_PER_HOST + ' 个房间，先回原来的房间，或者离开后再建');
        log.push(now); createLog.set(ip, log);
        const r = newRoom(); join(r, b.pid, cleanName(b.name)); return send(res, 200, { room: r.code });
      }
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
