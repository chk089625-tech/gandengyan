/* 干瞪眼规则：服务器和网页共用同一份 */
(function(root){
const isJoker = c => c.r >= 16;
const rankLabel = r => ({11:'J',12:'Q',13:'K',14:'A',15:'2',16:'小王',17:'大王'}[r] || String(r));

function makeDeck(){
  const d = []; let id = 0;
  for (const s of ['♠','♥','♣','♦']) for (let r = 3; r <= 15; r++) d.push({id:id++, r, s});
  d.push({id:id++, r:16, s:'J'}); d.push({id:id++, r:17, s:'J'});
  return d;
}
function shuffle(a){
  for (let i = a.length - 1; i > 0; i--){ const j = Math.floor(Math.random()*(i+1)); [a[i],a[j]] = [a[j],a[i]]; }
  return a;
}
function sortHand(h){ h.sort((a,b) => b.r - a.r || a.id - b.id); }

/* 一手牌可能的全部解释（王是百搭，所以可能不止一种） */
function interpret(cards){
  const n = cards.length, out = [];
  if (!n) return out;
  const nat = cards.filter(c => !isJoker(c)).map(c => c.r).sort((a,b) => a-b);
  const w = n - nat.length;
  if (n === 1){ out.push(w ? {type:'joker1',rank:16,len:1} : {type:'single',rank:nat[0],len:1}); return out; }
  if (n === 2 && w === 2){ out.push({type:'bomb',size:99,rank:17,len:2}); return out; }
  if (nat.every(r => r === nat[0])){
    if (n === 2) out.push({type:'pair',rank:nat[0],len:2});
    if (n === 3 || n === 4) out.push({type:'bomb',size:n,rank:nat[0],len:n});
  }
  if (n >= 3 && nat.every(r => r <= 14)){
    const lo = nat[0], hi = nat[nat.length-1];
    if (n <= 12 && new Set(nat).size === nat.length){
      for (let s = 14-n+1; s >= 3; s--) if (lo >= s && hi <= s+n-1) out.push({type:'straight',rank:s,len:n});
    }
    if (n % 2 === 0 && n >= 4){
      const k = n/2, cnt = {}; nat.forEach(r => cnt[r] = (cnt[r]||0)+1);
      if (Object.values(cnt).every(c => c <= 2)){
        for (let s = 14-k+1; s >= 3; s--) if (lo >= s && hi <= s+k-1) out.push({type:'pairs',rank:s,len:n});
      }
    }
  }
  return out;
}
function canBeat(c, prev){
  if (!prev) return true;
  if (c.type === 'bomb'){
    if (prev.type !== 'bomb') return true;
    return c.size > prev.size || (c.size === prev.size && c.rank > prev.rank);
  }
  if (prev.type === 'bomb' || c.type !== prev.type || c.len !== prev.len || c.type === 'joker1') return false;
  if (c.rank === prev.rank + 1) return true;
  return (c.type === 'single' || c.type === 'pair') && c.rank === 15 && prev.rank < 15;
}
/* 选中的牌所有合法出法。带王时同一组牌可能有几种解释（如 5 5 王 王：连对或四张炸），
   普通牌型排在前、炸弹排在后，因为炸弹会让倍数翻倍，不能默认替玩家选 */
function resolveAll(cards, prev, handSize){
  const ok = interpret(cards).filter(c => !(c.type === 'joker1' && (prev || handSize !== 1)) && canBeat(c, prev));
  return ok.filter(c => c.type !== 'bomb').concat(ok.filter(c => c.type === 'bomb'));
}
function resolve(cards, prev, handSize){ return resolveAll(cards, prev, handSize)[0] || null; }
function sameCombo(a, b){
  return !!a && !!b && a.type === b.type && a.rank === b.rank && a.len === b.len && (a.size || 0) === (b.size || 0);
}
function comboName(c){
  if (c.type === 'single') return '单张 ' + rankLabel(c.rank);
  if (c.type === 'joker1') return '单张王';
  if (c.type === 'pair') return '对 ' + rankLabel(c.rank);
  if (c.type === 'straight') return '顺子 ' + rankLabel(c.rank) + '–' + rankLabel(c.rank + c.len - 1);
  if (c.type === 'pairs') return '连对 ' + rankLabel(c.rank) + '–' + rankLabel(c.rank + c.len/2 - 1);
  if (c.size === 99) return '王炸';
  return (c.size === 4 ? '四张炸 ' : '三张炸 ') + rankLabel(c.rank);
}

/* 从手牌里列出所有能出的组合 */
function genPlays(hand){
  const by = {}, jk = [];
  hand.forEach(c => { if (isJoker(c)) jk.push(c); else (by[c.r] = by[c.r] || []).push(c); });
  const w = jk.length, plays = [];
  const add = (cards, combo) => plays.push({cards, combo, jokers: cards.filter(isJoker).length});
  for (const k in by){
    const cs = by[k], R = +k;
    add([cs[0]], {type:'single',rank:R,len:1});
    if (cs.length >= 2) add(cs.slice(0,2), {type:'pair',rank:R,len:2});
    else if (w >= 1) add([cs[0], jk[0]], {type:'pair',rank:R,len:2});
    for (const size of [3,4]){
      const use = Math.min(cs.length, size), need = size - use;
      if (need <= w) add([...cs.slice(0,use), ...jk.slice(0,need)], {type:'bomb',size,rank:R,len:size});
    }
  }
  if (w === 2) add(jk.slice(), {type:'bomb',size:99,rank:17,len:2});
  if (hand.length === 1 && w === 1) add([jk[0]], {type:'joker1',rank:16,len:1});
  for (let n = 3; n <= 12; n++) for (let s = 3; s+n-1 <= 14; s++){
    const cards = []; let miss = 0;
    for (let r = s; r < s+n; r++){ if (by[r]) cards.push(by[r][0]); else miss++; }
    if (miss <= w && cards.length >= 2) add([...cards, ...jk.slice(0,miss)], {type:'straight',rank:s,len:n});
  }
  for (let k = 2; k <= 6; k++) for (let s = 3; s+k-1 <= 14; s++){
    const cards = []; let miss = 0;
    for (let r = s; r < s+k; r++){ const have = Math.min(2, by[r] ? by[r].length : 0); if (have) cards.push(...by[r].slice(0,have)); miss += 2-have; }
    if (miss <= w && cards.length >= 2) add([...cards, ...jk.slice(0,miss)], {type:'pairs',rank:s,len:2*k});
  }
  return plays;
}

/* 把能出的牌按“推荐程度”排好：电脑取第一手，提示按钮依次轮换 */
function rankPlays(hand, prev, minOpp){
  const cnt = {}; hand.forEach(c => cnt[c.r] = (cnt[c.r]||0)+1);
  const plays = genPlays(hand).filter(p => canBeat(p.combo, prev));
  const bombs = plays.filter(p => p.combo.type === 'bomb')
    .sort((a,b) => a.combo.size - b.combo.size || a.combo.rank - b.combo.rank || a.jokers - b.jokers);
  const rest = plays.filter(p => p.combo.type !== 'bomb');
  const small = p => p.combo.type === 'single' || p.combo.type === 'pair';
  if (!prev){
    const score = p => p.cards.length*10 - p.jokers*15 - p.combo.rank*0.5
      - (small(p) && p.combo.rank === 15 ? 8 : 0)
      - (p.combo.type === 'single' && cnt[p.combo.rank] > 1 ? 4 : 0)
      + (p.combo.type === 'single' && minOpp === 1 ? p.combo.rank - 20 : 0);
    rest.sort((a,b) => score(b) - score(a));
  } else {
    const cost = p => p.jokers*10 + (small(p) && p.combo.rank === 15 ? 6 : 0)
      + (p.combo.type === 'single' && cnt[p.combo.rank] > 1 ? 3 : 0) + p.combo.rank*0.1;
    rest.forEach(p => p.cost = cost(p));
    rest.sort((a,b) => a.cost - b.cost);
  }
  const all = [...rest, ...bombs];
  const fin = all.filter(p => p.cards.length === hand.length);
  return [...fin, ...all.filter(p => p.cards.length !== hand.length)];
}
/* 电脑决定出什么；返回 null 表示不要 */
function aiChoose(hand, prev, minOpp){
  const list = rankPlays(hand, prev, minOpp);
  if (!list.length) return null;
  const p = list[0];
  if (p.cards.length === hand.length || !prev) return p;
  if (p.combo.type === 'bomb'){
    const worth = minOpp <= 2 || hand.length - p.cards.length <= 2 || Math.random() < 0.3;
    return worth ? p : null;
  }
  if (p.cost >= 6 && minOpp > 2 && hand.length > 3 && Math.random() < 0.5) return null;
  return p;
}

const api = {isJoker, rankLabel, makeDeck, shuffle, sortHand, interpret, canBeat, resolve, resolveAll, sameCombo, comboName, genPlays, rankPlays, aiChoose};
if (typeof module !== "undefined" && module.exports) module.exports = api; else root.GDY = api;
})(typeof self !== "undefined" ? self : this);
