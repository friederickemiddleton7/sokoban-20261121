// Room-by-room push-optimal Sokoban solver.
// Levels are a one-square hallway with 1-4 rooms off it; a box never leaves its room,
// so the level's push optimum is the sum of its rooms' optima. Each room is solved with
// breadth-first search over push states (boxes + player region), pruned by dead squares
// and frozen 2x2 blocks. Deterministic: no clock, no randomness, fixed tie-break order.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
const D = [[0, -1], [0, 1], [-1, 0], [1, 0]];
const MAX_STATES = 400_000;

function parse(t) {
  const rows = t.split('\n').filter((r) => r.length > 0);
  const h = rows.length, w = Math.max(...rows.map((r) => r.length));
  const wall = new Uint8Array(w * h).fill(1);
  const goals = [], boxes = [];
  let player = 0;
  rows.forEach((row, y) => {
    for (let x = 0; x < row.length; x++) {
      const c = row[x], i = y * w + x;
      if (c === '#') continue;
      wall[i] = 0;
      if ('.*+'.includes(c)) goals.push(i);
      if ('$*'.includes(c)) boxes.push(i);
      if ('@+'.includes(c)) player = i;
    }
  });
  // The outermost frame is a wall whatever it shows.
  for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) if (x === 0 || y === 0 || x === w - 1 || y === h - 1) wall[y * w + x] = 1;
  boxes.sort((a, b) => a - b);
  return { w, h, wall, goals, boxes, player };
}

function liveSquares(w, h, wall, goals) {
  const size = w * h;
  const live = new Uint8Array(size);
  const q = [];
  for (const g of goals) { live[g] = 1; q.push(g); }
  for (let qi = 0; qi < q.length; qi++) {
    const x = q[qi];
    for (const [dx, dy] of D) {
      const d = dy * w + dx, y = x - d;
      if (!wall[y] && !wall[y - d] && !live[y]) { live[y] = 1; q.push(y); }
    }
  }
  return live;
}

// The player's reachable region from `from` with `box` in the way; marks `seen` with `stamp`; returns its lowest square.
function region(w, wall, box, from, seen, stamp, stack) {
  let low = from, n = 0;
  stack[n++] = from; seen[from] = stamp;
  while (n > 0) {
    const p = stack[--n];
    if (p < low) low = p;
    for (let k = 0; k < 4; k++) {
      const q = k === 0 ? p - w : k === 1 ? p + w : k === 2 ? p - 1 : p + 1;
      if (wall[q] === 0 && box[q] === 0 && seen[q] !== stamp) { seen[q] = stamp; stack[n++] = q; }
    }
  }
  return low;
}

function frozen(w, wall, box, goal, t) {
  for (const a of [t, t - 1, t - w, t - w - 1]) {
    const b = a + 1, c = a + w, d = c + 1;
    if (!(wall[a] || box[a]) || !(wall[b] || box[b]) || !(wall[c] || box[c]) || !(wall[d] || box[d])) continue;
    if ((box[a] && !goal[a]) || (box[b] && !goal[b]) || (box[c] && !goal[c]) || (box[d] && !goal[d])) return true;
  }
  return false;
}

const keyOf = (boxes, low, size) => {
  let k = low;
  for (const b of boxes) k = k * size + b;
  return k;
};

// Push-optimal BFS over one room: {pushes, moves} or null.
function solveRoom(w, h, wall, goals, boxes, player) {
  const size = w * h;
  const goal = new Uint8Array(size);
  for (const g of goals) goal[g] = 1;
  const live = liveSquares(w, h, wall, goals);
  const box = new Uint8Array(size);
  const seen = new Int32Array(size), mark = new Int32Array(size), stack = new Int32Array(size);
  let stamp = 0;
  const solved = (bs) => bs.every((b) => goal[b]);
  if (boxes.some((b) => !live[b])) return null;
  const stB = [boxes], stP = [player], par = [-1];
  const idx = new Map();
  for (const b of boxes) box[b] = 1;
  idx.set(keyOf(boxes, region(w, wall, box, player, seen, ++stamp, stack), size), 0);
  for (const b of boxes) box[b] = 0;
  let found = solved(boxes) ? 0 : -1;
  for (let head = 0; found < 0 && head < stB.length; head++) {
    const bs = stB[head];
    for (const b of bs) box[b] = 1;
    region(w, wall, box, stP[head], seen, ++stamp, stack);
    const here = stamp;
    for (let bi = 0; bi < bs.length && found < 0; bi++) {
      const b = bs[bi];
      for (const [dx, dy] of D) {
        const d = dy * w + dx, t = b + d;
        if (seen[b - d] !== here || wall[t] || box[t] || !live[t]) continue;
        box[b] = 0; box[t] = 1;
        const fr = frozen(w, wall, box, goal, t);
        let next = null, key = -1;
        if (!fr) {
          next = bs.slice(); next[bi] = t; next.sort((x, y) => x - y);
          key = keyOf(next, region(w, wall, box, b, mark, ++stamp, stack), size);
        }
        box[t] = 0; box[b] = 1;
        if (fr || idx.has(key)) continue;
        if (stB.length >= MAX_STATES) { for (const x of bs) box[x] = 0; return null; }
        idx.set(key, stB.length);
        stB.push(next); stP.push(b); par.push(head);
        if (solved(next)) { found = stB.length - 1; break; }
      }
    }
    for (const x of bs) box[x] = 0;
  }
  if (found < 0) return null;
  const path = [];
  for (let s = found; s > 0; s = par[s]) path.push(s);
  path.reverse();
  let moves = '';
  let pl = player, cur = boxes;
  for (const s of path) {
    const nb = stB[s];
    const from = cur.find((b) => !nb.includes(b));
    const to = nb.find((b) => !cur.includes(b));
    const d = to - from;
    const letter = d === -w ? 'U' : d === w ? 'D' : d === -1 ? 'L' : 'R';
    for (const b of cur) box[b] = 1;
    moves += walkTo(w, wall, box, pl, from - d);
    for (const b of cur) box[b] = 0;
    moves += letter;
    pl = from;
    cur = nb;
  }
  return { pushes: path.length, moves };
}

function walkTo(w, wall, box, from, to) {
  if (from === to) return '';
  const prev = new Int32Array(wall.length).fill(-1);
  const how = new Array(wall.length);
  const queue = [from];
  prev[from] = from;
  for (let qi = 0; qi < queue.length; qi++) {
    const p = queue[qi];
    if (p === to) break;
    for (const [dx, dy, letter] of [[0, -1, 'u'], [0, 1, 'd'], [-1, 0, 'l'], [1, 0, 'r']]) {
      const q = p + dy * w + dx;
      if (wall[q] || box[q] || prev[q] !== -1) continue;
      prev[q] = p; how[q] = letter; queue.push(q);
    }
  }
  if (prev[to] === -1) throw new Error('walkTo: out of reach');
  let s = '';
  for (let p = to; p !== from; p = prev[p]) s = how[p] + s;
  return s;
}

const endOf = (w, from, moves) => {
  let p = from;
  for (const ch of moves.toLowerCase()) p += ch === 'u' ? -w : ch === 'd' ? w : ch === 'l' ? -1 : 1;
  return p;
};

// Cut the dead squares of the player's row out of the floor; each part left that holds a box is a room.
function roomsOf(level) {
  const { w, wall, goals, boxes, player } = level;
  const live = liveSquares(w, level.h, wall, goals);
  const row = Math.floor(player / w);
  const cut = new Uint8Array(wall.length);
  for (let i = row * w; i < (row + 1) * w; i++) if (!wall[i] && !live[i]) cut[i] = 1;
  if (boxes.some((b) => cut[b])) return null;
  const part = new Int32Array(wall.length).fill(-1);
  const rooms = [];
  for (let s = 0; s < wall.length; s++) {
    if (wall[s] || cut[s] || part[s] >= 0) continue;
    const squares = [s];
    part[s] = rooms.length;
    for (let i = 0; i < squares.length; i++) {
      for (const [dx, dy] of D) {
        const q = squares[i] + dy * w + dx;
        if (!wall[q] && !cut[q] && part[q] < 0) { part[q] = rooms.length; squares.push(q); }
      }
    }
    rooms.push({ squares, boxes: [], goals: [] });
  }
  for (const b of boxes) rooms[part[b]].boxes.push(b);
  for (const g of goals) if (part[g] >= 0) rooms[part[g]].goals.push(g);
  if (goals.some((g) => part[g] < 0) || rooms.some((r) => r.boxes.length !== r.goals.length)) return null;
  return rooms.filter((r) => r.boxes.length > 0);
}

function solveLevel(level) {
  const rooms = roomsOf(level);
  if (rooms === null) return null;
  let player = level.player, pushes = 0, moves = '';
  for (const room of rooms) {
    const wall = level.wall.slice();
    for (const other of rooms) if (other !== room) for (const b of other.done ? other.goals : other.boxes) wall[b] = 1;
    const sub = { w: level.w, h: level.h, wall, goals: room.goals.slice().sort((a, b) => a - b), boxes: room.boxes.slice().sort((a, b) => a - b), player };
    const solved = solveRoom(sub.w, sub.h, sub.wall, sub.goals, sub.boxes, sub.player);
    if (solved === null) return null;
    pushes += solved.pushes;
    moves += solved.moves;
    player = endOf(level.w, player, solved.moves);
    room.done = true;
  }
  return { pushes, moves };
}

for (const id of readdirSync(I).sort()) {
  const level = parse(readFileSync(join(I, id, 'level.txt'), 'utf8'));
  const solved = solveLevel(level);
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'solution.txt'), `${solved ? solved.moves : ''}\n`);
}
