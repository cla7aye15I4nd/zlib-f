// Teaching models only. These functions do not execute the C or Lean translation.
export const SAMPLE = 'ABABABAB';

export function copyBack(history, length, distance) {
  if (!Number.isInteger(length) || length < 0 || !Number.isInteger(distance) ||
      distance < 1 || distance > history.length) throw new RangeError('Invalid match');
  const out = [...history];
  for (let i = 0; i < length; i++) out.push(out[out.length - distance]);
  return out.join('');
}

export function canonical(lengths) {
  if (lengths.some(n => !Number.isInteger(n) || n < 0 || n > 15))
    throw new RangeError('Invalid length');
  const max = Math.max(0, ...lengths);
  const counts = Array(max + 1).fill(0);
  lengths.forEach(n => { if (n) counts[n]++; });
  const used = lengths.filter(Boolean).length;
  const kraft = lengths.reduce((sum, n) => sum + (n ? 2 ** -n : 0), 0);
  if (kraft > 1) return { valid: false, complete: false, kraft, entries: [] };
  const next = Array(max + 1).fill(0);
  for (let n = 2; n <= max; n++) next[n] = 2 * (next[n - 1] + counts[n - 1]);
  const entries = lengths.map((length, symbol) => {
    const value = length ? next[length]++ : null;
    return { symbol: String.fromCharCode(65 + symbol), length, value,
      code: length ? value.toString(2).padStart(length, '0') : '' };
  });
  return { valid: true, complete: used > 0 && kraft === 1, kraft, entries };
}

export function lookup(symbol) {
  const entry = canonical([1, 2, 3, 3]).entries.find(e => e.symbol === symbol);
  if (!entry) throw new RangeError('Invalid symbol');
  const reversed = [...entry.code].reverse().join('');
  const value = parseInt(reversed, 2);
  return { ...entry, buffer: reversed.padStart(3, '0'),
    root: value & 3, sub: entry.length > 2 ? (value >> 2) & 1 : null };
}

export function search(budget) {
  const text = 'ABCQABCRABCQABCX';
  const current = 8;
  const candidates = [];
  for (let i = current - 1; i >= 0; i--) {
    if (text.slice(i, i + 3) === text.slice(current, current + 3)) {
      let length = 0;
      while (current + length < text.length && text[i + length] === text[current + length]) length++;
      candidates.push({ position: i, distance: current - i, length });
    }
  }
  const visited = candidates.slice(0, budget);
  const best = visited.reduce((a, b) => !a || b.length > a.length ? b : a, null);
  return { text, current, candidates, visited, best };
}

export function streamCall(produced, room) {
  if (!Number.isInteger(produced) || produced < 0 || produced > 8 ||
      !Number.isInteger(room) || room < 1) throw new RangeError('Invalid stream state');
  const next = Math.min(8, produced + room);
  return { produced: next, chunk: SAMPLE.slice(produced, next), output: SAMPLE.slice(0, next),
    mode: next === 8 ? 'PAYLOAD_DONE' : next < 2 ? 'LIT' : 'MATCH',
    remaining: next < 2 ? 6 : 8 - next, distance: 2 };
}

export const PLANS = {
  safe: [3, 3, 3, 2, 2, 2, 1],
  unsafe: [12, 1, 1, 1, 1, 1, 1],
};

export function overlay(plan, q) {
  const writes = PLANS[plan];
  if (!writes || !Number.isInteger(q) || q < 0 || q > 7) throw new RangeError('Invalid prefix');
  const B = 8, capacity = 32, symbolEnd = B + 3 * writes.length;
  let pending = 2;
  const corrupted = new Set();
  for (let i = 0; i < q; i++) {
    const end = pending + writes[i];
    const unread = B + 3 * (i + 1);
    for (let cell = pending; cell < end; cell++) {
      if (cell >= unread && cell < symbolEnd) corrupted.add(cell);
    }
    pending = end;
  }
  return { B, capacity, pending, unread: B + 3 * q, symbolEnd,
    finalSize: 2 + writes.reduce((a, b) => a + b, 0), corrupted: [...corrupted] };
}

export function ownership(failure, step) {
  const events = failure === 1 ? [
    { text: 'state 分配失败；没有获得新资源。', live: [] },
  ] : failure === 2 ? [
    { text: 'state 分配成功，模型开始拥有它。', live: ['state'] },
    { text: 'window 分配失败；state 仍需清理。', live: ['state'] },
    { text: '失败清理释放 state，返回分配错误。', live: [] },
  ] : [
    { text: 'state 分配成功。', live: ['state'] },
    { text: 'window 分配成功。', live: ['state', 'window'] },
    { text: '初始化成功；两项资源继续归流所有。', live: ['state', 'window'] },
    { text: '调用 end，释放 window。', live: ['state'] },
    { text: 'end 释放 state；生命周期结束。', live: [] },
  ];
  const initial = { text: '还没有开始分配。背景中的其他对象始终保持不变。', live: [] };
  const index = Math.min(Math.max(step, 0), events.length);
  return { ...(index ? events[index - 1] : initial), index, total: events.length,
    history: events.slice(0, index).map(e => e.text) };
}
