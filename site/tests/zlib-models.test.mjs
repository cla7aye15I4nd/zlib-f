import test from 'node:test';
import assert from 'node:assert/strict';
import { copyBack, canonical, lookup, search, streamCall, overlay, ownership } from '../static/zlib-models.mjs';

test('overlapping matches extend history, including length greater than distance', () => {
  assert.equal(copyBack('AB', 6, 2), 'ABABABAB');
  assert.equal(copyBack('A', 7, 1), 'AAAAAAAA');
  assert.equal(copyBack('abcdef', 8, 3), 'abcdefdefdefde');
  assert.throws(() => copyBack('AB', 3, 3), RangeError);
});

test('canonical example, zero-length symbols and oversubscribed input', () => {
  assert.deepEqual(canonical([1,2,3,3]).entries.map(e => e.code), ['0','10','110','111']);
  assert.equal(canonical([1,2,3,3]).complete, true);
  assert.equal(canonical([1,1,2,2]).valid, false);
  assert.deepEqual(canonical([0,2,0,2]).entries.map(e => e.code), ['', '00', '', '01']);
  assert.equal(canonical([0,0,0,0]).complete, false);
});

test('every valid four-symbol length assignment gives distinct prefix-free codes', () => {
  for (let n = 0; n < 625; n++) {
    let k = n;
    const lengths = Array.from({length:4}, () => { const x = k % 5; k = Math.floor(k / 5); return x; });
    const result = canonical(lengths);
    if (!result.valid) continue;
    const codes = result.entries.filter(e => e.length).map(e => e.code);
    codes.forEach((code,i) => codes.forEach((other,j) => {
      if (i !== j) assert.equal(other.startsWith(code), false, `${lengths}: ${code}, ${other}`);
    }));
  }
});

test('lookup distinguishes inspected bits from consumed bits', () => {
  assert.deepEqual([lookup('A').root,lookup('A').length], [0,1]);
  assert.deepEqual([lookup('B').root,lookup('B').length], [1,2]);
  assert.deepEqual([lookup('C').root,lookup('C').sub], [3,0]);
  assert.deepEqual([lookup('D').root,lookup('D').sub], [3,1]);
});

test('a larger search budget reaches the longer candidate', () => {
  assert.equal(search(1).best.length, 3);
  assert.equal(search(2).best.length, 7);
  assert.equal(search(2).best.distance, 8);
});

test('all compositions of positive output capacities preserve the same output', () => {
  const visit = (produced, chunks) => {
    if (produced === 8) { assert.equal(chunks.join(''), 'ABABABAB'); return; }
    for (let room = 1; room <= 8; room++) {
      const state = streamCall(produced, room);
      assert.ok(state.produced > produced);
      assert.equal(state.remaining, state.produced < 2 ? 6 : 8-state.produced);
      visit(state.produced, [...chunks, state.chunk]);
    }
  };
  visit(0, []);
});

test('a later safe boundary does not erase an earlier overwrite', () => {
  for (let q = 0; q <= 7; q++) assert.deepEqual(overlay('safe',q).corrupted, []);
  const early = overlay('unsafe',1);
  assert.ok(early.finalSize < early.capacity);
  assert.deepEqual(early.corrupted, [11,12,13]);
  const later = overlay('unsafe',7);
  assert.deepEqual(later.corrupted, [11,12,13,14]);
});

test('every allocation outcome finishes with no owned resources', () => {
  for (const failure of [0,1,2]) {
    const total = ownership(failure,0).total;
    assert.deepEqual(ownership(failure,total).live, []);
  }
  assert.deepEqual(ownership(2,2).live, ['state']);
  assert.deepEqual(ownership(0,3).live, ['state','window']);
});
