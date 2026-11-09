// Already-decoded length-description symbols, not a complete DEFLATE header.
const instructions = [
  {symbol: 3},
  {symbol: 16, extra: 1},
  {symbol: 17, extra: 2},
  {symbol: 2},
  {symbol: 18, extra: 2},
];

export const lengthExamples = Object.freeze({
  valid: {capacity: 24, instructions},
  overrun: {capacity: 23, instructions},
  previous: {capacity: 24, instructions: [{symbol: 16, extra: 0}]},
});

export function createLengthsState(example = 'valid') {
  const sample = lengthExamples[example];
  if (!sample) throw new RangeError('Unknown length example');
  return {
    example, capacity: sample.capacity, instructions: sample.instructions,
    cursor: 0, output: [], phase: 'read', current: null,
    pending: 0, value: null, amount: 0, start: 0, error: null,
    extraBits: 0, extraConsumed: 0,
  };
}

export function stepLengths(state) {
  if (state.phase === 'done' || state.phase === 'error') return state;
  const s = {...state, output: [...state.output]};
  if (s.phase === 'read') {
    if (s.cursor >= s.instructions.length) {
      s.phase = s.output.length === s.capacity ? 'done' : 'error';
      if (s.phase === 'error') s.error = 'short';
      return s;
    }
    s.current = s.instructions[s.cursor++];
    s.start = s.output.length;
    s.amount = 0;
    s.pending = 0;
    s.value = null;
    s.extraBits = 0;
    s.phase = 'expand';
    return s;
  }
  if (s.phase === 'expand') {
    const {symbol, extra = 0} = s.current;
    if (symbol === 16 && s.output.length === 0) {
      s.phase = 'error';
      s.error = 'previous';
      return s;
    }
    s.extraBits = symbol === 16 ? 2 : symbol === 17 ? 3 : symbol === 18 ? 7 : 0;
    s.extraConsumed += s.extraBits;
    s.value = symbol < 16 ? symbol : symbol === 16 ? s.output.at(-1) : 0;
    s.amount = symbol < 16 ? 1 : (symbol === 18 ? 11 : 3) + extra;
    s.pending = s.amount;
    if (s.output.length + s.amount > s.capacity) {
      s.phase = 'error';
      s.error = 'overrun';
      return s;
    }
    s.phase = 'write';
    return s;
  }
  s.output.push(s.value);
  s.pending--;
  if (s.pending === 0) {
    s.phase = s.cursor === s.instructions.length && s.output.length === s.capacity
      ? 'done' : 'read';
  }
  return s;
}
