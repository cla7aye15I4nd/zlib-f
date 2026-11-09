/** Capacity admission for the LEN branch, not a compressed-data validator. */
export const FAST_LIMITS = Object.freeze({input: 6, output: 258, held: 8});
export const FIELD_BOUNDS = Object.freeze([
  Object.freeze({name: 'length-code', bits: 15}),
  Object.freeze({name: 'length-extra', bits: 5}),
  Object.freeze({name: 'distance-code', bits: 15}),
  Object.freeze({name: 'distance-extra', bits: 13}),
]);
export function fastAdmission(input, output, held) {
  const tests = [input >= FAST_LIMITS.input, output >= FAST_LIMITS.output, held < FAST_LIMITS.held];
  return {tests, fast: tests.every(Boolean)};
}
/** The dependency-preserving recurrence; grouping changes no store order. */
export function orderedMatch(seed, length, distance, group = 1) {
  if (!Number.isInteger(length) || length < 0 || !Number.isInteger(distance) || distance < 1 || distance > seed.length || !Number.isInteger(group) || group < 1)
    throw new RangeError('Invalid teaching match');
  const bytes = Array.from(seed), batches = [];
  let remaining = length;
  while (remaining) {
    const batch = [];
    for (let i = 0, count = Math.min(group, remaining); i < count; i++) {
      const source = bytes.length - distance;
      batch.push({source, target: bytes.length, byte: bytes[source]});
      bytes.push(bytes[source]);
      remaining--;
    }
    batches.push(batch);
  }
  return {output: bytes.join(''), batches};
}
