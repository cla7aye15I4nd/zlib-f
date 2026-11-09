import {FIXED_FIELDS, writerTrace} from './zlib-writer-model.mjs';

export const ROUNDTRIP_INPUT = 'ABABABAB';
export const ROUNDTRIP_BYTES = Object.freeze([0x73, 0x74, 0x82, 0x40, 0x00]);
export const ROUNDTRIP_LAST = 16;
let offset = 0;
export const ROUNDTRIP_FIELDS = Object.freeze(FIXED_FIELDS.map(field => {
  const start = offset;
  offset += field.width;
  return Object.freeze({...field, start, end: offset,
    bits: Array.from({length: field.width}, (_, bit) => (field.value >>> bit) & 1)});
}));
const encoded = writerTrace().at(-1).bytes;
if (encoded.some((byte, i) => byte !== ROUNDTRIP_BYTES[i]) || encoded.length !== 5)
  throw new Error('Round-trip fields disagree with the byte trace');

// Format positions, not C call counts or the engine's read-ahead cursor.
export function roundtripState(step) {
  if (!Number.isInteger(step) || step < 0 || step > ROUNDTRIP_LAST)
    throw new RangeError('Invalid round-trip step');
  const encoding = step >= 2 && step <= 7;
  const field = encoding ? step - 2 : step === 8 ? 1 : step === 9 ? 2
    : step >= 10 && step <= 15 ? 4 : step === 16 ? 5 : -1;
  const outputLength = step < 8 ? 0 : Math.min(8, step - 7);
  let output = '';
  for (let i = 0; i < outputLength; i++) output += i < 2 ? ROUNDTRIP_INPUT[i] : output[i - 2];
  return Object.freeze({step, field, encoding, output,
    encodedBits: step < 2 ? 0 : step >= 7 ? 38 : ROUNDTRIP_FIELDS[step - 2].end,
    decodedBits: step < 8 ? 0 : step === 8 ? 11 : step === 9 ? 19 : step === 16 ? 38 : 31,
    source: step >= 10 && step <= 15 ? outputLength - 3 : -1,
    target: step >= 10 && step <= 15 ? outputLength - 1 : -1,
    remaining: step < 10 ? 6 : Math.max(0, 8 - outputLength),
    complete: step === ROUNDTRIP_LAST,
    prefixCorrect: output === ROUNDTRIP_INPUT.slice(0, outputLength)});
}
