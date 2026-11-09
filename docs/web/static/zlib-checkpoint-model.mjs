// Call-boundary snapshots for the selected raw ABABABAB example.
// Byte cells describe observations; they are not individual inflate calls.
export const CHECKPOINT_INPUT = Object.freeze([0x73, 0x74, 0x82, 0x40, 0x00]);
export const RESET_INPUT = Object.freeze([0x73, 0x76, 0x71, 0x76, 0x01, 0x00]);
export const checkpointSteps = Object.freeze({continue: 2, reset: 3, copy: 6});

function saved(id) {
  return {id, live: true, windowLive: true, mode: 'MATCH', remaining: 4,
    validHistory: 'ABAB', heldBits: 1, totalOut: 4, binding: 'prefix', input: 'suffix'};
}
function complete(stream, text, total) {
  stream.mode = 'DONE'; stream.remaining = null; stream.heldBits = 0;
  stream.validHistory = total === 8 ? 'ABABABAB' : text;
  stream.totalOut = total; stream.input = 'empty';
}
function end(stream) {
  stream.live = false; stream.windowLive = false;
}
export function checkpointSnapshot(action = 'continue', requestedStep = 0) {
  if (!Object.hasOwn(checkpointSteps, action)) throw new RangeError('Unknown checkpoint action');
  const step = Math.max(0, Math.min(checkpointSteps[action], Math.trunc(Number(requestedStep) || 0)));
  const a = saved('A');
  const result = {action, step, last: checkpointSteps[action], prefix: 'ABAB', a, b: null,
    outputA: '', outputB: '', inputKind: 'suffix', copiedAliases: false};
  if (action === 'continue') {
    if (step >= 1) a.binding = 'outputA';
    if (step >= 2) {result.outputA = 'ABAB'; complete(a, 'ABAB', 8);}
  } else if (action === 'reset') {
    if (step >= 1) {
      a.mode = 'HEAD'; a.remaining = null; a.heldBits = 0;
      a.validHistory = ''; a.totalOut = 0;
    }
    if (step >= 2) {a.binding = 'outputA'; a.input = 'fresh'; result.inputKind = 'fresh';}
    if (step >= 3) {result.outputA = 'CDCD'; complete(a, 'CDCD', 4);}
  } else {
    if (step >= 1) {result.b = saved('B'); result.copiedAliases = step === 1;}
    if (step >= 2) {a.binding = 'outputA'; result.b.binding = 'outputB';}
    if (step >= 3) {result.outputA = 'ABAB'; complete(a, 'ABAB', 8);}
    if (step >= 4) end(a);
    if (step >= 5) {result.outputB = 'ABAB'; complete(result.b, 'ABAB', 8);}
    if (step >= 6) end(result.b);
  }
  return result;
}
