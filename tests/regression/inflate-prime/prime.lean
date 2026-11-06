import ZlibF.Zlib.«inflate.c»
import ZlibF.Zlib.«zutil.c»

/-!
# Lean side of the inflatePrime boundary regression (tests/regression/inflate-prime)

It calls the actual translated `inflateInit2_`, `inflatePrime`, `inflateEnd` of
`ZlibF/Zlib/inflate.c.lean` — the module the proofs are about — and prints exactly
what `prime.c` prints: the case key, the return code, `hold` and `bits` after every
call. No specification, no formula that replaces the prime call. A runtime fault is
reported and makes the process exit nonzero.
-/

open C Zlib.Inflate Zlib.Zutil

/-- A stream with the default allocator fields, as the C driver sets them. -/
def newStream : M ZStreamPtr := do
  let p ← allocZStream
  stZStream p { ZStream.zeroed with
    zalloc := .fn "zcalloc", zfree := .fn "zcfree", «opaque» := .null }
  return p

/-- `hold` and `bits` of the state behind the stream, as `prime.c` reads them. -/
def holdBits (strm : ZStreamPtr) : M (UInt64 × UInt32) := do
  let z ← ldZStream strm
  let s ← ldInflateState (← castInflateState z.state)
  return (s.hold, s.bits)

/-- The observed state after a call: `rc=<rc> hold=<hold> bits=<bits>`. -/
def obs (rc : Int32) (strm : ZStreamPtr) : M String := do
  let (hold, bits) ← holdBits strm
  return s!"rc={rc.toInt} hold={hold.toNat} bits={bits.toNat}"

/-- One fresh-stream case: init, prime(bits, value), print, end. -/
def fresh (lines : Array String) (bits value : Int32) : M (Array String) := do
  let strm ← newStream
  let ver ← zlibVersion
  let rc ← inflateInit2_ strm (-15) ver 112
  if rc != Z_OK then ub "inflatePrime test init failed"
  let lines := lines.push s!"fresh b={bits.toInt} v={value.toInt} {← obs rc strm}"
  let rc ← inflatePrime strm bits value
  let lines := lines.push s!"prime b={bits.toInt} v={value.toInt} {← obs rc strm}"
  let ended ← inflateEnd strm
  if ended != Z_OK then ub "inflatePrime test end failed"
  freeZStream strm
  return lines

/-- The append sequence on one stream. -/
def seqCase (lines : Array String) : M (Array String) := do
  let strm ← newStream
  let ver ← zlibVersion
  let rc ← inflateInit2_ strm (-15) ver 112
  if rc != Z_OK then ub "inflatePrime test init failed"
  let lines := lines.push s!"seq init {← obs rc strm}"
  let calls : List (Int32 × Int32) := [(16, -1), (16, -1), (1, 0), (0, 5), (-1, 7)]
  let mut lines := lines
  for i in [0:calls.length] do
    let (b, v) := calls[i]!
    let rc ← inflatePrime strm b v
    lines := lines.push s!"seq step={i} call=prime({b.toInt},{v.toInt}) {← obs rc strm}"
  let ended ← inflateEnd strm
  if ended != Z_OK then ub "inflatePrime test end failed"
  freeZStream strm
  return lines

def bitv : List Int32 := [-2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]
def valv : List Int32 :=
  [Int32.ofInt (-2147483648), Int32.ofInt (-65537), -2, -1, 0, 1, 65535, 65536, 2147483647]

def program : M (Array String) := do
  let mut lines : Array String := #[]
  for b in bitv do
    for v in valv do
      lines ← fresh lines b v
  lines ← seqCase lines
  return lines

def main : IO UInt32 := do
  match C.run program Heap.empty with
  | .ok (lines, _) =>
    for l in lines do
      IO.println l
    return 0
  | .error f =>
    let d := match f with
      | .ub w => s!"ub {w}"
      | .outOfFuel => "outOfFuel"
    IO.eprintln s!"FAULT: {d}"
    return 1
