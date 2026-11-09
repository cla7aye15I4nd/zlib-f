import ZlibF.Proof.«compress.c.chunks»

/-! # Connecting chunk refills to the actual compress2_z loop

The equations below unfold the translated function itself. They assume no
callee contract and make no whole-call safety or termination assertion.
-/

namespace ZlibF.Spec.Public.Proofs.CompressLoop
open C Zlib.Compress Zlib.Deflate
open ZlibF.Spec.Public.Proofs.CompressChunks
set_option autoImplicit false

abbrev Locals := Int32 × UInt64 × UInt64

/-- The body extracted from the real compress2_z cdoWhile. The full-function
unfolding theorem below checks this extraction by definitional equality. -/
def body (strm : ZStreamPtr) : Locals → M Locals :=
  let max : UInt32 := 0xffffffff
  fun ((_, left, sourceLen) : Int32 × UInt64 × UInt64) => do
      let mut left := left
      let mut sourceLen := sourceLen
      -- if (stream.avail_out == 0) { stream.avail_out = left > (z_size_t)max ? max : (uInt)left; left -= stream.avail_out; }
      if (← zrd strm (·.avail_out)) == 0 then
        let ao : UInt32 := if left > max.toUInt64 then max else left.toUInt32
        zwr strm (fun z => { z with avail_out := ao })
        left := left - ao.toUInt64
      -- if (stream.avail_in == 0) { stream.avail_in = sourceLen > (z_size_t)max ? max : (uInt)sourceLen; sourceLen -= stream.avail_in; }
      if (← zrd strm (·.avail_in)) == 0 then
        let ai : UInt32 := if sourceLen > max.toUInt64 then max else sourceLen.toUInt32
        zwr strm (fun z => { z with avail_in := ai })
        sourceLen := sourceLen - ai.toUInt64
      -- err = deflate(&stream, sourceLen ? Z_NO_FLUSH : Z_FINISH);
      let err ← deflate strm (if sourceLen != 0 then Z_NO_FLUSH else Z_FINISH)
      pure (err, left, sourceLen)

def condition (st : Locals) : M (Bool × Locals) := pure (st.1 == Z_OK, st)

def loop (strm : ZStreamPtr) (st : Locals) : M Locals :=
  cdoWhile (body strm) condition st

/-- `int compress2_z(Bytef *dest, z_size_t *destLen, const Bytef *source,
z_size_t sourceLen, int level)`.
Unconditional equality with the actual translated program, retaining its
entry checks, real init, real loop, pointer subtraction, real end and cleanup. -/
theorem compress2_z_unfold (dest : BPtr) (destLen : Option UInt64)
    (source : BPtr) (sourceLen : UInt64) (level : Int32) :
    compress2_z dest destLen source sourceLen level =
    do
    -- if ((sourceLen > 0 && source == Z_NULL) || destLen == Z_NULL || (*destLen > 0 && dest == Z_NULL)) return Z_STREAM_ERROR;
    let some dl := destLen | return (Z_STREAM_ERROR, none)
    if (sourceLen > 0 && source == .null) || (dl > 0 && dest == .null) then return (Z_STREAM_ERROR, destLen)
    -- left = *destLen; *destLen = 0;
    let mut left : UInt64 := dl
    -- z_stream stream;  stream.zalloc = 0; stream.zfree = 0; stream.opaque = 0;
    let strm ← allocLocalZ
    zwr strm (fun z => { z with zalloc := FnPtr.null, zfree := FnPtr.null, «opaque» := .null })
    -- err = deflateInit(&stream, level); if (err != Z_OK) return err;
    let ver ← Zlib.Zutil.zlibVersion
    let mut err ← deflateInit_ strm level ver sizeof_z_stream
    if err != Z_OK then
      freeZStream strm
      return (err, some 0)
    -- stream.next_out = dest; stream.avail_out = 0; stream.next_in = source; stream.avail_in = 0;
    zwr strm (fun z => { z with next_out := dest, avail_out := 0, next_in := source, avail_in := 0 })
    let mut sourceLen := sourceLen
    -- do { ... } while (err == Z_OK);
    let (e, l, sl) ← loop strm
      (err, left, sourceLen)
    err := e
    left := l
    sourceLen := sl
    -- *destLen = (z_size_t)(stream.next_out - dest);
    let no ← zrd strm (·.next_out)
    let n ← ptrDiff no dest
    -- deflateEnd(&stream);
    let _ ← deflateEnd strm
    freeZStream strm
    -- return err == Z_STREAM_END ? Z_OK : err;
    return (if err == Z_STREAM_END then Z_OK else err, some n.toUInt64)
   := by
  rfl

/-- The actual do-while unfolds once, preserving the real remaining fuel.
The recursive call here is the same translated body, not a replacement loop. -/
theorem loop_unfold (strm : ZStreamPtr) (st : Locals) :
    loop strm st = (do
      let next ← body strm st
      if next.1 == Z_OK then
        cdoWhile.go (body strm) condition (fuel - 1) next
      else pure next) := by
  rfl

/-- The exact heap and still-unoffered lengths immediately before the
actual deflate invocation in one extracted body. -/
def prepare (h : Heap) (slot : Nat) (z : ZStream) (left sourceLen : UInt64) :
    UInt64 × UInt64 × Heap :=
  let outEmpty := z.avail_out == 0
  let zOut := if outEmpty then { z with avail_out := chunk left } else z
  let outHeap := if outEmpty then { h with streams := upd h.streams slot (some zOut) } else h
  let nextLeft := if outEmpty then left - (chunk left).toUInt64 else left
  if z.avail_in == 0 then
    (nextLeft, sourceLen - (chunk sourceLen).toUInt64,
      { outHeap with streams := upd outHeap.streams slot (some { zOut with avail_in := chunk sourceLen }) })
  else (nextLeft, sourceLen, outHeap)

/-- `int compress2_z(Bytef *dest, z_size_t *destLen, const Bytef *source,
z_size_t sourceLen, int level)`.
All four refill/no-refill cases of the body extracted from the actual
compressor reduce to the actual deflate invocation on the exact prepared
heap. This equation leaves the real callee result untouched, including faults. -/
theorem body_prepare (h : Heap) (slot : Nat) (z : ZStream) (old : Int32)
    (left sourceLen : UInt64) (get : h.streams slot = some z) :
    body (some (.tab slot)) (old, left, sourceLen) h =
      let (nextLeft, nextSourceLen, prepared) := prepare h slot z left sourceLen
      (do
        let err ← deflate (some (.tab slot)) (if nextSourceLen != 0 then Z_NO_FLUSH else Z_FINISH)
        pure (err, nextLeft, nextSourceLen)) prepared := by
  by_cases outEmpty : z.avail_out = 0 <;>
    by_cases inEmpty : z.avail_in = 0 <;>
    simp [body, prepare, chunk, zrd, zwr, ldZStream, stZStream,
      ZStreamRef.get, ZStreamRef.put, ZStreamRef.isRo, get, outEmpty, inEmpty]

/-- The first iteration of the real loop, with the real engine's success
or fault result and the exact remaining-fuel recursion both exposed. -/
theorem loop_first_call (h : Heap) (slot : Nat) (z : ZStream) (old : Int32)
    (left sourceLen : UInt64) (get : h.streams slot = some z) :
    loop (some (.tab slot)) (old, left, sourceLen) h =
      let (nextLeft, nextSourceLen, prepared) := prepare h slot z left sourceLen
      match deflate (some (.tab slot)) (if nextSourceLen != 0 then Z_NO_FLUSH else Z_FINISH) prepared with
      | .error e => .error e
      | .ok (err, after) =>
        if err == Z_OK then
          cdoWhile.go (body (some (.tab slot))) condition (fuel - 1) (err, nextLeft, nextSourceLen) after
        else .ok ((err, nextLeft, nextSourceLen), after) := by
  rw [loop_unfold]
  simp only [bind_app, body_prepare h slot z old left sourceLen get]
  rcases prepare h slot z left sourceLen with ⟨a, b, prepared⟩
  cases run : deflate (some (.tab slot)) (if b != 0 then Z_NO_FLUSH else Z_FINISH) prepared with
  | error e => rfl
  | ok pair =>
    rcases pair with ⟨err, after⟩
    by_cases good : err = Z_OK <;> simp [good]

/-- The stream that the real loop presents to the engine after refills. -/
def preparedStream (z : ZStream) (left sourceLen : UInt64) : ZStream :=
  { z with
    avail_out := if z.avail_out == 0 then chunk left else z.avail_out
    avail_in := if z.avail_in == 0 then chunk sourceLen else z.avail_in }

/-- The heap passed to the real deflate call contains exactly this refilled
stream. This identifies the stream used by the count equations below. -/
theorem prepare_get (h : Heap) (slot : Nat) (z : ZStream) (left sourceLen : UInt64)
    (get : h.streams slot = some z) :
    (prepare h slot z left sourceLen).2.2.streams slot = some (preparedStream z left sourceLen) := by
  by_cases outEmpty : z.avail_out = 0 <;>
    by_cases inEmpty : z.avail_in = 0 <;>
    simp [prepare, preparedStream, get, outEmpty, inEmpty]

/-- `int compress2_z(Bytef *dest, z_size_t *destLen, const Bytef *source,
z_size_t sourceLen, int level)`.
Immediately before each actual engine call, refill preserves both budgets:
still-unoffered bytes plus available bytes. Once a proved engine step is
connected, its exact used/written counts can decrease these same budgets. -/
theorem prepare_counts (h : Heap) (slot : Nat) (z : ZStream) (left sourceLen : UInt64) :
    let (nextLeft, nextSourceLen, _) := prepare h slot z left sourceLen
    let next := preparedStream z left sourceLen
    nextLeft.toNat + next.avail_out.toNat = left.toNat + z.avail_out.toNat ∧
      nextSourceLen.toNat + next.avail_in.toNat = sourceLen.toNat + z.avail_in.toNat := by
  have outCount := (chunk_accounting left).2
  have inCount := (chunk_accounting sourceLen).2
  by_cases outEmpty : z.avail_out = 0 <;>
    by_cases inEmpty : z.avail_in = 0 <;>
    simp [prepare, preparedStream, outEmpty, inEmpty] <;> omega

/-- If the actual loop selects NO_FLUSH, it has offered nonempty input.
This discharges the nonempty-input guard in the requested engine progress
interface, instead of requiring the caller to assume it. -/
theorem prepare_no_flush_input (h : Heap) (slot : Nat) (z : ZStream) (left sourceLen : UInt64)
    (ordinary : (prepare h slot z left sourceLen).2.1 ≠ 0) :
    (preparedStream z left sourceLen).avail_in ≠ 0 := by
  have value := chunk_value sourceLen
  by_cases empty : z.avail_in = 0
  · simp only [prepare, empty, beq_self_eq_true, ite_true] at ordinary
    intro zero
    have small : (chunk sourceLen).toNat = 0 := by
      simpa [preparedStream, empty] using congrArg UInt32.toNat zero
    have srcZero : sourceLen = 0 := UInt64.toNat_inj.mp (by change sourceLen.toNat = 0; omega)
    apply ordinary
    simp [srcZero, chunk]
  · simp [preparedStream, empty]

/-- A nonzero remaining output budget gives positive actual avail_out on
entry to the engine, whether or not this iteration refilled that field. -/
theorem prepare_output_positive (z : ZStream) (left sourceLen : UInt64)
    (room : 0 < left.toNat + z.avail_out.toNat) :
    0 < (preparedStream z left sourceLen).avail_out.toNat := by
  have value := chunk_value left
  by_cases empty : z.avail_out = 0
  · simp only [preparedStream, empty, beq_self_eq_true, ite_true]
    have room' : 0 < left.toNat := by simpa [empty] using room
    omega
  · have nz : z.avail_out.toNat ≠ 0 := fun e => empty (UInt32.toNat_inj.mp e)
    simp only [preparedStream, beq_iff_eq, empty, ite_false]
    omega

end ZlibF.Spec.Public.Proofs.CompressLoop
