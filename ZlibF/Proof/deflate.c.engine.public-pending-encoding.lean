import ZlibF.Proof.«deflate.c.engine.raw-prefix»
import ZlibF.Proof.«deflate.c.engine.public-buffered-pending»

/-! # A real public output-full pending request retains the raw stream history -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Every accepted public flush scalar preserves independent raw encoding
when old pending bytes fill the caller output. This includes the actual
last-flush and retry stores and advanced private pending cursors. No input
is consumed. Header/trailer pending bytes have their separate encoding
phases; this theorem uses the established raw phase representation. -/
theorem public_pending_exhausted_raw_prefix {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List Symbol} {config : EngineConfig}
    {published : List UInt8} (flush : Int32)
    (boundary : BufferedBoundary h r ds z d input origin base xs config) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (flagLo : 0 ≤ flush.toInt) (flagHi : flush.toInt ≤ Z_BLOCK.toInt)
    (status : d.status = FINISH_STATE → flush = Z_FINISH) (output : 0 < z.avail_out.toNat)
    (enough : z.avail_out.toNat ≤ d.pending.toNat) (encoding : RawPrefix h d input base published) :
    ∃ after z' result written,
      deflate (some r) flush h = .ok (Z_OK, after) ∧
      BufferedBoundary after r ds z' result input origin base xs config ∧ StreamBuffers after r ∧
      StreamAccounting z z' 0 written.length ∧ Bytes after z.next_out written.length written ∧
      z'.avail_out = 0 ∧ result.last_flush = -1 ∧
      RawPrefix after result input base (published ++ written) := by
  obtain ⟨before, encoded, pending, wire, meaning⟩ := encoding
  obtain ⟨_pb, after, z', result, written, remaining, _base,
      run, stateA, buffersA, accountA, _sizes, _storage, outputA, lastA, _count,
      _bits, _fields, bytesA, pendingA, wireA⟩ :=
    public_pending_buffered_exhausted flush boundary buffers pointer inputValid flagLo flagHi status output enough pending
  have length := public_bytes_length bytesA
  have wireAll : ZlibF.Spec.bytesToBits (published ++ written) ++ remaining = encoded := by
    simp only [ZlibF.Spec.bytesToBits, List.flatMap_append, List.append_assoc] at wire wireA ⊢
    rw [wireA, wire]
  refine ⟨after, z', result, written, run, stateA, buffersA, ?_, ?_, outputA, lastA,
    remaining, encoded, pendingA, wireAll, meaning⟩
  · rw [length]; exact accountA
  · rw [length]; exact bytesA

end Zlib.Deflate.Engine.Proofs
