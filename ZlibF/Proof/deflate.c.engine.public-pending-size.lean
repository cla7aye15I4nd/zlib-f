import ZlibF.Proof.«deflate.c.engine.public-finish-pending-entry»
import ZlibF.Proof.«deflate.c.engine.pending-size»

/-! # The actual pending-only public return preserves its size history -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The real top pending branch can exhaust output and return OK even
when that drain removes the last pending byte. Its exact output potential
and current block facts are retained without claiming that it reached
the strategy or acknowledged END. All valid signed flush scalars and
every initialized buffered phase at this cutpoint are covered. -/
theorem public_pending_exhausted_byte_potential {h : Heap} {r : ZStreamRef}
    {ds ob oo origin base : Nat} {z : ZStream} {d : DeflateState}
    {input : Nat → UInt8} {xs : List Symbol} {config : EngineConfig} (flush : Int32)
    (boundary : BufferedBoundary h r ds z d input origin base xs config) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (valid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (flagLo : 0 ≤ flush.toInt) (flagHi : flush.toInt ≤ Z_BLOCK.toInt)
    (status : d.status = FINISH_STATE → flush = Z_FINISH) (positive : 0 < z.avail_out.toNat)
    (enough : z.avail_out.toNat ≤ d.pending.toNat) :
    ∃ after z' result,
      deflate (some r) flush h = .ok (Z_OK, after) ∧
      BufferedBoundary after r ds z' result input origin base xs config ∧ StreamBuffers after r ∧
      StreamAccounting z z' 0 z.avail_out.toNat ∧ z'.avail_out = 0 ∧ fillEnd result = fillEnd d ∧
      z.avail_out.toNat + result.pending.toNat + (result.bi_valid.toInt.toNat + 7) / 8 =
        d.pending.toNat + (d.bi_valid.toInt.toNat + 7) / 8 ∧
      (ShortCandidateQuality d → ShortCandidateQuality result) ∧
      (StoredSourceFloor d → StoredSourceFloor result) := by
  obtain ⟨before, pending⟩ := good_pending_bits boundary.good
  obtain ⟨_pb, after, z', result, _written, _remaining, _base, run, stateA, buffersA,
    accountA, _sizes, _storage, zeroA, _lastA, countA, _bitsA, fields, _bytes, _pendingA, _wire⟩ :=
    public_pending_buffered_exhausted flush boundary buffers pointer valid flagLo flagHi status positive enough pending
  have bits : result.bi_valid = d.bi_valid := by rw [fields]
  refine ⟨after, z', result, run, stateA, buffersA, accountA, zeroA, by rw [fields]; rfl,
    by rw [bits]; omega, ?_, ?_⟩
  · intro candidate
    rw [fields]
    exact candidate
  · intro floor
    rw [fields]
    exact floor

end Zlib.Deflate.Engine.Proofs
