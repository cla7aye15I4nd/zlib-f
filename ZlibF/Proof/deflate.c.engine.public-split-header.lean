import ZlibF.Proof.«deflate.c.engine.header-buffered»
import ZlibF.Proof.«deflate.c.engine.public-buffered-pending»

/-! # Two actual split-header calls with legal caller rebuffering -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Two actual one-byte FINISH calls, separated by a legal caller
rebuffer, finish the header while retaining the initialized boundary.
The second return is publication-ready even though caller output is
again exhausted. Both calls consume no input. -/
theorem split_header_rebuffer_pending {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {config : EngineConfig}
    (initial : EngineStart h r ds z d) (level : d.level = 6)
    (boundary : BufferedBoundary h r ds z d input origin base [] config) (header : d.gzhead = none)
    (buffers : StreamBuffers h r) (pointer : z.next_out = .ref (.blk ob) oo)
    (one : z.avail_out = 1) (valid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ after z' result,
      deflate (some r) Z_FINISH h = .ok (Z_OK, after) ∧
      BufferedBoundary after r ds z' result input origin base [] config ∧ StreamBuffers after r ∧
      StreamAccounting z z' 0 1 ∧
      ∀ g, Rebuffer after g r → ∃ zg,
        BufferedBoundary g r ds zg result input origin base [] config ∧
        ∀ ob2 oo2, zg.next_out = .ref (.blk ob2) oo2 → zg.avail_out = 1 → StreamBuffers g r →
          (zg.avail_in ≠ 0 → zg.next_in ≠ .null) →
          ∃ after2 z2 result2,
            deflate (some r) Z_FINISH g = .ok (Z_OK, after2) ∧
            BufferedBoundary after2 r ds z2 result2 input origin base [] config ∧ StreamBuffers after2 r ∧
            StreamAccounting zg z2 0 1 ∧ z2.avail_out = 0 ∧ result2.pending = 0 ∧
            PublishReady result2 ∧ result2.status = BUSY_STATE ∧ result2.last_flush = -1 := by
  obtain ⟨after, z', result, run, stateA, buffersA, accountA, _outA, pendingA, statusA, _lastA⟩ :=
    first_finish_one_buffered initial level boundary buffers pointer one valid
  have headerA : result.gzhead = none :=
    ((congrArg EngineConfig.header stateA.configuration).trans
      (congrArg EngineConfig.header boundary.configuration).symm).trans header
  obtain ⟨_w, _p, _q, pb, blocks⟩ := stateA.good.inv.blocks
  obtain ⟨buf, get, size⟩ := blocks.ba
  obtain ⟨po, cursor, bound⟩ := blocks.pout
  have originalPending := pending_bits_slice cursor get (by rw [size, ← blocks.psize]; exact bound)
  refine ⟨after, z', result, run, stateA, buffersA, accountA, ?_⟩
  intro g edit
  obtain ⟨zg, _getG, stateG⟩ := rebuffer_buffered_boundary stateA edit headerA
  have pendingG := rebuffer_pending_bits stateA.good edit originalPending
  refine ⟨zg, stateG, ?_⟩
  intro ob2 oo2 pointer2 one2 buffers2 valid2
  obtain ⟨_pb2, after2, z2, result2, _written, _remaining, _base2, second, state2, buffersB,
      accountB, _sizesB, _storageB, outB, lastB, pendingB, _lowB, fieldsB, _bytesB, _pendingB, _bitsB⟩ :=
    public_pending_buffered_exhausted Z_FINISH stateG buffers2 pointer2 valid2
      (by decide) (by decide) (fun _ => rfl) (by rw [one2]; decide)
      (by rw [one2, pendingA]; decide) pendingG
  have account : StreamAccounting zg z2 0 1 := by simpa only [one2, show ((1 : UInt32).toNat) = 1 from rfl] using accountB
  have empty : result2.pending = 0 := by
    apply UInt64.toNat_inj.mp
    rw [one2, pendingA] at pendingB
    change result2.pending.toNat = 0
    change result2.pending.toNat + 1 = 1 at pendingB
    omega
  have publish : PublishReady result2 := ⟨empty, state2.empty_cursor empty, state2.bits⟩
  have busy : result2.status = BUSY_STATE := by rw [fieldsB]; exact statusA
  exact ⟨after2, z2, result2, second, state2, buffersB, account, outB, empty, publish, busy, lastB⟩

end Zlib.Deflate.Engine.Proofs
