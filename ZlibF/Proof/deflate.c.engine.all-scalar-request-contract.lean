import ZlibF.Proof.«deflate.c.engine.marker-request-contract»
import ZlibF.Proof.«deflate.c.engine.ordinary-block-request-contract»

/-! # The complete scoped public contract for every signed request -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Every signed default request has the full public safety/control
contract. All six valid flags and invalid-scalar refusals are included
on the same actual returned heap. Scope remains null/raw caller output. -/
theorem DefaultFinishBoundary.all_scalar_request_contract {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (boundary : DefaultFinishBoundary h r ds z d config) (flush : Int32)
    (buffers : StreamBuffers h r)
    (raw : z.next_out = .null ∨ ∃ ob oo, z.next_out = .ref (.blk ob) oo) :
    ∃ used written rc after z' result,
      C.run (deflate (some r) flush) h = .ok (rc, after) ∧
      DefaultFinishBoundary after r ds z' result config ∧ StreamBuffers after r ∧
      DGood after r ds z' result ∧ StreamAccounting z z' used written.length ∧
      Bytes after z.next_out written.length written ∧
      z'.total_in = z.total_in + UInt64.ofNat used ∧ z'.total_out = z.total_out + UInt64.ofNat written.length ∧
      (rc = Z_OK ∨ rc = Z_STREAM_END ∨ rc = Z_STREAM_ERROR ∨ rc = Z_BUF_ERROR) ∧
      (rc = Z_STREAM_ERROR ↔ flush.toInt < 0 ∨ 5 < flush.toInt ∨ z.next_out = .null ∨
        (z.next_in = .null ∧ z.avail_in ≠ 0) ∨ (d.status = FINISH_STATE ∧ flush ≠ Z_FINISH)) ∧
      (flush.toInt < 0 ∨ 5 < flush.toInt → rc = Z_STREAM_ERROR ∧ after = h) ∧
      (rc = Z_STREAM_END → flush = Z_FINISH ∧ result.status = FINISH_STATE ∧
        z'.avail_in = 0 ∧ result.pending = 0 ∧ result.bi_valid = 0) ∧
      Shape h after ∧ BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out, written.length⟩] ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  by_cases marker : flush = Z_PARTIAL_FLUSH ∨ flush = Z_SYNC_FLUSH ∨ flush = Z_FULL_FLUSH
  · exact boundary.marker_request_contract buffers raw flush marker
  · have supported : (flush = Z_NO_FLUSH ∨ flush = Z_FINISH ∨ flush = Z_BLOCK) ∨
        (flush.toInt < 0 ∨ 5 < flush.toInt) := by
      by_cases bad : flush.toInt < 0 ∨ 5 < flush.toInt
      · exact Or.inr bad
      · left
        have notOne : flush.toInt ≠ 1 := fun eq => marker (Or.inl (Int32.toInt_inj.mp eq))
        have notTwo : flush.toInt ≠ 2 := fun eq => marker (Or.inr (Or.inl (Int32.toInt_inj.mp eq)))
        have notThree : flush.toInt ≠ 3 := fun eq => marker (Or.inr (Or.inr (Int32.toInt_inj.mp eq)))
        simp only [← Int32.toInt_inj]
        change flush.toInt = 0 ∨ flush.toInt = 4 ∨ flush.toInt = 5
        omega
    exact boundary.scalar_request_contract_with_block flush supported buffers raw

end Zlib.Deflate.Engine.Proofs
