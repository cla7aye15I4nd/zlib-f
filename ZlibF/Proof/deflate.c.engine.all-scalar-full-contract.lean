import ZlibF.Proof.«deflate.c.engine.all-scalar-request-contract»

/-! # Actual initialization and all signed histories establish full request contracts -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Actual default initialization and every finite signed-request/rebuffer
history establish the next request's full public safety/control contract.
Includes all six valid flags, invalid scalars, refusals, exact counters and
precise BufferFrame. Scope is level 6, memLevel 8, zlib without a custom
header and null/raw output. Encoded history and advanced APIs are separate. -/
theorem default_init_all_scalar_full_request_contract {h : Heap} {r : ZStreamRef}
    {z : ZStream} {version : BPtr}
    (hf : Fresh h) (hu : Uniq h) (hg : LibraryGlobals h) (hz : r.get h = some z)
    (ha : DefaultOrNull z) (hv : VersionValue h version (some 49))
    (alloc : ∀ j, j < 5 → h.allocOk (h.nalloc + j) = true) :
    ∃ initialized config,
      C.run (deflateInit_ (some r) Z_DEFAULT_COMPRESSION version 112) h = .ok (Z_OK, initialized) ∧
      ∀ after, DefaultScalarRequests r h.nextBlk initialized after →
        ∃ za da, DefaultFinishBoundary after r h.nextBlk za da config ∧
          ∀ flush, StreamBuffers after r →
            (za.next_out = .null ∨ ∃ ob oo, za.next_out = .ref (.blk ob) oo) →
            ∃ used written rc next zn dn,
              C.run (deflate (some r) flush) after = .ok (rc, next) ∧
              DefaultFinishBoundary next r h.nextBlk zn dn config ∧ StreamBuffers next r ∧
              DGood next r h.nextBlk zn dn ∧ StreamAccounting za zn used written.length ∧
              Bytes next za.next_out written.length written ∧
              zn.total_in = za.total_in + UInt64.ofNat used ∧ zn.total_out = za.total_out + UInt64.ofNat written.length ∧
              (rc = Z_OK ∨ rc = Z_STREAM_END ∨ rc = Z_STREAM_ERROR ∨ rc = Z_BUF_ERROR) ∧
              (rc = Z_STREAM_ERROR ↔ flush.toInt < 0 ∨ 5 < flush.toInt ∨ za.next_out = .null ∨
                (za.next_in = .null ∧ za.avail_in ≠ 0) ∨ (da.status = FINISH_STATE ∧ flush ≠ Z_FINISH)) ∧
              (flush.toInt < 0 ∨ 5 < flush.toInt → rc = Z_STREAM_ERROR ∧ next = after) ∧
              (rc = Z_STREAM_END → flush = Z_FINISH ∧ dn.status = FINISH_STATE ∧
                zn.avail_in = 0 ∧ dn.pending = 0 ∧ dn.bi_valid = 0) ∧
              Shape after next ∧ BufferFrame after next (fun b => StreamRoot r b ∨ DeflateOwned h.nextBlk da b) [⟨za.next_out, written.length⟩] ∧
              LiveChange after next (fun _ => False) (fun _ => False) ∧ next.nalloc = after.nalloc ∧ next.nextBlk = after.nextBlk := by
  obtain ⟨initialized, zf, sf, run, boundary⟩ := default_initialization_finish_protocol hf hu hg hz ha hv alloc
  refine ⟨initialized, engineConfig sf, run, ?_⟩
  intro after history
  obtain ⟨za, da, stateA⟩ := history.preserves boundary
  exact ⟨za, da, stateA, fun flush buffers raw => stateA.all_scalar_request_contract flush buffers raw⟩

end Zlib.Deflate.Engine.Proofs
