import ZlibF.Proof.«deflate.c.engine.ordinary-block-request-contract»
import ZlibF.Proof.«deflate.c.engine.ordinary-block-history»

/-! # Full scoped public contracts after actual ordinary and BLOCK histories -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Actual default initialization and every finite NO_FLUSH/FINISH/BLOCK
history establish the next supported request's full public safety/control
contract. It includes precise BufferFrame, actual produced-byte slice,
wrapping counters and no allocation changes. The scope is level 6, memLevel
8, zlib wrapping and null/raw output. Other valid flags, embedded output,
advanced APIs and encoded-output correctness remain separate obligations. -/
theorem default_init_ordinary_block_full_request_contract {h : Heap} {r : ZStreamRef}
    {z : ZStream} {version : BPtr}
    (hf : Fresh h) (hu : Uniq h) (hg : LibraryGlobals h) (hz : r.get h = some z)
    (ha : DefaultOrNull z) (hv : VersionValue h version (some 49))
    (alloc : ∀ j, j < 5 → h.allocOk (h.nalloc + j) = true) :
    ∃ initialized config,
      C.run (deflateInit_ (some r) Z_DEFAULT_COMPRESSION version 112) h = .ok (Z_OK, initialized) ∧
      ∀ after, DefaultOrdinaryBlockRequests r h.nextBlk initialized after →
        ∃ za da, DefaultFinishBoundary after r h.nextBlk za da config ∧
          ∀ flush, (flush = Z_NO_FLUSH ∨ flush = Z_FINISH ∨ flush = Z_BLOCK) → StreamBuffers after r →
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
  exact ⟨za, da, stateA, fun flush flag buffers raw => stateA.request_contract_with_block flush flag buffers raw⟩

/-- The same actual mixed histories also establish every invalid signed
flush refusal on the unchanged heap. Invalid flushes are next-request
extensions; the history constructors remain the three supported flags. -/
theorem default_init_ordinary_block_full_scalar_contract {h : Heap} {r : ZStreamRef}
    {z : ZStream} {version : BPtr}
    (hf : Fresh h) (hu : Uniq h) (hg : LibraryGlobals h) (hz : r.get h = some z)
    (ha : DefaultOrNull z) (hv : VersionValue h version (some 49))
    (alloc : ∀ j, j < 5 → h.allocOk (h.nalloc + j) = true) :
    ∃ initialized config,
      C.run (deflateInit_ (some r) Z_DEFAULT_COMPRESSION version 112) h = .ok (Z_OK, initialized) ∧
      ∀ after, DefaultOrdinaryBlockRequests r h.nextBlk initialized after →
        ∃ za da, DefaultFinishBoundary after r h.nextBlk za da config ∧
          ∀ flush, ((flush = Z_NO_FLUSH ∨ flush = Z_FINISH ∨ flush = Z_BLOCK) ∨ (flush.toInt < 0 ∨ 5 < flush.toInt)) → StreamBuffers after r →
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
  exact ⟨za, da, stateA, fun flush flag buffers raw => stateA.scalar_request_contract_with_block flush flag buffers raw⟩

end Zlib.Deflate.Engine.Proofs
