import ZlibF.Proof.«deflate.c.engine.ordinary-block-history»

/-! # Actual default initialization closes ordinary and BLOCK request histories -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Actual default initialization, every finite NO_FLUSH/FINISH/BLOCK
history and legal rebuffering retain the same boundary and establish that
the next supported request returns. All capacities and refusal cases are
included for null/raw-array output, level 6, memLevel 8 and the zlib wrapper.
Other valid flags, embedded output, advanced APIs and encoded correctness
remain open. This supporting theorem does not replace Goal.deflate. -/
theorem default_init_ordinary_block_next_request {h : Heap} {r : ZStreamRef} {z : ZStream} {version : BPtr}
    (hf : Fresh h) (hu : Uniq h) (hg : LibraryGlobals h) (hz : r.get h = some z)
    (ha : DefaultOrNull z) (hv : VersionValue h version (some 49))
    (alloc : ∀ j, j < 5 → h.allocOk (h.nalloc + j) = true) :
    ∃ initialized config,
      C.run (deflateInit_ (some r) Z_DEFAULT_COMPRESSION version 112) h = .ok (Z_OK, initialized) ∧
      ∀ after, DefaultOrdinaryBlockRequests r h.nextBlk initialized after →
        ∃ z' result, DefaultFinishBoundary after r h.nextBlk z' result config ∧
          ∀ flush, (flush = Z_NO_FLUSH ∨ flush = Z_FINISH ∨ flush = Z_BLOCK) → StreamBuffers after r →
            (z'.next_out = .null ∨ ∃ ob oo, z'.next_out = .ref (.blk ob) oo) →
            ∃ used produced rc next z'' result',
              deflate (some r) flush after = .ok (rc, next) ∧
              DefaultFinishBoundary next r h.nextBlk z'' result' config ∧ StreamBuffers next r ∧
              StreamAccounting z' z'' used produced ∧
              (rc = Z_OK ∨ rc = Z_STREAM_END ∨ rc = Z_STREAM_ERROR ∨ rc = Z_BUF_ERROR) := by
  obtain ⟨initialized, zf, sf, run, boundary⟩ := default_initialization_finish_protocol hf hu hg hz ha hv alloc
  refine ⟨initialized, engineConfig sf, run, ?_⟩
  intro after history
  obtain ⟨z', result, state⟩ := history.preserves boundary
  exact ⟨z', result, state, fun flush flag buffers raw => state.request_with_block flush flag buffers raw⟩

end Zlib.Deflate.Engine.Proofs
