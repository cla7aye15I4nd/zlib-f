import ZlibF.Proof.«deflate.c.engine.public-request-counters»

/-! # Actual default initialization and ordinary histories establish counters -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Actual default initialization and every finite ordinary request
history establish the exact counter theorem for the next public call.
The scope is level 6, memory level 8, the zlib wrapper without a custom
header, NO_FLUSH/FINISH and null/raw-array output. Full heap frame and
encoded-output history remain separate obligations. -/
theorem default_init_ordinary_request_histories_with_counters {h : Heap} {r : ZStreamRef}
    {z : ZStream} {version : BPtr}
    (hf : Fresh h) (hu : Uniq h) (hg : LibraryGlobals h) (hz : r.get h = some z)
    (ha : DefaultOrNull z) (hv : VersionValue h version (some 49))
    (alloc : ∀ j, j < 5 → h.allocOk (h.nalloc + j) = true) :
    ∃ initialized config,
      C.run (deflateInit_ (some r) Z_DEFAULT_COMPRESSION version 112) h = .ok (Z_OK, initialized) ∧
      ∀ after, DefaultOrdinaryRequests r h.nextBlk initialized after →
        ∃ z' result, DefaultFinishBoundary after r h.nextBlk z' result config ∧
          ∀ flush, (flush = Z_NO_FLUSH ∨ flush = Z_FINISH) → StreamBuffers after r →
            (z'.next_out = .null ∨ ∃ ob oo, z'.next_out = .ref (.blk ob) oo) →
            ∃ used produced rc next z'' result',
              deflate (some r) flush after = .ok (rc, next) ∧
              DefaultFinishBoundary next r h.nextBlk z'' result' config ∧ StreamBuffers next r ∧
              StreamAccounting z' z'' used produced ∧ z''.total_in = z'.total_in + UInt64.ofNat used ∧
              z''.total_out = z'.total_out + UInt64.ofNat produced ∧
              (rc = Z_OK ∨ rc = Z_STREAM_END ∨ rc = Z_STREAM_ERROR ∨ rc = Z_BUF_ERROR) := by
  obtain ⟨initialized, zf, sf, run, boundary⟩ := default_initialization_finish_protocol hf hu hg hz ha hv alloc
  refine ⟨initialized, engineConfig sf, run, ?_⟩
  intro after history
  obtain ⟨z', result, state⟩ := history.preserves boundary
  exact ⟨z', result, state, fun flush flag buffers raw => state.request_with_counters flush flag buffers raw⟩

end Zlib.Deflate.Engine.Proofs
