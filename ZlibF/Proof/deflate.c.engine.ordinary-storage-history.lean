import ZlibF.Proof.«deflate.c.engine.public-request-full-storage»

/-! # Actual default initialization and ordinary histories yield output byte slices -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Actual default initialization and every finite ordinary request
history establish the exact produced-byte slice, counters and full storage frame for the next public call.
The scope is level 6, memory level 8, the zlib wrapper without a custom
header, NO_FLUSH/FINISH and null/raw-array output. Exact untouched output intervals and
encoded-output history remain separate obligations. -/
theorem default_init_ordinary_request_histories_with_full_storage {h : Heap} {r : ZStreamRef}
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
            ∃ used out rc next z'' result',
              deflate (some r) flush after = .ok (rc, next) ∧
              DefaultFinishBoundary next r h.nextBlk z'' result' config ∧ StreamBuffers next r ∧
              StreamAccounting z' z'' used out.length ∧ Bytes next z'.next_out out.length out ∧ z''.total_in = z'.total_in + UInt64.ofNat used ∧
              z''.total_out = z'.total_out + UInt64.ofNat out.length ∧
              Shape after next ∧
              Frame after next (fun b => StreamRoot r b ∨ DeflateOwned h.nextBlk result b ∨ ByteRoot z'.next_out b) ∧
              LiveChange after next (fun _ => False) (fun _ => False) ∧ next.nalloc = after.nalloc ∧ next.nextBlk = after.nextBlk ∧
              (rc = Z_OK ∨ rc = Z_STREAM_END ∨ rc = Z_STREAM_ERROR ∨ rc = Z_BUF_ERROR) := by
  obtain ⟨initialized, zf, sf, run, boundary⟩ := default_initialization_finish_protocol hf hu hg hz ha hv alloc
  refine ⟨initialized, engineConfig sf, run, ?_⟩
  intro after history
  obtain ⟨z', result, state⟩ := history.preserves boundary
  exact ⟨z', result, state, fun flush flag buffers raw => state.request_with_full_storage flush flag buffers raw⟩

end Zlib.Deflate.Engine.Proofs
