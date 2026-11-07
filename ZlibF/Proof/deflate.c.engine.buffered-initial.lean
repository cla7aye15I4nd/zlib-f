import ZlibF.Proof.«deflate.c.engine.buffered-boundary»

/-! # Actual default initialization establishes the public buffered boundary -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Successful actual default-parameter initialization establishes the
caller-independent boundary, including the empty-cursor phase. Every
legal caller rebuffering retains it on an actual reachable heap. The
universal Init2 theorem and any engine invariant are not premises. -/
theorem default_initialization_buffered_boundary {h : Heap} {r : ZStreamRef} {z : ZStream}
    {version : BPtr} {level : Int32} {p : ZlibF.Spec.Api.DeflParams}
    (hf : Fresh h) (hu : Uniq h) (hg : LibraryGlobals h) (hz : r.get h = some z)
    (ha : DefaultOrNull z) (hv : VersionValue h version (some 49))
    (params : ZlibF.Spec.Api.deflInit? level.toInt 8 15 8 0 = some p)
    (alloc : ∀ j, j < 5 → h.allocOk (h.nalloc + j) = true) (input : Nat → UInt8) :
    ∃ after zf sf,
      C.run (deflateInit_ (some r) level version 112) h = .ok (Z_OK, after) ∧
      BufferedBoundary after r h.nextBlk zf sf input 0 0 [] (engineConfig sf) ∧
      StreamReachable .deflate after r ∧
      ∀ g, Rebuffer after g r → ∃ zg,
        BufferedBoundary g r h.nextBlk zg sf input 0 0 [] (engineConfig sf) ∧ StreamReachable .deflate g r := by
  obtain ⟨after, zf, sf, run, start, boundary, frontier, initial, reachable⟩ :=
    default_initialization_end_frontier hf hu hg hz ha hv params alloc input
  have buffered := boundary.buffered frontier (fun _ => start.pendingOut)
  refine ⟨after, zf, sf, run, buffered, reachable, ?_⟩
  intro g edit
  obtain ⟨zg, _getG, bufferedG⟩ := rebuffer_buffered_boundary buffered edit (initial_no_header start initial)
  exact ⟨zg, bufferedG, StreamReachable.rebuffer reachable edit⟩

end Zlib.Deflate.Engine.Proofs
