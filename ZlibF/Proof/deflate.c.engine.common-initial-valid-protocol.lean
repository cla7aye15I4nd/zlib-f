import ZlibF.Proof.«deflate.c.engine.common-initial-protocol»
import ZlibF.Proof.«deflate.c.engine.common-first-valid-header»

/-! # Actual common-level initialization starts with any legal flush flag -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Actual initialization and any legal one-byte first request establish
the common post-header invariant. In particular ordinary NO_FLUSH data
histories start without making a prior FINISH request. The actual flag
and actual run extend the same initialization's public reachable history. -/
theorem common_initialization_valid_split_boundary {h : Heap} {r : ZStreamRef} {z : ZStream}
    {version : BPtr} {level : Int32} {p : ZlibF.Spec.Api.DeflParams}
    (hf : Fresh h) (hu : Uniq h) (hg : LibraryGlobals h) (hz : r.get h = some z)
    (ha : DefaultOrNull z) (hv : VersionValue h version (some 49))
    (params : ZlibF.Spec.Api.deflInit? level.toInt 8 15 8 0 = some p)
    (low : 4 ≤ p.level) (high : p.level ≤ 9)
    (alloc : ∀ j, j < 5 → h.allocOk (h.nalloc + j) = true) :
    ∃ initialized zf sf,
      C.run (deflateInit_ (some r) level version 112) h = .ok (Z_OK, initialized) ∧
      EngineStart initialized r h.nextBlk zf sf ∧ DeflateInitial h initialized r p ∧
      ∀ g, Rebuffer initialized g r → ∃ zg, r.get g = some zg ∧
        ∀ ob oo, zg.next_out = .ref (.blk ob) oo → zg.avail_out = 1 → StreamBuffers g r →
          (zg.avail_in ≠ 0 → zg.next_in ≠ .null) →
          ∀ flush : Int32, 0 ≤ flush.toInt → flush.toInt ≤ 5 →
            ∃ after z' result,
              C.run (deflate (some r) flush) g = .ok (Z_OK, after) ∧
              CommonSlowFinishBoundary after r h.nextBlk z' result (engineConfig sf) ∧
              StreamBuffers after r ∧ StreamAccounting zg z' 0 1 := by
  obtain ⟨initialized, zf, sf, initRun, start, initial, first⟩ :=
    common_initialization_split_finish_boundary hf hu hg hz ha hv params low high alloc
  obtain ⟨otherHeap, otherRun, _otherInitial, reachable⟩ :=
    default_initialization_reachable hf hu hg hz ha hv params alloc
  have heaps : otherHeap = initialized := (Prod.mk.inj (Except.ok.inj (otherRun.symm.trans initRun))).2
  subst otherHeap
  have header := initial_no_header start initial
  refine ⟨initialized, zf, sf, initRun, start, initial, ?_⟩
  intro g edit
  obtain ⟨zg, getG, firstG⟩ := first g edit
  obtain ⟨otherZ, startG⟩ := rebuffer_engine_start start edit header
  have streams : otherZ = zg := Option.some.inj (startG.good.live.hz.symm.trans getG)
  subst otherZ
  refine ⟨zg, getG, ?_⟩
  intro ob oo pointer one buffers valid flush flagLow flagHigh
  obtain ⟨after, z', result, firstRun, stateA, buffersA, accountA⟩ :=
    firstG ob oo pointer one buffers valid
  have actual : deflate (some r) flush g = .ok (Z_OK, after) :=
    (first_common_valid_one_eq_finish startG buffers pointer one valid flush flagLow flagHigh).trans firstRun
  have reachableA : StreamReachable .deflate after r := by
    apply StreamReachable.step (call := .deflate (some r) flush) (value := Z_OK)
      (StreamReachable.rebuffer reachable edit (fun k => nomatch k)) (fun k => nomatch k)
    · exact ⟨rfl, rfl⟩
    · exact ⟨buffers, default_finish_active_header startG.good header⟩
    · simpa only [Call.execute, heapCall, actual]
  exact ⟨after, z', result, actual, { stateA with reachable := reachableA }, buffersA, accountA⟩

end Zlib.Deflate.Engine.Proofs
