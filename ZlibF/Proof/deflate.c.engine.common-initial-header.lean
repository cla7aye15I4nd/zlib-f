import ZlibF.Proof.«deflate.c.engine.common-header-buffered»

/-! # Real initialization and first public FINISH at every admitted level -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- `int deflateInit_(z_streamp, int, const char *, int)` followed by
`int deflate(z_streamp, int)`.
Every level admitted by the standard entry, including its default alias,
establishes the same private boundary after a real split-header call.
The caller may legally replace buffers after initialization. No engine
invariant or execution contract is a premise. This first call consumes
no input and emits one byte; later compression is a separate obligation. -/
theorem common_initialization_then_split_finish {h : Heap} {r : ZStreamRef} {z : ZStream}
    {version : BPtr} {level : Int32} {p : ZlibF.Spec.Api.DeflParams}
    (hf : Fresh h) (hu : Uniq h) (hg : LibraryGlobals h) (hz : r.get h = some z)
    (ha : DefaultOrNull z) (hv : VersionValue h version (some 49))
    (params : ZlibF.Spec.Api.deflInit? level.toInt 8 15 8 0 = some p)
    (alloc : ∀ j, j < 5 → h.allocOk (h.nalloc + j) = true) :
    ∃ initialized zf sf,
      C.run (deflateInit_ (some r) level version 112) h = .ok (Z_OK, initialized) ∧
      EngineStart initialized r h.nextBlk zf sf ∧ DeflateInitial h initialized r p ∧
      StreamReachable .deflate initialized r ∧
      ∀ g, Rebuffer initialized g r → ∃ zg, r.get g = some zg ∧
        ∀ ob oo, zg.next_out = .ref (.blk ob) oo → zg.avail_out = 1 → StreamBuffers g r →
          (zg.avail_in ≠ 0 → zg.next_in ≠ .null) →
          ∃ after z' result,
            C.run (deflate (some r) Z_FINISH) g = .ok (Z_OK, after) ∧
            BufferedBoundary after r h.nextBlk z' result (fun _ => 0) 0 0 [] (engineConfig sf) ∧
            StreamBuffers after r ∧ StreamAccounting zg z' 0 1 ∧
            StreamReachable .deflate after r ∧ z'.avail_out = 0 ∧
            result.pending = 1 ∧ result.status = BUSY_STATE ∧ result.last_flush = -1 := by
  obtain ⟨initialized, zf, sf, initRun, start, strategy, frontier, initial, reachable⟩ :=
    default_initialization_end_frontier hf hu hg hz ha hv params alloc (fun _ => 0)
  have header := initial_no_header start initial
  have boundary := strategy.buffered frontier (fun _ => start.pendingOut)
  refine ⟨initialized, zf, sf, initRun, start, initial, reachable, ?_⟩
  intro g edit
  obtain ⟨zg, getG, stateG⟩ := rebuffer_buffered_boundary boundary edit header
  obtain ⟨otherZ, startG⟩ := rebuffer_engine_start start edit header
  have streams : otherZ = zg := Option.some.inj (startG.good.live.hz.symm.trans getG)
  subst otherZ
  have reachableG := StreamReachable.rebuffer reachable edit
  have active : ActiveHeader g r := by
    refine ⟨zg, getG, ?_, ?_⟩
    · intro i s kind _live
      rw [startG.good.live.zst] at kind
      cases kind
    · intro i s kind live
      have keys : h.nextBlk = i := by
        simpa only [startG.good.live.zst, Option.some.injEq, StateRef.deflate.injEq] using kind
      subst i
      have states : s = sf := Option.some.inj (live.symm.trans startG.good.live.hs)
      subst s
      exact ⟨fun _ => Or.inl header, fun _ _ known _ => by rw [header] at known; cases known⟩
  refine ⟨zg, getG, ?_⟩
  intro ob oo pointer one buffers valid
  obtain ⟨after, z', result, run, stateA, buffersA, accountA, emptyA, pendingA, statusA, lastA⟩ :=
    first_common_finish_one_buffered startG stateG buffers pointer one valid
  have reachableA : StreamReachable .deflate after r := by
    apply StreamReachable.step (call := .deflate (some r) Z_FINISH) (value := Z_OK) reachableG
    · exact ⟨rfl, rfl⟩
    · exact ⟨buffers, active⟩
    · simpa only [Call.execute, heapCall, run]
  exact ⟨after, z', result, run, stateA, buffersA, accountA, reachableA,
    emptyA, pendingA, statusA, lastA⟩

end Zlib.Deflate.Engine.Proofs
