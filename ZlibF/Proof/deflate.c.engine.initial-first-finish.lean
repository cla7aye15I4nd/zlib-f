import ZlibF.Proof.«deflate.c.engine.public-first-finish-all»
import ZlibF.Proof.«deflate.c.engine.content-boundary»

/-! # Actual default initialization, legal caller edits and first FINISH -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Proofs.DefaultInit
set_option autoImplicit false

/-- Real default initialization establishes the first public FINISH proof
after any legal caller buffer replacement. No engine invariant or callee
contract is a caller premise. Every positive raw output capacity is
included. The resulting actual call also extends the public reachable
history. Allocation success is explicit here; initialization failure has
its separately proved public contract. This is the first call, not the
arbitrary-history or full output/frame correctness goal. -/
theorem default_init_then_first_finish {h : Heap} {r : ZStreamRef} {z : ZStream} {version : BPtr}
    (hf : Fresh h) (hu : Uniq h) (hg : LibraryGlobals h) (hz : r.get h = some z)
    (ha : DefaultOrNull z) (hv : VersionValue h version (some 49))
    (alloc : ∀ j, j < 5 → h.allocOk (h.nalloc + j) = true) :
    ∃ initialized,
      C.run (deflateInit_ (some r) Z_DEFAULT_COMPRESSION version 112) h = .ok (Z_OK, initialized) ∧
      StreamReachable .deflate initialized r ∧
      ∀ g, Rebuffer initialized g r → ∃ zg, r.get g = some zg ∧
        ∀ ob oo, zg.next_out = .ref (.blk ob) oo → 0 < zg.avail_out.toNat →
          StreamBuffers g r → (zg.avail_in ≠ 0 → zg.next_in ≠ .null) →
          ∃ used produced rc after z' result,
            C.run (deflate (some r) Z_FINISH) g = .ok (rc, after) ∧
            DGood after r h.nextBlk z' result ∧ StreamBuffers after r ∧ StreamAccounting zg z' used produced ∧
            StreamReachable .deflate after r ∧ (rc = Z_OK ∨ rc = Z_STREAM_END) ∧ result.bi_valid.toInt < 8 ∧
            (rc = Z_STREAM_END → result.status = FINISH_STATE ∧ result.wrap = -1 ∧
              z'.avail_in = 0 ∧ result.lookahead = 0 ∧ result.pending = 0 ∧ result.bi_valid.toInt = 0) := by
  obtain ⟨initialized, zf, sf, initRun, start, boundary, frontier, initial, reachable⟩ :=
    default_initialization_end_frontier (h := h) (r := r) (z := z)
      (level := Z_DEFAULT_COMPRESSION) (p := ZlibF.Spec.Public.Proofs.DeflateInit.settings 6) hf hu hg hz ha hv
      (by decide +kernel) alloc (fun _ => 0)
  have header := initial_no_header start initial
  have level : sf.level = 6 := by
    obtain ⟨zi, si, goodI, _allocI, _freeI, levelI, _rest⟩ := initial
    have states : si = sf := Option.some.inj (goodI.live.hs.symm.trans start.good.live.hs)
    rw [states] at levelI
    apply Int32.toInt_inj.mp
    exact levelI
  have memory : sf.lit_bufsize.toNat = 16384 := by
    have size := start.good.inv.hsize
    rw [start.hashBits] at size
    change sf.hash_size.toNat = 32768 at size
    have lit := start.good.inv.lit
    omega
  have publish : PublishReady sf := ⟨start.pending, start.pendingOut, by rw [start.bits]; decide⟩
  refine ⟨initialized, initRun, reachable, ?_⟩
  intro g edit
  obtain ⟨zg, getG, contentG⟩ := rebuffer_content_boundary boundary.toContentBoundary edit header
  obtain ⟨otherZ, startG⟩ := rebuffer_engine_start start edit header
  have streams : otherZ = zg := Option.some.inj (startG.good.live.hz.symm.trans getG)
  subst otherZ
  have stateG : StrategyBoundary g r h.nextBlk zg sf (fun _ => 0) 0 0 [] (engineConfig sf) :=
    ⟨contentG, rfl, boundary.clear, boundary.bits, boundary.strict, fun _ => publish⟩
  have endG : EndFrontier g sf := rebuffer_chains start.good edit frontier
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
  intro ob oo pointer output buffers valid
  obtain ⟨used, produced, rc, after, z', result, run, goodA, buffersA, accountA, allowed, bits, ended⟩ :=
    public_default_first_finish startG level stateG endG buffers pointer output memory valid
  have reachableA : StreamReachable .deflate after r := by
    apply StreamReachable.step (call := .deflate (some r) Z_FINISH) (value := rc) reachableG
    · exact ⟨rfl, rfl⟩
    · exact ⟨buffers, active⟩
    · simpa only [Call.execute, heapCall, run]
  exact ⟨used, produced, rc, after, z', result, run, goodA, buffersA, accountA, reachableA, allowed, bits, ended⟩

end Zlib.Deflate.Engine.Proofs
