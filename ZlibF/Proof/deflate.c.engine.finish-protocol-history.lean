import ZlibF.Proof.«deflate.c.engine.finish-protocol-initial»

/-! # Arbitrarily long accepted default FINISH histories

The relation below records actual runs and legal caller edits, not callee
specifications. The initialized boundary is derived and preserved by induction.
Other flush flags, refusal cases and advanced operations remain separate.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Actual accepted FINISH histories at a fixed initialized state object. -/
inductive DefaultFinishSteps (r : ZStreamRef) (ds : Nat) : Heap → Heap → Prop
  | refl (h : Heap) : DefaultFinishSteps r ds h h
  | rebuffer {h middle after : Heap} : DefaultFinishSteps r ds h middle →
      Rebuffer middle after r → DefaultFinishSteps r ds h after
  | finish {h middle after : Heap} {z : ZStream} {d : DeflateState} {ob oo : Nat} {rc : Int32} :
      DefaultFinishSteps r ds h middle → r.get middle = some z → middle.dstates ds = some d →
      StreamBuffers middle r → z.next_out = .ref (.blk ob) oo → 0 < z.avail_out.toNat →
      (z.avail_in ≠ 0 → z.next_in ≠ .null) → (d.status = FINISH_STATE → z.avail_in = 0) →
      C.run (deflate (some r) Z_FINISH) middle = .ok (rc, after) → DefaultFinishSteps r ds h after

/-- The same boundary holds after any finite accepted history. Each
induction step invokes its proved actual execution and matches its heap to
the recorded actual run. No invariant is a history-constructor premise. -/
theorem DefaultFinishSteps.preserves {h after : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (boundary : DefaultFinishBoundary h r ds z d config) (history : DefaultFinishSteps r ds h after) :
    ∃ z' result, DefaultFinishBoundary after r ds z' result config := by
  induction history with
  | refl => exact ⟨z, d, boundary⟩
  | rebuffer _ edit ih =>
      obtain ⟨zm, dm, stateM⟩ := ih
      obtain ⟨zg, _getG, stateG⟩ := stateM.rebuffer edit
      exact ⟨zg, dm, stateG⟩
  | finish _ getZ getD buffers pointer output valid accepted actual ih =>
      obtain ⟨zm, dm, stateM⟩ := ih
      have stream : zm = _ := Option.some.inj (stateM.good.live.hz.symm.trans getZ)
      have state : dm = _ := Option.some.inj (stateM.good.live.hs.symm.trans getD)
      subst zm dm
      obtain ⟨_used, _produced, _rc, computed, z', result, run, stateA, _buffersA, _account, _allowed, _ended⟩ :=
        stateM.finish buffers pointer output valid accepted
      have heaps : computed = _ := (Prod.mk.inj (Except.ok.inj (run.symm.trans actual))).2
      subst computed
      exact ⟨z', result, stateA⟩

/-- Actual default initialization establishes the invariant for every
finite accepted FINISH history, including arbitrary legal rebuffering. -/
theorem default_init_finish_histories {h : Heap} {r : ZStreamRef} {z : ZStream} {version : BPtr}
    (hf : Fresh h) (hu : Uniq h) (hg : LibraryGlobals h) (hz : r.get h = some z)
    (ha : DefaultOrNull z) (hv : VersionValue h version (some 49))
    (alloc : ∀ j, j < 5 → h.allocOk (h.nalloc + j) = true) :
    ∃ initialized config,
      C.run (deflateInit_ (some r) Z_DEFAULT_COMPRESSION version 112) h = .ok (Z_OK, initialized) ∧
      (∀ after, DefaultFinishSteps r h.nextBlk initialized after →
        ∃ z' result, DefaultFinishBoundary after r h.nextBlk z' result config) := by
  obtain ⟨initialized, zf, sf, run, boundary⟩ := default_initialization_finish_protocol hf hu hg hz ha hv alloc
  exact ⟨initialized, engineConfig sf, run, fun _ history => history.preserves boundary⟩

end Zlib.Deflate.Engine.Proofs
