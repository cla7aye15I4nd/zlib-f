import ZlibF.Proof.«deflate.c.engine.block-protocol»
import ZlibF.Proof.«deflate.c.engine.ordinary-request-history»

/-! # Initialized histories of actual ordinary and BLOCK requests -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Ordinary and BLOCK requests share the same actually initialized
boundary, including all capacities and scalar/pointer refusal branches. -/
theorem DefaultFinishBoundary.request_with_block {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (boundary : DefaultFinishBoundary h r ds z d config) (flush : Int32)
    (flag : flush = Z_NO_FLUSH ∨ flush = Z_FINISH ∨ flush = Z_BLOCK) (buffers : StreamBuffers h r)
    (raw : z.next_out = .null ∨ ∃ ob oo, z.next_out = .ref (.blk ob) oo) :
    ∃ used produced rc after z' result,
      deflate (some r) flush h = .ok (rc, after) ∧
      DefaultFinishBoundary after r ds z' result config ∧ StreamBuffers after r ∧
      StreamAccounting z z' used produced ∧
      (rc = Z_OK ∨ rc = Z_STREAM_END ∨ rc = Z_STREAM_ERROR ∨ rc = Z_BUF_ERROR) := by
  rcases flag with ordinary | finish | block
  · exact boundary.request flush (Or.inl ordinary) buffers raw
  · exact boundary.request flush (Or.inr finish) buffers raw
  · subst flush
    obtain ⟨used, produced, rc, after, z', result, run, stateA, buffersA, accountA, allowed⟩ := boundary.block_total buffers raw
    exact ⟨used, produced, rc, after, z', result, run, stateA, buffersA, accountA,
      allowed.elim Or.inl (fun err => Or.inr (Or.inr err))⟩

/-- Actual histories admit exactly NO_FLUSH, FINISH, BLOCK and legal
rebuffering. No invariant or successful-return condition is a constructor
premise. Other flags, advanced operations and encoded history remain open. -/
inductive DefaultOrdinaryBlockRequests (r : ZStreamRef) (ds : Nat) : Heap → Heap → Prop
  | refl (h : Heap) : DefaultOrdinaryBlockRequests r ds h h
  | rebuffer {h middle after : Heap} : DefaultOrdinaryBlockRequests r ds h middle →
      Rebuffer middle after r → DefaultOrdinaryBlockRequests r ds h after
  | step {h middle after : Heap} {z : ZStream} {flush rc : Int32} :
      DefaultOrdinaryBlockRequests r ds h middle → r.get middle = some z → StreamBuffers middle r →
      (z.next_out = .null ∨ ∃ ob oo, z.next_out = .ref (.blk ob) oo) →
      (flush = Z_NO_FLUSH ∨ flush = Z_FINISH ∨ flush = Z_BLOCK) →
      C.run (deflate (some r) flush) middle = .ok (rc, after) → DefaultOrdinaryBlockRequests r ds h after

/-- The protocol is proved by induction over actual ordinary requests.
No invariant or callee contract is an assumed history-constructor field. -/
theorem DefaultOrdinaryBlockRequests.preserves {h after : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (boundary : DefaultFinishBoundary h r ds z d config) (history : DefaultOrdinaryBlockRequests r ds h after) :
    ∃ z' result, DefaultFinishBoundary after r ds z' result config := by
  induction history with
  | refl => exact ⟨z, d, boundary⟩
  | rebuffer _ edit ih =>
      obtain ⟨zm, dm, stateM⟩ := ih
      obtain ⟨zg, _getG, stateG⟩ := stateM.rebuffer edit
      exact ⟨zg, dm, stateG⟩
  | step _ getZ buffers raw flag actual ih =>
      obtain ⟨zm, dm, stateM⟩ := ih
      have stream : zm = _ := Option.some.inj (stateM.good.live.hz.symm.trans getZ)
      subst zm
      obtain ⟨_used, _produced, _rc, computed, z', result, run, stateA, _buffersA, _account, _allowed⟩ :=
        stateM.request_with_block _ flag buffers raw
      have heaps : computed = _ := (Prod.mk.inj (Except.ok.inj (run.symm.trans actual))).2
      subst computed
      exact ⟨z', result, stateA⟩

/-- Actual default initialization establishes the same boundary after
any finite ordinary request history, including real error returns. -/
theorem default_init_ordinary_block_request_histories {h : Heap} {r : ZStreamRef} {z : ZStream} {version : BPtr}
    (hf : Fresh h) (hu : Uniq h) (hg : LibraryGlobals h) (hz : r.get h = some z)
    (ha : DefaultOrNull z) (hv : VersionValue h version (some 49))
    (alloc : ∀ j, j < 5 → h.allocOk (h.nalloc + j) = true) :
    ∃ initialized config,
      C.run (deflateInit_ (some r) Z_DEFAULT_COMPRESSION version 112) h = .ok (Z_OK, initialized) ∧
      (∀ after, DefaultOrdinaryBlockRequests r h.nextBlk initialized after →
        ∃ z' result, DefaultFinishBoundary after r h.nextBlk z' result config) := by
  obtain ⟨initialized, zf, sf, run, boundary⟩ := default_initialization_finish_protocol hf hu hg hz ha hv alloc
  exact ⟨initialized, engineConfig sf, run, fun _ history => history.preserves boundary⟩

end Zlib.Deflate.Engine.Proofs
