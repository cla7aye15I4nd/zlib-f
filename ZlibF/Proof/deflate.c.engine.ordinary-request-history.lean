import ZlibF.Proof.«deflate.c.engine.public-no-flush-total»
import ZlibF.Proof.«deflate.c.engine.public-finish-total»
import ZlibF.Proof.«deflate.c.engine.finish-protocol-initial»

/-! # Initialized ordinary request histories include actual error returns -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Every ordinary NO_FLUSH or FINISH request, including refusals,
returns and preserves the same actually initialized protocol. -/
theorem DefaultFinishBoundary.request {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (boundary : DefaultFinishBoundary h r ds z d config) (flush : Int32)
    (flag : flush = Z_NO_FLUSH ∨ flush = Z_FINISH) (buffers : StreamBuffers h r)
    (raw : z.next_out = .null ∨ ∃ ob oo, z.next_out = .ref (.blk ob) oo) :
    ∃ used produced rc after z' result,
      deflate (some r) flush h = .ok (rc, after) ∧
      DefaultFinishBoundary after r ds z' result config ∧ StreamBuffers after r ∧
      StreamAccounting z z' used produced ∧
      (rc = Z_OK ∨ rc = Z_STREAM_END ∨ rc = Z_STREAM_ERROR ∨ rc = Z_BUF_ERROR) := by
  rcases flag with rfl | rfl
  · obtain ⟨used, produced, rc, after, z', result, run, stateA, buffersA, accountA, allowed⟩ := boundary.no_flush_total buffers raw
    refine ⟨used, produced, rc, after, z', result, run, stateA, buffersA, accountA, ?_⟩
    rcases allowed with ok | err
    · exact Or.inl ok
    · exact Or.inr (Or.inr err)
  · exact boundary.finish_total buffers raw

/-- All actual ordinary requests and legal rebuffering. Guards do not
exclude zero capacities, invalid pointer arguments, empty input, duplicate
calls, new input after finishing or requests after stream end. Other flush
flags and advanced operations are separate obligations. -/
inductive DefaultOrdinaryRequests (r : ZStreamRef) (ds : Nat) : Heap → Heap → Prop
  | refl (h : Heap) : DefaultOrdinaryRequests r ds h h
  | rebuffer {h middle after : Heap} : DefaultOrdinaryRequests r ds h middle →
      Rebuffer middle after r → DefaultOrdinaryRequests r ds h after
  | step {h middle after : Heap} {z : ZStream} {flush rc : Int32} :
      DefaultOrdinaryRequests r ds h middle → r.get middle = some z → StreamBuffers middle r →
      (z.next_out = .null ∨ ∃ ob oo, z.next_out = .ref (.blk ob) oo) →
      (flush = Z_NO_FLUSH ∨ flush = Z_FINISH) →
      C.run (deflate (some r) flush) middle = .ok (rc, after) → DefaultOrdinaryRequests r ds h after

/-- The protocol is proved by induction over actual ordinary requests.
No invariant or callee contract is an assumed history-constructor field. -/
theorem DefaultOrdinaryRequests.preserves {h after : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (boundary : DefaultFinishBoundary h r ds z d config) (history : DefaultOrdinaryRequests r ds h after) :
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
        stateM.request _ flag buffers raw
      have heaps : computed = _ := (Prod.mk.inj (Except.ok.inj (run.symm.trans actual))).2
      subst computed
      exact ⟨z', result, stateA⟩

/-- Actual default initialization establishes the same boundary after
any finite ordinary request history, including real error returns. -/
theorem default_init_ordinary_request_histories {h : Heap} {r : ZStreamRef} {z : ZStream} {version : BPtr}
    (hf : Fresh h) (hu : Uniq h) (hg : LibraryGlobals h) (hz : r.get h = some z)
    (ha : DefaultOrNull z) (hv : VersionValue h version (some 49))
    (alloc : ∀ j, j < 5 → h.allocOk (h.nalloc + j) = true) :
    ∃ initialized config,
      C.run (deflateInit_ (some r) Z_DEFAULT_COMPRESSION version 112) h = .ok (Z_OK, initialized) ∧
      (∀ after, DefaultOrdinaryRequests r h.nextBlk initialized after →
        ∃ z' result, DefaultFinishBoundary after r h.nextBlk z' result config) := by
  obtain ⟨initialized, zf, sf, run, boundary⟩ := default_initialization_finish_protocol hf hu hg hz ha hv alloc
  exact ⟨initialized, engineConfig sf, run, fun _ history => history.preserves boundary⟩

end Zlib.Deflate.Engine.Proofs
