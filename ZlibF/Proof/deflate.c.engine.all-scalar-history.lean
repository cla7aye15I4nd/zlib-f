import ZlibF.Proof.«deflate.c.engine.all-scalar-request»

/-! # Actual initialization and all finite signed request histories retain the boundary -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Finite histories of actual default compressor requests and legal
caller rebuffering. All signed flush scalars and all real return codes
are admitted. The constructors assume no representation invariant. -/
inductive DefaultScalarRequests (r : ZStreamRef) (ds : Nat) : Heap → Heap → Prop
  | refl (h : Heap) : DefaultScalarRequests r ds h h
  | rebuffer {h middle after : Heap} : DefaultScalarRequests r ds h middle →
      Rebuffer middle after r → DefaultScalarRequests r ds h after
  | step {h middle after : Heap} {z : ZStream} {flush rc : Int32} :
      DefaultScalarRequests r ds h middle → r.get middle = some z → StreamBuffers middle r →
      (z.next_out = .null ∨ ∃ ob oo, z.next_out = .ref (.blk ob) oo) →
      C.run (deflate (some r) flush) middle = .ok (rc, after) → DefaultScalarRequests r ds h after

/-- The actual initialized boundary is preserved through every finite
request history, with all valid flags, invalid scalars and error returns. -/
theorem DefaultScalarRequests.preserves {h after : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (boundary : DefaultFinishBoundary h r ds z d config) (history : DefaultScalarRequests r ds h after) :
    ∃ z' result, DefaultFinishBoundary after r ds z' result config := by
  induction history with
  | refl => exact ⟨z, d, boundary⟩
  | rebuffer _ edit ih =>
      obtain ⟨zm, dm, stateM⟩ := ih
      obtain ⟨zg, _getG, stateG⟩ := stateM.rebuffer edit
      exact ⟨zg, dm, stateG⟩
  | step _ getZ buffers raw actual ih =>
      obtain ⟨zm, dm, stateM⟩ := ih
      have stream : zm = _ := Option.some.inj (stateM.good.live.hz.symm.trans getZ)
      subst zm
      obtain ⟨_used, _produced, _rc, computed, z', result, run, stateA, _buffersA, _account, _allowed⟩ :=
        stateM.all_scalar_request buffers raw _
      have heaps : computed = _ := (Prod.mk.inj (Except.ok.inj (run.symm.trans actual))).2
      subst computed
      exact ⟨z', result, stateA⟩

/-- Successful actual default initialization, every finite actual request
history and rebuffering establish totality of the next signed request.
Scope is default level 6, memLevel 8, zlib without a custom header and
null/raw caller output. Encoded history and advanced APIs remain separate. -/
theorem default_init_all_scalar_next_request {h : Heap} {r : ZStreamRef} {z : ZStream} {version : BPtr}
    (hf : Fresh h) (hu : Uniq h) (hg : LibraryGlobals h) (hz : r.get h = some z)
    (ha : DefaultOrNull z) (hv : VersionValue h version (some 49))
    (alloc : ∀ j, j < 5 → h.allocOk (h.nalloc + j) = true) :
    ∃ initialized config,
      C.run (deflateInit_ (some r) Z_DEFAULT_COMPRESSION version 112) h = .ok (Z_OK, initialized) ∧
      ∀ after, DefaultScalarRequests r h.nextBlk initialized after →
        ∃ z' result, DefaultFinishBoundary after r h.nextBlk z' result config ∧
          ∀ flush, StreamBuffers after r →
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
  exact ⟨z', result, state, fun flush buffers raw => state.all_scalar_request buffers raw flush⟩

end Zlib.Deflate.Engine.Proofs
