import ZlibF.Proof.«deflate.c.engine.generic-foreign-ordinary-total-protocol»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-output-base»
import ZlibF.Proof.«deflate.c.engine.ordinary-request-history»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Public caller writability admits null, raw and embedded depth output.
The storage classification is derived, not a caller domain restriction. -/
theorem caller_output_storage_cases {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r) :
    z.next_out=.null ∨ (∃ ob oo,z.next_out=.ref (.blk ob) oo) ∨
      ∃ owner oo,z.next_out=.ref (.dstate_depth owner) oo := by
  obtain ⟨old,get,_input,output,_separate⟩:=buffers
  have states : old=z:=Option.some.inj (get.symm.trans good.live.hz)
  subst old
  cases ptr : z.next_out with
  | null => exact Or.inl rfl
  | ref ref off =>
    rw [ptr] at output
    rcases output with impossible|⟨_bytes,writable,_outside⟩
    · cases impossible
    · rcases writable_reference_cases (writable rfl) with ⟨b,same⟩|⟨owner,same⟩
      · subst ref
        exact Or.inr (Or.inl ⟨b,off,rfl⟩)
      · subst ref
        exact Or.inr (Or.inr ⟨owner,off,rfl⟩)

/-- Actual ordinary requests preserve the initialized protocol on the foreign branch,
including zero output, duplicate and finished-state refusal paths. -/
theorem DefaultFinishBoundary.foreign_ordinary_request {h : Heap} {r : ZStreamRef} {ds owner oo : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (boundary : DefaultFinishBoundary h r ds z d config) (flush : Int32)
    (flag : flush=Z_NO_FLUSH ∨ flush=Z_FINISH) (buffers : StreamBuffers h r)
    (pointer : z.next_out=.ref (.dstate_depth owner) oo) :
    ∃ used produced rc after z' result,
      deflate (some r) flush h=.ok (rc,after) ∧
      DefaultFinishBoundary after r ds z' result config ∧ StreamBuffers after r ∧
      StreamAccounting z z' used produced ∧
      (rc=Z_OK ∨ rc=Z_STREAM_END ∨ rc=Z_STREAM_ERROR ∨ rc=Z_BUF_ERROR) := by
  rcases flag with rfl|rfl
  · obtain ⟨used,produced,rc,after,z',result,run,stateA,buffersA,accountA,allowed⟩:=boundary.foreign_no_flush_total buffers pointer
    refine ⟨used,produced,rc,after,z',result,run,stateA,buffersA,accountA,?_⟩
    rcases allowed with ok|error
    · exact Or.inl ok
    · exact Or.inr (Or.inr error)
  · exact boundary.foreign_finish_total buffers pointer

/-- Every publicly admitted output reference is included. NO_FLUSH/FINISH is an
explicit per-flag scope, not a replacement for the unchanged all-scalar default core. -/
theorem DefaultFinishBoundary.generic_ordinary_request {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (boundary : DefaultFinishBoundary h r ds z d config) (flush : Int32)
    (flag : flush=Z_NO_FLUSH ∨ flush=Z_FINISH) (buffers : StreamBuffers h r) :
    ∃ used produced rc after z' result,
      deflate (some r) flush h=.ok (rc,after) ∧
      DefaultFinishBoundary after r ds z' result config ∧ StreamBuffers after r ∧
      StreamAccounting z z' used produced ∧
      (rc=Z_OK ∨ rc=Z_STREAM_END ∨ rc=Z_STREAM_ERROR ∨ rc=Z_BUF_ERROR) := by
  rcases caller_output_storage_cases boundary.good buffers with null|raw|⟨owner,oo,pointer⟩
  · exact boundary.request flush flag buffers (Or.inl null)
  · exact boundary.request flush flag buffers (Or.inr raw)
  · exact boundary.foreign_ordinary_request flush flag buffers pointer

/-- Actual run uniqueness attaches the generic ordinary protocol to the exact
heap and stream/state already used by independent byte-encoding refinements. -/
theorem generic_ordinary_protocol_of_run {h after : Heap} {r : ZStreamRef} {ds : Nat}
    {z z' : ZStream} {d result : DeflateState} {config : EngineConfig} {flush rc : Int32}
    (boundary : DefaultFinishBoundary h r ds z d config) (buffers : StreamBuffers h r)
    (flag : flush=Z_NO_FLUSH ∨ flush=Z_FINISH)
    (run : deflate (some r) flush h=.ok (rc,after)) (goodA : DGood after r ds z' result) :
    DefaultFinishBoundary after r ds z' result config := by
  obtain ⟨_used,_produced,_rc,other,otherZ,otherD,actual,stateA,_buffers,_account,_allowed⟩:=boundary.generic_ordinary_request flush flag buffers
  have heaps : other=after:=(Prod.mk.inj (Except.ok.inj (actual.symm.trans run))).2
  subst other
  have streams : otherZ=z':=Option.some.inj (stateA.good.live.hz.symm.trans goodA.live.hz)
  have states : otherD=result:=Option.some.inj (stateA.good.live.hs.symm.trans goodA.live.hs)
  subst otherZ otherD
  exact stateA

end Zlib.Deflate.Engine.Proofs
