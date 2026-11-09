import ZlibF.Proof.«deflate.c.engine.generic-request-trace-cleanup»
import ZlibF.Proof.«deflate.c.engine.generic-all-scalar-encoding»
import ZlibF.Proof.«deflate.c.engine.generic-unreadable-refusal»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Public caller buffers provide a full readable input observation unless the
actual entry guard rejects NULL positive input. No snapshot is added as a premise. -/
theorem caller_input_snapshot_or_invalid {h : Heap} {r : ZStreamRef} {z : ZStream}
    (buffers : StreamBuffers h r) (get : r.get h=some z) :
    (∃ input,Bytes h z.next_in z.avail_in.toNat input) ∨ (z.avail_in≠0 ∧ z.next_in=.null) := by
  obtain ⟨old,oldGet,input,_output,_separate⟩ := buffers
  have same : old=z := Option.some.inj (oldGet.symm.trans get)
  subst old
  rcases input with null|⟨readable,_writable,_outside⟩
  · by_cases empty : z.avail_in=0
    · exact Or.inl ⟨[],Or.inl ⟨null,by rw [empty];rfl,rfl⟩⟩
    · exact Or.inr ⟨empty,null⟩
  · exact Or.inl readable

/-- Every real basic request history derives an original exact encoding state.
Readable calls append their actual consumed/published bytes. NULL positive-input
refusals consume and publish zero, preserving both lists without a false snapshot.
The history constructors assume no representation invariant or callee contract. -/
theorem GenericDefaultRequestTrace.encoding_state {h : Heap} {r : ZStreamRef}
    (history : GenericDefaultRequestTrace r h) :
    ∃ ds z d config accepted observed,
      DefaultEncodingState h r ds z d config accepted observed := by
  induction history with
  | init domain actual =>
      obtain ⟨fresh,unique,globals,version,z,get,allocators,_null⟩ := domain
      obtain ⟨zf,sf,state⟩ := observed_default_init_encoding_state fresh unique globals get allocators version actual
      exact ⟨_,zf,sf,_,[],[],state⟩
  | caller _ edit ih =>
      obtain ⟨ds,z,d,config,accepted,observed,state⟩ := ih
      obtain ⟨z',_get',stateA⟩ := state.rebuffer edit
      exact ⟨ds,z',d,config,accepted,observed,stateA⟩
  | step previous buffers actual ih =>
      obtain ⟨ds,z,d,config,accepted,observed,state⟩ := ih
      rcases caller_input_snapshot_or_invalid buffers state.protocol.good.live.hz with ⟨input,snapshot⟩|invalid
      · obtain ⟨used,rc,computed,z',result,written,run,stateA,_buffers,_account,_bytes,_validity⟩ :=
          state.generic_scalar_encoding_request buffers _ snapshot
        have heaps := (Prod.mk.inj (Except.ok.inj (run.symm.trans actual))).2
        subst computed
        exact ⟨ds,z',result,config,accepted++input.take used,observed++written,stateA⟩
      · obtain ⟨computed,z',run,stateA,_buffers,_account,_bytes⟩ :=
          state.unreadable_input_refusal buffers invalid _
        have heaps := (Prod.mk.inj (Except.ok.inj (run.symm.trans actual))).2
        subst computed
        exact ⟨ds,z',d,config,accepted,observed,stateA⟩

end Zlib.Deflate.Engine.Proofs
