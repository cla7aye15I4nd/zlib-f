import ZlibF.Proof.«deflate.c.engine.generic-ownership-pointers»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- A successful real default init gives the original five birth keys and
allocation count. The fixed wrapper's proved implementation is used directly;
universal Init2 correctness and allocation success are not caller premises. -/
theorem generic_default_initial_birth_ledger {before initialized : Heap} {r : ZStreamRef} {version : BPtr}
    (domain : InitDomain before r version)
    (actual : C.run (deflateInit_ (some r) Z_DEFAULT_COMPRESSION version 112) before=.ok (Z_OK,initialized)) :
    initialized.nalloc=before.nalloc+5 ∧
    DeflateInitial before initialized r (ZlibF.Spec.Public.Proofs.DeflateInit.settings 6) ∧
    LiveChange before initialized (fun b=>before.nextBlk≤b ∧ b<before.nextBlk+5) (fun _=>False) ∧
    (∀ b, before.nextBlk≤b → b<before.nextBlk+5 → initialized.live b ∧ ¬ before.live b) ∧
    (∀ b, before.live b → initialized.live b) := by
  obtain ⟨hf,hu,hg,hv,z,hz,ha,_null⟩:=domain
  have allocations:=default_init_success_allocations hf hu hg hz ha hv actual
  obtain ⟨rc,computed,execution,properties⟩:=
    (ZlibF.Spec.Public.Proofs.DeflateInit.deflateInit_proof Z_DEFAULT_COMPRESSION).2.2
      before r z version hf hu hg hz ha hv
  obtain ⟨_code,heaps⟩:=Prod.mk.inj (Except.ok.inj (execution.symm.trans actual))
  rw [heaps] at properties
  have first : before.allocOk before.nalloc≠false := by
    have zero : before.allocOk before.nalloc=true := by simpa only [Nat.add_zero] using allocations 0 (by decide)
    rw [zero]
    decide
  have all : (List.range 5).all (fun j=>before.allocOk (before.nalloc+j))=true := by
    simpa only [List.all_eq_true,List.mem_range] using allocations
  simp only [ite_eq_right first,ite_eq_left all] at properties
  have initial : DeflateInitial before initialized r (ZlibF.Spec.Public.Proofs.DeflateInit.settings 6):=properties.2.2
  have copyInitial:=initial
  obtain ⟨zf,df,_good,_alloc,_free,_level,_strategy,_window,_hash,_wrap,_start,_look,_pending,
    _bits,_header,_totalIn,_totalOut,_message,_frame,live,owned⟩:=copyInitial
  have keys : DeflateOwned before.nextBlk df=(fun b=>before.nextBlk≤b ∧ b<before.nextBlk+5) := by
    funext b
    exact propext (owned b)
  rw [keys] at live
  refine ⟨properties.1,initial,live,?_,?_⟩
  · intro b lower upper
    exact ⟨(live b).mpr (Or.inr ⟨lower,upper⟩),hf b lower⟩
  · intro b old
    exact (live b).mpr (Or.inl ⟨old,not_false⟩)
end Zlib.Deflate.Engine.Proofs
