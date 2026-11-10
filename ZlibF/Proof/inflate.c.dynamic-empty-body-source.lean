import ZlibF.Proof.«inflate.c.dynamic-reader-bad-call-cut»
namespace Zlib.Inflate.Proofs.DynamicRejects
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false
set_option maxHeartbeats 2200000

theorem empty_body_source
    {c : Ctx} {l : IL} {h : Heap} {zs : Nat} {s : InflateState} {bs : List UInt8}
    (hc : c.st=some (.tab zs)) (hs : h.istates zs=some s)
    (size : s.lens.size=320) (mode : s.mode=CODELENS) (stateInv : CodeLengthInvariant zs s)
    (root : s.lenbits.toNat=1) (first : s.codes[0]?=some (⟨64,1,0⟩:Code))
    (second : s.codes[1]?=some (⟨64,1,0⟩:Code))
    (more : s.«have».toNat<s.nlen.toNat+s.ndist.toNat) (B : BitInv h l bs) :
    ∃outcome regs after used,runX (clReadBody c) l h=.ok ((outcome,regs),after) ∧
      used≤bs.length ∧ BitInv after regs (bs.drop used) ∧
      (∃word,stream l bs=word++stream regs (bs.drop used)) ∧
      ((outcome=.error Ex.leave ∧ after=h) ∨ (outcome=.ok false ∧ after=setI h zs (clWrite s 0))) := by
  obtain ⟨pointer,table,nlen,ndist,_have,initialized⟩ := stateInv mode
  have arrayGet:=CodeRef.get_istate_codes hs
  obtain ⟨outcome,looked,used,lookupRun,_one,bound,inv,sameStream,_shape,_bits,_lower,_width,kinds,enough,_empty,_cursor,_count⟩ :=
    lookup1_codes_run_cursor hc hs pointer arrayGet table B
  obtain ⟨_heap,selected⟩ := lookup1_codes_selected hc hs pointer arrayGet table B lookupRun
  have indexBound : looked.hold.toNat%2^s.lenbits.toNat<2 := by
    have inside:=Nat.mod_lt looked.hold.toNat (Nat.two_pow_pos s.lenbits.toNat)
    rw [root] at inside ⊢;exact inside
  have casesIndex : looked.hold.toNat%2^s.lenbits.toNat=0 ∨ looked.hold.toNat%2^s.lenbits.toNat=1 := by omega
  have here : looked.here=(⟨64,1,0⟩:Code) := by
    rw [selected,codeLookupValue,Array.getD_eq_getD_getElem?]
    rcases casesIndex with zero|one
    · simp only [zero,Nat.zero_add,first,Option.getD_some]
    · simp only [one,Nat.zero_add,second,Option.getD_some]
  cases outcome with
  | error exit =>
    have exitEq : exit=Ex.leave := by
      rcases kinds with impossible|same
      · cases impossible
      · exact Except.error.inj same
    subst exit
    refine ⟨.error Ex.leave,looked,h,used,?_,bound,inv,⟨[],by simpa only [List.nil_append] using sameStream.symm⟩,Or.inl ⟨rfl,rfl⟩⟩
    rw [clReadBody_eq,runX_bind,lookupRun]
  | ok done =>
    cases done
    obtain ⟨literalRun,afterInv,remaining,_newCount,_values⟩ := clAfterLookup_literal_run hc hs size
      (by omega) (by simpa only [here] using (by decide : (0:UInt16).toNat<16))
      (by simpa only [here] using (by decide : (1:UInt8).toNat≤7)) (enough rfl) inv initialized
    have zero : looked.here.val=0 := by rw [here]
    rw [zero] at literalRun afterInv
    refine ⟨.ok false,_,setI h zs (clWrite s 0),used,?_,bound,afterInv,?_,Or.inr ⟨rfl,rfl⟩⟩
    · rw [clReadBody_eq,runX_bind,lookupRun]
      simp only [runX_bind,runX_get]
      exact literalRun
    · refine ⟨(stream l bs).take 1,?_⟩
      rw [remaining,here,sameStream]
      exact (List.take_append_drop 1 (stream l bs)).symm

#print axioms empty_body_source
end Zlib.Inflate.Proofs.DynamicRejects
