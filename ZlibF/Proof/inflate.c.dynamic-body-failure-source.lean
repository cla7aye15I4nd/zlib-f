import ZlibF.Proof.«inflate.c.dynamic-previous-failure-source»
namespace Zlib.Inflate.Proofs.DynamicRejects
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false
set_option maxHeartbeats 2400000

theorem after_lookup_true_source
    {c : Ctx} {l regs : IL} {h after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {bs : List UInt8} {alphabet : List Nat} (E : Env c h r zs z s)
    (size : s.lens.size=320) (nlen : s.nlen.toNat≤286) (ndist : s.ndist.toNat≤30)
    (more : s.«have».toNat<s.nlen.toNat+s.ndist.toNat)
    (initialized : ∀k,k<s.«have».toNat→(s.lens.getD k 0).toNat≤15)
    (B : BitInv h l bs) (here : Code) (width : here.bits.toNat≤7)
    (enough : here.bits.toNat≤l.bits.toNat) (small : here.val.toNat<19)
    (acceptable : Acceptable .codeLength alphabet)
    (decoded : decodeSym alphabet (stream l bs)=some (here.val.toNat,(stream l bs).drop here.bits.toNat))
    (actual : runX (clAfterLookup c here) l h=.ok ((.ok true,regs),after)) :
    ∃used word,used≤bs.length ∧ BitInv after regs (bs.drop used) ∧
      stream l bs=word++stream regs (bs.drop used) ∧
      NoCodeLensExtension alphabet (s.nlen.toNat+s.ndist.toNat) (actualLengthPrefix s) word := by
  by_cases literal : here.val<16
  · have literalNat:=UInt16.lt_iff_toNat_lt.mp literal
    obtain ⟨run,_inv,_remaining,_count,_values⟩ := clAfterLookup_literal_run E.st E.hs size (by omega) literalNat width enough B initialized
    rw [run] at actual;cases actual
  · by_cases previous : here.val=16
    · rw [clAfterLookup_repeat16 c here previous] at actual
      apply previous_repeat_true_source E size nlen ndist more initialized B here width acceptable _ actual
      simpa only [previous,show (16 : UInt16).toNat=16 by decide] using decoded
    · by_cases zero17 : here.val=17
      · rw [clAfterLookup_zero17 c here zero17] at actual
        exact zero_repeat_true_source E size nlen ndist more initialized B here 3 3 width (by decide) (by decide) (by decide)
          (Or.inl ⟨by rw [zero17];rfl,rfl,rfl⟩) acceptable decoded actual
      · have not16 : here.val.toNat≠16 := fun eq=>previous (UInt16.toNat_inj.mp eq)
        have not17 : here.val.toNat≠17 := fun eq=>zero17 (UInt16.toNat_inj.mp eq)
        have notLiteral : ¬here.val.toNat<16 := (not_congr UInt16.lt_iff_toNat_lt).mp literal
        have symbol18 : here.val.toNat=18 := by omega
        rw [clAfterLookup_zero18 c here literal previous zero17] at actual
        exact zero_repeat_true_source E size nlen ndist more initialized B here 7 11 width (by decide) (by decide) (by decide)
          (Or.inr ⟨symbol18,rfl,rfl⟩) acceptable decoded actual

/-- One actual ordinary-root failure rejects a canonical consumed prefix,
not a stream containing the original unread byte suffix. -/
theorem clReadBody_true_source
    {c : Ctx} {l regs : IL} {h after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {bs : List UInt8} {alphabet : List Nat}
    (E : Env c h r zs z s) (size : s.lens.size=320) (mode : s.mode=CODELENS)
    (stateInv : CodeLengthInvariant zs s)
    (contents : Zlib.Inftrees.Proofs.CodeLengthContents s.codes 0 s.lenbits.toNat alphabet)
    (ordinaryRoot : ∀index,index<2^s.lenbits.toNat→∃entry,s.codes[index]?=some entry ∧ entry.op=0)
    (more : s.«have».toNat<s.nlen.toNat+s.ndist.toNat) (B : BitInv h l bs)
    (actual : runX (clReadBody c) l h=.ok ((.ok true,regs),after)) :
    ∃used word,used≤bs.length ∧ BitInv after regs (bs.drop used) ∧
      stream l bs=word++stream regs (bs.drop used) ∧
      NoCodeLensExtension alphabet (s.nlen.toNat+s.ndist.toNat) (actualLengthPrefix s) word := by
  obtain ⟨pointer,_table,nlen,ndist,_have,initialized⟩ := stateInv mode
  have arrayGet:=CodeRef.get_istate_codes E.hs
  obtain ⟨result,looked,used1,lookupRun,_one,bound1,inv,sameStream,_shape,_bits,
    _lower,_width,_kinds,enough,_empty,_next,_count⟩ :=
    lookup1_codes_run_cursor E.st E.hs pointer arrayGet contents.safe B
  rw [clReadBody_eq,runX_bind,lookupRun] at actual
  cases result with
  | error exit => cases actual
  | ok done =>
    cases done
    change runX (do let here:=(←get:IL).here;clAfterLookup c here) looked h=.ok ((.ok true,regs),after) at actual
    simp only [runX_bind,runX_get] at actual
    obtain ⟨_heap,cell,_fields⟩ := lookup1_codes_contents E.st E.hs pointer arrayGet contents B lookupRun
    have inside : looked.hold.toNat%2^s.lenbits.toNat<2^s.lenbits.toNat := Nat.mod_lt _ (Nat.two_pow_pos _)
    obtain ⟨entry,actualCell,op⟩ := ordinaryRoot _ inside
    have sameEntry : entry=looked.here := Option.some.inj (actualCell.symm.trans (by simpa only [Nat.zero_add] using cell))
    have ordinary : looked.here.op=0 := by rw [←sameEntry];exact op
    obtain ⟨symbol,small,value,_length,decoded⟩ := lookup1_codes_symbol E.st E.hs pointer arrayGet contents.toCodeLengthMeaning B lookupRun ordinary
    have decodedHere : decodeSym alphabet (stream looked (bs.drop used1))=
        some (looked.here.val.toNat,(stream looked (bs.drop used1)).drop looked.here.bits.toNat) := by
      rw [sameStream,value];exact decoded
    obtain ⟨used2,word,bound2,outputInv,source,rejected⟩ := after_lookup_true_source E size nlen ndist more initialized inv looked.here
      (by have:=contents.safe.2.1;omega) (enough rfl) (by rw [value];exact small) contents.acceptable decodedHere actual
    have bound : used1+used2≤bs.length := by simp only [List.length_drop] at bound2;omega
    have remainder : (bs.drop used1).drop used2=bs.drop (used1+used2) := by simp only [List.drop_drop]
    rw [remainder] at outputInv source
    rw [sameStream] at source
    exact ⟨used1+used2,word,bound,outputInv,source,rejected⟩

#print axioms after_lookup_true_source
#print axioms clReadBody_true_source
end Zlib.Inflate.Proofs.DynamicRejects
