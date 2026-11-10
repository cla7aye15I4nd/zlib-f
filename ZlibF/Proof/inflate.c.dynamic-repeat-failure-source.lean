import ZlibF.Proof.«inflate.c.dynamic-parser-context-seed-resume»
namespace Zlib.Inflate.Proofs.DynamicRejects
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inffast.Proofs
set_option autoImplicit false
set_option maxHeartbeats 2400000

/-- A real true repeat result identifies the checked overflow branch and
its exact unchanged registers/actual BAD heap. -/
theorem repeat_finish_true_observed
    {c : Ctx} {l regs : IL} {h after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (E : Env c h r zs z s) (size : s.lens.size=320) (nlen : s.nlen.toNat≤286) (ndist : s.ndist.toNat≤30)
    (haveBound : s.«have».toNat≤s.nlen.toNat+s.ndist.toNat) (copyLo : 1≤l.copy.toNat) (copyHi : l.copy.toNat≤138)
    (value : l.len.toNat≤15) (initialized : ∀k,k<s.«have».toNat→(s.lens.getD k 0).toNat≤15)
    (actual : runX (clRepeatFinish c) l h=.ok ((.ok true,regs),after)) :
    s.nlen.toNat+s.ndist.toNat<s.«have».toNat+l.copy.toNat ∧ regs=l ∧
      ∃i,after=tcBadHeap h r zs z s i := by
  by_cases overflow : s.nlen.toNat+s.ndist.toNat<s.«have».toNat+l.copy.toNat
  · obtain ⟨i,_literal,run⟩ := (clRepeatFinish_run E.strm E.st E.hz E.hs size nlen ndist haveBound copyLo copyHi value initialized).1 overflow
    rw [run] at actual
    cases actual
    exact ⟨overflow,rfl,i,rfl⟩
  · have room : s.«have».toNat+l.copy.toNat≤s.nlen.toNat+s.ndist.toNat := by omega
    obtain ⟨state,normal,_⟩ := (clRepeatFinish_run E.strm E.st E.hz E.hs size nlen ndist haveBound copyLo copyHi value initialized).2 room
    rw [normal] at actual
    cases actual

/-- Actual zero-repeat overflow, retaining the canonical code and extra
bits as a rejected prefix before arbitrary unread input replacements. -/
theorem zero_repeat_true_source
    {c : Ctx} {l regs : IL} {h after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {bs : List UInt8} {alphabet : List Nat} (E : Env c h r zs z s)
    (size : s.lens.size=320) (nlen : s.nlen.toNat≤286) (ndist : s.ndist.toNat≤30)
    (more : s.«have».toNat<s.nlen.toNat+s.ndist.toNat)
    (initialized : ∀k,k<s.«have».toNat→(s.lens.getD k 0).toNat≤15)
    (B : BitInv h l bs) (here : Code) (extra base : UInt32)
    (width : here.bits.toNat≤7) (extraBound : extra.toNat≤7) (baseLo : 3≤base.toNat) (baseHi : base.toNat≤11)
    (symbol : (here.val.toNat=17 ∧ extra=3 ∧ base=3) ∨ (here.val.toNat=18 ∧ extra=7 ∧ base=11))
    (acceptable : Acceptable .codeLength alphabet)
    (decoded : decodeSym alphabet (stream l bs)=some (here.val.toNat,(stream l bs).drop here.bits.toNat))
    (actual : runX (do clZeroSetup here extra base;clRepeatFinish c) l h=.ok ((.ok true,regs),after)) :
    ∃used word,used≤bs.length ∧ BitInv after regs (bs.drop used) ∧
      stream l bs=word++stream regs (bs.drop used) ∧
      NoCodeLensExtension alphabet (s.nlen.toNat+s.ndist.toNat) (actualLengthPrefix s) word := by
  obtain ⟨result,prepared,used,setupRun,usedBound,inv,_shape,_bits,counts,_cursor,_budget⟩ :=
    clZeroSetup_run_cursor B here extra base width extraBound baseLo baseHi
  obtain ⟨result0,prepared0,used0,setupRun0,_bound0,inv0,semantic⟩ := clZeroSetup_read B here extra base width extraBound baseLo baseHi
  rw [setupRun] at setupRun0
  cases setupRun0
  have uses : used0=used := by
    have a:=inv.have_eq;have b:=inv0.have_eq;simp only [List.length_drop] at a b;omega
  subst used0
  rw [runX_bind,setupRun] at actual
  cases result with
  | error exit => cases actual
  | ok done =>
    cases done
    obtain ⟨zero,copyLo,copyHi⟩ := counts rfl
    obtain ⟨value,read,_zero,count⟩ := semantic rfl
    obtain ⟨overflow,regsEq,i,heapEq⟩ := repeat_finish_true_observed E size nlen ndist (by omega) (by omega) copyHi (by rw [zero];decide) initialized actual
    subst regs
    subst after
    obtain ⟨valueBound,extraWord⟩ := ZlibF.Math.CodeLengthPrefix.read_word read
    have wordSource:=ZlibF.Math.CodeLengthPrefix.decoded_word decoded
    have prefixMore : (actualLengthPrefix s).length<s.nlen.toNat+s.ndist.toNat := by
      simpa only [actualLengthPrefix,Zlib.Inftrees.Proofs.lensOf_length] using more
    let word:=codeOf alphabet here.val.toNat++bitsOfNat value extra.toNat
    refine ⟨used,word,usedBound,(inv.put_stream r _).setI zs _,?_,?_⟩
    · rw [wordSource,extraWord,List.append_assoc]
    · rcases symbol with ⟨symbol,rfl,rfl⟩ | ⟨symbol,rfl,rfl⟩
      · change NoCodeLensExtension alphabet _ _ (codeOf alphabet here.val.toNat++bitsOfNat value (3 : UInt32).toNat)
        rw [symbol]
        have nonzero:= (Zlib.Inftrees.Proofs.decoded_symbol_prefix decoded).2.1
        rw [symbol] at nonzero
        exact repeat17_overflow_no_extension acceptable prefixMore nonzero valueBound (by rw [count] at overflow;simpa only [actualLengthPrefix,Zlib.Inftrees.Proofs.lensOf_length,UInt32.toNat_ofNat,Nat.reduceMod] using overflow)
      · change NoCodeLensExtension alphabet _ _ (codeOf alphabet here.val.toNat++bitsOfNat value (7 : UInt32).toNat)
        rw [symbol]
        have nonzero:= (Zlib.Inftrees.Proofs.decoded_symbol_prefix decoded).2.1
        rw [symbol] at nonzero
        exact repeat18_overflow_no_extension acceptable prefixMore nonzero valueBound (by rw [count] at overflow;simpa only [actualLengthPrefix,Zlib.Inftrees.Proofs.lensOf_length,UInt32.toNat_ofNat,Nat.reduceMod] using overflow)

#print axioms repeat_finish_true_observed
#print axioms zero_repeat_true_source
end Zlib.Inflate.Proofs.DynamicRejects
