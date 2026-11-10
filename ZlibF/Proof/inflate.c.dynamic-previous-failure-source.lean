import ZlibF.Proof.«inflate.c.dynamic-repeat-failure-source»
namespace Zlib.Inflate.Proofs.DynamicRejects
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inffast.Proofs
set_option autoImplicit false
set_option maxHeartbeats 2400000

theorem previous_repeat_true_source
    {c : Ctx} {l regs : IL} {h after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {bs : List UInt8} {alphabet : List Nat} (E : Env c h r zs z s)
    (size : s.lens.size=320) (nlen : s.nlen.toNat≤286) (ndist : s.ndist.toNat≤30)
    (more : s.«have».toNat<s.nlen.toNat+s.ndist.toNat)
    (initialized : ∀k,k<s.«have».toNat→(s.lens.getD k 0).toNat≤15)
    (B : BitInv h l bs) (here : Code) (width : here.bits.toNat≤7)
    (acceptable : Acceptable .codeLength alphabet)
    (decoded : decodeSym alphabet (stream l bs)=some (16,(stream l bs).drop here.bits.toNat))
    (actual : runX (clRepeat16 c here) l h=.ok ((.ok true,regs),after)) :
    ∃used word,used≤bs.length ∧ BitInv after regs (bs.drop used) ∧
      stream l bs=word++stream regs (bs.drop used) ∧
      NoCodeLensExtension alphabet (s.nlen.toNat+s.ndist.toNat) (actualLengthPrefix s) word := by
  obtain ⟨result,dropped,_oldUsed,prefixRun,_oldBound,_oldInv,_shape,_bits,_enough,_cursor,_budget⟩ :=
    clNeedDrop_run_cursor B here 2 width (by decide)
  cases result with
  | error exit =>
    have stopped : runX (clRepeat16 c here) l h=.ok ((.error exit,dropped),h) := by
      unfold clRepeat16;rw [runX_bind,prefixRun]
    rw [stopped] at actual;cases actual
  | ok done =>
    cases done
    obtain ⟨used,bound,inv,source,enough⟩ := clNeedDrop_stream_of_run B here 2 width (by decide) prefixRun
    have wordSource:=ZlibF.Math.CodeLengthPrefix.decoded_word decoded
    have nonzero:=(Zlib.Inftrees.Proofs.decoded_symbol_prefix decoded).2.1
    have prefixLength : (actualLengthPrefix s).length=s.«have».toNat := Zlib.Inftrees.Proofs.lensOf_length _ _
    by_cases empty : s.«have»=0
    · obtain ⟨i,_literal,bad⟩ := tcBadMode_run (c:=c) "invalid bit length repeat" lit_bit_length_repeat E.strm E.st E.hz E.hs
      have rejected : runX (clRepeat16 c here) l h=.ok ((.ok true,dropped),tcBadHeap h r zs z s i) := by
        unfold clRepeat16
        rw [runX_bind,prefixRun,E.st]
        simp [runX_bind,runX_lift,ldI_eq,E.hs,empty,bad,runX_pure]
      rw [rejected] at actual;cases actual
      refine ⟨used,codeOf alphabet 16,bound,(inv.put_stream r _).setI zs _,?_,?_⟩
      · rw [source];exact wordSource
      · have emptyPrefix : actualLengthPrefix s=[] := List.length_eq_zero_iff.mp (by rw [prefixLength,empty];rfl)
        rw [emptyPrefix]
        exact previous_without_length_no_extension acceptable (by rw [empty] at more;exact more) nonzero
    · have positive : 1≤s.«have».toNat := by
        have notZero : s.«have».toNat≠0 := fun zero=>empty (UInt32.toNat_inj.mp zero)
        omega
      obtain ⟨prepared,value,previousRun,preparedInv,previous,read,count⟩ :=
        clPrevBits_read E.st E.hs size positive (by omega) inv enough
      have cut : runX (clRepeat16 c here) l h=runX (do clPrevBits c s.«have»;clRepeatFinish c) dropped h := by
        unfold clRepeat16
        rw [runX_bind,prefixRun,E.st]
        simp [runX_bind,runX_lift,ldI_eq,E.hs,empty]
      rw [cut,runX_bind,previousRun] at actual
      change runX (clRepeatFinish c) prepared h=.ok ((.ok true,regs),after) at actual
      have low:=readBits_held_stream dropped (bs.drop used) 2 enough
      have sameValue : value=dropped.hold.toNat%4 := congrArg Prod.fst (Option.some.inj (read.symm.trans low))
      have valueBound : value<4 := by rw [sameValue];exact Nat.mod_lt _ (by decide)
      have valueRange : prepared.len.toNat≤15 := by
        rw [previous]
        exact initialized _ (by omega)
      obtain ⟨overflow,regsEq,i,heapEq⟩ := repeat_finish_true_observed E size nlen ndist (by omega)
        (by rw [count];omega) (by rw [count];omega) valueRange initialized actual
      subst regs;subst after
      rw [source] at read
      obtain ⟨_valueBound,extraWord⟩ := ZlibF.Math.CodeLengthPrefix.read_word read
      refine ⟨used,codeOf alphabet 16++bitsOfNat value 2,bound,(preparedInv.put_stream r _).setI zs _,?_,?_⟩
      · rw [wordSource,extraWord,List.append_assoc]
      · exact repeat16_overflow_no_extension acceptable (by rw [prefixLength];exact more) nonzero valueBound
          (by rw [count] at overflow;simpa only [prefixLength] using overflow)

#print axioms previous_repeat_true_source
end Zlib.Inflate.Proofs.DynamicRejects
