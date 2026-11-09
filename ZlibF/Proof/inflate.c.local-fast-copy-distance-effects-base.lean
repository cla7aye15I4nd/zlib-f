import ZlibF.Proof.«inflate.c.local-fast-copy-distance-effects-cont»
import ZlibF.Proof.«inflate.c.local-fast-copy-distance-effects-pull»
import ZlibF.Proof.«inflate.c.local-fast-parser-dodist-base-invariant»
namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

theorem FastInputPacket.dodistBase_effect
    {h : Heap} {cutoff : Nat} {slow : IL} {first second : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow (first :: second :: rest) l)
    (invariant : LocalStateJ h cutoff r zs z s)
    (buffers : DispatchBuffers h r slow (first :: second :: rest))
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    (whaveEq : c.whave = s.whave)
    (wsizeEq : c.wsize = s.wsize)
    (wnextEq : c.wnext = s.wnext)
    (windowEq : c.window = s.window)
    (extraBound : l.op.toNat ≤ 13)
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    (length : 3 ≤ l.len.toNat ∧ l.len.toNat ≤ 258)
    {dest : BRef} {output : Array UInt8} {oo bg j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (begPtr : c.beg = .ref dest bg)
    (endPtr : c.end_ = .ref dest
      (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (beginLe : bg ≤ j)
    (span : j - bg < 2 ^ 32)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h))
    {value : Zlib.Inffast.L} {finalHeap : Heap}
    (observed : C.run (Zlib.Inffast.Proofs.dodistBase c l) h = .ok (value, finalHeap)) :
    FastExecEffect h finalHeap r zs z s slow dest j l value 2 258 := by
  by_cases needsFirst : l.bits < l.op
  · have small0 : slow.bits.toNat ≤ 22 := by
      have selected := UInt32.lt_iff_toNat_lt.mp needsFirst
      rw [packet.bits] at selected
      omega
    obtain ⟨next1, fast1, slow1, pull1, next1Eq,
      slow1Eq, fast1Eq, packet1, _, buffers1, stream1⟩ :=
      (Zlib.Inflate.Local.FastInputPacket.pull_local_state packet) invariant buffers small0
    have len1 : fast1.len = l.len := by rw [fast1Eq]; rfl
    have op1 : fast1.op = l.op := by rw [fast1Eq]; rfl
    have out1 : fast1.out = .ref dest j := by rw [fast1Eq]; exact outPtr
    have put1 : slow1.put = .ref dest oo := by rw [slow1Eq]; exact outputPtr
    have end1 : c.end_ = .ref dest
        (oo + slow1.left.toNat - 257) := by
      simpa only [slow1Eq, pulled] using endPtr
    have left1 : slow1.left ≠ 0 := by simpa only [slow1Eq, pulled] using left
    have avail1 : 258 ≤ slow1.left.toNat := by
      simpa only [slow1Eq, pulled] using avail
    have size1 : oo + slow1.left.toNat ≤ output.size := by
      simpa only [slow1Eq, pulled] using outputSize
    have guard1 : C.run (Ptr.lt fast1.out c.end_) h = .ok (true, h) := by
      simpa only [fast1Eq, Zlib.Inffast.Proofs.pullL] using guard
    by_cases needsSecond : fast1.bits < fast1.op
    · have small1 : slow1.bits.toNat ≤ 22 := by
        have selected := UInt32.lt_iff_toNat_lt.mp needsSecond
        rw [packet1.bits, op1] at selected
        omega
      obtain ⟨next2, fast2, slow2, pull2, next2Eq,
        slow2Eq, fast2Eq, packet2, _, buffers2, stream2⟩ :=
        (Zlib.Inflate.Local.FastInputPacket.pull_local_state packet1) invariant buffers1 small1
      have len2 : fast2.len = l.len := by
        simpa only [fast2Eq, Zlib.Inffast.Proofs.pullL] using len1
      have op2 : fast2.op = l.op := by
        simpa only [fast2Eq, Zlib.Inffast.Proofs.pullL] using op1
      have out2 : fast2.out = .ref dest j := by rw [fast2Eq]; exact out1
      have put2 : slow2.put = .ref dest oo := by rw [slow2Eq]; exact put1
      have end2 : c.end_ = .ref dest
          (oo + slow2.left.toNat - 257) := by
        simpa only [slow2Eq, pulled] using end1
      have left2 : slow2.left ≠ 0 := by
        simpa only [slow2Eq, pulled] using left1
      have avail2 : 258 ≤ slow2.left.toNat := by
        simpa only [slow2Eq, pulled] using avail1
      have size2 : oo + slow2.left.toNat ≤ output.size := by
        simpa only [slow2Eq, pulled] using size1
      have guard2 : C.run (Ptr.lt fast2.out c.end_) h =
          .ok (true, h) := by
        simpa only [fast2Eq, Zlib.Inffast.Proofs.pullL] using guard1
      have bits1 : slow1.bits.toNat = slow.bits.toNat + 8 := by
        rw [slow1Eq]
        exact u32_add8 slow.bits (by omega)
      have bits2 : slow2.bits.toNat = slow1.bits.toNat + 8 := by
        rw [slow2Eq]
        exact u32_add8 slow1.bits (by omega)
      have fits2 : fast2.op.toNat ≤ slow2.bits.toNat := by
        rw [op2, bits2, bits1]
        omega
      have fastLength2 : 3 ≤ fast2.len.toNat ∧
          fast2.len.toNat ≤ 258 := by rw [len2]; exact length
      obtain ⟨result, after, contRun, post, bitsAfter⟩ :=
        (Zlib.Inflate.Local.FastInputPacket.distCont_post packet2) invariant buffers2 streamPtr statePtr
          whaveEq wsizeEq wnextEq windowEq fits2
          (by rw [op2]; omega) left2 avail2 fastLength2
          out2 put2 begPtr end2 outputGet outputWrite size2
          current beginLe span guard2
      have effect :=
        Zlib.Inflate.Local.FastInputPacket.distCont_effect packet2 invariant buffers2 streamPtr statePtr
          whaveEq wsizeEq wnextEq windowEq fits2
          (by rw [op2]; omega) left2 avail2 fastLength2
          out2 put2 begPtr end2 outputGet outputWrite size2
          current beginLe span guard2 contRun
      have run : C.run (Zlib.Inffast.Proofs.dodistBase c l) h =
          .ok (result, after) := by
        change (Zlib.Inffast.Proofs.dodistBase c l) h =
          .ok (result, after)
        unfold Zlib.Inffast.Proofs.dodistBase
        simp only [needsFirst, ite_true]
        rw [bind_ok (by simpa only [C.run] using pull1)]
        simp only [needsSecond, ite_true]
        rw [bind_ok (by simpa only [C.run] using pull2)]
        exact contRun
      have same := Prod.mk.inj (Except.ok.inj (run.symm.trans observed))
      rcases same with ⟨rfl, rfl⟩
      have firstEffect := effect.pull_prefix packet1.cursor packet1.bits small1
        next2Eq slow2Eq fast2Eq
      exact firstEffect.pull_prefix packet.cursor packet.bits small0
        next1Eq slow1Eq fast1Eq
    · have fits1 : fast1.op.toNat ≤ slow1.bits.toNat := by
        have notLess : ¬ slow1.bits.toNat < fast1.op.toNat := by
          intro hlt
          exact needsSecond (UInt32.lt_iff_toNat_lt.mpr
            (by rw [packet1.bits]; exact hlt))
        omega
      have fastLength1 : 3 ≤ fast1.len.toNat ∧
          fast1.len.toNat ≤ 258 := by rw [len1]; exact length
      obtain ⟨result, after, contRun, post, bitsAfter⟩ :=
        (Zlib.Inflate.Local.FastInputPacket.distCont_post packet1) invariant buffers1 streamPtr statePtr
          whaveEq wsizeEq wnextEq windowEq fits1
          (by rw [op1]; omega) left1 avail1 fastLength1
          out1 put1 begPtr end1 outputGet outputWrite size1
          current beginLe span guard1
      have effect :=
        Zlib.Inflate.Local.FastInputPacket.distCont_effect packet1 invariant buffers1 streamPtr statePtr
          whaveEq wsizeEq wnextEq windowEq fits1
          (by rw [op1]; omega) left1 avail1 fastLength1
          out1 put1 begPtr end1 outputGet outputWrite size1
          current beginLe span guard1 contRun
      have run : C.run (Zlib.Inffast.Proofs.dodistBase c l) h =
          .ok (result, after) := by
        change (Zlib.Inffast.Proofs.dodistBase c l) h =
          .ok (result, after)
        unfold Zlib.Inffast.Proofs.dodistBase
        simp only [needsFirst, ite_true]
        rw [bind_ok (by simpa only [C.run] using pull1)]
        simp only [needsSecond, ite_false]
        exact contRun
      have same := Prod.mk.inj (Except.ok.inj (run.symm.trans observed))
      rcases same with ⟨rfl, rfl⟩
      exact (effect.pull_prefix packet.cursor packet.bits small0 next1Eq slow1Eq fast1Eq).widen
        (by omega) (by omega)
  · have fits0 : l.op.toNat ≤ slow.bits.toNat := by
      have notLess : ¬ slow.bits.toNat < l.op.toNat := by
        intro hlt
        exact needsFirst (UInt32.lt_iff_toNat_lt.mpr
          (by rw [packet.bits]; exact hlt))
      omega
    obtain ⟨result, after, contRun, post, bitsAfter⟩ :=
      (Zlib.Inflate.Local.FastInputPacket.distCont_post packet) invariant buffers streamPtr statePtr
        whaveEq wsizeEq wnextEq windowEq fits0
        (by omega) left avail length outPtr outputPtr begPtr
        endPtr outputGet outputWrite outputSize current beginLe
        span guard
    have effect :=
      Zlib.Inflate.Local.FastInputPacket.distCont_effect packet invariant buffers streamPtr statePtr
        whaveEq wsizeEq wnextEq windowEq fits0
        (by omega) left avail length outPtr outputPtr begPtr
        endPtr outputGet outputWrite outputSize current beginLe
        span guard contRun
    have run : C.run (Zlib.Inffast.Proofs.dodistBase c l) h =
        .ok (result, after) := by
      change (Zlib.Inffast.Proofs.dodistBase c l) h =
        .ok (result, after)
      unfold Zlib.Inffast.Proofs.dodistBase
      simp only [needsFirst, ite_false]
      exact contRun
    have same := Prod.mk.inj (Except.ok.inj (run.symm.trans observed))
    rcases same with ⟨rfl, rfl⟩
    exact effect.widen (by omega) (by omega)

#print axioms FastInputPacket.dodistBase_effect
end Zlib.Inflate.Local
