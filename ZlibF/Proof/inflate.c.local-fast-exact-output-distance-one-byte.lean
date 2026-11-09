import ZlibF.Proof.«inflate.c.local-fast-exact-output-interface»
import ZlibF.Proof.«inflate.c.local-fast-exact-output-distance-base»
import ZlibF.Proof.«inflate.c.local-fast-parser-dodist-one-byte-invariant»
namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

theorem FastInputPacket.dodistBase_one_byte_exact_output
    {h : Heap} {cutoff : Nat} {slow : IL} {first : UInt8} {rest : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow (first :: rest) l)
    (invariant : LocalStateJ h cutoff r zs z s)
    (buffers : DispatchBuffers h r slow (first :: rest))
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    (whaveEq : c.whave = s.whave)
    (wsizeEq : c.wsize = s.wsize)
    (wnextEq : c.wnext = s.wnext)
    (windowEq : c.window = s.window)
    (held : 5 ≤ slow.bits.toNat)
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
    FastExactOutput h finalHeap r zs dest j value := by
  by_cases needsFirst : l.bits < l.op
  · have small : slow.bits.toNat ≤ 22 := by
      have less := UInt32.lt_iff_toNat_lt.mp needsFirst
      rw [packet.bits] at less
      omega
    obtain ⟨next1, fast1, slow1, pull1, nextEq,
      slow1Eq, fast1Eq, packet1, _, buffers1, stream1⟩ :=
      (Zlib.Inflate.Local.FastInputPacket.pull_local_state packet) invariant buffers small
    have op1 : fast1.op = l.op := by rw [fast1Eq]; rfl
    have len1 : fast1.len = l.len := by rw [fast1Eq]; rfl
    have out1 : fast1.out = .ref dest j := by
      rw [fast1Eq]
      exact outPtr
    have put1 : slow1.put = .ref dest oo := by
      rw [slow1Eq]
      exact outputPtr
    have end1 : c.end_ = .ref dest
        (oo + slow1.left.toNat - 257) := by
      simpa only [slow1Eq, pulled] using endPtr
    have left1 : slow1.left ≠ 0 := by
      simpa only [slow1Eq, pulled] using left
    have avail1 : 258 ≤ slow1.left.toNat := by
      simpa only [slow1Eq, pulled] using avail
    have size1 : oo + slow1.left.toNat ≤ output.size := by
      simpa only [slow1Eq, pulled] using outputSize
    have guard1 : C.run (Ptr.lt fast1.out c.end_) h =
        .ok (true, h) := by
      simpa only [fast1Eq, Zlib.Inffast.Proofs.pullL] using guard
    have bits1 : slow1.bits.toNat = slow.bits.toNat + 8 := by
      rw [slow1Eq]
      exact u32_add8 slow.bits (by omega)
    have fits1 : fast1.op.toNat ≤ slow1.bits.toNat := by
      rw [op1, bits1]
      omega
    have noSecond : ¬ fast1.bits < fast1.op := by
      intro hlt
      have less := UInt32.lt_iff_toNat_lt.mp hlt
      rw [packet1.bits, op1, bits1] at less
      omega
    obtain ⟨result, after, contRun, post, bitsAfter⟩ :=
      (Zlib.Inflate.Local.FastInputPacket.distCont_post packet1) invariant buffers1 streamPtr statePtr
        whaveEq wsizeEq wnextEq windowEq fits1
        (by rw [op1]; omega) left1 avail1
        (by rw [len1]; exact length) out1 put1 begPtr end1
        outputGet outputWrite size1 current beginLe span guard1
    have effect :=
      Zlib.Inflate.Local.FastInputPacket.distCont_exact_output packet1 invariant buffers1 streamPtr statePtr
        whaveEq wsizeEq wnextEq windowEq fits1
        (by rw [op1]; omega) left1 avail1
        (by rw [len1]; exact length) out1 put1 begPtr end1
        outputGet outputWrite size1 current beginLe span guard1 contRun
    have run : C.run (Zlib.Inffast.Proofs.dodistBase c l) h =
        .ok (result, after) := by
      change (Zlib.Inffast.Proofs.dodistBase c l) h =
        .ok (result, after)
      unfold Zlib.Inffast.Proofs.dodistBase
      simp only [needsFirst, ite_true]
      rw [bind_ok (by simpa only [C.run] using pull1)]
      simp only [noSecond, ite_false]
      exact contRun
    have same := Prod.mk.inj (Except.ok.inj (run.symm.trans observed))
    rcases same with ⟨rfl, rfl⟩
    exact effect
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
      Zlib.Inflate.Local.FastInputPacket.distCont_exact_output packet invariant buffers streamPtr statePtr
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
    exact effect

#print axioms FastInputPacket.dodistBase_one_byte_exact_output
end Zlib.Inflate.Local
