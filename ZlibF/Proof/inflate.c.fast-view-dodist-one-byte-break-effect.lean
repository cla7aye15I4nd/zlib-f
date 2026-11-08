import ZlibF.Proof.«inflate.c.fast-view-dist-cont-frame-invariant»
import ZlibF.Proof.«inflate.c.fast-view-dist-cont-break-effect»
import ZlibF.Proof.«inflate.c.fast-view-dodist-one-byte-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- With five held bits, the actual distance-extra suffix can read at most
one more caller byte. -/
theorem FastInputPacket.dodistBase_one_byte_break_effect
    {h : Heap} {slow : IL} {first : UInt8} {rest : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow (first :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
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
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h)) :
    ∃ used slowNext result after,
      used ≤ 1 ∧
      C.run (Zlib.Inffast.Proofs.dodistBase c l) h =
        .ok (result, after) ∧
      FastDistancePost h after r zs z s slowNext
        ((first :: rest).drop used) result
        dest output j l.len.toNat ∧
      stream slowNext ((first :: rest).drop used) =
        (stream slow (first :: rest)).drop l.op.toNat ∧
      slowNext.put = slow.put ∧
      slowNext.left = slow.left ∧
      slowNext.out_ = slow.out_ ∧
      slowNext.next = inputAdvance slow.next used ∧
      ((result.broke = l.broke ∧
        BufferFrame h after (fun b => StreamRoot r b ∨ b = zs)
          [⟨slow.put, slow.left.toNat⟩]) ∨
       ∃ i, result.broke = true ∧
         after = badHeap h r zs z s i) := by
  by_cases needsFirst : l.bits < l.op
  · have small : slow.bits.toNat ≤ 22 := by
      have less := UInt32.lt_iff_toNat_lt.mp needsFirst
      rw [packet.bits] at less
      omega
    obtain ⟨next1, fast1, slow1, pull1, next1Eq,
      slow1Eq, fast1Eq, packet1, _, buffers1, stream1⟩ :=
      packet.pull_default_state invariant buffers small
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
    obtain ⟨result, after, contRun, post, bitsAfter,
      _, _, _, _, _⟩ :=
      packet1.distCont_frame invariant buffers1 streamPtr statePtr
        whaveEq wsizeEq wnextEq windowEq fits1
        (by rw [op1]; omega) left1 avail1
        (by rw [len1]; exact length) out1 put1 begPtr end1
        outputGet outputWrite size1 current beginLe span guard1
    have run : C.run (Zlib.Inffast.Proofs.dodistBase c l) h =
        .ok (result, after) := by
      change (Zlib.Inffast.Proofs.dodistBase c l) h =
        .ok (result, after)
      unfold Zlib.Inffast.Proofs.dodistBase
      simp only [needsFirst, ite_true]
      rw [bind_ok (by simpa only [C.run] using pull1)]
      simp only [noSecond, ite_false]
      exact contRun
    let slowAfter : IL := { slow1 with
      hold := slow1.hold >>> fast1.op.toUInt64,
      bits := slow1.bits - fast1.op }
    have streamEq : stream slowAfter rest =
        (stream slow (first :: rest)).drop l.op.toNat := by
      rw [bitsAfter, op1, stream1]
    obtain ⟨effectResult, effectAfter, effectRun, effect1⟩ :=
      packet1.distCont_break_effect invariant buffers1 streamPtr statePtr
        whaveEq wsizeEq wnextEq windowEq fits1
        (by rw [op1]; omega) left1 avail1
        (by rw [len1]; exact length) out1 put1 begPtr end1
        outputGet outputWrite size1 current beginLe span guard1
    have same : effectResult = result ∧ effectAfter = after := by
      rw [contRun] at effectRun
      cases effectRun
      exact ⟨rfl, rfl⟩
    rw [same.1, same.2] at effect1
    have effect :
        (result.broke = l.broke ∧
          BufferFrame h after (fun b => StreamRoot r b ∨ b = zs)
            [⟨slow.put, slow.left.toNat⟩]) ∨
        ∃ i, result.broke = true ∧
          after = badHeap h r zs z s i := by
      simpa only [slow1Eq, pulled, fast1Eq,
        Zlib.Inffast.Proofs.pullL] using effect1
    exact ⟨1, slowAfter, result, after, by omega,
      run, by simpa [slowAfter, len1, List.drop] using post,
      by simpa using streamEq,
      by simp only [slowAfter, slow1Eq, pulled],
      by simp only [slowAfter, slow1Eq, pulled],
      by simp only [slowAfter, slow1Eq, pulled],
      by simp only [slowAfter, slow1Eq, pulled, next1Eq], effect⟩
  · have fits0 : l.op.toNat ≤ slow.bits.toNat := by
      have notLess : ¬ slow.bits.toNat < l.op.toNat := by
        intro hlt
        exact needsFirst (UInt32.lt_iff_toNat_lt.mpr
          (by rw [packet.bits]; exact hlt))
      omega
    obtain ⟨result, after, contRun, post, bitsAfter,
      _, _, _, _, _⟩ :=
      packet.distCont_frame invariant buffers streamPtr statePtr
        whaveEq wsizeEq wnextEq windowEq fits0
        (by omega) left avail length outPtr outputPtr begPtr
        endPtr outputGet outputWrite outputSize current beginLe
        span guard
    have run : C.run (Zlib.Inffast.Proofs.dodistBase c l) h =
        .ok (result, after) := by
      change (Zlib.Inffast.Proofs.dodistBase c l) h =
        .ok (result, after)
      unfold Zlib.Inffast.Proofs.dodistBase
      simp only [needsFirst, ite_false]
      exact contRun
    let slowAfter : IL := { slow with
      hold := slow.hold >>> l.op.toUInt64,
      bits := slow.bits - l.op }
    obtain ⟨effectResult, effectAfter, effectRun, effect0⟩ :=
      packet.distCont_break_effect invariant buffers streamPtr statePtr
        whaveEq wsizeEq wnextEq windowEq fits0
        (by omega) left avail length outPtr outputPtr begPtr
        endPtr outputGet outputWrite outputSize current beginLe
        span guard
    have same : effectResult = result ∧ effectAfter = after := by
      rw [contRun] at effectRun
      cases effectRun
      exact ⟨rfl, rfl⟩
    rw [same.1, same.2] at effect0
    exact ⟨0, slowAfter, result, after, by omega,
      run, by simpa only [List.drop_zero] using post,
      by simpa only [List.drop_zero] using bitsAfter,
      rfl, rfl, rfl, by simp only [slowAfter, inputAdvance_zero], effect0⟩

#print axioms FastInputPacket.dodistBase_one_byte_break_effect

end Zlib.Inflate.Proofs
