import ZlibF.Proof.«inflate.c.fast-view-bit-accounting-invariant»
import ZlibF.Proof.«inflate.c.fast-view-dodist-base-frame-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual distance-base suffix retains the 30-bit loop bound across
zero, one, or two guarded input pulls. -/
theorem FastInputPacket.dodistBase_bits_default_state
    {h : Heap} {slow : IL} {first second : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow (first :: second :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow (first :: second :: rest))
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    (whaveEq : c.whave = s.whave)
    (wsizeEq : c.wsize = s.wsize)
    (wnextEq : c.wnext = s.wnext)
    (windowEq : c.window = s.window)
    (extraBound : l.op.toNat ≤ 13)
    (bitsBound : slow.bits.toNat ≤ 30)
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
      used ≤ 2 ∧
      C.run (Zlib.Inffast.Proofs.dodistBase c l) h =
        .ok (result, after) ∧
      FastDistancePost h after r zs z s slowNext
        ((first :: second :: rest).drop used) result
        dest output j l.len.toNat ∧
      stream slowNext ((first :: second :: rest).drop used) =
        (stream slow (first :: second :: rest)).drop l.op.toNat ∧
      slowNext.put = slow.put ∧
      slowNext.left = slow.left ∧
      slowNext.out_ = slow.out_ ∧
      slowNext.next = inputAdvance slow.next used ∧
      slowNext.bits.toNat ≤ 30 := by
  obtain ⟨used, slowNext, result, after, usedLimit, run,
    post, source, putEq, leftEq, outEq, nextEq⟩ :=
    packet.dodistBase_frame_default_state invariant buffers
      streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
      extraBound left avail length outPtr outputPtr begPtr
      endPtr outputGet outputWrite outputSize current
      beginLe span guard
  have usedBound : used ≤ (first :: second :: rest).length := by
    simp only [List.length_cons]
    omega
  have bitBound : slowNext.bits.toNat ≤ 30 := by
    by_cases needsFirst : l.bits < l.op
    · have initialLess : slow.bits.toNat < l.op.toNat := by
        have selected := UInt32.lt_iff_toNat_lt.mp needsFirst
        rwa [packet.bits] at selected
      have consumedBound :
          l.op.toNat ≤ (stream slow (first :: second :: rest)).length := by
        simp only [stream, List.length_append, natBits_length,
          bytesBits_length, List.length_cons]
        omega
      have accounted := fast_stream_drop_bit_accounting
        usedBound consumedBound source
      omega
    · have extraBits : l.op.toNat ≤ slow.bits.toNat := by
        have notLess : ¬ slow.bits.toNat < l.op.toNat := by
          intro contrary
          exact needsFirst (UInt32.lt_iff_toNat_lt.mpr
            (by rw [packet.bits]; exact contrary))
        omega
      obtain ⟨result0, after0, contRun, contPost, _,
        _, _, _, _, _⟩ :=
        packet.distCont_frame invariant buffers streamPtr
          statePtr whaveEq wsizeEq wnextEq windowEq
          extraBits (by omega) left avail length outPtr
          outputPtr begPtr endPtr outputGet outputWrite
          outputSize current beginLe span guard
      have baseRun : C.run (Zlib.Inffast.Proofs.dodistBase c l) h =
          .ok (result0, after0) := by
        change (Zlib.Inffast.Proofs.dodistBase c l) h =
          .ok (result0, after0)
        unfold Zlib.Inffast.Proofs.dodistBase
        simp only [needsFirst, ite_false]
        exact contRun
      rw [run] at baseRun
      cases baseRun
      let slowDrop : IL := { slow with
        hold := slow.hold >>> l.op.toUInt64,
        bits := slow.bits - l.op }
      have resultBits : slowNext.bits = slowDrop.bits := by
        exact post.1.bits.symm.trans contPost.1.bits
      rw [resultBits]
      exact packet.distCont_bits_bound extraBits bitsBound
  exact ⟨used, slowNext, result, after, usedLimit, run,
    post, source, putEq, leftEq, outEq, nextEq, bitBound⟩

end Zlib.Inflate.Proofs
