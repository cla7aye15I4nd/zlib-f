import ZlibF.Proof.«inflate.c.fast-view-dolen-dist-bits-invariant»
import ZlibF.Proof.«inflate.c.fast-view-dolen-refill-frame-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- The distance lookup after a length code preserves the 30-bit bound,
including the branch that first reads two input bytes. -/
theorem FastInputPacket.dolenRefill_bits_default_state
    {h : Heap} {slow : IL}
    {first second third fourth : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: rest))
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    (whaveEq : c.whave = s.whave)
    (wsizeEq : c.wsize = s.wsize)
    (wnextEq : c.wnext = s.wnext)
    (windowEq : c.window = s.window)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth : Nat}
    (dcodePtr : c.dcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : DistTableSafe codes baseOff rootWidth)
    (mask : c.dmask.toUInt64.toNat = 2 ^ rootWidth - 1)
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
      C.run (Zlib.Inffast.Proofs.dolenRefill c l) h =
        .ok (result, after) ∧
      FastInputPacket after slowNext
        ((first :: second :: third :: fourth :: rest).drop used)
        result ∧
      (result.broke = false → slowNext.bits.toNat ≤ 30) := by
  obtain ⟨used, _, slowNext, result, after, _, _, run,
    _, finalPacket, _, _, _, _, _⟩ :=
    packet.dolenRefill_frame_default_state invariant buffers
      streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
      dcodePtr codesGet safe mask bitsBound left avail
      length outPtr outputPtr begPtr endPtr outputGet
      outputWrite outputSize current beginLe span guard
  have finalBound : result.broke = false →
      slowNext.bits.toNat ≤ 30 := by
    intro notBroken
    by_cases needsPull : l.bits < 15
    · have small0 : slow.bits.toNat ≤ 22 := by
        have bitsSmall : slow.bits.toNat < 15 := by
          rw [← packet.bits]
          simpa using UInt32.lt_iff_toNat_lt.mp needsPull
        omega
      obtain ⟨next1, fast1, slow1, pull1, next1Eq,
        slow1Eq, fast1Eq, packet1, _, buffers1, _⟩ :=
        packet.pull_default_state invariant buffers small0
      have small1 : slow1.bits.toNat ≤ 22 := by
        rw [slow1Eq]
        change (slow.bits + 8).toNat ≤ 22
        rw [u32_add8 slow.bits (by omega)]
        have bitsSmall : slow.bits.toNat < 15 := by
          rw [← packet.bits]
          simpa using UInt32.lt_iff_toNat_lt.mp needsPull
        omega
      obtain ⟨next2, fast2, slow2, pull2, next2Eq,
        slow2Eq, fast2Eq, packet2, _, buffers2, _⟩ :=
        packet1.pull_default_state invariant buffers1 small1
      have held2 : 15 ≤ slow2.bits.toNat := by
        rw [slow2Eq, slow1Eq]
        change ((slow.bits + 8) + 8).toNat ≥ 15
        rw [u32_add8 (slow.bits + 8) (by
            have bound : (slow.bits + 8).toNat ≤ 22 := by
              simpa only [slow1Eq, pulled] using small1
            omega),
          u32_add8 slow.bits (by omega)]
        omega
      have bound2 : slow2.bits.toNat ≤ 30 := by
        rw [slow2Eq, slow1Eq]
        change ((slow.bits + 8) + 8).toNat ≤ 30
        rw [u32_add8 (slow.bits + 8) (by
            have bound : (slow.bits + 8).toNat ≤ 22 := by
              simpa only [slow1Eq, pulled] using small1
            omega),
          u32_add8 slow.bits (by omega)]
        have bitsSmall : slow.bits.toNat < 15 := by
          rw [← packet.bits]
          simpa using UInt32.lt_iff_toNat_lt.mp needsPull
        omega
      have length2 : 3 ≤ fast2.len.toNat ∧
          fast2.len.toNat ≤ 258 := by
        simpa only [fast2Eq, fast1Eq,
          Zlib.Inffast.Proofs.pullL] using length
      have out2 : fast2.out = .ref dest j := by
        simpa only [fast2Eq, fast1Eq,
          Zlib.Inffast.Proofs.pullL] using outPtr
      have put2 : slow2.put = .ref dest oo := by
        simpa only [slow2Eq, slow1Eq, pulled] using outputPtr
      have end2 : c.end_ = .ref dest
          (oo + slow2.left.toNat - 257) := by
        simpa only [slow2Eq, slow1Eq, pulled] using endPtr
      have size2 : oo + slow2.left.toNat ≤ output.size := by
        simpa only [slow2Eq, slow1Eq, pulled] using outputSize
      have left2 : slow2.left ≠ 0 := by
        simpa only [slow2Eq, slow1Eq, pulled] using left
      have avail2 : 258 ≤ slow2.left.toNat := by
        simpa only [slow2Eq, slow1Eq, pulled] using avail
      have guard2 : C.run (Ptr.lt fast2.out c.end_) h =
          .ok (true, h) := by
        simpa only [fast2Eq, fast1Eq,
          Zlib.Inffast.Proofs.pullL] using guard
      obtain ⟨used0, slowDist, result0, after0, distRun,
        distPacket, distBound⟩ :=
        packet2.dolenDist_bits_default_state invariant buffers2
          streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
          dcodePtr codesGet safe mask held2 bound2 left2 avail2
          length2 out2 put2 begPtr end2 outputGet outputWrite
          size2 current beginLe span guard2
      have run0 : C.run (Zlib.Inffast.Proofs.dolenRefill c l) h =
          .ok (result0, after0) := by
        unfold Zlib.Inffast.Proofs.dolenRefill
        simp only [needsPull, ite_true]
        change (Zlib.Inffast.pull l >>= fun q =>
          Zlib.Inffast.pull q >>= fun q' =>
          Zlib.Inffast.Proofs.dolenDist c q') h =
            .ok (result0, after0)
        change (Zlib.Inffast.pull l) h =
          .ok (fast1, h) at pull1
        change (Zlib.Inffast.pull fast1) h =
          .ok (fast2, h) at pull2
        change (Zlib.Inffast.Proofs.dolenDist c fast2) h =
          .ok (result0, after0) at distRun
        simp only [bind_app, pull1, pull2, distRun]
      rw [run] at run0
      cases run0
      have sameBits : slowNext.bits = slowDist.bits :=
        finalPacket.bits.symm.trans distPacket.bits
      rw [sameBits]
      exact distBound notBroken
    · have held : 15 ≤ slow.bits.toNat := by
        have h : ¬ l.bits.toNat < 15 := by
          intro less
          exact needsPull (UInt32.lt_iff_toNat_lt.mpr less)
        rw [packet.bits] at h
        omega
      obtain ⟨used0, slowDist, result0, after0, distRun,
        distPacket, distBound⟩ :=
        packet.dolenDist_bits_default_state invariant buffers
          streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
          dcodePtr codesGet safe mask held bitsBound left avail
          length outPtr outputPtr begPtr endPtr outputGet
          outputWrite outputSize current beginLe span guard
      have run0 : C.run (Zlib.Inffast.Proofs.dolenRefill c l) h =
          .ok (result0, after0) := by
        unfold Zlib.Inffast.Proofs.dolenRefill
        simp only [needsPull, ite_false]
        exact distRun
      rw [run] at run0
      cases run0
      have sameBits : slowNext.bits = slowDist.bits :=
        finalPacket.bits.symm.trans distPacket.bits
      rw [sameBits]
      exact distBound notBroken
  exact ⟨used, slowNext, result, after, run,
    finalPacket, finalBound⟩

end Zlib.Inflate.Proofs
