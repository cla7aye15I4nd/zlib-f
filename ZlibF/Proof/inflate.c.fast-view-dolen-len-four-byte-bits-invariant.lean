import ZlibF.Proof.«inflate.c.fast-view-dolen-extra-bits-invariant»
import ZlibF.Proof.«inflate.c.fast-view-dolen-extra-three-byte-bits-invariant»
import ZlibF.Proof.«inflate.c.fast-view-dolen-len-four-byte-frame-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- The length-extra-bit selection retains the 30-bit fast-loop bound,
including its optional input pull and zero-extra-bit branch. -/
theorem FastInputPacket.dolenLen_four_byte_bits_default_state
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
    (extraWidth : l.op.toNat ≤ 5)
    (held : 1 ≤ slow.bits.toNat)
    (bitsBound : slow.bits.toNat ≤ 30)
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    (length : 3 ≤ l.len.toNat ∧
      l.len.toNat + 2 ^ l.op.toNat ≤ 259)
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
      C.run (Zlib.Inffast.Proofs.dolenLen c l) h =
        .ok (result, after) ∧
      FastInputPacket after slowNext
        ((first :: second :: third :: fourth :: rest).drop used)
        result ∧
      (result.broke = false → slowNext.bits.toNat ≤ 30) := by
  obtain ⟨_, used, _, slowNext, result, after, _, _, _,
    run, _, finalPacket, _, _, _, _, _⟩ :=
    packet.dolenLen_four_byte_frame_default_state invariant buffers
      streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
      dcodePtr codesGet safe mask extraWidth bitsBound held left
      avail length outPtr outputPtr begPtr endPtr outputGet
      outputWrite outputSize current beginLe span guard
  have finalBound : result.broke = false →
      slowNext.bits.toNat ≤ 30 := by
    intro notBroken
    by_cases hasExtra : l.op != 0
    · by_cases needsPull : l.bits < l.op
      · have small : slow.bits.toNat ≤ 22 := by
          have less := UInt32.lt_iff_toNat_lt.mp needsPull
          rw [packet.bits] at less
          omega
        obtain ⟨next1, fast1, slow1, pullRun, next1Eq,
          slow1Eq, fast1Eq, packet1, _, buffers1, _⟩ :=
          packet.pull_default_state invariant buffers small
        have opEq : fast1.op = l.op := by
          rw [fast1Eq]
          rfl
        have fits1 : fast1.op.toNat ≤ slow1.bits.toNat := by
          rw [opEq, slow1Eq]
          change l.op.toNat ≤ (slow.bits + 8).toNat
          rw [u32_add8 slow.bits (by omega)]
          omega
        have bound1 : slow1.bits.toNat ≤ 30 := by
          rw [slow1Eq]
          change (slow.bits + 8).toNat ≤ 30
          rw [u32_add8 slow.bits (by omega)]
          omega
        have held1 : 4 + fast1.op.toNat ≤ slow1.bits.toNat := by
          rw [opEq, slow1Eq]
          change 4 + l.op.toNat ≤ (slow.bits + 8).toNat
          rw [u32_add8 slow.bits (by omega)]
          omega
        have width1 : fast1.op.toNat ≤ 5 := by
          rw [opEq]
          exact extraWidth
        have length1 : 3 ≤ fast1.len.toNat ∧
            fast1.len.toNat + 2 ^ fast1.op.toNat ≤ 259 := by
          simpa only [fast1Eq, Zlib.Inffast.Proofs.pullL]
            using length
        have out1 : fast1.out = .ref dest j := by
          simpa only [fast1Eq, Zlib.Inffast.Proofs.pullL]
            using outPtr
        have put1 : slow1.put = .ref dest oo := by
          simpa only [slow1Eq, pulled] using outputPtr
        have end1 : c.end_ = .ref dest
            (oo + slow1.left.toNat - 257) := by
          simpa only [slow1Eq, pulled] using endPtr
        have size1 : oo + slow1.left.toNat ≤ output.size := by
          simpa only [slow1Eq, pulled] using outputSize
        have left1 : slow1.left ≠ 0 := by
          simpa only [slow1Eq, pulled] using left
        have avail1 : 258 ≤ slow1.left.toNat := by
          simpa only [slow1Eq, pulled] using avail
        have guard1 : C.run (Ptr.lt fast1.out c.end_) h =
            .ok (true, h) := by
          simpa only [fast1Eq, Zlib.Inffast.Proofs.pullL]
            using guard
        obtain ⟨_, slowExt, result0, after0, extRun,
          extPacket, extBound⟩ :=
          packet1.dolenExt_three_byte_bits_default_state invariant buffers1
            streamPtr statePtr whaveEq wsizeEq wnextEq
            windowEq dcodePtr codesGet safe mask width1
            fits1 held1 bound1 left1 avail1 length1 out1 put1
            begPtr end1 outputGet outputWrite size1 current
            beginLe span guard1
        have run0 : C.run (Zlib.Inffast.Proofs.dolenLen c l) h =
            .ok (result0, after0) := by
          change (Zlib.Inffast.Proofs.dolenLen c l) h =
            .ok (result0, after0)
          unfold Zlib.Inffast.Proofs.dolenLen
          simp only [hasExtra, needsPull, ite_true]
          change (Zlib.Inffast.pull l >>= fun q =>
            Zlib.Inffast.Proofs.dolenExt c q) h =
              .ok (result0, after0)
          change (Zlib.Inffast.pull l) h =
            .ok (fast1, h) at pullRun
          change (Zlib.Inffast.Proofs.dolenExt c fast1) h =
            .ok (result0, after0) at extRun
          simp only [bind_app, pullRun, extRun]
        rw [run] at run0
        cases run0
        have sameBits : slowNext.bits = slowExt.bits :=
          finalPacket.bits.symm.trans extPacket.bits
        rw [sameBits]
        exact extBound notBroken
      · have fits : l.op.toNat ≤ slow.bits.toNat := by
          have noLess : ¬ l.op.toNat > l.bits.toNat := by
            intro h
            exact needsPull (UInt32.lt_iff_toNat_lt.mpr h)
          rw [packet.bits] at noLess
          omega
        obtain ⟨_, slowExt, result0, after0, extRun,
          extPacket, extBound⟩ :=
          packet.dolenExt_bits_default_state invariant buffers
            streamPtr statePtr whaveEq wsizeEq wnextEq
            windowEq dcodePtr codesGet safe mask extraWidth
            fits bitsBound left avail length outPtr outputPtr
            begPtr endPtr outputGet outputWrite outputSize
            current beginLe span guard
        have run0 : C.run (Zlib.Inffast.Proofs.dolenLen c l) h =
            .ok (result0, after0) := by
          unfold Zlib.Inffast.Proofs.dolenLen
          simp only [hasExtra, needsPull, ite_true, ite_false]
          exact extRun
        rw [run] at run0
        cases run0
        have sameBits : slowNext.bits = slowExt.bits :=
          finalPacket.bits.symm.trans extPacket.bits
        rw [sameBits]
        exact extBound notBroken
    · have opZero : l.op = 0 := by
        simpa using hasExtra
      have length0 : 3 ≤ l.len.toNat ∧
          l.len.toNat ≤ 258 := by
        rw [opZero] at length
        simp only [UInt32.toNat_zero, Nat.pow_zero] at length
        omega
      obtain ⟨_, slowRefill, result0, after0, refillRun,
        refillPacket, refillBound⟩ :=
        packet.dolenRefill_bits_default_state invariant buffers
          streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
          dcodePtr codesGet safe mask bitsBound left avail
          length0 outPtr outputPtr begPtr endPtr outputGet
          outputWrite outputSize current beginLe span guard
      have run0 : C.run (Zlib.Inffast.Proofs.dolenLen c l) h =
          .ok (result0, after0) := by
        unfold Zlib.Inffast.Proofs.dolenLen
        simp only [hasExtra, ite_false]
        exact refillRun
      rw [run] at run0
      cases run0
      have sameBits : slowNext.bits = slowRefill.bits :=
        finalPacket.bits.symm.trans refillPacket.bits
      rw [sameBits]
      exact refillBound notBroken
  exact ⟨used, slowNext, result, after, run,
    finalPacket, finalBound⟩

end Zlib.Inflate.Proofs
