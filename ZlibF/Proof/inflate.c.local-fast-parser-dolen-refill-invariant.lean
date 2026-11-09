import ZlibF.Proof.«inflate.c.local-fast-parser-distance-post»
import ZlibF.Proof.«inflate.c.local-fast-parser-dolen-dist-invariant»
import ZlibF.Proof.«inflate.c.local-fast-parser-pull»
import ZlibF.Proof.«inflate.c.fast-view-dolen-refill-invariant»
import ZlibF.Proof.«inflate.c.local-fast-copy-bad-data-invariant»
import ZlibF.Proof.«inflate.c.local-fast-copy-literal-write-invariant»

namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- The length branch's distance refill and lookup run on caller byte
views, with the exact unread bit stream across zero or two initial pulls. -/
theorem FastInputPacket.dolenRefill_local_state
    {h : Heap} {cutoff : Nat} {slow : IL}
    {first second third fourth : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: rest) l)
    (invariant : LocalStateJ h cutoff r zs z s)
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
    ∃ used consumed slowNext result after,
      used ≤ 4 ∧ consumed ≤ 28 ∧
      C.run (Zlib.Inffast.Proofs.dolenRefill c l) h =
        .ok (result, after) ∧
      result.againD = false ∧
      FastInputPacket after slowNext
        ((first :: second :: third :: fourth :: rest).drop used)
        result ∧
      DispatchBuffers after r slowNext
        ((first :: second :: third :: fourth :: rest).drop used) ∧
      ByteViewSizes h after ∧
      stream slowNext
        ((first :: second :: third :: fourth :: rest).drop used) =
        List.drop consumed
          (stream slow (first :: second :: third :: fourth :: rest)) ∧
      (LocalFastDistancePost cutoff h after r zs z s slowNext
        ((first :: second :: third :: fourth :: rest).drop used)
        result dest output j l.len.toNat ∨
       ∃ i, result.broke = true ∧
         after = badHeap h r zs z s i ∧
         LocalStateJ after cutoff r zs
           { z with msg := .ref (.str i) 0 }
           { s with mode := BAD }) := by
  by_cases needsPull : l.bits < 15
  · have small0 : slow.bits.toNat ≤ 22 := by
      have bitsSmall : slow.bits.toNat < 15 := by
        rw [← packet.bits]
        simpa using UInt32.lt_iff_toNat_lt.mp needsPull
      omega
    obtain ⟨next1, fast1, slow1, pull1, _,
      slow1Eq, fast1Eq, packet1, _, buffers1, stream1⟩ :=
      (Zlib.Inflate.Local.FastInputPacket.pull_local_state packet) invariant buffers small0
    have small1 : slow1.bits.toNat ≤ 22 := by
      rw [slow1Eq]
      change (slow.bits + 8).toNat ≤ 22
      rw [u32_add8 slow.bits (by omega)]
      have bitsSmall : slow.bits.toNat < 15 := by
        rw [← packet.bits]
        simpa using UInt32.lt_iff_toNat_lt.mp needsPull
      omega
    obtain ⟨next2, fast2, slow2, pull2, _,
      slow2Eq, fast2Eq, packet2, _, buffers2, stream2⟩ :=
      (Zlib.Inflate.Local.FastInputPacket.pull_local_state packet1) invariant buffers1 small1
    have held2 : 15 ≤ slow2.bits.toNat := by
      rw [slow2Eq, slow1Eq]
      change ((slow.bits + 8) + 8).toNat ≥ 15
      rw [u32_add8 (slow.bits + 8) (by
          have bound : (slow.bits + 8).toNat ≤ 22 := by
            simpa only [slow1Eq, pulled] using small1
          omega),
        u32_add8 slow.bits (by omega)]
      omega
    have left2 : slow2.left ≠ 0 := by
      simpa only [slow2Eq, slow1Eq, pulled] using left
    have avail2 : 258 ≤ slow2.left.toNat := by
      simpa only [slow2Eq, slow1Eq, pulled] using avail
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
    have guard2 : C.run (Ptr.lt fast2.out c.end_) h =
        .ok (true, h) := by
      simpa only [fast2Eq, fast1Eq,
        Zlib.Inffast.Proofs.pullL] using guard
    obtain ⟨usedD, consumed, slowNext, result, after,
      usedBound, consumedBound, distRun, againD,
      finalPacket, finalBuffers, sizes, source, outcome⟩ :=
      (Zlib.Inflate.Local.FastInputPacket.dolenDist_local_state packet2) invariant buffers2
        streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
        dcodePtr codesGet safe mask held2 left2 avail2
        length2 out2 put2 begPtr end2 outputGet outputWrite
        size2 current beginLe span guard2
    have run : C.run (Zlib.Inffast.Proofs.dolenRefill c l) h =
        .ok (result, after) := by
      unfold Zlib.Inffast.Proofs.dolenRefill
      simp only [needsPull, ite_true]
      change (Zlib.Inffast.pull l >>= fun q =>
        Zlib.Inffast.pull q >>= fun q' =>
        Zlib.Inffast.Proofs.dolenDist c q') h =
          .ok (result, after)
      change (Zlib.Inffast.pull l) h =
        .ok (fast1, h) at pull1
      change (Zlib.Inffast.pull fast1) h =
        .ok (fast2, h) at pull2
      change (Zlib.Inffast.Proofs.dolenDist c fast2) h =
        .ok (result, after) at distRun
      simp only [bind_app, pull1, pull2, distRun]
    have suffix :
        (third :: fourth :: rest).drop usedD =
        (first :: second :: third :: fourth :: rest).drop
          (2 + usedD) := by
      calc
        (third :: fourth :: rest).drop usedD =
            List.drop usedD
              (List.drop 2
                (first :: second :: third :: fourth :: rest)) := rfl
        _ = (first :: second :: third :: fourth :: rest).drop
              (2 + usedD) := by rw [List.drop_drop]
    refine ⟨2 + usedD, consumed, slowNext, result, after,
      by omega, consumedBound, run, againD,
      by simpa only [suffix] using finalPacket,
      by simpa only [suffix] using finalBuffers, sizes,
      ?_, ?_⟩
    · rw [← suffix]
      rw [stream2, stream1] at source
      exact source
    · rcases outcome with post | bad
      · exact Or.inl (by simpa only [suffix, fast2Eq,
          fast1Eq, Zlib.Inffast.Proofs.pullL] using post)
      · exact Or.inr bad
  · have held : 15 ≤ slow.bits.toNat := by
      have h : ¬ l.bits.toNat < 15 := by
        intro less
        exact needsPull (UInt32.lt_iff_toNat_lt.mpr less)
      rw [packet.bits] at h
      omega
    obtain ⟨used, consumed, slowNext, result, after,
      usedBound, consumedBound, distRun, againD,
      finalPacket, finalBuffers, sizes, source, outcome⟩ :=
      (Zlib.Inflate.Local.FastInputPacket.dolenDist_local_state packet) invariant buffers
        streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
        dcodePtr codesGet safe mask held left avail length
        outPtr outputPtr begPtr endPtr outputGet outputWrite
        outputSize current beginLe span guard
    have run : C.run (Zlib.Inffast.Proofs.dolenRefill c l) h =
        .ok (result, after) := by
      unfold Zlib.Inffast.Proofs.dolenRefill
      simp only [needsPull, ite_false]
      exact distRun
    exact ⟨used, consumed, slowNext, result, after,
      by omega, consumedBound, run, againD,
      finalPacket, finalBuffers, sizes, source, outcome⟩

end Zlib.Inflate.Local
