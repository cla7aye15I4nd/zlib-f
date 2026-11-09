import ZlibF.Proof.«inflate.c.local-fast-parser-distance-post»
import ZlibF.Proof.«inflate.c.local-fast-parser-dolen-extra-invariant»
import ZlibF.Proof.«inflate.c.local-fast-parser-dolen-extra-three-byte-invariant»
import ZlibF.Proof.«inflate.c.local-fast-parser-dolen-refill-invariant»
import ZlibF.Proof.«inflate.c.local-fast-parser-pull»
import ZlibF.Proof.«inflate.c.fast-view-dolen-len-four-byte-invariant»
import ZlibF.Proof.«inflate.c.local-fast-copy-bad-data-invariant»
import ZlibF.Proof.«inflate.c.local-fast-copy-literal-write-invariant»

namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- The source length-extra-bit selection and distance suffix run with four
unread bytes when the selected length code leaves at least one held bit. -/
theorem FastInputPacket.dolenLen_four_byte_local_state
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
    (extraWidth : l.op.toNat ≤ 5)
    (bitsBound : slow.bits.toNat ≤ 30)
    (held : 1 ≤ slow.bits.toNat)
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
    ∃ extra used consumed slowNext result after,
      extra < 2 ^ l.op.toNat ∧ used ≤ 4 ∧
      consumed ≤ 33 ∧
      C.run (Zlib.Inffast.Proofs.dolenLen c l) h =
        .ok (result, after) ∧
      result.againD = false ∧
      FastInputPacket after slowNext
        (List.drop used
          (first :: second :: third :: fourth :: rest))
        result ∧
      DispatchBuffers after r slowNext
        (List.drop used
          (first :: second :: third :: fourth :: rest)) ∧
      ByteViewSizes h after ∧
      stream slowNext
        (List.drop used
          (first :: second :: third :: fourth :: rest)) =
        List.drop consumed
          (stream slow
            (first :: second :: third :: fourth :: rest)) ∧
      (LocalFastDistancePost cutoff h after r zs z s slowNext
        (List.drop used
          (first :: second :: third :: fourth :: rest))
        result dest output j
          (l.len.toNat + extra) ∨
       ∃ i, result.broke = true ∧
         after = badHeap h r zs z s i ∧
         LocalStateJ after cutoff r zs
           { z with msg := .ref (.str i) 0 }
           { s with mode := BAD }) := by
  by_cases hasExtra : l.op != 0
  · by_cases needsPull : l.bits < l.op
    · have small : slow.bits.toNat ≤ 22 := by
        have less := UInt32.lt_iff_toNat_lt.mp needsPull
        rw [packet.bits] at less
        omega
      obtain ⟨next1, fast1, slow1, pullRun, _,
        slow1Eq, fast1Eq, packet1, _, buffers1, stream1⟩ :=
        (Zlib.Inflate.Local.FastInputPacket.pull_local_state packet) invariant buffers small
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
      have guard1 : C.run (Ptr.lt fast1.out c.end_) h =
          .ok (true, h) := by
        simpa only [fast1Eq, Zlib.Inffast.Proofs.pullL]
          using guard
      obtain ⟨used, consumed, slowNext, result, after,
        usedBound, consumedBound, extRun, againD,
        finalPacket, finalBuffers, sizes, source, outcome⟩ :=
        (Zlib.Inflate.Local.FastInputPacket.dolenExt_three_byte_local_state packet1) invariant buffers1
          streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
          dcodePtr codesGet safe mask width1 fits1 held1 bound1
          (by simpa only [slow1Eq, pulled] using left)
          (by simpa only [slow1Eq, pulled] using avail)
          length1 out1 put1 begPtr end1 outputGet outputWrite
          size1 current beginLe span guard1
      have run : C.run (Zlib.Inffast.Proofs.dolenLen c l) h =
          .ok (result, after) := by
        change (Zlib.Inffast.Proofs.dolenLen c l) h =
          .ok (result, after)
        unfold Zlib.Inffast.Proofs.dolenLen
        simp only [hasExtra, needsPull, ite_true]
        change (Zlib.Inffast.pull l >>= fun q =>
          Zlib.Inffast.Proofs.dolenExt c q) h =
            .ok (result, after)
        change (Zlib.Inffast.pull l) h =
          .ok (fast1, h) at pullRun
        change (Zlib.Inffast.Proofs.dolenExt c fast1) h =
          .ok (result, after) at extRun
        simp only [bind_app, pullRun, extRun]
      let extra : Nat := fast1.hold.toNat % 2 ^ fast1.op.toNat
      have extraBound : extra < 2 ^ l.op.toNat := by
        rw [← opEq]
        exact Nat.mod_lt _ (Nat.pow_pos (by omega))
      have suffix :
          (second :: third :: fourth :: rest).drop used =
          List.drop (1 + used)
            (first :: second :: third :: fourth :: rest) := by
        calc
          (second :: third :: fourth :: rest).drop used =
              List.drop used (List.drop 1
                (first :: second :: third :: fourth :: rest)) := rfl
          _ = List.drop (1 + used)
                (first :: second :: third :: fourth :: rest) := by
                  rw [List.drop_drop]
      refine ⟨extra, 1 + used, consumed, slowNext, result,
        after, extraBound, by omega, consumedBound,
        run, againD,
        by simpa only [suffix] using finalPacket,
        by simpa only [suffix] using finalBuffers,
        sizes, ?_, ?_⟩
      · rw [← suffix]
        rw [stream1] at source
        exact source
      · rcases outcome with post | bad
        · apply Or.inl
          rw [← suffix]
          simpa only [extra, fast1Eq,
            Zlib.Inffast.Proofs.pullL] using post
        · exact Or.inr bad
    · have fits : l.op.toNat ≤ slow.bits.toNat := by
        have noLess : ¬ l.op.toNat > l.bits.toNat := by
          intro h
          exact needsPull (UInt32.lt_iff_toNat_lt.mpr h)
        rw [packet.bits] at noLess
        omega
      obtain ⟨used, consumed, slowNext, result, after,
        usedBound, consumedBound, extRun, againD,
        finalPacket, finalBuffers, sizes, source, outcome⟩ :=
        (Zlib.Inflate.Local.FastInputPacket.dolenExt_local_state packet) invariant buffers
          streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
          dcodePtr codesGet safe mask extraWidth fits bitsBound
          left avail length outPtr outputPtr begPtr endPtr
          outputGet outputWrite outputSize current beginLe
          span guard
      have run : C.run (Zlib.Inffast.Proofs.dolenLen c l) h =
          .ok (result, after) := by
        unfold Zlib.Inffast.Proofs.dolenLen
        simp only [hasExtra, needsPull, ite_true, ite_false]
        exact extRun
      exact ⟨l.hold.toNat % 2 ^ l.op.toNat, used,
        consumed, slowNext, result, after,
        Nat.mod_lt _ (Nat.pow_pos (by omega)),
        by omega, consumedBound, run, againD,
        finalPacket, finalBuffers, sizes, source, outcome⟩
  · have opZero : l.op = 0 := by
      simpa using hasExtra
    have length0 : 3 ≤ l.len.toNat ∧ l.len.toNat ≤ 258 := by
      rw [opZero] at length
      simp only [UInt32.toNat_zero, Nat.pow_zero] at length
      omega
    obtain ⟨used, consumed, slowNext, result, after,
      usedBound, consumedBound, refillRun, againD,
      finalPacket, finalBuffers, sizes, source, outcome⟩ :=
      (Zlib.Inflate.Local.FastInputPacket.dolenRefill_local_state packet) invariant buffers
        streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
        dcodePtr codesGet safe mask bitsBound left avail
        length0 outPtr outputPtr begPtr endPtr outputGet
        outputWrite outputSize current beginLe span guard
    have run : C.run (Zlib.Inffast.Proofs.dolenLen c l) h =
        .ok (result, after) := by
      unfold Zlib.Inffast.Proofs.dolenLen
      simp only [hasExtra, ite_false]
      exact refillRun
    refine ⟨0, used, consumed, slowNext, result, after,
      by rw [opZero]; decide, by omega, by omega,
      run, againD, finalPacket, finalBuffers, sizes,
      source, ?_⟩
    simpa only [Nat.add_zero] using outcome

end Zlib.Inflate.Local
