import ZlibF.Proof.«inflate.c.fast-semantic-slice-04»
set_option autoImplicit false

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec

/-- The actual positive length-extra prefix reads at most one new byte.
It preserves the bit stream and carries the same numerical length and
extra-width registers into the source `dolenExt` suffix. -/
theorem FastInputPacket.dolenLen_extra_prefix
    {h : Heap} {slow : IL}
    {first second third fourth fifth : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: fifth :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: fifth :: rest))
    (extraWidth : l.op.toNat ≤ 5)
    (bitsBound : slow.bits.toNat ≤ 30) :
    ∃ used slowNext fastNext,
      used ≤ 1 ∧
      C.run (if l.bits < l.op then Zlib.Inffast.pull l
        else pure l) h = .ok (fastNext, h) ∧
      FastInputPacket h slowNext
        ((first :: second :: third :: fourth :: fifth :: rest).drop used)
        fastNext ∧
      DispatchBuffers h r slowNext
        ((first :: second :: third :: fourth :: fifth :: rest).drop used) ∧
      stream slowNext
        ((first :: second :: third :: fourth :: fifth :: rest).drop used) =
        stream slow
          (first :: second :: third :: fourth :: fifth :: rest) ∧
      fastNext.op = l.op ∧ fastNext.len = l.len ∧
      fastNext.out = l.out ∧
      slowNext.put = slow.put ∧ slowNext.left = slow.left ∧
      l.op.toNat ≤ slowNext.bits.toNat ∧
      slowNext.bits.toNat ≤ 30 := by
  by_cases needsPull : l.bits < l.op
  · have small : slow.bits.toNat ≤ 22 := by
      have less := UInt32.lt_iff_toNat_lt.mp needsPull
      rw [packet.bits] at less
      omega
    obtain ⟨next, fast1, slow1, pullRun, _, slow1Eq,
      fast1Eq, packet1, _, buffers1, stream1⟩ :=
      packet.pull_default_state invariant buffers small
    have bits1 : slow1.bits.toNat = slow.bits.toNat + 8 := by
      rw [slow1Eq]
      exact u32_add8 slow.bits (by omega)
    refine ⟨1, slow1, fast1, by omega, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [needsPull, ite_true]
      exact pullRun
    · simpa only [List.drop, List.drop_cons] using packet1
    · simpa only [List.drop, List.drop_cons] using buffers1
    · simpa only [List.drop, List.drop_cons] using stream1
    · simp only [fast1Eq, Zlib.Inffast.Proofs.pullL]
    · simp only [fast1Eq, Zlib.Inffast.Proofs.pullL]
    · simp only [fast1Eq, Zlib.Inffast.Proofs.pullL]
    · simp only [slow1Eq, pulled]
    · simp only [slow1Eq, pulled]
    · rw [bits1]
      omega
    · rw [bits1]
      omega
  · have fits : l.op.toNat ≤ slow.bits.toNat := by
      have less : ¬ l.bits.toNat < l.op.toNat := by
        intro hlt
        exact needsPull (UInt32.lt_iff_toNat_lt.mpr hlt)
      rw [packet.bits] at less
      omega
    refine ⟨0, slow, l, by omega, ?_, ?_, ?_, ?_,
      rfl, rfl, rfl, rfl, rfl, fits, bitsBound⟩
    · simp [needsPull, C.run, pure]
    · simpa only [List.drop_zero] using packet
    · simpa only [List.drop_zero] using buffers
    · simp only [List.drop_zero]

#print axioms FastInputPacket.dolenLen_extra_prefix
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec

/-- The independent length extra read identifies the actual held low bits
after the translated optional one-byte pull. The same `used` indexes the
physical unread byte slice; no whole-object input equality is required. -/
theorem FastInputPacket.dolenLen_extra_read
    {h : Heap} {slow : IL}
    {first second third fourth fifth : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: fifth :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: fifth :: rest))
    (extraWidth : l.op.toNat ≤ 5)
    (bitsBound : slow.bits.toNat ≤ 30)
    {symbol lengthExtra : Nat} {r1 r2 : List Bool}
    (width : l.op.toNat =
      lengthExtras.getD (symbol - 257) 0)
    (lengthInput : r1 = stream slow
      (first :: second :: third :: fourth :: fifth :: rest))
    (lengthBits : readBits
      (lengthExtras.getD (symbol - 257) 0) r1 =
      some (lengthExtra, r2)) :
    ∃ used slowNext fastNext,
      used ≤ 1 ∧
      C.run (if l.bits < l.op then Zlib.Inffast.pull l
        else pure l) h = .ok (fastNext, h) ∧
      FastInputPacket h slowNext
        ((first :: second :: third :: fourth :: fifth :: rest).drop used)
        fastNext ∧
      DispatchBuffers h r slowNext
        ((first :: second :: third :: fourth :: fifth :: rest).drop used) ∧
      fastNext.op = l.op ∧ fastNext.len = l.len ∧
      fastNext.out = l.out ∧
      slowNext.put = slow.put ∧ slowNext.left = slow.left ∧
      l.op.toNat ≤ slowNext.bits.toNat ∧
      slowNext.bits.toNat ≤ 30 ∧
      stream slowNext
        ((first :: second :: third :: fourth :: fifth :: rest).drop used) =
        stream slow
          (first :: second :: third :: fourth :: fifth :: rest) ∧
      lengthExtra = fastNext.hold.toNat % 2 ^ l.op.toNat ∧
      r2 = (stream slowNext
        ((first :: second :: third :: fourth :: fifth :: rest).drop used)).drop
          l.op.toNat := by
  obtain ⟨used, slowNext, fastNext, usedBound,
    prefixRun, nextPacket, nextBuffers, streamEq,
    opEq, lenEq, outEq, putEq, leftEq, fits,
    bitsNext⟩ :=
    packet.dolenLen_extra_prefix invariant buffers
      extraWidth bitsBound
  let remain := (first :: second :: third :: fourth :: fifth :: rest).drop used
  have read := readBits_held_stream slowNext remain
    l.op.toNat fits
  have selected : readBits l.op.toNat (stream slowNext remain) =
      some (lengthExtra, r2) := by
    rw [streamEq, ← lengthInput, width]
    exact lengthBits
  rw [read] at selected
  have actualExtra : lengthExtra =
      fastNext.hold.toNat % 2 ^ l.op.toNat := by
    simpa only [Prod.fst, ← nextPacket.hold] using
      (congrArg Prod.fst (Option.some.inj selected)).symm
  have actualRest : r2 =
      (stream slowNext remain).drop l.op.toNat := by
    simpa only [Prod.snd] using
      (congrArg Prod.snd (Option.some.inj selected)).symm
  exact ⟨used, slowNext, fastNext, usedBound,
    prefixRun, nextPacket, nextBuffers, opEq, lenEq, outEq,
    putEq, leftEq, fits, bitsNext, streamEq, actualExtra,
    actualRest⟩

#print axioms FastInputPacket.dolenLen_extra_read
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec

/-- Reassembles the actual positive-extra branch of translated `dolenLen`
from its optional pull and exact `dolenExt` suffix. -/
private theorem dolenLen_positive_from_prefix
    {h after : Heap} {c : Zlib.Inffast.Ctx}
    {l fast result : Zlib.Inffast.L}
    (positive : l.op ≠ 0)
    (prefixRun : C.run
      (if l.bits < l.op then Zlib.Inffast.pull l else pure l) h =
      .ok (fast, h))
    (extRun : C.run (Zlib.Inffast.Proofs.dolenExt c fast) h =
      .ok (result, after)) :
    C.run (Zlib.Inffast.Proofs.dolenLen c l) h =
      .ok (result, after) := by
  have nonzero : (l.op != 0) = true := by
    simp [positive]
  by_cases needsPull : l.bits < l.op
  · have pullRun : C.run (Zlib.Inffast.pull l) h =
        .ok (fast, h) := by
      simpa only [needsPull, ite_true] using prefixRun
    change (Zlib.Inffast.Proofs.dolenLen c l) h =
      .ok (result, after)
    unfold Zlib.Inffast.Proofs.dolenLen
    simp only [nonzero, ite_true, needsPull]
    rw [bind_ok (by simpa only [C.run] using pullRun)]
    exact extRun
  · have fastEq : fast = l := by
      have pureRun : C.run (pure l : C.M Zlib.Inffast.L) h =
          .ok (fast, h) := by
        simpa only [needsPull, ite_false] using prefixRun
      have fields : fast = l ∧ h = h := by
        simpa only [C.run, pure, Except.ok.injEq,
          Prod.mk.injEq] using pureRun.symm
      exact fields.1
    change (Zlib.Inffast.Proofs.dolenLen c l) h =
      .ok (result, after)
    unfold Zlib.Inffast.Proofs.dolenLen
    simp only [nonzero, ite_true, needsPull, ite_false]
    simpa only [fastEq, C.run] using extRun

#print axioms dolenLen_positive_from_prefix
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec

/-- The translated `dolenLen` positive-extra branch with enough held bits
keeps the independently decoded extra value through the actual full suffix. -/
theorem FastInputPacket.dolenLen_no_pull_length_semantics
    {h : Heap} {slow : IL}
    {first second third fourth fifth : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: fifth :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: fifth :: rest))
    (positive : l.op ≠ 0)
    (noPull : ¬ l.bits < l.op)
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
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h))
    {symbol lengthExtra : Nat} {r1 r2 : List Bool}
    (width : l.op.toNat =
      lengthExtras.getD (symbol - 257) 0)
    (lengthInput : r1 = stream slow
      (first :: second :: third :: fourth :: fifth :: rest))
    (lengthBits : readBits
      (lengthExtras.getD (symbol - 257) 0) r1 =
      some (lengthExtra, r2)) :
    ∃ used consumed slowNext result after,
      used ≤ 4 ∧ consumed ≤ 33 ∧
      C.run (Zlib.Inffast.Proofs.dolenLen c l) h =
        .ok (result, after) ∧
      FastInputPacket after slowNext
        ((first :: second :: third :: fourth :: fifth :: rest).drop used)
        result ∧
      stream slowNext
        ((first :: second :: third :: fourth :: fifth :: rest).drop used) =
        (stream slow
          (first :: second :: third :: fourth :: fifth :: rest)).drop consumed ∧
      (FastDistancePost h after r zs z s slowNext
        ((first :: second :: third :: fourth :: fifth :: rest).drop used)
        result dest output j (l.len.toNat + lengthExtra) ∨
       ∃ i, result.broke = true ∧
         after = badHeap h r zs z s i) := by
  have fits : l.op.toNat ≤ slow.bits.toNat := by
    have noLess : ¬ l.bits.toNat < l.op.toNat := by
      intro hlt
      exact noPull (UInt32.lt_iff_toNat_lt.mpr hlt)
    rw [packet.bits] at noLess
    omega
  obtain ⟨extraEq, restEq, used, consumed, slowNext,
    result, after, usedBound, consumedBound, extRun,
    packetNext, sourceNext, outcome⟩ :=
    packet.dolenExt_length_extra_semantics invariant
      buffers streamPtr statePtr whaveEq wsizeEq
      wnextEq windowEq dcodePtr codesGet safe mask
      extraWidth fits bitsBound left avail length
      outPtr outputPtr begPtr endPtr outputGet outputWrite
      outputSize current beginLe span guard
      width lengthInput lengthBits
  have prefixRun : C.run
      (if l.bits < l.op then Zlib.Inffast.pull l else pure l) h =
      .ok (l, h) := by
    simp [noPull, C.run, pure]
  have fullRun := dolenLen_positive_from_prefix positive
    prefixRun extRun
  exact ⟨used, consumed, slowNext, result, after,
    usedBound, consumedBound, fullRun, packetNext,
    sourceNext, outcome⟩

#print axioms FastInputPacket.dolenLen_no_pull_length_semantics
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec

/-- The translated one-pull length-extra branch preserves the independent
extra value and the same physical input-count witness through `dolenLen`. -/
theorem FastInputPacket.dolenLen_one_pull_length_semantics
    {h : Heap} {slow : IL}
    {first second third fourth fifth : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: fifth :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: fifth :: rest))
    (positive : l.op ≠ 0)
    (needsPull : l.bits < l.op)
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
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h))
    {symbol lengthExtra : Nat} {r1 r2 : List Bool}
    (width : l.op.toNat =
      lengthExtras.getD (symbol - 257) 0)
    (lengthInput : r1 = stream slow
      (first :: second :: third :: fourth :: fifth :: rest))
    (lengthBits : readBits
      (lengthExtras.getD (symbol - 257) 0) r1 =
      some (lengthExtra, r2)) :
    ∃ used consumed slowNext result after,
      used ≤ 5 ∧ consumed ≤ 33 ∧
      C.run (Zlib.Inffast.Proofs.dolenLen c l) h =
        .ok (result, after) ∧
      FastInputPacket after slowNext
        ((first :: second :: third :: fourth :: fifth :: rest).drop used)
        result ∧
      stream slowNext
        ((first :: second :: third :: fourth :: fifth :: rest).drop used) =
        (stream slow
          (first :: second :: third :: fourth :: fifth :: rest)).drop consumed ∧
      (FastDistancePost h after r zs z s slowNext
        ((first :: second :: third :: fourth :: fifth :: rest).drop used)
        result dest output j (l.len.toNat + lengthExtra) ∨
       ∃ i, result.broke = true ∧
         after = badHeap h r zs z s i) := by
  have small : slow.bits.toNat ≤ 22 := by
    have less := UInt32.lt_iff_toNat_lt.mp needsPull
    rw [packet.bits] at less
    omega
  obtain ⟨next, fast1, slow1, pullRun, _, slow1Eq,
    fast1Eq, packet1, _, buffers1, stream1⟩ :=
    packet.pull_default_state invariant buffers small
  have opEq : fast1.op = l.op := by
    rw [fast1Eq]
    rfl
  have lenEq : fast1.len = l.len := by
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
  have width1 : fast1.op.toNat ≤ 5 := by rw [opEq]; exact extraWidth
  have length1 : 3 ≤ fast1.len.toNat ∧
      fast1.len.toNat + 2 ^ fast1.op.toNat ≤ 259 := by
    simpa only [opEq, lenEq] using length
  have out1 : fast1.out = .ref dest j := by
    rw [fast1Eq]
    exact outPtr
  have put1 : slow1.put = .ref dest oo := by
    rw [slow1Eq]
    exact outputPtr
  have end1 : c.end_ = .ref dest
      (oo + slow1.left.toNat - 257) := by
    simpa only [slow1Eq, pulled] using endPtr
  have size1 : oo + slow1.left.toNat ≤ output.size := by
    simpa only [slow1Eq, pulled] using outputSize
  have guard1 : C.run (Ptr.lt fast1.out c.end_) h =
      .ok (true, h) := by
    rw [out1]
    simpa only [outPtr] using guard
  have left1 : slow1.left ≠ 0 := by
    simpa only [slow1Eq, pulled] using left
  have avail1 : 258 ≤ slow1.left.toNat := by
    simpa only [slow1Eq, pulled] using avail
  have input1 : r1 = stream slow1
      (second :: third :: fourth :: fifth :: rest) := by
    rw [lengthInput, stream1]
  obtain ⟨extraEq, restEq, usedExt, consumed,
    slowNext, result, after, usedBound, consumedBound,
    extRun, packetNext, sourceNext, outcome⟩ :=
    packet1.dolenExt_length_extra_semantics invariant
      buffers1 streamPtr statePtr whaveEq wsizeEq
      wnextEq windowEq dcodePtr codesGet safe mask
      width1 fits1 bound1 left1 avail1 length1
      out1 put1 begPtr end1 outputGet outputWrite
      size1 current beginLe span guard1
      (by rw [opEq]; exact width) input1 lengthBits
  have prefixRun : C.run
      (if l.bits < l.op then Zlib.Inffast.pull l else pure l) h =
      .ok (fast1, h) := by
    simpa only [needsPull, ite_true] using pullRun
  have fullRun := dolenLen_positive_from_prefix positive
    prefixRun extRun
  let used := 1 + usedExt
  have tailEq :
      (second :: third :: fourth :: fifth :: rest).drop usedExt =
      (first :: second :: third :: fourth :: fifth :: rest).drop used := by
    calc
      (second :: third :: fourth :: fifth :: rest).drop usedExt =
          ((first :: second :: third :: fourth :: fifth :: rest).drop 1).drop usedExt := rfl
      _ = (first :: second :: third :: fourth :: fifth :: rest).drop used := by
        simp only [used, List.drop_drop]
  have packetFinal : FastInputPacket after slowNext
      ((first :: second :: third :: fourth :: fifth :: rest).drop used)
      result := by simpa only [← tailEq] using packetNext
  have streamFinal : stream slowNext
      ((first :: second :: third :: fourth :: fifth :: rest).drop used) =
      (stream slow
        (first :: second :: third :: fourth :: fifth :: rest)).drop consumed := by
    rw [← tailEq, sourceNext, stream1]
  have finalOutcome : FastDistancePost h after r zs z s slowNext
      ((first :: second :: third :: fourth :: fifth :: rest).drop used)
      result dest output j (l.len.toNat + lengthExtra) ∨
      ∃ i, result.broke = true ∧
        after = badHeap h r zs z s i := by
    simpa only [← tailEq, lenEq] using outcome
  exact ⟨used, consumed, slowNext, result, after,
    by dsimp only [used]; omega, consumedBound, fullRun,
    packetFinal, streamFinal, finalOutcome⟩

#print axioms FastInputPacket.dolenLen_one_pull_length_semantics
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec

/-- Zero length-extra bits dispatch the actual `dolenRefill` path with no
additional length consumption. -/
theorem FastInputPacket.dolenLen_zero_extra_semantics
    {h : Heap} {slow : IL}
    {first second third fourth fifth : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: fifth :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: fifth :: rest))
    (zero : l.op = 0)
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
      C.run (Zlib.Inffast.Proofs.dolenLen c l) h =
        .ok (result, after) ∧
      FastInputPacket after slowNext
        ((first :: second :: third :: fourth :: fifth :: rest).drop used)
        result ∧
      stream slowNext
        ((first :: second :: third :: fourth :: fifth :: rest).drop used) =
        (stream slow
          (first :: second :: third :: fourth :: fifth :: rest)).drop consumed ∧
      (FastDistancePost h after r zs z s slowNext
        ((first :: second :: third :: fourth :: fifth :: rest).drop used)
        result dest output j l.len.toNat ∨
       ∃ i, result.broke = true ∧
         after = badHeap h r zs z s i) := by
  obtain ⟨used, consumed, slowNext, result, after,
    usedBound, consumedBound, refillRun, _, packetNext,
    _, _, sourceNext, outcome⟩ :=
    packet.dolenRefill_default_state invariant buffers
      streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
      dcodePtr codesGet safe mask bitsBound left avail length
      outPtr outputPtr begPtr endPtr outputGet outputWrite
      outputSize current beginLe span guard
  have fullRun : C.run (Zlib.Inffast.Proofs.dolenLen c l) h =
      .ok (result, after) := by
    unfold Zlib.Inffast.Proofs.dolenLen
    simp only [zero, bne_self_eq_false, Bool.false_eq_true,
      ite_false]
    exact refillRun
  refine ⟨used, consumed, slowNext, result, after,
    usedBound, consumedBound, fullRun, packetNext,
    sourceNext, ?_⟩
  rcases outcome with copied | bad
  · exact Or.inl copied
  · rcases bad with ⟨i, broke, heapEq, _⟩
    exact Or.inr ⟨i, broke, heapEq⟩

#print axioms FastInputPacket.dolenLen_zero_extra_semantics
end Zlib.Inflate.Proofs

