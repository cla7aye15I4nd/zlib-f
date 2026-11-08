import ZlibF.Proof.«inflate.c.fast-view-dist-loop-bit-budget»
import ZlibF.Proof.«inflate.c.fast-view-body-output-bridge»
import ZlibF.Proof.«inffast.c.length-bit-ledger»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- The actual distance lookup suffix retains one count for input cursor and bits. -/
theorem FastInputPacket.dolenDist_bit_budget
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
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth : Nat}
    (dcodePtr : c.dcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : DistTableSafe codes baseOff rootWidth)
    (mask : c.dmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (held : 15 ≤ slow.bits.toNat)
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
    ∃ result after pulled,
      pulled ≤ 2 ∧
      C.run (Zlib.Inffast.Proofs.dolenDist c l) h = .ok (result, after) ∧
      result.in_ = inputAdvance l.in_ pulled ∧
      result.bits.toNat ≤ l.bits.toNat + 8 * pulled := by
  let idx : Nat := (l.hold &&& c.dmask.toUInt64).toNat
  have idxEq : idx = l.hold.toNat % 2 ^ rootWidth :=
    Zlib.Inffast.Proofs.u64_and_mask mask
  have idxBound : idx < 2 ^ rootWidth := by
    rw [idxEq]
    exact Nat.mod_lt _ (Nat.pow_pos (by omega))
  have addRun : C.run (Ptr.add c.dcode idx) h =
      .ok (.ref codeRef (baseOff + idx), h) := by
    rw [dcodePtr]
    exact Ptr.add_nat_ok codesGet (by
      have rootSize := safe.2.1
      omega)
  let selected : Zlib.Inffast.L :=
    { l with here := .ref codeRef (baseOff + idx) }
  have selectedPacket : FastInputPacket h slow
      (first :: second :: rest) selected :=
    ⟨packet.source, packet.cursor, packet.hold, packet.bits⟩
  obtain ⟨result, after, pulled, pulledBound, loopRun,
    cursor, budget⟩ :=
    selectedPacket.dodist_loop_bit_budget invariant buffers
      streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
      (by rfl) dcodePtr codesGet safe idxBound held left avail
      length outPtr outputPtr begPtr endPtr outputGet
      outputWrite outputSize current beginLe span guard
  have run : C.run (Zlib.Inffast.Proofs.dolenDist c l) h =
      .ok (result, after) := by
    change (Zlib.Inffast.Proofs.dolenDist c l) h =
      .ok (result, after)
    unfold Zlib.Inffast.Proofs.dolenDist
    change Ptr.add c.dcode idx h =
      .ok (.ref codeRef (baseOff + idx), h) at addRun
    rw [bind_ok addRun]
    simpa [C.run, selected] using loopRun
  exact ⟨result, after, pulled, pulledBound, run,
    by simpa only [selected] using cursor,
    by simpa only [selected] using budget⟩

#print axioms FastInputPacket.dolenDist_bit_budget
/-- The optional two-byte refill and distance lookup share a physical pull count. -/
theorem FastInputPacket.dolenRefill_bit_budget
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
    ∃ result after pulled,
      pulled ≤ 4 ∧
      C.run (Zlib.Inffast.Proofs.dolenRefill c l) h = .ok (result, after) ∧
      result.in_ = inputAdvance l.in_ pulled ∧
      result.bits.toNat ≤ l.bits.toNat + 8 * pulled := by
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
    have slowBits2 : slow2.bits.toNat = slow.bits.toNat + 16 := by
      rw [slow2Eq]
      change (slow1.bits + 8).toNat = slow.bits.toNat + 16
      rw [u32_add8 slow1.bits (by omega)]
      have slowBits1 : slow1.bits.toNat = slow.bits.toNat + 8 := by
        rw [slow1Eq]
        exact u32_add8 slow.bits (by omega)
      omega
    have held2 : 15 ≤ slow2.bits.toNat := by omega
    have left2 : slow2.left ≠ 0 := by
      simpa only [slow2Eq, slow1Eq, pulled] using left
    have avail2 : 258 ≤ slow2.left.toNat := by
      simpa only [slow2Eq, slow1Eq, pulled] using avail
    have length2 : 3 ≤ fast2.len.toNat ∧ fast2.len.toNat ≤ 258 := by
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
    obtain ⟨result, after, distancePulled, distanceBound,
      distRun, distCursor, distBits⟩ :=
      packet2.dolenDist_bit_budget invariant buffers2
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
      change (Zlib.Inffast.pull l) h = .ok (fast1, h) at pull1
      change (Zlib.Inffast.pull fast1) h = .ok (fast2, h) at pull2
      change (Zlib.Inffast.Proofs.dolenDist c fast2) h =
        .ok (result, after) at distRun
      simp only [bind_app, pull1, pull2, distRun]
    refine ⟨result, after, 2 + distancePulled,
      by omega, run, ?_, ?_⟩
    · rw [distCursor]
      simp only [fast2Eq, fast1Eq, Zlib.Inffast.Proofs.pullL]
      rw [next2Eq, inputAdvance_add]
      simp only [slow1Eq, pulled]
      rw [next1Eq, ← packet.cursor, inputAdvance_add]
      congr 1
      omega
    · have fast2Bits : fast2.bits.toNat = slow.bits.toNat + 16 := by
        rw [packet2.bits]
        exact slowBits2
      rw [fast2Bits] at distBits
      rw [packet.bits]
      omega
  · have held : 15 ≤ slow.bits.toNat := by
      have notSmall : ¬ l.bits.toNat < 15 := by
        intro less
        exact needsPull (UInt32.lt_iff_toNat_lt.mpr less)
      rw [packet.bits] at notSmall
      omega
    obtain ⟨result, after, pulled, bound, distRun,
      cursor, bits⟩ :=
      packet.dolenDist_bit_budget invariant buffers
        streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
        dcodePtr codesGet safe mask held left avail length
        outPtr outputPtr begPtr endPtr outputGet outputWrite
        outputSize current beginLe span guard
    have run : C.run (Zlib.Inffast.Proofs.dolenRefill c l) h =
        .ok (result, after) := by
      unfold Zlib.Inffast.Proofs.dolenRefill
      simp only [needsPull, ite_false]
      exact distRun
    exact ⟨result, after, pulled, by omega, run, cursor, bits⟩

#print axioms FastInputPacket.dolenRefill_bit_budget
/-- The actual extra-length bit drop and refill retain one cursor count and bit budget. -/
theorem FastInputPacket.dolenExt_bit_budget
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
    (extraFits : l.op.toNat ≤ slow.bits.toNat)
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
    ∃ result after pulled,
      pulled ≤ 4 ∧
      C.run (Zlib.Inffast.Proofs.dolenExt c l) h = .ok (result, after) ∧
      result.in_ = inputAdvance l.in_ pulled ∧
      result.bits.toNat ≤ l.bits.toNat + 8 * pulled := by
  let extra : Nat := l.hold.toNat % 2 ^ l.op.toNat
  have opSmall : l.op.toNat < 32 := by omega
  have low := Zlib.Inffast.Proofs.hold_low32
    (x := l.hold) (k := l.op) opSmall
  have extraBound : extra < 2 ^ l.op.toNat := by
    exact Nat.mod_lt _ (Nat.pow_pos (by omega))
  have lenSum : l.len.toNat + extra ≤ 258 := by omega
  let delta : UInt32 := l.hold.toUInt32 &&&
    (((1 : UInt32) <<< l.op) - 1)
  have deltaEq : delta.toNat = extra := by
    simpa only [delta, extra] using low
  have lenValue : (l.len + delta).toNat =
      l.len.toNat + extra := by
    rw [Zlib.Inffast.Proofs.u32_toNat_add
      (by rw [deltaEq]; omega), deltaEq]
  have shlRun : Zlib.Inffast.shl32 1 l.op h =
      .ok ((1 : UInt32) <<< l.op, h) :=
    Zlib.Inffast.Proofs.shl32_ok opSmall
  have shrRun : Zlib.Inffast.shr64 l.hold l.op.toUInt64 h =
      .ok (l.hold >>> l.op.toUInt64, h) := by
    apply Zlib.Inffast.Proofs.shr64_ok
    rw [UInt32.toNat_toUInt64]
    omega
  let afterLen : Zlib.Inffast.L := { l with len := l.len + delta }
  have afterLenPacket : FastInputPacket h slow
      (first :: second :: third :: fourth :: rest) afterLen :=
    ⟨packet.source, packet.cursor, packet.hold, packet.bits⟩
  have within : l.op.toNat ≤ slow.bits.toNat := extraFits
  have dropped := afterLenPacket.drop_bits_default_state buffers
    l.op within (by omega)
  let slowDrop : IL := { slow with
    hold := slow.hold >>> l.op.toUInt64,
    bits := slow.bits - l.op }
  let fastDrop : Zlib.Inffast.L := { afterLen with
    hold := afterLen.hold >>> l.op.toUInt64,
    bits := afterLen.bits - l.op }
  have dropPacket : FastInputPacket h slowDrop
      (first :: second :: third :: fourth :: rest) fastDrop :=
    dropped.1
  have dropBuffers : DispatchBuffers h r slowDrop
      (first :: second :: third :: fourth :: rest) :=
    dropped.2.1
  have dropStream : stream slowDrop
      (first :: second :: third :: fourth :: rest) =
      (stream slow
        (first :: second :: third :: fourth :: rest)).drop
          l.op.toNat := dropped.2.2.1
  have dropBits : slowDrop.bits.toNat =
      slow.bits.toNat - l.op.toNat := dropped.2.2.2
  have dropBound : slowDrop.bits.toNat ≤ 30 := by omega
  have dropLength : 3 ≤ fastDrop.len.toNat ∧
      fastDrop.len.toNat ≤ 258 := by
    simpa only [fastDrop, afterLen, lenValue] using
      (show 3 ≤ l.len.toNat + extra ∧
        l.len.toNat + extra ≤ 258 by omega)
  have dropOut : fastDrop.out = .ref dest j := outPtr
  have dropPut : slowDrop.put = .ref dest oo := outputPtr
  have dropEnd : c.end_ = .ref dest
      (oo + slowDrop.left.toNat - 257) := endPtr
  have dropSize : oo + slowDrop.left.toNat ≤ output.size :=
    outputSize
  have dropGuard : C.run (Ptr.lt fastDrop.out c.end_) h =
      .ok (true, h) := guard
  obtain ⟨result, after, pulled, pulledBound, refillRun,
    cursor, bits⟩ :=
    dropPacket.dolenRefill_bit_budget invariant dropBuffers
      streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
      dcodePtr codesGet safe mask dropBound left avail
      dropLength dropOut dropPut begPtr dropEnd outputGet
      outputWrite dropSize current beginLe span dropGuard
  have run : C.run (Zlib.Inffast.Proofs.dolenExt c l) h =
      .ok (result, after) := by
    change (Zlib.Inffast.Proofs.dolenExt c l) h =
      .ok (result, after)
    unfold Zlib.Inffast.Proofs.dolenExt
    rw [bind_ok shlRun]
    rw [bind_ok shrRun]
    simpa only [fastDrop, afterLen, delta, C.run] using refillRun
  have fastDropBits : fastDrop.bits.toNat ≤ l.bits.toNat := by
    rw [dropPacket.bits]
    rw [packet.bits]
    omega
  exact ⟨result, after, pulled, pulledBound, run,
    by simpa only [fastDrop, afterLen] using cursor,
    by omega⟩


#print axioms FastInputPacket.dolenExt_bit_budget
/-- The actual length-extra selector, optional pull, refill, and distance lookup retain one cursor count and bit budget. -/
theorem FastInputPacket.dolenLen_bit_budget
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
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h)) :
    ∃ result after pulled,
      pulled ≤ 5 ∧
      C.run (Zlib.Inffast.Proofs.dolenLen c l) h = .ok (result, after) ∧
      result.in_ = inputAdvance l.in_ pulled ∧
      result.bits.toNat ≤ l.bits.toNat + 8 * pulled := by
  by_cases hasExtra : l.op != 0
  · by_cases needsPull : l.bits < l.op
    · have small : slow.bits.toNat ≤ 22 := by
        have less := UInt32.lt_iff_toNat_lt.mp needsPull
        rw [packet.bits] at less
        omega
      obtain ⟨next1, fast1, slow1, pullRun, next1Eq,
        slow1Eq, fast1Eq, packet1, _, buffers1, stream1⟩ :=
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
      obtain ⟨result, after, extPulled, extBound, extRun,
        extCursor, extBits⟩ :=
        packet1.dolenExt_bit_budget invariant buffers1
          streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
          dcodePtr codesGet safe mask width1 fits1 bound1
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
      have firstBits : fast1.bits.toNat = l.bits.toNat + 8 := by
        rw [packet1.bits, slow1Eq]
        change (slow.bits + 8).toNat = l.bits.toNat + 8
        rw [u32_add8 slow.bits (by omega), packet.bits]
      refine ⟨result, after, 1 + extPulled, by omega,
        run, ?_, ?_⟩
      · rw [extCursor]
        simp only [fast1Eq, Zlib.Inffast.Proofs.pullL]
        rw [next1Eq, ← packet.cursor, inputAdvance_add]
      · rw [firstBits] at extBits
        omega
    · have fits : l.op.toNat ≤ slow.bits.toNat := by
        have noLess : ¬ l.op.toNat > l.bits.toNat := by
          intro h
          exact needsPull (UInt32.lt_iff_toNat_lt.mpr h)
        rw [packet.bits] at noLess
        omega
      obtain ⟨result, after, pulled, bound, extRun,
        cursor, bits⟩ :=
        packet.dolenExt_bit_budget invariant buffers
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
      exact ⟨result, after, pulled, by omega, run, cursor, bits⟩
  · have opZero : l.op = 0 := by
      simpa using hasExtra
    have length0 : 3 ≤ l.len.toNat ∧ l.len.toNat ≤ 258 := by
      rw [opZero] at length
      simp only [UInt32.toNat_zero, Nat.pow_zero] at length
      omega
    obtain ⟨result, after, pulled, bound, refillRun,
      cursor, bits⟩ :=
      packet.dolenRefill_bit_budget invariant buffers
        streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
        dcodePtr codesGet safe mask bitsBound left avail
        length0 outPtr outputPtr begPtr endPtr outputGet
        outputWrite outputSize current beginLe span guard
    have run : C.run (Zlib.Inffast.Proofs.dolenLen c l) h =
        .ok (result, after) := by
      unfold Zlib.Inffast.Proofs.dolenLen
      simp only [hasExtra]
      exact refillRun
    exact ⟨result, after, pulled, by omega, run, cursor, bits⟩


#print axioms FastInputPacket.dolenLen_bit_budget
/-- Any given successful run of the actual length suffix has the same cursor and bit budget. -/
theorem FastInputPacket.dolenLen_result_bit_budget
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
    {result : Zlib.Inffast.L} {after : Heap}
    (run : C.run (Zlib.Inffast.Proofs.dolenLen c l) h =
      .ok (result, after)) :
    ∃ pulled, pulled ≤ 5 ∧
      result.in_ = inputAdvance l.in_ pulled ∧
      result.bits.toNat ≤ l.bits.toNat + 8 * pulled := by
  obtain ⟨found, foundAfter, pulled, bound, foundRun,
      cursor, bits⟩ :=
    packet.dolenLen_bit_budget invariant buffers streamPtr statePtr
      whaveEq wsizeEq wnextEq windowEq dcodePtr codesGet safe
      mask extraWidth bitsBound left avail length outPtr outputPtr
      begPtr endPtr outputGet outputWrite outputSize current
      beginLe span guard
  have same : (result, after) = (found, foundAfter) :=
    Except.ok.inj (run.symm.trans foundRun)
  have resultEq : result = found := congrArg Prod.fst same
  subst found
  exact ⟨pulled, bound, cursor, bits⟩

#print axioms FastInputPacket.dolenLen_result_bit_budget
end Zlib.Inflate.Proofs
