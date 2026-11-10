import ZlibF.Proof.«inflate.c.fast-arbitrary-body-rejection»
namespace Zlib.Inflate.Proofs.FastArbitraryBody
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inffast.Spec Zlib.Inftrees
open Zlib.Inffast.Proofs
set_option autoImplicit false
set_option maxRecDepth 8192

/-- The optional real length-extra pull is total on the current capacity.
No complete token or future input is presumed. -/
theorem length_optional_current_pull
    {h : Heap} {slow : IL} {bs : List UInt8} {l : Zlib.Inffast.L}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs) (extra : l.op.toNat ≤ 5) (bits : slow.bits.toNat ≤ 30)
    (capacity : l.op.toNat ≤ (stream slow bs).length) :
    ∃ used next localRegs,
      used ≤ 1 ∧ used ≤ bs.length ∧
      localRegs.in_ = inputAdvance l.in_ used ∧
      C.run (if l.bits < l.op then Zlib.Inffast.pull l else pure l) h = .ok (localRegs, h) ∧
      FastInputPacket h next (bs.drop used) localRegs ∧ DispatchBuffers h r next (bs.drop used) ∧
      stream next (bs.drop used) = stream slow bs ∧
      localRegs.op = l.op ∧ localRegs.len = l.len ∧ localRegs.out = l.out ∧
      localRegs.againL = l.againL ∧ localRegs.broke = l.broke ∧
      next.put = slow.put ∧ next.left = slow.left ∧
      l.op.toNat ≤ next.bits.toNat ∧ next.bits.toNat ≤ 30 := by
  by_cases needs : l.bits < l.op
  · have short : slow.bits.toNat < l.op.toNat := by rw [← packet.bits]; exact UInt32.lt_iff_toNat_lt.mp needs
    cases bs with
    | nil => simp only [stream, bytesBits, List.flatMap_nil, List.append_nil, natBits_length] at capacity; omega
    | cons byte tail =>
      obtain ⟨nextPtr, localRegs, next, actual, _nextPtrEq, nextEq, localEq, nextPacket, _current, nextBuffers, source⟩ :=
        packet.pull_default_state invariant buffers (by omega)
      have nextBits : next.bits.toNat = slow.bits.toNat + 8 := by rw [nextEq]; exact u32_add8 _ (by omega)
      exact ⟨1, next, localRegs, by omega, by simp, (by rw [localEq]; change nextPtr = inputAdvance l.in_ 1; rw [packet.cursor]; exact _nextPtrEq), by simp only [needs, ite_true]; exact actual,
        nextPacket, nextBuffers, source,
        by simp only [localEq, pullL], by simp only [localEq, pullL], by simp only [localEq, pullL],
        by simp only [localEq, pullL], by simp only [localEq, pullL],
        by rw [nextEq]; rfl, by rw [nextEq]; rfl, by omega, by omega⟩
  · have fits : l.op.toNat ≤ slow.bits.toNat := by
      have notShort : ¬ l.bits.toNat < l.op.toNat := fun bad => needs (UInt32.lt_iff_toNat_lt.mpr bad)
      rw [packet.bits] at notShort
      omega
    exact ⟨0, slow, l, by omega, by omega, (by cases l.in_ <;> simp [inputAdvance]), by simp [needs, C.run, pure],
      by simpa only [List.drop_zero] using packet, by simpa only [List.drop_zero] using buffers,
      by simp only [List.drop_zero], rfl, rfl, rfl, rfl, rfl, rfl, rfl, fits, bits⟩

/-- The actual length-extra code determines its independent read and
exact scalar length, then exposes the real distance-refill continuation.
All current bytes, including zero and repeated values, remain in source. -/
theorem length_extra_current_source
    {h : Heap} {slow : IL} {bs : List UInt8} {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs) (extraWidth : l.op.toNat ≤ 5) (bits : slow.bits.toNat ≤ 30)
    (length : 3 ≤ l.len.toNat ∧ l.len.toNat + 2 ^ l.op.toNat ≤ 259)
    (capacity : l.op.toNat ≤ (stream slow bs).length) :
    ∃ used next localRegs extra,
      used ≤ 1 ∧ used ≤ bs.length ∧
      localRegs.in_ = inputAdvance l.in_ used ∧
      C.run (dolenLen c l) h = C.run (dolenRefill c localRegs) h ∧
      FastInputPacket h next (bs.drop used) localRegs ∧ DispatchBuffers h r next (bs.drop used) ∧
      readBits l.op.toNat (stream slow bs) = some (extra, stream next (bs.drop used)) ∧
      (stream next (bs.drop used)) = (stream slow bs).drop l.op.toNat ∧
      localRegs.len.toNat = l.len.toNat + extra ∧ 3 ≤ localRegs.len.toNat ∧ localRegs.len.toNat ≤ 258 ∧
      localRegs.out = l.out ∧ localRegs.againL = l.againL ∧ localRegs.broke = l.broke ∧
      next.put = slow.put ∧ next.left = slow.left ∧ next.bits.toNat ≤ 30 := by
  obtain ⟨used, pulledSlow, pulledFast, one, raw, inputEq, actual, pulledPacket, pulledBuffers, source,
    opEq, lenEq, outEq, againEq, brokeEq, putEq, leftEq, fit, bound⟩ :=
    length_optional_current_pull packet invariant buffers extraWidth bits capacity
  have pullWidth : pulledFast.op.toNat ≤ 5 := by rw [opEq]; exact extraWidth
  have pullFits : pulledFast.op.toNat ≤ pulledSlow.bits.toNat := by rw [opEq]; exact fit
  let count := pulledFast.op
  obtain ⟨dropPacket, dropBuffers, dropSource, dropBits⟩ := pulledPacket.drop_bits_default_state pulledBuffers count pullFits (by dsimp only [count]; omega)
  let next := {pulledSlow with hold := pulledSlow.hold >>> count.toUInt64, bits := pulledSlow.bits - count}
  let value := pulledFast.hold.toNat % 2 ^ count.toNat
  let final := {pulledFast with len := pulledFast.len + (pulledFast.hold.toUInt32 &&& (((1 : UInt32) <<< count) - 1)), hold := pulledFast.hold >>> count.toUInt64, bits := pulledFast.bits - count}
  have finalPacket : FastInputPacket h next (bs.drop used) final := ⟨dropPacket.source, dropPacket.cursor, dropPacket.hold, dropPacket.bits⟩
  have countFits : count.toNat ≤ pulledSlow.bits.toNat := pullFits
  have countSmall : count.toNat < 32 := by dsimp only [count]; omega
  have low := hold_low32 (x := pulledFast.hold) (k := count) countSmall
  have extraBound : value < 2 ^ l.op.toNat := by dsimp only [value, count]; rw [opEq]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have lengthEq : final.len.toNat = l.len.toNat + value := by
    change (pulledFast.len + (pulledFast.hold.toUInt32 &&& (((1 : UInt32) <<< count) - 1))).toNat = _
    rw [u32_toNat_add (by rw [low, lenEq]; have := length.2; omega), low, lenEq]
  have read := readBits_held_stream pulledSlow (bs.drop used) l.op.toNat fit
  have finalSource : stream next (bs.drop used) = (stream slow bs).drop l.op.toNat := by
    rw [dropSource, source]
    change (stream slow bs).drop pulledFast.op.toNat = (stream slow bs).drop l.op.toNat
    rw [opEq]
  have decoded : readBits l.op.toNat (stream slow bs) = some (value, stream next (bs.drop used)) := by
    rw [source] at read
    rw [finalSource]
    simpa only [value, count, opEq, pulledPacket.hold] using read
  have extension : C.run (dolenExt c pulledFast) h = C.run (dolenRefill c final) h := by
    change (dolenExt c pulledFast) h = (dolenRefill c final) h
    unfold dolenExt
    rw [bind_ok (shl32_ok (show pulledFast.op.toNat < 32 from countSmall))]
    rw [bind_ok (shr64_ok (x := pulledFast.hold) (n := pulledFast.op.toUInt64) (by rw [UInt32.toNat_toUInt64]; omega))]
  have actualPrefix : C.run (dolenLen c l) h = C.run (dolenRefill c final) h := by
    by_cases zero : l.op = 0
    · have sourceRun : C.run (if l.bits < l.op then Zlib.Inffast.pull l else pure l) h = .ok (l, h) := by
        rw [zero]
        simp only [UInt32.not_lt_zero, ite_false]
        rfl
      have same : pulledFast = l := congrArg Prod.fst (Except.ok.inj (actual.symm.trans sourceRun))
      have finalEq : final = l := by
        have eta : {l with op := (0 : UInt32)} = l := by rw [← zero]
        simpa [final, count, same, zero] using eta
      simp only [dolenLen, zero, bne_self_eq_false, Bool.false_eq_true, ite_false, finalEq]
    · have selected : C.run (dolenLen c l) h = C.run ((if l.bits < l.op then Zlib.Inffast.pull l else pure l) >>= dolenExt c) h := by
        unfold dolenLen
        simp only [zero, bne_iff_ne, ne_eq, not_false_eq_true, ite_true]
        split <;> rfl
      rw [selected]
      change ((if l.bits < l.op then Zlib.Inffast.pull l else pure l) >>= dolenExt c) h = _
      rw [bind_ok (show (if l.bits < l.op then Zlib.Inffast.pull l else pure l : M Zlib.Inffast.L) h = .ok (pulledFast, h) from actual)]
      exact extension
  refine ⟨used, next, final, value, one, raw, inputEq, actualPrefix, finalPacket, dropBuffers, decoded,
    finalSource, lengthEq, by omega, by omega, outEq, againEq, brokeEq, putEq, leftEq, ?_⟩
  change (pulledSlow.bits - count).toNat ≤ 30
  rw [u32_toNat_sub countFits]
  omega

#print axioms length_optional_current_pull
#print axioms length_extra_current_source
end Zlib.Inflate.Proofs.FastArbitraryBody
