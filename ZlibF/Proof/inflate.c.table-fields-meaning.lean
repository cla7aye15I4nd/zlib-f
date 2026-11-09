import ZlibF.Proof.«inflate.c.code-length-repeat-meaning»
import ZlibF.Proof.«inflate.c.table-mode»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec Zlib.Inffast.Proofs
set_option autoImplicit false

/-- The actual held fourteen-bit word supplies the independent 5/5/4
header reads and the exact nonwrapping state counts. -/
theorem tableCounts_read_fields {h : Heap} {l : IL} {bs : List UInt8}
    (s : InflateState) (B : BitInv h l bs) (enough : 14 ≤ l.bits.toNat) :
    ∃ hlit hdist hclen firstRest secondRest,
      readBits 5 (stream l bs) = some (hlit, firstRest) ∧
      readBits 5 firstRest = some (hdist, secondRest) ∧
      readBits 4 secondRest = some (hclen, stream (tableRegs l) bs) ∧
      (tableCounts s l.hold).nlen.toNat = hlit + 257 ∧
      (tableCounts s l.hold).ndist.toNat = hdist + 1 ∧
      (tableCounts s l.hold).ncode.toNat = hclen + 4 := by
  have five : (5 : UInt32).toNat = 5 := by decide
  have four : (4 : UInt32).toNat = 4 := by decide
  let first : IL := { l with hold := l.hold >>> 5, bits := l.bits - 5 }
  let second : IL := { first with hold := first.hold >>> 5, bits := first.bits - 5 }
  let third : IL := { second with hold := second.hold >>> 4, bits := second.bits - 4 }
  obtain ⟨firstInv, firstStream, firstBits⟩ := DROPBITS_inv B 5 (by rw [five]; omega) (by decide)
  change BitInv h first bs at firstInv
  change stream first bs = (stream l bs).drop 5 at firstStream
  change first.bits.toNat = l.bits.toNat - 5 at firstBits
  have secondEnough : 5 ≤ first.bits.toNat := by omega
  obtain ⟨secondInv, secondStream, secondBits⟩ := DROPBITS_inv firstInv 5 secondEnough (by decide)
  change BitInv h second bs at secondInv
  change stream second bs = (stream first bs).drop 5 at secondStream
  change second.bits.toNat = first.bits.toNat - 5 at secondBits
  have thirdEnough : 4 ≤ second.bits.toNat := by omega
  obtain ⟨_thirdInv, thirdStream, _thirdBits⟩ := DROPBITS_inv secondInv 4 thirdEnough (by decide)
  change stream third bs = (stream second bs).drop 4 at thirdStream
  have thirdEq : third = tableRegs l := by simp [third, second, first, tableRegs, tcShr14, tcSub14]
  have readFirst := readBits_held_stream l bs 5 (by omega)
  rw [← firstStream] at readFirst
  have readSecond := readBits_held_stream first bs 5 secondEnough
  rw [← secondStream] at readSecond
  have readThird := readBits_held_stream second bs 4 thirdEnough
  rw [← thirdStream, thirdEq] at readThird
  let hlit := l.hold.toNat % 32
  let hdist := first.hold.toNat % 32
  let hclen := second.hold.toNat % 16
  have firstValue : (l.hold.toUInt32 &&& 31).toNat = hlit := by
    simpa only [tcMask5, five] using BITS_toNat l 5 (by decide)
  have secondValue : (first.hold.toUInt32 &&& 31).toNat = hdist := by
    simpa only [tcMask5, five] using BITS_toNat first 5 (by decide)
  have thirdValue : (second.hold.toUInt32 &&& 15).toNat = hclen := by
    simpa only [tcMask4, four] using BITS_toNat second 4 (by decide)
  have firstBound : hlit < 32 := Nat.mod_lt _ (by decide)
  have secondBound : hdist < 32 := Nat.mod_lt _ (by decide)
  have thirdBound : hclen < 16 := Nat.mod_lt _ (by decide)
  refine ⟨hlit, hdist, hclen, stream first bs, stream second bs, readFirst, readSecond, readThird, ?_, ?_, ?_⟩
  · change ((l.hold.toUInt32 &&& 31) + 257).toNat = hlit + 257
    rw [UInt32.toNat_add]
    change ((l.hold.toUInt32 &&& 31).toNat + 257) % 2 ^ 32 = hlit + 257
    rw [firstValue]
    omega
  · change ((first.hold.toUInt32 &&& 31) + 1).toNat = hdist + 1
    rw [UInt32.toNat_add]
    change ((first.hold.toUInt32 &&& 31).toNat + 1) % 2 ^ 32 = hdist + 1
    rw [secondValue]
    omega
  · change ((second.hold.toUInt32 &&& 15) + 4).toNat = hclen + 4
    rw [UInt32.toNat_add]
    change ((second.hold.toUInt32 &&& 15).toNat + 4) % 2 ^ 32 = hclen + 4
    rw [thirdValue]
    omega


/-- The actual TABLE prefix retains waiting and both validity branches.
On a complete word the real counts match the independent dynamic fields;
passing the real check supplies DynamicCountsOK and the actual LENLENS cut. -/
theorem inflate_TABLE_independent_fields {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs))
    (hz : r.get h = some z) (hs : h.istates zs = some s) (B : BitInv h l bs) :
    ∃ outcome regs used, runX (NEEDBITS 14) l h = .ok ((outcome, regs), h) ∧
      used ≤ bs.length ∧ BitInv h regs (bs.drop used) ∧
      (outcome = .error Ex.leave → runX (inflate_TABLE c) l h = .ok ((.error Ex.leave, regs), h)) ∧
      (outcome = .ok () → ∃ hlit hdist hclen firstRest secondRest,
        readBits 5 (stream l bs) = some (hlit, firstRest) ∧
        readBits 5 firstRest = some (hdist, secondRest) ∧
        readBits 4 secondRest = some (hclen, stream (tableRegs regs) (bs.drop used)) ∧
        (tableCounts s regs.hold).nlen.toNat = hlit + 257 ∧
        (tableCounts s regs.hold).ndist.toNat = hdist + 1 ∧
        (tableCounts s regs.hold).ncode.toNat = hclen + 4 ∧
        (¬ ((tableCounts s regs.hold).nlen > 286 ∨ (tableCounts s regs.hold).ndist > 30) →
          DynamicCountsOK hlit hdist ∧
          runX (inflate_TABLE c) l h = runX (inflate_LENLENS c) (tableRegs regs)
            (setI h zs { tableCounts s regs.hold with «have» := 0, mode := LENLENS })) ∧
        (((tableCounts s regs.hold).nlen > 286 ∨ (tableCounts s regs.hold).ndist > 30) →
          ∃ i, strTable[i]? = some "too many length or distance symbols" ∧
            runX (inflate_TABLE c) l h = .ok ((.ok (), tableRegs regs),
              tcBadHeap h r zs z (tableCounts s regs.hold) i))) := by
  obtain ⟨outcome, regs, used, needRun, usedBound, inv, sameInput, wait, complete⟩ :=
    inflate_TABLE_run hr hc hz hs B
  refine ⟨outcome, regs, used, needRun, usedBound, inv, ?_, ?_⟩
  · intro waiting
    exact (wait waiting).2.2.2
  · intro normal
    obtain ⟨enough, _afterBits, _remaining, rejected, accepted⟩ := complete normal
    obtain ⟨hlit, hdist, hclen, firstRest, secondRest, firstRead, secondRead, thirdRead,
      litCount, distCount, codeCount⟩ := tableCounts_read_fields s inv enough
    rw [sameInput] at firstRead
    refine ⟨hlit, hdist, hclen, firstRest, secondRest, firstRead, secondRead, thirdRead,
      litCount, distCount, codeCount, ?_, rejected⟩
    intro valid
    refine ⟨?_, accepted valid⟩
    have litBound := (not_or.mp valid).1
    have distBound := (not_or.mp valid).2
    rw [gt_iff_lt, UInt32.lt_iff_toNat_lt] at litBound distBound
    change ¬ 286 < (tableCounts s regs.hold).nlen.toNat at litBound
    change ¬ 30 < (tableCounts s regs.hold).ndist.toNat at distBound
    rw [litCount] at litBound
    rw [distCount] at distBound
    constructor <;> omega

#print axioms inflate_TABLE_independent_fields

#print axioms tableCounts_read_fields
end Zlib.Inflate.Proofs
