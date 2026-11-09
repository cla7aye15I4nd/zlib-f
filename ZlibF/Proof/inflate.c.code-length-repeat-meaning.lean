import ZlibF.Proof.«inflate.c.code-length-literal-meaning»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec Zlib.Inffast.Proofs
set_option autoImplicit false

/-- Reading available held bits returns exactly the corresponding low word
and drops exactly that many real stream bits. -/
theorem readBits_held_stream (l : IL) (bs : List UInt8) (width : Nat) (bound : width ≤ l.bits.toNat) :
    readBits width (stream l bs) = some (l.hold.toNat % 2 ^ width, (stream l bs).drop width) := by
  have read := readBits_bitsOfNat width l.bits.toNat l.hold.toNat (bytesBits bs) bound
  have rest : bitsOfNat (l.hold.toNat / 2 ^ width) (l.bits.toNat - width) ++ bytesBits bs =
      (stream l bs).drop width := by
    rw [stream, List.drop_append_of_le_length (by simpa only [natBits_length] using bound), natBits_drop _ _ _ bound]
    rw [natBits_testBit]
    rfl
  rw [rest] at read
  simpa only [stream, natBits_testBit, bitsOfNat] using read

/-- The actual zero-repeat setup reads the independently specified extra
bits and stores their precise base-adjusted count. Waiting remains admitted. -/
theorem clZeroSetup_read {h : Heap} {l : IL} {bs : List UInt8} (B : BitInv h l bs)
    (here : Code) (extra base : UInt32) (width : here.bits.toNat ≤ 7)
    (extraBound : extra.toNat ≤ 7) (baseLo : 3 ≤ base.toNat) (baseHi : base.toNat ≤ 11) :
    ∃ result regs used,
      runX (clZeroSetup here extra base) l h = .ok ((result, regs), h) ∧
      used ≤ bs.length ∧ BitInv h regs (bs.drop used) ∧
      (result = .ok () → ∃ value,
        readBits extra.toNat ((stream l bs).drop here.bits.toNat) =
          some (value, stream regs (bs.drop used)) ∧ regs.len = 0 ∧ regs.copy.toNat = base.toNat + value) := by
  have total : (here.bits.toUInt32 + extra).toNat = here.bits.toNat + extra.toNat := by
    rw [UInt32.toNat_add, UInt8.toNat_toUInt32, Nat.mod_eq_of_lt (by omega)]
  obtain ⟨result, regs, used, needRun, usedBound, needInv, needStream, _bitCount, _shape, _bitBound,
    _identity, enough, _same, _short, _cursor⟩ :=
    NEEDBITS_run_cursor B (here.bits.toUInt32 + extra) (by rw [total]; omega)
  cases result with
  | error fault =>
    refine ⟨.error fault, regs, used, ?_, usedBound, needInv, ?_⟩
    · unfold clZeroSetup
      rw [runX_bind, needRun]
    · intro impossible
      cases impossible
  | ok done =>
    cases done
    have available := enough rfl
    rw [total] at available
    have firstBound : here.bits.toUInt32.toNat < 64 := by rw [UInt8.toNat_toUInt32]; omega
    have extraSmall : extra.toNat < 32 := by omega
    let dropped := { regs with hold := regs.hold >>> here.bits.toUInt32.toUInt64, bits := regs.bits - here.bits.toUInt32 }
    obtain ⟨firstInv, firstStream, firstCount⟩ := DROPBITS_inv needInv here.bits.toUInt32
      (by rw [UInt8.toNat_toUInt32]; omega) firstBound
    have source : stream dropped (bs.drop used) = (stream l bs).drop here.bits.toNat := by
      simpa only [UInt8.toNat_toUInt32, needStream] using firstStream
    let bits := dropped.hold.toUInt32 &&& ((1 : UInt32) <<< extra - 1)
    have bitsNat : bits.toNat = dropped.hold.toNat % 2 ^ extra.toNat := BITS_toNat dropped extra extraSmall
    have bitsBound : bits.toNat < 128 := by
      have bound := Nat.mod_lt dropped.hold.toNat (Nat.two_pow_pos extra.toNat)
      have power : 2 ^ extra.toNat ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) extraBound
      omega
    have copyNat : (base + bits).toNat = base.toNat + bits.toNat := by
      rw [UInt32.toNat_add, Nat.mod_eq_of_lt (by omega)]
    let prepared := { dropped with len := 0, copy := base + bits }
    have preparedInv : BitInv h prepared (bs.drop used) := ⟨firstInv.have_eq, firstInv.next, firstInv.hold_lt⟩
    have secondEnough : extra.toNat ≤ prepared.bits.toNat := by
      change extra.toNat ≤ (regs.bits - here.bits.toUInt32).toNat
      rw [firstCount, UInt8.toNat_toUInt32]
      omega
    obtain ⟨finalInv, finalStream, _finalCount⟩ := DROPBITS_inv preparedInv extra secondEnough (by omega)
    let final := { prepared with hold := prepared.hold >>> extra.toUInt64, bits := prepared.bits - extra }
    refine ⟨.ok (), final, used, ?_, usedBound, finalInv, ?_⟩
    · unfold clZeroSetup
      rw [runX_bind, needRun]
      dsimp only
      rw [runX_bind, DROPBITS_run regs h here.bits.toUInt32 firstBound]
      dsimp only
      rw [runX_bind, BITS_run dropped h extra extraSmall]
      dsimp only
      rw [runX_bind, runX_modify]
      dsimp only
      exact DROPBITS_run prepared h extra (by omega)
    · intro _
      refine ⟨bits.toNat, ?_, rfl, copyNat⟩
      have read := readBits_held_stream dropped (bs.drop used) extra.toNat secondEnough
      change stream final (bs.drop used) = (stream dropped (bs.drop used)).drop extra.toNat at finalStream
      rw [← bitsNat, ← finalStream, source] at read
      exact read

/-- The previous-length repeat reads exactly the preceding lens cell,
and its two actual extra bits determine the exact repetition count. -/
theorem clPrevBits_read {c : Ctx} {l : IL} {h : Heap} {zs : Nat}
    {s : InflateState} {bs : List UInt8}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (size : s.lens.size = 320) (nonempty : 1 ≤ s.«have».toNat) (haveBound : s.«have».toNat ≤ 320)
    (B : BitInv h l bs) (enough : 2 ≤ l.bits.toNat) :
    ∃ regs value,
      runX (clPrevBits c s.«have») l h = .ok ((.ok (), regs), h) ∧ BitInv h regs bs ∧
      regs.len.toNat = (s.lens.getD (s.«have».toNat - 1) 0).toNat ∧
      readBits 2 (stream l bs) = some (value, stream regs bs) ∧ regs.copy.toNat = 3 + value := by
  have index : (s.«have» - 1).toNat = s.«have».toNat - 1 := by
    rw [UInt32.toNat_sub_of_le _ _ (by apply UInt32.le_iff_toNat_le.mpr; exact nonempty)]
    rfl
  have inside : (s.«have» - 1).toNat < s.lens.size := by rw [index]; omega
  have lens := WRef.get_istate_lens hs
  have read := Ptr.index_ok (off := 0) (i := (s.«have» - 1).toNat) lens (by simpa using inside)
  let previous := s.lens.getD (s.«have».toNat - 1) 0
  have cell : s.lens[0 + (s.«have» - 1).toNat] = previous := by
    dsimp only [previous]
    rw [← index, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem inside, Option.getD_some]
    simp only [Nat.zero_add]
  let bits := l.hold.toUInt32 &&& ((1 : UInt32) <<< 2 - 1)
  have bitsNat : bits.toNat = l.hold.toNat % 4 := BITS_toNat l 2 (by decide)
  have copyNat : ((3 : UInt32) + bits).toNat = 3 + bits.toNat := by
    rw [UInt32.toNat_add]
    change (3 + bits.toNat) % 2 ^ 32 = 3 + bits.toNat
    rw [Nat.mod_eq_of_lt (by have := Nat.mod_lt l.hold.toNat (by decide : 0 < 4); omega)]
  let prepared := { l with len := previous.toUInt32, copy := 3 + bits }
  have preparedInv : BitInv h prepared bs := ⟨B.have_eq, B.next, B.hold_lt⟩
  obtain ⟨finalInv, sameStream, _count⟩ := DROPBITS_inv preparedInv 2 enough (by decide)
  let regs := { prepared with hold := prepared.hold >>> (2 : UInt32).toUInt64, bits := prepared.bits - 2 }
  refine ⟨regs, bits.toNat, ?_, finalInv, ?_, ?_, copyNat⟩
  · unfold clPrevBits
    rw [hc]
    simp only [lensP, runX_bind, runX_lift_ok read, cell, BITS_run l h 2 (by decide), runX_modify]
    exact DROPBITS_run prepared h 2 (by decide)
  · change previous.toUInt32.toNat = previous.toNat
    exact UInt16.toNat_toUInt32 previous
  · have decoded := readBits_held_stream l bs 2 enough
    change stream regs bs = (stream l bs).drop 2 at sameStream
    rw [← bitsNat, ← sameStream] at decoded
    exact decoded

#print axioms clPrevBits_read
#print axioms readBits_held_stream
#print axioms clZeroSetup_read
end Zlib.Inflate.Proofs
