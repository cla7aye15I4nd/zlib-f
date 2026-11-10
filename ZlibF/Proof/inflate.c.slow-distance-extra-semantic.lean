import ZlibF.Proof.«inflate.c.slow-extra-semantic»

namespace Zlib.Inflate.Proofs.SlowExtraSemanticPath
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec Zlib.Inflate.Proofs Zlib.Inffast.Proofs
set_option autoImplicit false

/-- A successful independent distance-extra read drives the actual DISTEXT
source and stores the exact base-adjusted distance. The real MATCH call
remains the continuation, rather than an assumed contract. -/
theorem DISTEXT_read_semantics {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8}
    {value : Nat} {rest : List Bool} (before : Nat)
    (hr : c.strm = some r) (hc : c.st = some (.tab zs))
    (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (B : BitInv h l bs) (extra : s.extra.toNat ≤ 13)
    (lower : 1 ≤ s.offset.toNat) (budget : s.offset.toNat + 2 ^ s.extra.toNat ≤ 73727)
    (back : s.back = Int32.ofNat before) (backBound : before ≤ 35)
    (read : readBits s.extra.toNat (stream l bs) = some (value, rest)) :
    ∃ regs after state used,
      runX (inflate_DISTEXT c) l h = runX (inflate_MATCH c) regs after ∧
      used ≤ bs.length ∧ Good after r zs z state ∧ DataTablesSafe after state ∧
      BitInv after regs (bs.drop used) ∧ state.mode = MATCH ∧ DecodeStateFrame s state ∧
      SymbolRegShape l regs ∧ stream regs (bs.drop used) = rest ∧
      state.offset.toNat = s.offset.toNat + value ∧
      state = { s with offset := state.offset, back := Int32.ofNat (before + s.extra.toNat), mode := MATCH } ∧
      1 ≤ state.offset.toNat ∧ state.offset.toNat ≤ 73726 ∧
      after = setI h zs state ∧ regs.next = inputAdvance l.next used ∧
      regs.bits.toNat ≤ max l.bits.toNat 20 := by
  have env : Env c h r zs z s := ⟨hr, hc, good.live.hz, good.live.hs⟩
  have load : ldInflateState c.st h = .ok (s, h) := by rw [hc, ldI_eq, good.live.hs]
  by_cases zero : s.extra = 0
  · let state := { s with mode := MATCH }
    have finalGood := good.decode_update (after := state) rfl
      (by change HEAD ≤ MATCH ∧ MATCH ≤ SYNC; decide)
    have finalTables := tables.decode_update good.live.hs (after := state) rfl
    have readZero : (0, stream l bs) = (value, rest) := by
      apply Option.some.inj
      simpa only [zero, UInt32.toNat_zero, readBits] using read
    have valueZero := (Prod.mk.inj readZero).1.symm
    refine ⟨l, setI h zs state, state, 0, ?_, by omega, finalGood, finalTables,
      B.decode_update zs state, rfl, rfl, by rfl, ?_, ?_, ?_, lower, ?_, rfl,
      (inputAdvance_zero l.next).symm, Nat.le_max_left _ _⟩
    · unfold inflate_DISTEXT
      simp only [runX_bind, runX_lift_ok load, zero, bne_self_eq_false,
        Bool.false_eq_true, ite_false, runX_setMode env]
      simp only [state, zero]
    · simpa only [List.drop_zero] using (Prod.mk.inj readZero).2
    · change s.offset.toNat = s.offset.toNat + value
      rw [valueZero, Nat.add_zero]
    · simp only [zero, UInt32.toNat_zero, Nat.add_zero, state, back]
    · rw [zero] at budget
      change s.offset.toNat ≤ 73726
      have : (0 : UInt32).toNat = 0 := rfl
      simp only [this, Nat.pow_zero] at budget
      omega
  · obtain ⟨current, used, run, usedBound, currentInv, sameStream, count, shape,
        bitBound, available, cursor, valueEq, restEq⟩ :=
      NEEDBITS_read_semantics B (by omega) read
    have prefixRun := inflate_DISTEXT_need_cut (l := l) hc good.live.hs zero
    let bits := current.hold.toUInt32 &&& ((1 : UInt32) <<< s.extra - 1)
    have bitsNat : bits.toNat = current.hold.toNat % 2 ^ s.extra.toNat :=
      BITS_toNat current s.extra (by omega)
    have bitsBound : bits.toNat < 2 ^ s.extra.toNat := by
      rw [bitsNat]
      exact Nat.mod_lt _ (Nat.two_pow_pos _)
    have offsetNat : (s.offset + bits).toNat = s.offset.toNat + bits.toNat := by
      rw [UInt32.toNat_add, Nat.mod_eq_of_lt (by omega)]
    have unsignedBack : (i2u s.back).toNat = before := by
      rw [back]
      simp [i2u, Nat.mod_eq_of_lt (by omega : before < 2 ^ 32)]
    have backNat : (i2u s.back + s.extra).toNat = before + s.extra.toNat := by
      rw [UInt32.toNat_add, unsignedBack, Nat.mod_eq_of_lt (by omega)]
    have backEq : u2i (i2u s.back + s.extra) = Int32.ofNat (before + s.extra.toNat) := by
      unfold u2i
      rw [backNat]
      rfl
    have small : s.extra.toNat < 64 := by omega
    obtain ⟨finalInv, finalStream, finalCount⟩ :=
      DROPBITS_inv currentInv s.extra available small
    let regs := { current with hold := current.hold >>> s.extra.toUInt64, bits := current.bits - s.extra }
    let state := { s with offset := s.offset + bits, back := Int32.ofNat (before + s.extra.toNat), mode := MATCH }
    let after := setI h zs state
    have finalGood := good.decode_update (after := state) rfl
      (by change HEAD ≤ MATCH ∧ MATCH ≤ SYNC; decide)
    have finalTables := tables.decode_update good.live.hs (after := state) rfl
    refine ⟨regs, after, state, used, ?_, usedBound, finalGood, finalTables,
      finalInv.decode_update zs state, rfl, rfl, ?_, ?_, ?_, rfl, ?_, ?_, rfl,
      cursor, ?_⟩
    · rw [prefixRun]
      unfold distExtraNeed
      rw [runX_bind, run]
      simp only [runX_bind, BITS_run current h s.extra (by omega), runX_lift,
        hc, wrI_eq, good.live.hs, setI_istates_same, DROPBITS_run, small,
        setI_setI, setMode]
      simp only [backEq]
      rfl
    · unfold SymbolRegShape
      dsimp only [regs]
      rw [shape]
    · exact (finalStream.trans (congrArg (List.drop s.extra.toNat) sameStream)).trans restEq.symm
    · change (s.offset + bits).toNat = s.offset.toNat + value
      rw [offsetNat, bitsNat, valueEq]
    · change 1 ≤ (s.offset + bits).toNat
      rw [offsetNat]
      omega
    · change (s.offset + bits).toNat ≤ 73726
      rw [offsetNat]
      omega
    · change (current.bits - s.extra).toNat ≤ max l.bits.toNat 20
      rw [UInt32.toNat_sub_of_le _ _ available]
      omega

/-- Exact bounds of every independently specified distance base/extra pair. -/
theorem distance_base_extra_bounds : ∀ symbol, symbol ≤ 29 →
    1 ≤ distBases.getD symbol 0 ∧ distExtras.getD symbol 0 ≤ 13 ∧
      distBases.getD symbol 0 + 2 ^ distExtras.getD symbol 0 ≤ 32769 := by
  decide +kernel

/-- An independent successful read never exceeds its stated bit width. -/
theorem readBits_value_bound {width value : Nat} {input rest : List Bool}
    (read : readBits width input = some (value, rest)) : value < 2 ^ width := by
  obtain ⟨actualValue, actualRest, actualRead, bound, _⟩ :=
    ZlibF.Math.InflateDecode.read_total width input (readBits_fits read)
  obtain ⟨same, _⟩ := Prod.mk.inj (Option.some.inj (actualRead.symm.trans read))
  simpa only [same] using bound

/-- For a constructor-derived valid distance symbol, the actual DISTEXT
result is the format base plus the independent extra value, between one
and 32768. The source addition is within UInt32 without wrapping. -/
theorem DISTEXT_symbol_read_semantics {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8}
    {symbol value : Nat} {rest : List Bool} (before : Nat)
    (hr : c.strm = some r) (hc : c.st = some (.tab zs))
    (good : Good h r zs z s) (tables : DataTablesSafe h s) (B : BitInv h l bs)
    (valid : symbol ≤ 29) (base : s.offset.toNat = distBases.getD symbol 0)
    (width : s.extra.toNat = distExtras.getD symbol 0)
    (back : s.back = Int32.ofNat before) (backBound : before ≤ 35)
    (read : readBits (distExtras.getD symbol 0) (stream l bs) = some (value, rest)) :
    ∃ regs after state used,
      runX (inflate_DISTEXT c) l h = runX (inflate_MATCH c) regs after ∧
      used ≤ bs.length ∧ Good after r zs z state ∧ DataTablesSafe after state ∧
      BitInv after regs (bs.drop used) ∧ state.mode = MATCH ∧ DecodeStateFrame s state ∧
      SymbolRegShape l regs ∧ stream regs (bs.drop used) = rest ∧
      state.offset.toNat = distBases.getD symbol 0 + value ∧
      state = { s with offset := state.offset, back := Int32.ofNat (before + s.extra.toNat), mode := MATCH } ∧
      1 ≤ state.offset.toNat ∧ state.offset.toNat ≤ 32768 ∧
      distBases.getD symbol 0 + value < 2 ^ 32 ∧
      after = setI h zs state ∧ regs.next = inputAdvance l.next used ∧
      regs.bits.toNat ≤ max l.bits.toNat 20 := by
  obtain ⟨positive, extra, capacity⟩ := distance_base_extra_bounds symbol valid
  have realRead : readBits s.extra.toNat (stream l bs) = some (value, rest) := by
    simpa only [width] using read
  obtain ⟨regs, after, state, used, run, usedBound, finalGood, finalTables,
    finalB, mode, frame, shape, source, offset, stateEq, lower, upper, heap,
    cursor, bits⟩ := DISTEXT_read_semantics before hr hc good tables B
      (by rw [width]; exact extra) (by rw [base]; exact positive)
      (by rw [base, width]; omega) back backBound realRead
  have valueBound := readBits_value_bound read
  have exactOffset : state.offset.toNat = distBases.getD symbol 0 + value := by
    rw [offset, base]
  refine ⟨regs, after, state, used, run, usedBound, finalGood, finalTables,
    finalB, mode, frame, shape, source, exactOffset, stateEq, lower, ?_, ?_,
    heap, cursor, bits⟩
  · omega
  · omega

#print axioms DISTEXT_read_semantics
#print axioms distance_base_extra_bounds
#print axioms readBits_value_bound
#print axioms DISTEXT_symbol_read_semantics
end Zlib.Inflate.Proofs.SlowExtraSemanticPath
