import ZlibF.Proof.«inflate.c.length-extra»
import ZlibF.Proof.«inflate.c.distance-extra»
import ZlibF.Math.InflateDecodeBits
namespace Zlib.Inflate.Proofs.SlowExtraSemanticPath
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec Zlib.Inflate.Proofs Zlib.Inffast.Proofs
set_option autoImplicit false
/-- Successful independent extra-bit reads fit their actual input. -/
theorem readBits_fits {n value : Nat} {input rest : List Bool}
    (read : readBits n input = some (value, rest)) : n ≤ input.length := by
  induction n generalizing input value rest with
  | zero => omega
  | succ n ih =>
    cases input with
    | nil => cases read
    | cons bit input =>
      simp only [readBits] at read
      cases previous : readBits n input with
      | none => rw [previous] at read; cases read
      | some pair =>
        obtain ⟨previousValue, previousRest⟩ := pair
        have fits := ih previous
        simp only [List.length_cons]
        omega
/-- Independent successful extra bits drive the actual NEEDBITS refill
and identify the exact machine BITS result on the same original source. -/
theorem NEEDBITS_read_semantics
    {h : Heap} {l : IL} {bs : List UInt8} {n : UInt32} {value : Nat} {rest : List Bool}
    (B : BitInv h l bs) (bound : n.toNat ≤ 49)
    (read : readBits n.toNat (stream l bs) = some (value, rest)) :
    ∃ regs used,
      runX (NEEDBITS n) l h = .ok ((.ok (), regs), h) ∧ used ≤ bs.length ∧
      BitInv h regs (bs.drop used) ∧ stream regs (bs.drop used) = stream l bs ∧
      regs.bits.toNat = l.bits.toNat + 8 * used ∧
      regs = {l with next := regs.next, have_ := regs.have_, hold := regs.hold, bits := regs.bits} ∧
      regs.bits.toNat ≤ max l.bits.toNat (n.toNat + 7) ∧
      n.toNat ≤ regs.bits.toNat ∧ regs.next = inputAdvance l.next used ∧
      regs.hold.toNat % 2 ^ n.toNat = value ∧ rest = (stream l bs).drop n.toNat := by
  obtain ⟨result, regs, used, run, usedBound, inv, source, count, shape, bitBound,
    noPull, enough, empty, kinds, cursor⟩ := NEEDBITS_run_cursor B n bound
  have fit := readBits_fits read
  have normal : result = .ok () := by
    rcases kinds with normal | leave
    · exact normal
    · obtain ⟨allBytes, noInput, short⟩ := empty leave
      have sourceLength : (stream l bs).length = regs.bits.toNat := by
        rw [← source, allBytes]
        simp only [List.drop_length, stream, bytesBits, List.flatMap_nil, List.append_nil, natBits_length]
      omega
  have readActual := readBits_bitsOfNat n.toNat regs.bits.toNat regs.hold.toNat
    (bytesBits (bs.drop used)) (enough normal)
  have sourceEq : bitsOfNat regs.hold.toNat regs.bits.toNat ++ bytesBits (bs.drop used) = stream l bs := by
    simpa only [stream, natBits_testBit, bitsOfNat] using source
  rw [sourceEq] at readActual
  obtain ⟨valueEq, restEq⟩ := Prod.mk.inj (Option.some.inj (readActual.symm.trans read))
  have suffix : bitsOfNat (regs.hold.toNat / 2 ^ n.toNat) (regs.bits.toNat - n.toNat) ++
      bytesBits (bs.drop used) = (stream l bs).drop n.toNat := by
    rw [← sourceEq, List.drop_append_of_le_length (by simpa only [bitsOfNat_length] using enough normal),
      ← bitsOfNat_drop _ _ _ (enough normal)]
  refine ⟨regs, used, ?_, usedBound, inv, source, count, shape, bitBound, enough normal, cursor, valueEq, ?_⟩
  · simpa only [normal] using run
  · exact restEq.symm.trans suffix
/-- Exact independent extra-bit meaning for actual LENEXT, retaining the
real DIST continuation and the precise decoded length. -/
theorem LENEXT_read_semantics {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8} {value : Nat} {rest : List Bool} (before : Nat)
    (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (B : BitInv h l bs) (extra : s.extra.toNat ≤ 5)
    (lower : 3 ≤ s.length.toNat) (budget : s.length.toNat + 2 ^ s.extra.toNat ≤ 259)
    (back : s.back = Int32.ofNat before) (backBound : before ≤ 15)
    (read : readBits s.extra.toNat (stream l bs) = some (value, rest)) :
    ∃ regs after state used,
      runX (inflate_LENEXT c) l h = runX (inflate_DIST c) regs after ∧
      used ≤ bs.length ∧ Good after r zs z state ∧ DataTablesSafe after state ∧
      BitInv after regs (bs.drop used) ∧ state.mode = DIST ∧ DecodeStateFrame s state ∧
      SymbolRegShape l regs ∧ stream regs (bs.drop used) = (stream l bs).drop s.extra.toNat ∧
      state.was = state.length ∧ state.length.toNat = s.length.toNat + value ∧
      stream regs (bs.drop used) = rest ∧ 3 ≤ state.length.toNat ∧ state.length.toNat ≤ 258 ∧
      state.back = Int32.ofNat (before + s.extra.toNat) ∧ after = setI h zs state ∧ regs.next = inputAdvance l.next used ∧ regs.bits.toNat ≤ max l.bits.toNat 12 := by
  have env : Env c h r zs z s := ⟨hr, hc, good.live.hz, good.live.hs⟩
  have load : ldInflateState c.st h = .ok (s, h) := by rw [hc, ldI_eq, good.live.hs]
  by_cases zero : s.extra = 0
  ·
    let state := { s with was := s.length, mode := DIST }
    have finalGood := good.decode_update (after := state) rfl (by change HEAD ≤ DIST ∧ DIST ≤ SYNC; decide)
    have finalTables := tables.decode_update good.live.hs (after := state) rfl
    refine ⟨l, setI h zs state, state, 0, ?_, by omega, finalGood, finalTables,
      B.decode_update zs state, rfl, rfl, by rfl, ?_, rfl, ?_, ?_, lower, ?_, ?_, rfl, (inputAdvance_zero l.next).symm, Nat.le_max_left _ _⟩
    · unfold inflate_LENEXT
      simp only [runX_bind, runX_lift_ok load, zero, bne_self_eq_false, Bool.false_eq_true, ite_false,
        runX_wrS env]
      simp only [state, zero]
    · simp only [zero, UInt32.toNat_zero, List.drop_zero]
    · have readZero : (0, stream l bs) = (value, rest) := by
        apply Option.some.inj
        simpa only [zero, UInt32.toNat_zero, readBits] using read
      have valueZero := (Prod.mk.inj readZero).1.symm
      change s.length.toNat = s.length.toNat + value
      rw [valueZero, Nat.add_zero]
    · have readZero : (0, stream l bs) = (value, rest) := by
        apply Option.some.inj
        simpa only [zero, UInt32.toNat_zero, readBits] using read
      exact (Prod.mk.inj readZero).2
    · rw [zero] at budget
      change s.length.toNat ≤ 258
      have : (0 : UInt32).toNat = 0 := rfl
      simp only [this, Nat.pow_zero] at budget
      omega
    · simp only [zero, UInt32.toNat_zero, Nat.add_zero]
      exact back
  · obtain ⟨current, used, run, usedBound, currentInv, sameStream, count, shape,
        bitBound, availableNat, cursor, valueEq, restEq⟩ := NEEDBITS_read_semantics B (by omega) read
    have prefixRun := inflate_LENEXT_need_cut (l := l) hc good.live.hs zero
    have available := availableNat
    let bits := current.hold.toUInt32 &&& ((1 : UInt32) <<< s.extra - 1)
    have bitsNat : bits.toNat = current.hold.toNat % 2 ^ s.extra.toNat := BITS_toNat current s.extra (by omega)
    have bitsBound : bits.toNat < 2 ^ s.extra.toNat := by rw [bitsNat]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
    have lengthNat : (s.length + bits).toNat = s.length.toNat + bits.toNat := by
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
    obtain ⟨finalInv, finalStream, finalCount⟩ := DROPBITS_inv currentInv s.extra available small
    let regs := { current with hold := current.hold >>> s.extra.toUInt64, bits := current.bits - s.extra }
    let state := { s with length := s.length + bits, back := Int32.ofNat (before + s.extra.toNat), was := s.length + bits, mode := DIST }
    let after := setI h zs state
    have finalGood := good.decode_update (after := state) rfl (by change HEAD ≤ DIST ∧ DIST ≤ SYNC; decide)
    have finalTables := tables.decode_update good.live.hs (after := state) rfl
    refine ⟨regs, after, state, used, ?_, usedBound, finalGood, finalTables,
      finalInv.decode_update zs state, rfl, rfl, ?_, ?_, rfl, ?_, ?_, ?_, ?_, rfl, rfl, cursor, by
        change (current.bits - s.extra).toNat ≤ max l.bits.toNat 12
        rw [UInt32.toNat_sub_of_le _ _ available]
        omega⟩
    · rw [prefixRun]
      unfold lenExtraNeed
      rw [runX_bind, run]
      simp only [runX_bind, BITS_run current h s.extra (by omega), runX_lift, hc,
        wrI_eq, good.live.hs, setI_istates_same, DROPBITS_run, small, setI_setI]
      simp only [backEq]
      rfl
    · unfold SymbolRegShape
      dsimp only [regs]
      rw [shape]
    · exact finalStream.trans (congrArg (List.drop s.extra.toNat) sameStream)
    · change (s.length + bits).toNat = s.length.toNat + value
      rw [lengthNat, bitsNat, valueEq]
    · exact (finalStream.trans (congrArg (List.drop s.extra.toNat) sameStream)).trans restEq.symm
    · change 3 ≤ (s.length + bits).toNat
      rw [lengthNat]
      omega
    · change (s.length + bits).toNat ≤ 258
      rw [lengthNat]
      omega

#print axioms readBits_fits
#print axioms NEEDBITS_read_semantics
#print axioms LENEXT_read_semantics
end Zlib.Inflate.Proofs.SlowExtraSemanticPath
