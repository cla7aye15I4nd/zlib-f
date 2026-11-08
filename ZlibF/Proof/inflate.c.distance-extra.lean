import ZlibF.Proof.«inflate.c.distance-finish»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

/-- Source-order suffix entered when DISTEXT needs extra bits. -/
def distExtraNeed (c : Ctx) (extra : UInt32) : X Unit := do
  NEEDBITS extra
  let b ← BITS extra
  wrS c.st fun s => { s with offset := s.offset + b }
  DROPBITS extra
  wrS c.st fun s => { s with back := u2i (i2u s.back + s.extra) }
  setMode c.st MATCH
  inflate_MATCH c

/-- The nonzero-extra source cut is the actual DISTEXT suffix. -/
theorem inflate_DISTEXT_need_cut {c : Ctx} {l : IL} {h : Heap} {zs : Nat} {s : InflateState}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s) (nonzero : s.extra ≠ 0) :
    runX (inflate_DISTEXT c) l h = runX (distExtraNeed c s.extra) l h := by
  have load : ldInflateState c.st h = .ok (s, h) := by rw [hc, ldI_eq, hs]
  unfold inflate_DISTEXT distExtraNeed
  rw [runX_bind, runX_lift_ok load]
  simp [nonzero]

/-- Actual DISTEXT either leaves for input or reaches the actual MATCH call.
Its base and extra-bit budget implies a positive bounded distance.
The signed back value is derived from the bounded actual unsigned update. -/
theorem inflate_DISTEXT_boundary_bounded {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8} (before : Nat)
    (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (B : BitInv h l bs) (extra : s.extra.toNat ≤ 13)
    (lower : 1 ≤ s.offset.toNat) (budget : s.offset.toNat + 2 ^ s.extra.toNat ≤ 73727)
    (back : s.back = Int32.ofNat before) (backBound : before ≤ 35) :
    (∃ regs used,
      runX (inflate_DISTEXT c) l h = .ok ((.error Ex.leave, regs), h) ∧
      used ≤ bs.length ∧ BitInv h regs (bs.drop used) ∧ regs.have_ = 0 ∧
      stream regs (bs.drop used) = stream l bs ∧ SymbolRegShape l regs ∧ regs.next = inputAdvance l.next used ∧ regs.bits.toNat ≤ max l.bits.toNat 20) ∨
    (∃ regs after state used,
      runX (inflate_DISTEXT c) l h = runX (inflate_MATCH c) regs after ∧
      used ≤ bs.length ∧ Good after r zs z state ∧ DataTablesSafe after state ∧
      BitInv after regs (bs.drop used) ∧ state.mode = MATCH ∧ DecodeStateFrame s state ∧
      SymbolRegShape l regs ∧ stream regs (bs.drop used) = (stream l bs).drop s.extra.toNat ∧
      after = setI h zs state ∧ state = { s with offset := state.offset, back := Int32.ofNat (before + s.extra.toNat), mode := MATCH } ∧
      1 ≤ state.offset.toNat ∧ state.offset.toNat ≤ 73726 ∧
      state.back = Int32.ofNat (before + s.extra.toNat) ∧ regs.next = inputAdvance l.next used ∧ regs.bits.toNat ≤ max l.bits.toNat 20) := by
  have env : Env c h r zs z s := ⟨hr, hc, good.live.hz, good.live.hs⟩
  have load : ldInflateState c.st h = .ok (s, h) := by rw [hc, ldI_eq, good.live.hs]
  by_cases zero : s.extra = 0
  · right
    let state := { s with mode := MATCH }
    have finalGood := good.decode_update (after := state) rfl (by change HEAD ≤ MATCH ∧ MATCH ≤ SYNC; decide)
    have finalTables := tables.decode_update good.live.hs (after := state) rfl
    refine ⟨l, setI h zs state, state, 0, ?_, by omega, finalGood, finalTables,
      B.decode_update zs state, rfl, rfl, by rfl, ?_, rfl, ?_, lower, ?_, ?_, (inputAdvance_zero l.next).symm, Nat.le_max_left _ _⟩
    · unfold inflate_DISTEXT
      simp only [runX_bind, runX_lift_ok load, zero, bne_self_eq_false, Bool.false_eq_true, ite_false,
        runX_setMode env]
      simp only [state, zero]
    · simp only [zero, UInt32.toNat_zero, List.drop_zero]
    · simp only [zero, UInt32.toNat_zero, Nat.add_zero]
      simp only [state, back, zero]
    · rw [zero] at budget
      change s.offset.toNat ≤ 73726
      have : (0 : UInt32).toNat = 0 := rfl
      simp only [this, Nat.pow_zero] at budget
      omega
    · simp only [zero, UInt32.toNat_zero, Nat.add_zero]
      exact back
  · obtain ⟨result, current, used, run, usedBound, currentInv, sameStream, count, shape,
        bitBound, _, enough, empty, kinds, cursor⟩ := NEEDBITS_run_cursor B s.extra (by omega)
    have prefixRun := inflate_DISTEXT_need_cut (l := l) hc good.live.hs zero
    cases result with
    | error e =>
      have equal : e = Ex.leave := by
        rcases kinds with impossible | equal
        · cases impossible
        · exact Except.error.inj equal
      subst e
      left
      refine ⟨current, used, ?_, usedBound, currentInv, (empty rfl).2.1, sameStream, ?_, cursor, by omega⟩
      · rw [prefixRun]
        unfold distExtraNeed
        rw [runX_bind, run]
      · unfold SymbolRegShape
        rw [shape]
    | ok unit =>
      cases unit
      have available := enough rfl
      let bits := current.hold.toUInt32 &&& ((1 : UInt32) <<< s.extra - 1)
      have bitsNat : bits.toNat = current.hold.toNat % 2 ^ s.extra.toNat := BITS_toNat current s.extra (by omega)
      have bitsBound : bits.toNat < 2 ^ s.extra.toNat := by rw [bitsNat]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
      have lengthNat : (s.offset + bits).toNat = s.offset.toNat + bits.toNat := by
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
      let state := { s with offset := s.offset + bits, back := Int32.ofNat (before + s.extra.toNat), mode := MATCH }
      let after := setI h zs state
      have finalGood := good.decode_update (after := state) rfl (by change HEAD ≤ MATCH ∧ MATCH ≤ SYNC; decide)
      have finalTables := tables.decode_update good.live.hs (after := state) rfl
      right
      refine ⟨regs, after, state, used, ?_, usedBound, finalGood, finalTables,
        finalInv.decode_update zs state, rfl, rfl, ?_, ?_, rfl, rfl, ?_, ?_, rfl, cursor, by
          change (current.bits - s.extra).toNat ≤ max l.bits.toNat 20
          rw [UInt32.toNat_sub_of_le _ _ available]
          omega⟩
      · rw [prefixRun]
        unfold distExtraNeed
        rw [runX_bind, run]
        simp only [runX_bind, BITS_run current h s.extra (by omega), runX_lift, hc,
          wrI_eq, good.live.hs, setI_istates_same, DROPBITS_run, small, setI_setI, setMode]
        simp only [backEq]
        rfl
      · unfold SymbolRegShape
        dsimp only [regs]
        rw [shape]
      · exact finalStream.trans (congrArg (List.drop s.extra.toNat) sameStream)
      · change 1 ≤ (s.offset + bits).toNat
        rw [lengthNat]
        omega
      · change (s.offset + bits).toNat ≤ 73726
        rw [lengthNat]
        omega


/-- Projection retaining the previous boundary. -/
theorem inflate_DISTEXT_boundary_cursor {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8} (before : Nat)
    (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (B : BitInv h l bs) (extra : s.extra.toNat ≤ 13)
    (lower : 1 ≤ s.offset.toNat) (budget : s.offset.toNat + 2 ^ s.extra.toNat ≤ 73727)
    (back : s.back = Int32.ofNat before) (backBound : before ≤ 35) :
    (∃ regs used,
      runX (inflate_DISTEXT c) l h = .ok ((.error Ex.leave, regs), h) ∧
      used ≤ bs.length ∧ BitInv h regs (bs.drop used) ∧ regs.have_ = 0 ∧
      stream regs (bs.drop used) = stream l bs ∧ SymbolRegShape l regs ∧ regs.next = inputAdvance l.next used) ∨
    (∃ regs after state used,
      runX (inflate_DISTEXT c) l h = runX (inflate_MATCH c) regs after ∧
      used ≤ bs.length ∧ Good after r zs z state ∧ DataTablesSafe after state ∧
      BitInv after regs (bs.drop used) ∧ state.mode = MATCH ∧ DecodeStateFrame s state ∧
      SymbolRegShape l regs ∧ stream regs (bs.drop used) = (stream l bs).drop s.extra.toNat ∧
      after = setI h zs state ∧ state = { s with offset := state.offset, back := Int32.ofNat (before + s.extra.toNat), mode := MATCH } ∧
      1 ≤ state.offset.toNat ∧ state.offset.toNat ≤ 73726 ∧
      state.back = Int32.ofNat (before + s.extra.toNat) ∧ regs.next = inputAdvance l.next used) := by
  rcases inflate_DISTEXT_boundary_bounded before hr hc good tables B extra lower budget back backBound with wait | continued
  · obtain ⟨regs, used, run, usedBound, inv, empty, bits, shape, cursor, _⟩ := wait
    exact Or.inl ⟨regs, used, run, usedBound, inv, empty, bits, shape, cursor⟩
  · obtain ⟨regs, after, state, used, run, usedBound, finalGood, finalTables, inv,
      mode, frame, shape, bits, heap, stateEq, lower, upper, back, cursor, _⟩ := continued
    exact Or.inr ⟨regs, after, state, used, run, usedBound, finalGood, finalTables, inv,
      mode, frame, shape, bits, heap, stateEq, lower, upper, back, cursor⟩

/-- Projection retaining the original distance-extra boundary. -/
theorem inflate_DISTEXT_boundary {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8} (before : Nat)
    (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (B : BitInv h l bs) (extra : s.extra.toNat ≤ 13)
    (lower : 1 ≤ s.offset.toNat) (budget : s.offset.toNat + 2 ^ s.extra.toNat ≤ 73727)
    (back : s.back = Int32.ofNat before) (backBound : before ≤ 35) :
    (∃ regs used,
      runX (inflate_DISTEXT c) l h = .ok ((.error Ex.leave, regs), h) ∧
      used ≤ bs.length ∧ BitInv h regs (bs.drop used) ∧ regs.have_ = 0 ∧
      stream regs (bs.drop used) = stream l bs ∧ SymbolRegShape l regs) ∨
    (∃ regs after state used,
      runX (inflate_DISTEXT c) l h = runX (inflate_MATCH c) regs after ∧
      used ≤ bs.length ∧ Good after r zs z state ∧ DataTablesSafe after state ∧
      BitInv after regs (bs.drop used) ∧ state.mode = MATCH ∧ DecodeStateFrame s state ∧
      SymbolRegShape l regs ∧ stream regs (bs.drop used) = (stream l bs).drop s.extra.toNat ∧
      after = setI h zs state ∧ state = { s with offset := state.offset, back := Int32.ofNat (before + s.extra.toNat), mode := MATCH } ∧
      1 ≤ state.offset.toNat ∧ state.offset.toNat ≤ 73726 ∧
      state.back = Int32.ofNat (before + s.extra.toNat)) := by
  rcases inflate_DISTEXT_boundary_cursor before hr hc good tables B extra lower budget back backBound with wait | continued
  · obtain ⟨regs, used, run, usedBound, inv, empty, bits, shape, _⟩ := wait
    exact Or.inl ⟨regs, used, run, usedBound, inv, empty, bits, shape⟩
  · obtain ⟨regs, after, state, used, run, usedBound, finalGood, finalTables, inv,
      mode, frame, shape, bits, heap, stateEq, lower, upper, back, _⟩ := continued
    exact Or.inr ⟨regs, after, state, used, run, usedBound, finalGood, finalTables, inv,
      mode, frame, shape, bits, heap, stateEq, lower, upper, back⟩

end Zlib.Inflate.Proofs
