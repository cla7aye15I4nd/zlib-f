import ZlibF.Proof.«inflate.c.length-finish»
import ZlibF.Proof.«inflate.c.bits-complete»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

/-- Source-order suffix entered when LENEXT needs extra bits. -/
def lenExtraNeed (c : Ctx) (extra : UInt32) : X Unit := do
  NEEDBITS extra
  let b ← BITS extra
  wrS c.st fun s => { s with length := s.length + b }
  DROPBITS extra
  wrS c.st fun s => { s with back := u2i (i2u s.back + s.extra) }
  wrS c.st fun s => { s with was := s.length, mode := DIST }
  inflate_DIST c

/-- The nonzero-extra source cut is the actual LENEXT suffix. -/
theorem inflate_LENEXT_need_cut {c : Ctx} {l : IL} {h : Heap} {zs : Nat} {s : InflateState}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s) (nonzero : s.extra ≠ 0) :
    runX (inflate_LENEXT c) l h = runX (lenExtraNeed c s.extra) l h := by
  have load : ldInflateState c.st h = .ok (s, h) := by rw [hc, ldI_eq, hs]
  unfold inflate_LENEXT lenExtraNeed
  rw [runX_bind, runX_lift_ok load]
  simp [nonzero]

/-- Actual LENEXT either leaves for input or reaches the actual DIST call.
Its base and extra-bit budget implies a decoded length between 3 and 258.
The signed back value is derived from the bounded actual unsigned update. -/
theorem inflate_LENEXT_boundary_bounded {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8} (before : Nat)
    (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (B : BitInv h l bs) (extra : s.extra.toNat ≤ 5)
    (lower : 3 ≤ s.length.toNat) (budget : s.length.toNat + 2 ^ s.extra.toNat ≤ 259)
    (back : s.back = Int32.ofNat before) (backBound : before ≤ 15) :
    (∃ regs used,
      runX (inflate_LENEXT c) l h = .ok ((.error Ex.leave, regs), h) ∧
      used ≤ bs.length ∧ BitInv h regs (bs.drop used) ∧ regs.have_ = 0 ∧
      stream regs (bs.drop used) = stream l bs ∧ SymbolRegShape l regs ∧ regs.next = inputAdvance l.next used ∧ regs.bits.toNat ≤ max l.bits.toNat 12) ∨
    (∃ regs after state used,
      runX (inflate_LENEXT c) l h = runX (inflate_DIST c) regs after ∧
      used ≤ bs.length ∧ Good after r zs z state ∧ DataTablesSafe after state ∧
      BitInv after regs (bs.drop used) ∧ state.mode = DIST ∧ DecodeStateFrame s state ∧
      SymbolRegShape l regs ∧ stream regs (bs.drop used) = (stream l bs).drop s.extra.toNat ∧
      state.was = state.length ∧ 3 ≤ state.length.toNat ∧ state.length.toNat ≤ 258 ∧
      state.back = Int32.ofNat (before + s.extra.toNat) ∧ after = setI h zs state ∧ regs.next = inputAdvance l.next used ∧ regs.bits.toNat ≤ max l.bits.toNat 12) := by
  have env : Env c h r zs z s := ⟨hr, hc, good.live.hz, good.live.hs⟩
  have load : ldInflateState c.st h = .ok (s, h) := by rw [hc, ldI_eq, good.live.hs]
  by_cases zero : s.extra = 0
  · right
    let state := { s with was := s.length, mode := DIST }
    have finalGood := good.decode_update (after := state) rfl (by change HEAD ≤ DIST ∧ DIST ≤ SYNC; decide)
    have finalTables := tables.decode_update good.live.hs (after := state) rfl
    refine ⟨l, setI h zs state, state, 0, ?_, by omega, finalGood, finalTables,
      B.decode_update zs state, rfl, rfl, by rfl, ?_, rfl, lower, ?_, ?_, rfl, (inputAdvance_zero l.next).symm, Nat.le_max_left _ _⟩
    · unfold inflate_LENEXT
      simp only [runX_bind, runX_lift_ok load, zero, bne_self_eq_false, Bool.false_eq_true, ite_false,
        runX_wrS env]
      simp only [state, zero]
    · simp only [zero, UInt32.toNat_zero, List.drop_zero]
    · rw [zero] at budget
      change s.length.toNat ≤ 258
      have : (0 : UInt32).toNat = 0 := rfl
      simp only [this, Nat.pow_zero] at budget
      omega
    · simp only [zero, UInt32.toNat_zero, Nat.add_zero]
      exact back
  · obtain ⟨result, current, used, run, usedBound, currentInv, sameStream, count, shape,
        bitBound, _, enough, empty, kinds, cursor⟩ := NEEDBITS_run_cursor B s.extra (by omega)
    have prefixRun := inflate_LENEXT_need_cut (l := l) hc good.live.hs zero
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
        unfold lenExtraNeed
        rw [runX_bind, run]
      · unfold SymbolRegShape
        rw [shape]
    | ok unit =>
      cases unit
      have available := enough rfl
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
      right
      refine ⟨regs, after, state, used, ?_, usedBound, finalGood, finalTables,
        finalInv.decode_update zs state, rfl, rfl, ?_, ?_, rfl, ?_, ?_, rfl, rfl, cursor, by
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
      · change 3 ≤ (s.length + bits).toNat
        rw [lengthNat]
        omega
      · change (s.length + bits).toNat ≤ 258
        rw [lengthNat]
        omega

/-- Projection retaining the previous boundary. -/
theorem inflate_LENEXT_boundary_cursor {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8} (before : Nat)
    (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (B : BitInv h l bs) (extra : s.extra.toNat ≤ 5)
    (lower : 3 ≤ s.length.toNat) (budget : s.length.toNat + 2 ^ s.extra.toNat ≤ 259)
    (back : s.back = Int32.ofNat before) (backBound : before ≤ 15) :
    (∃ regs used,
      runX (inflate_LENEXT c) l h = .ok ((.error Ex.leave, regs), h) ∧
      used ≤ bs.length ∧ BitInv h regs (bs.drop used) ∧ regs.have_ = 0 ∧
      stream regs (bs.drop used) = stream l bs ∧ SymbolRegShape l regs ∧ regs.next = inputAdvance l.next used) ∨
    (∃ regs after state used,
      runX (inflate_LENEXT c) l h = runX (inflate_DIST c) regs after ∧
      used ≤ bs.length ∧ Good after r zs z state ∧ DataTablesSafe after state ∧
      BitInv after regs (bs.drop used) ∧ state.mode = DIST ∧ DecodeStateFrame s state ∧
      SymbolRegShape l regs ∧ stream regs (bs.drop used) = (stream l bs).drop s.extra.toNat ∧
      state.was = state.length ∧ 3 ≤ state.length.toNat ∧ state.length.toNat ≤ 258 ∧
      state.back = Int32.ofNat (before + s.extra.toNat) ∧ after = setI h zs state ∧ regs.next = inputAdvance l.next used) := by
  rcases inflate_LENEXT_boundary_bounded before hr hc good tables B extra lower budget back backBound with wait | continued
  · obtain ⟨regs, used, run, usedBound, inv, empty, bits, shape, cursor, _⟩ := wait
    exact Or.inl ⟨regs, used, run, usedBound, inv, empty, bits, shape, cursor⟩
  · obtain ⟨regs, after, state, used, run, usedBound, finalGood, finalTables, inv,
      mode, frame, shape, bits, was, lower, upper, back, heap, cursor, _⟩ := continued
    exact Or.inr ⟨regs, after, state, used, run, usedBound, finalGood, finalTables, inv,
      mode, frame, shape, bits, was, lower, upper, back, heap, cursor⟩

/-- Projection retaining the original length-extra heap boundary. -/
theorem inflate_LENEXT_boundary_heap {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8} (before : Nat)
    (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (B : BitInv h l bs) (extra : s.extra.toNat ≤ 5)
    (lower : 3 ≤ s.length.toNat) (budget : s.length.toNat + 2 ^ s.extra.toNat ≤ 259)
    (back : s.back = Int32.ofNat before) (backBound : before ≤ 15) :
    (∃ regs used,
      runX (inflate_LENEXT c) l h = .ok ((.error Ex.leave, regs), h) ∧
      used ≤ bs.length ∧ BitInv h regs (bs.drop used) ∧ regs.have_ = 0 ∧
      stream regs (bs.drop used) = stream l bs ∧ SymbolRegShape l regs) ∨
    (∃ regs after state used,
      runX (inflate_LENEXT c) l h = runX (inflate_DIST c) regs after ∧
      used ≤ bs.length ∧ Good after r zs z state ∧ DataTablesSafe after state ∧
      BitInv after regs (bs.drop used) ∧ state.mode = DIST ∧ DecodeStateFrame s state ∧
      SymbolRegShape l regs ∧ stream regs (bs.drop used) = (stream l bs).drop s.extra.toNat ∧
      state.was = state.length ∧ 3 ≤ state.length.toNat ∧ state.length.toNat ≤ 258 ∧
      state.back = Int32.ofNat (before + s.extra.toNat) ∧ after = setI h zs state) := by
  rcases inflate_LENEXT_boundary_cursor before hr hc good tables B extra lower budget back backBound with wait | continued
  · obtain ⟨regs, used, run, usedBound, inv, empty, bits, shape, _⟩ := wait
    exact Or.inl ⟨regs, used, run, usedBound, inv, empty, bits, shape⟩
  · obtain ⟨regs, after, state, used, run, usedBound, finalGood, finalTables, inv,
      mode, frame, shape, bits, was, lower, upper, back, heap, _⟩ := continued
    exact Or.inr ⟨regs, after, state, used, run, usedBound, finalGood, finalTables, inv,
      mode, frame, shape, bits, was, lower, upper, back, heap⟩

/-- Projection retaining the original length-extra boundary. -/
theorem inflate_LENEXT_boundary {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8} (before : Nat)
    (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (B : BitInv h l bs) (extra : s.extra.toNat ≤ 5)
    (lower : 3 ≤ s.length.toNat) (budget : s.length.toNat + 2 ^ s.extra.toNat ≤ 259)
    (back : s.back = Int32.ofNat before) (backBound : before ≤ 15) :
    (∃ regs used,
      runX (inflate_LENEXT c) l h = .ok ((.error Ex.leave, regs), h) ∧
      used ≤ bs.length ∧ BitInv h regs (bs.drop used) ∧ regs.have_ = 0 ∧
      stream regs (bs.drop used) = stream l bs ∧ SymbolRegShape l regs) ∨
    (∃ regs after state used,
      runX (inflate_LENEXT c) l h = runX (inflate_DIST c) regs after ∧
      used ≤ bs.length ∧ Good after r zs z state ∧ DataTablesSafe after state ∧
      BitInv after regs (bs.drop used) ∧ state.mode = DIST ∧ DecodeStateFrame s state ∧
      SymbolRegShape l regs ∧ stream regs (bs.drop used) = (stream l bs).drop s.extra.toNat ∧
      state.was = state.length ∧ 3 ≤ state.length.toNat ∧ state.length.toNat ≤ 258 ∧
      state.back = Int32.ofNat (before + s.extra.toNat)) := by
  rcases inflate_LENEXT_boundary_heap before hr hc good tables B extra lower budget back backBound with wait | continued
  · exact Or.inl wait
  · obtain ⟨regs, after, state, used, run, usedBound, finalGood, finalTables, inv,
      mode, frame, shape, bits, was, lower, upper, back, _⟩ := continued
    exact Or.inr ⟨regs, after, state, used, run, usedBound, finalGood, finalTables, inv,
      mode, frame, shape, bits, was, lower, upper, back⟩

/-- The actual slow LEN and LENEXT chain reaches safe terminal exits or the
actual DIST call. Every length/extra/back premise of LENEXT is derived from
the selected table leaf on the same run; none is a public caller assumption. -/
theorem inflate_LEN_slow_to_DIST_frame {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (good : Good h r zs z s)
    (tables : DataTablesSafe h s) (B : BitInv h l bs)
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    (∃ outcome regs after finalZ state used consumed,
      used ≤ bs.length ∧ consumed ≤ 20 ∧
      runX (inflate_LEN c) l h = .ok ((outcome, regs), after) ∧
      Good after r zs finalZ state ∧ DataTableInvariant after state ∧ BitInv after regs (bs.drop used) ∧
      stream regs (bs.drop used) = (stream l bs).drop consumed ∧
      SymbolRegShape l regs ∧ DecodeStateFrame s state ∧
      (outcome = .error Ex.leave ∨ (outcome = .ok () ∧ (state.mode = LIT ∨ state.mode = TYPE ∨ state.mode = BAD))) ∧
      regs.next = inputAdvance l.next used ∧ after = setI (r.put h finalZ) zs state) ∨
    (∃ regs after state used consumed,
      used ≤ bs.length ∧ consumed ≤ 20 ∧
      runX (inflate_LEN c) l h = runX (inflate_DIST c) regs after ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧ BitInv after regs (bs.drop used) ∧
      stream regs (bs.drop used) = (stream l bs).drop consumed ∧
      SymbolRegShape l regs ∧ DecodeStateFrame s state ∧ state.mode = DIST ∧
      state.was = state.length ∧ 3 ≤ state.length.toNat ∧ state.length.toNat ≤ 258 ∧
      state.back = Int32.ofNat consumed ∧ after = setI h zs state ∧ regs.next = inputAdvance l.next used) := by
  rcases inflate_LEN_slow_boundary_frame hr hc good tables B slow with stopped | continued
  · obtain ⟨outcome, regs, after, finalZ, state, used, consumed, _, usedBound, consumedBound,
      run, finalGood, data, inv, bits, shape, frame, _, kinds, cursor, heapEq⟩ := stopped
    exact Or.inl ⟨outcome, regs, after, finalZ, state, used, consumed, usedBound, by omega,
      run, finalGood, data, inv, bits, shape, frame, kinds, cursor, heapEq⟩
  · obtain ⟨regs, after, state, used, consumed, _, usedBound, consumedBound,
      source, nextGood, nextTables, nextInv, bits, shape, frame, _, _, extra, lower, upper, back, heapEq, cursor⟩ := continued
    rcases inflate_LENEXT_boundary_cursor consumed hr hc nextGood nextTables nextInv extra lower upper back consumedBound with wait | continued
    · obtain ⟨finalRegs, used2, run, usedBound2, finalInv, _, finalStream, finalShape, cursor2⟩ := wait
      have totalBound : used + used2 ≤ bs.length := by simp only [List.length_drop] at usedBound2; omega
      have inv : BitInv after finalRegs (bs.drop (used + used2)) := by
        simpa only [List.drop_drop, Nat.add_comm] using finalInv
      have finalBits : stream finalRegs (bs.drop (used + used2)) = (stream l bs).drop consumed := by
        simpa only [List.drop_drop, Nat.add_comm] using finalStream.trans bits
      exact Or.inl ⟨.error Ex.leave, finalRegs, after, z, state, used + used2, consumed,
        totalBound, by omega, source.trans run, nextGood, fun _ => nextTables, inv, finalBits,
        shape.trans finalShape, frame, Or.inl rfl, by rw [cursor2, cursor, inputAdvance_add],
        by rw [ZStreamRef.put_self good.live.hz]; exact heapEq⟩
    · obtain ⟨finalRegs, finalHeap, finalState, used2, run, usedBound2, finalGood, finalTables,
        finalInv, mode, finalFrame, finalShape, finalStream, was, finalLower, finalUpper, finalBack, finalHeapEq, cursor2⟩ := continued
      have totalBound : used + used2 ≤ bs.length := by simp only [List.length_drop] at usedBound2; omega
      have inv : BitInv finalHeap finalRegs (bs.drop (used + used2)) := by
        simpa only [List.drop_drop, Nat.add_comm] using finalInv
      have finalBits : stream finalRegs (bs.drop (used + used2)) =
          (stream l bs).drop (consumed + state.extra.toNat) := by
        simp only [List.drop_drop] at finalStream
        rw [bits, List.drop_drop] at finalStream
        exact finalStream
      exact Or.inr ⟨finalRegs, finalHeap, finalState, used + used2, consumed + state.extra.toNat,
        totalBound, by omega, source.trans run, finalGood, finalTables, inv, finalBits,
        shape.trans finalShape, frame.trans finalFrame, mode, was, finalLower, finalUpper, finalBack,
          by rw [finalHeapEq, heapEq, setI_setI], by rw [cursor2, cursor, inputAdvance_add]⟩

/-- Projection retaining the previous boundary. -/
theorem inflate_LEN_slow_to_DIST_cursor {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (good : Good h r zs z s)
    (tables : DataTablesSafe h s) (B : BitInv h l bs)
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    (∃ outcome regs after finalZ state used consumed,
      used ≤ bs.length ∧ consumed ≤ 20 ∧
      runX (inflate_LEN c) l h = .ok ((outcome, regs), after) ∧
      Good after r zs finalZ state ∧ DataTableInvariant after state ∧ BitInv after regs (bs.drop used) ∧
      stream regs (bs.drop used) = (stream l bs).drop consumed ∧
      SymbolRegShape l regs ∧ DecodeStateFrame s state ∧
      (outcome = .error Ex.leave ∨ (outcome = .ok () ∧ (state.mode = LIT ∨ state.mode = TYPE ∨ state.mode = BAD))) ∧
      regs.next = inputAdvance l.next used) ∨
    (∃ regs after state used consumed,
      used ≤ bs.length ∧ consumed ≤ 20 ∧
      runX (inflate_LEN c) l h = runX (inflate_DIST c) regs after ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧ BitInv after regs (bs.drop used) ∧
      stream regs (bs.drop used) = (stream l bs).drop consumed ∧
      SymbolRegShape l regs ∧ DecodeStateFrame s state ∧ state.mode = DIST ∧
      state.was = state.length ∧ 3 ≤ state.length.toNat ∧ state.length.toNat ≤ 258 ∧
      state.back = Int32.ofNat consumed ∧ after = setI h zs state ∧ regs.next = inputAdvance l.next used) := by
  rcases inflate_LEN_slow_to_DIST_frame hr hc good tables B slow with stopped | continued
  · obtain ⟨outcome, regs, after, finalZ, state, used, consumed, usedBound, consumedBound,
      run, finalGood, data, inv, bits, shape, frame, kinds, cursor, _⟩ := stopped
    exact Or.inl ⟨outcome, regs, after, finalZ, state, used, consumed, usedBound, consumedBound,
      run, finalGood, data, inv, bits, shape, frame, kinds, cursor⟩
  · exact Or.inr continued

/-- Projection retaining the original slow length/extra heap composition. -/
theorem inflate_LEN_slow_to_DIST_heap {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (good : Good h r zs z s)
    (tables : DataTablesSafe h s) (B : BitInv h l bs)
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    (∃ outcome regs after finalZ state used consumed,
      used ≤ bs.length ∧ consumed ≤ 20 ∧
      runX (inflate_LEN c) l h = .ok ((outcome, regs), after) ∧
      Good after r zs finalZ state ∧ DataTableInvariant after state ∧ BitInv after regs (bs.drop used) ∧
      stream regs (bs.drop used) = (stream l bs).drop consumed ∧
      SymbolRegShape l regs ∧ DecodeStateFrame s state ∧
      (outcome = .error Ex.leave ∨ (outcome = .ok () ∧ (state.mode = LIT ∨ state.mode = TYPE ∨ state.mode = BAD)))) ∨
    (∃ regs after state used consumed,
      used ≤ bs.length ∧ consumed ≤ 20 ∧
      runX (inflate_LEN c) l h = runX (inflate_DIST c) regs after ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧ BitInv after regs (bs.drop used) ∧
      stream regs (bs.drop used) = (stream l bs).drop consumed ∧
      SymbolRegShape l regs ∧ DecodeStateFrame s state ∧ state.mode = DIST ∧
      state.was = state.length ∧ 3 ≤ state.length.toNat ∧ state.length.toNat ≤ 258 ∧
      state.back = Int32.ofNat consumed ∧ after = setI h zs state) := by
  rcases inflate_LEN_slow_to_DIST_cursor hr hc good tables B slow with stopped | continued
  · obtain ⟨outcome, regs, after, finalZ, state, used, consumed, usedBound, consumedBound,
      run, finalGood, data, inv, bits, shape, frame, kinds, _⟩ := stopped
    exact Or.inl ⟨outcome, regs, after, finalZ, state, used, consumed, usedBound, consumedBound,
      run, finalGood, data, inv, bits, shape, frame, kinds⟩
  · obtain ⟨regs, after, state, used, consumed, usedBound, consumedBound, run,
      finalGood, finalTables, inv, bits, shape, frame, mode, was, lower, upper, back, heap, _⟩ := continued
    exact Or.inr ⟨regs, after, state, used, consumed, usedBound, consumedBound, run,
      finalGood, finalTables, inv, bits, shape, frame, mode, was, lower, upper, back, heap⟩

/-- Projection retaining the original slow LEN/DIST composition. -/
theorem inflate_LEN_slow_to_DIST {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (good : Good h r zs z s)
    (tables : DataTablesSafe h s) (B : BitInv h l bs)
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    (∃ outcome regs after finalZ state used consumed,
      used ≤ bs.length ∧ consumed ≤ 20 ∧
      runX (inflate_LEN c) l h = .ok ((outcome, regs), after) ∧
      Good after r zs finalZ state ∧ DataTableInvariant after state ∧ BitInv after regs (bs.drop used) ∧
      stream regs (bs.drop used) = (stream l bs).drop consumed ∧
      SymbolRegShape l regs ∧ DecodeStateFrame s state ∧
      (outcome = .error Ex.leave ∨ (outcome = .ok () ∧ (state.mode = LIT ∨ state.mode = TYPE ∨ state.mode = BAD)))) ∨
    (∃ regs after state used consumed,
      used ≤ bs.length ∧ consumed ≤ 20 ∧
      runX (inflate_LEN c) l h = runX (inflate_DIST c) regs after ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧ BitInv after regs (bs.drop used) ∧
      stream regs (bs.drop used) = (stream l bs).drop consumed ∧
      SymbolRegShape l regs ∧ DecodeStateFrame s state ∧ state.mode = DIST ∧
      state.was = state.length ∧ 3 ≤ state.length.toNat ∧ state.length.toNat ≤ 258 ∧
      state.back = Int32.ofNat consumed) := by
  rcases inflate_LEN_slow_to_DIST_heap hr hc good tables B slow with stopped | continued
  · exact Or.inl stopped
  · obtain ⟨regs, after, state, used, consumed, usedBound, consumedBound, run,
      finalGood, finalTables, inv, bits, shape, frame, mode, was, lower, upper, back, _⟩ := continued
    exact Or.inr ⟨regs, after, state, used, consumed, usedBound, consumedBound, run,
      finalGood, finalTables, inv, bits, shape, frame, mode, was, lower, upper, back⟩

end Zlib.Inflate.Proofs
