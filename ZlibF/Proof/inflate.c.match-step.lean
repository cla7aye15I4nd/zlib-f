import ZlibF.Proof.«inflate.c.match-boundary»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

/-- MATCH with no room leaves even when the output pointer is NULL. -/
theorem inflate_MATCH_wait (c : Ctx) (h : Heap) (l : IL) (left : l.left = 0) :
    runX (inflate_MATCH c) l h = .ok ((.error Ex.leave, l), h) := by
  rw [inflate_MATCH_select_cut]
  exact matchSelect_wait c h l left

/-- Complete actual MATCH safety with a conditional caller-output premise.
NULL empty output needs no array witness. A pending match retains its exact
distance, original length and sanity value, and a normal copied segment
strictly decreases output room. These internal premises still need dispatch
and legal-history producers for the public theorem. -/
theorem inflate_MATCH_step_input {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    {l : IL} {bs : List UInt8} (B : BitInv h l bs)
    (mode : s.mode = MATCH) (length : 0 < s.length.toNat) (lengthWas : s.length.toNat ≤ s.was.toNat)
    (wasBound : s.was.toNat ≤ 258) (offset : 0 < s.offset.toNat) (sane : s.sane ≠ 0)
    (output : l.left ≠ 0 → ∃ (dest : BRef) (array : Array UInt8) (outOffset : Nat),
      l.put = .ref dest outOffset ∧ Space.get h dest = some array ∧ Space.ro h dest = false ∧
      outOffset + l.left.toNat ≤ array.size ∧ l.left.toNat ≤ l.out_.toNat ∧
      l.out_.toNat - l.left.toNat ≤ outOffset ∧
      (∀ w, s.window = .ref (.blk w) 0 → dest ≠ .blk w) ∧
      (bs = [] ∨ ∀ i, l.next = .ref dest i → i + bs.length ≤ outOffset ∨ outOffset + l.left.toNat ≤ i)) :
    ∃ outcome regs after stream state,
      runX (inflate_MATCH c) l h = .ok ((outcome, regs), after) ∧
      Good after r zs stream state ∧ DataTableInvariant after state ∧ BitInv after regs bs ∧
      DecodeStateFrame s state ∧
      (outcome = .error Ex.leave ∨ outcome = .ok ()) ∧
      (state.mode = MATCH ∨ state.mode = LEN ∨ state.mode = BAD) ∧
      (state.mode = MATCH → 0 < state.length.toNat ∧ state.length.toNat ≤ state.was.toNat ∧
        state.was.toNat ≤ 258 ∧ state.offset = s.offset ∧ state.was = s.was ∧ state.sane = s.sane) ∧
      (outcome = .ok () → state.mode = BAD ∨ regs.left.toNat < l.left.toNat) ∧
      Zlib.Inflate.Proofs.stream regs bs = Zlib.Inflate.Proofs.stream l bs := by
  by_cases empty : l.left = 0
  · refine ⟨.error Ex.leave, l, h, z, s, inflate_MATCH_wait c h l empty, good,
      fun _ => tables, B, by rfl, Or.inl rfl, Or.inl mode,
      fun _ => ⟨length, lengthWas, wasBound, rfl, rfl, rfl⟩, ?_, rfl⟩
    intro impossible
    cases impossible
  · obtain ⟨dest, array, outOffset, put, get, write, room, count, produced, privateWindow, separate⟩ := output empty
    obtain ⟨outcome, regs, after, stream, state, run, finalGood, data, inv, frame, kinds⟩ :=
      inflate_MATCH_boundary_ranges E good tables B put get write mode length offset sane
        room count produced privateWindow separate
    refine ⟨outcome, regs, after, stream, state, run, finalGood, data, inv, frame, ?_, ?_, ?_, ?_, ?_⟩
    · rcases kinds with ⟨wait, _⟩ | ⟨ok, _⟩ | ⟨ok, _⟩
      · exact Or.inl wait
      · exact Or.inr ok
      · exact Or.inr ok
    · rcases kinds with ⟨_, _, _, stateEq⟩ | ⟨_, bad, _⟩ | ⟨_, copy, source, sourceOffset, saved, _, _, _, _, _, _, _, modes, _⟩
      · exact Or.inl ((congrArg InflateState.mode stateEq).trans mode)
      · exact Or.inr (Or.inr bad)
      · rcases modes with len | matchMode
        · exact Or.inr (Or.inl len)
        · exact Or.inl matchMode
    · intro matching
      rcases kinds with ⟨_, _, _, stateEq⟩ | ⟨_, bad, _⟩ | ⟨_, copy, source, sourceOffset, saved, positive, copyLeft, copyLength, _, _, stateEq, _, _, _⟩
      · subst state
        exact ⟨length, lengthWas, wasBound, rfl, rfl, rfl⟩
      · have impossible : MATCH ≠ BAD := by decide
        exact False.elim (impossible (matching.symm.trans bad))
      · rw [stateEq] at matching ⊢
        dsimp only [matchEmitState] at matching ⊢
        by_cases remaining : (s.length - copy == 0) = true
        · simp only [remaining, ↓reduceIte] at matching
          have impossible : LEN ≠ MATCH := by decide
          exact False.elim (impossible matching)
        · simp only [remaining, Bool.false_eq_true, ↓reduceIte]
          have nonzero : (s.length - copy).toNat ≠ 0 := by
            intro zero
            apply remaining
            exact beq_iff_eq.mpr (UInt32.toNat_inj.mp zero)
          have lengthNat := UInt32.toNat_sub_of_le s.length copy (by exact copyLength)
          exact ⟨by omega, by omega, wasBound, by trivial, by trivial, by trivial⟩
    · intro ok
      rcases kinds with ⟨wait, _⟩ | ⟨_, bad, _⟩ | ⟨_, copy, source, sourceOffset, saved, _, _, _, _, _, _, _, _, decrease⟩
      · rw [ok] at wait
        cases wait
      · exact Or.inl bad
      · exact Or.inr decrease

    · rcases kinds with ⟨_, regsEq, _, _⟩ | ⟨_, _, regsEq, _⟩ |
          ⟨_, copy, source, sourceOffset, saved, _, _, _, regsEq, _⟩
      · rw [regsEq]
      · rw [regsEq]
      · rw [regsEq]
        rfl
/-- Projection retaining the prior range-sensitive step. -/
theorem inflate_MATCH_step_ranges {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    {l : IL} {bs : List UInt8} (B : BitInv h l bs)
    (mode : s.mode = MATCH) (length : 0 < s.length.toNat) (lengthWas : s.length.toNat ≤ s.was.toNat)
    (wasBound : s.was.toNat ≤ 258) (offset : 0 < s.offset.toNat) (sane : s.sane ≠ 0)
    (output : l.left ≠ 0 → ∃ (dest : BRef) (array : Array UInt8) (outOffset : Nat),
      l.put = .ref dest outOffset ∧ Space.get h dest = some array ∧ Space.ro h dest = false ∧
      outOffset + l.left.toNat ≤ array.size ∧ l.left.toNat ≤ l.out_.toNat ∧
      l.out_.toNat - l.left.toNat ≤ outOffset ∧
      (∀ w, s.window = .ref (.blk w) 0 → dest ≠ .blk w) ∧
      (bs = [] ∨ ∀ i, l.next = .ref dest i → i + bs.length ≤ outOffset ∨ outOffset + l.left.toNat ≤ i)) :
    ∃ outcome regs after stream state,
      runX (inflate_MATCH c) l h = .ok ((outcome, regs), after) ∧
      Good after r zs stream state ∧ DataTableInvariant after state ∧ BitInv after regs bs ∧
      DecodeStateFrame s state ∧
      (outcome = .error Ex.leave ∨ outcome = .ok ()) ∧
      (state.mode = MATCH ∨ state.mode = LEN ∨ state.mode = BAD) ∧
      (state.mode = MATCH → 0 < state.length.toNat ∧ state.length.toNat ≤ state.was.toNat ∧
        state.was.toNat ≤ 258 ∧ state.offset = s.offset ∧ state.was = s.was ∧ state.sane = s.sane) ∧
      (outcome = .ok () → state.mode = BAD ∨ regs.left.toNat < l.left.toNat) := by
  obtain ⟨outcome, regs, after, stream, state, run, finalGood, data, inv, frame,
    kinds, modes, pending, progress, _⟩ :=
      inflate_MATCH_step_input E good tables B mode length lengthWas wasBound offset sane output
  exact ⟨outcome, regs, after, stream, state, run, finalGood, data, inv, frame,
    kinds, modes, pending, progress⟩

/-- Projection retaining the earlier nonempty-range interface. -/
theorem inflate_MATCH_step {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    {l : IL} {bs : List UInt8} (B : BitInv h l bs)
    (mode : s.mode = MATCH) (length : 0 < s.length.toNat) (lengthWas : s.length.toNat ≤ s.was.toNat)
    (wasBound : s.was.toNat ≤ 258) (offset : 0 < s.offset.toNat) (sane : s.sane ≠ 0)
    (output : l.left ≠ 0 → ∃ (dest : BRef) (array : Array UInt8) (outOffset : Nat),
      l.put = .ref dest outOffset ∧ Space.get h dest = some array ∧ Space.ro h dest = false ∧
      outOffset + l.left.toNat ≤ array.size ∧ l.left.toNat ≤ l.out_.toNat ∧
      l.out_.toNat - l.left.toNat ≤ outOffset ∧
      (∀ w, s.window = .ref (.blk w) 0 → dest ≠ .blk w) ∧
      (∀ i, l.next = .ref dest i → i + bs.length ≤ outOffset ∨ outOffset + l.left.toNat ≤ i)) :
    ∃ outcome regs after stream state,
      runX (inflate_MATCH c) l h = .ok ((outcome, regs), after) ∧
      Good after r zs stream state ∧ DataTableInvariant after state ∧ BitInv after regs bs ∧
      DecodeStateFrame s state ∧
      (outcome = .error Ex.leave ∨ outcome = .ok ()) ∧
      (state.mode = MATCH ∨ state.mode = LEN ∨ state.mode = BAD) ∧
      (state.mode = MATCH → 0 < state.length.toNat ∧ state.length.toNat ≤ state.was.toNat ∧
        state.was.toNat ≤ 258 ∧ state.offset = s.offset ∧ state.was = s.was ∧ state.sane = s.sane) ∧
      (outcome = .ok () → state.mode = BAD ∨ regs.left.toNat < l.left.toNat) := by
  apply inflate_MATCH_step_ranges E good tables B mode length lengthWas wasBound offset sane
  intro nonempty
  obtain ⟨dest, array, outOffset, put, get, write, room, count, produced, privateWindow, separate⟩ := output nonempty
  exact ⟨dest, array, outOffset, put, get, write, room, count, produced, privateWindow, Or.inr separate⟩

end Zlib.Inflate.Proofs
