import ZlibF.Proof.«inflate.c.slow-future-prefix»
import ZlibF.Proof.«inflate.c.slow-distance-extra-semantic»

namespace Zlib.Inflate.Proofs.SlowExtraFragmentProgress
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs SlowInputFragment SlowExtraSemanticPath
set_option autoImplicit false

/-- The length-extra phase exposes its exact source-installed fields. -/
theorem lenext_fields {L D : List Nat} {p : CopySyntax L D} {s : InflateState}
    {residual : List Bool} (mode : s.mode = LENEXT) (phase : PendingSyntax p s residual) :
    s.length.toNat = lengthBases.getD (p.symbol - 257) 0 ∧
      s.extra.toNat = lengthExtras.getD (p.symbol - 257) 0 ∧
      s.back = Int32.ofNat (L.getD p.symbol 0) := by
  cases phase with
  | len selected => rcases selected with selected | selected <;> rw [selected] at mode <;> contradiction
  | lenext _ base width back => exact ⟨base, width, back⟩
  | dist selected _ _ _ => rw [selected] at mode; contradiction
  | distext selected _ _ _ _ _ => rw [selected] at mode; contradiction
  | matching selected _ _ _ _ => rw [selected] at mode; contradiction

/-- The distance-extra phase retains the independently parsed length and
its exact source-installed distance base and extra-bit width. -/
theorem distext_fields {L D : List Nat} {p : CopySyntax L D} {s : InflateState}
    {residual : List Bool} (mode : s.mode = DISTEXT) (phase : PendingSyntax p s residual) :
    s.length.toNat = lengthBases.getD (p.symbol - 257) 0 + p.lengthValue ∧
      s.was = s.length ∧ s.offset.toNat = distBases.getD p.distanceSymbol 0 ∧
      s.extra.toNat = distExtras.getD p.distanceSymbol 0 ∧
      s.back = Int32.ofNat (L.getD p.symbol 0 + lengthExtras.getD (p.symbol - 257) 0 + D.getD p.distanceSymbol 0) := by
  cases phase with
  | len selected => rcases selected with selected | selected <;> rw [selected] at mode <;> contradiction
  | lenext selected _ _ _ => rw [selected] at mode; contradiction
  | dist selected _ _ _ => rw [selected] at mode; contradiction
  | distext _ length was base width back => exact ⟨length, was, base, width, back⟩
  | matching selected _ _ _ _ => rw [selected] at mode; contradiction

/-- Every legal length symbol has the exact source addition budget. -/
theorem length_base_extra_budget : ∀ i, i < 29 →
    3 ≤ lengthBases.getD i 0 ∧ lengthExtras.getD i 0 ≤ 5 ∧
      lengthBases.getD i 0 + 2 ^ lengthExtras.getD i 0 ≤ 259 := by
  decide +kernel

/-- A normal length-extra phase either really exhausts current input or
advances to DIST with exact pending syntax. Future bits are never allocated
or read by this proof. -/
theorem LENEXT_fragment_progress
    {L D : List Nat} {p : CopySyntax L D}
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8} {future : List Bool}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (B : BitInv h l bs) (mode : s.mode = LENEXT) (phase : PendingSyntax p s p.r1)
    (codeBound : L.getD p.symbol 0 ≤ 15) (source : FutureSource l bs future p.r1) :
    (∃ regs, InputWait (inflate_LENEXT c) h h l bs future p.r1 regs) ∨
    (∃ regs after state used,
      runX (inflate_LENEXT c) l h = runX (inflate_DIST c) regs after ∧
      used ≤ bs.length ∧ Good after r zs z state ∧ DataTablesSafe after state ∧
      BitInv after regs (bs.drop used) ∧ PendingSyntax p state p.r2 ∧
      FutureSource regs (bs.drop used) future p.r2 ∧ SymbolRegShape l regs ∧
      after = setI h zs state ∧ regs.next = inputAdvance l.next used) := by
  obtain ⟨base, width, back⟩ := lenext_fields mode phase
  obtain ⟨positive, extraBound, budget⟩ := length_base_extra_budget (p.symbol - 257) (by have := p.lengthLower; have := p.lengthUpper; omega)
  by_cases enough : s.extra.toNat ≤ l.bits.toNat + 8 * bs.length
  · right
    have completeRead : readBits s.extra.toNat (stream l bs ++ future) = some (p.lengthValue, p.r2) := by
      rw [width]
      unfold FutureSource at source
      rw [source]
      exact p.lengthRead
    have currentLength : (stream l bs).length = l.bits.toNat + 8 * bs.length := by
      simp only [stream, List.length_append, natBits_length, bytesBits_length]
    obtain ⟨localRest, localRead, suffix⟩ := readBits_restrict completeRead (by rw [currentLength]; exact enough)
    obtain ⟨regs, after, state, used, actual, usedBound, current, currentTables,
      currentBits, nextMode, frame, shape, _drop, was, length, rest, _lo, _hi,
      nextBack, heap, cursor, _bits⟩ := LENEXT_read_semantics (L.getD p.symbol 0)
        E.strm E.st good tables B (by rw [width]; exact extraBound)
        (by rw [base]; exact positive) (by rw [base, width]; exact budget)
        back codeBound localRead
    refine ⟨regs, after, state, used, actual, usedBound, current, currentTables,
      currentBits, ?_, ?_, shape, heap, cursor⟩
    · exact .dist nextMode (by rw [length, base]) was (by simpa only [width] using nextBack)
    · unfold FutureSource
      rw [rest]
      exact suffix.symm
  · exact Or.inl (LENEXT_fragment E B (by rw [width]; omega) (by omega) source)

/-- A normal distance-extra phase likewise either really waits or reaches
MATCH with exact distance, original length and residual semantic source. -/
theorem DISTEXT_fragment_progress
    {L D : List Nat} {p : CopySyntax L D}
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8} {future : List Bool}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (B : BitInv h l bs) (mode : s.mode = DISTEXT) (phase : PendingSyntax p s p.r3)
    (lengthCodeBound : L.getD p.symbol 0 ≤ 15) (distanceCodeBound : D.getD p.distanceSymbol 0 ≤ 15)
    (source : FutureSource l bs future p.r3) :
    (∃ regs, InputWait (inflate_DISTEXT c) h h l bs future p.r3 regs) ∨
    (∃ regs after state used,
      runX (inflate_DISTEXT c) l h = runX (inflate_MATCH c) regs after ∧
      used ≤ bs.length ∧ Good after r zs z state ∧ DataTablesSafe after state ∧
      BitInv after regs (bs.drop used) ∧ PendingSyntax p state p.rest ∧
      FutureSource regs (bs.drop used) future p.rest ∧ SymbolRegShape l regs ∧
      state.length = s.length ∧ state.was = s.was ∧
      1 ≤ state.offset.toNat ∧ state.offset.toNat ≤ 32768 ∧
      after = setI h zs state ∧ regs.next = inputAdvance l.next used) := by
  obtain ⟨length, was, base, width, back⟩ := distext_fields mode phase
  obtain ⟨_lengthLower, lengthExtraBound, _lengthBudget⟩ :=
    length_base_extra_budget (p.symbol - 257) (by have := p.lengthLower; have := p.lengthUpper; omega)
  obtain ⟨_positive, extraBound, _budget⟩ := distance_base_extra_bounds p.distanceSymbol p.distanceUpper
  by_cases enough : s.extra.toNat ≤ l.bits.toNat + 8 * bs.length
  · right
    have completeRead : readBits (distExtras.getD p.distanceSymbol 0) (stream l bs ++ future) = some (p.distanceValue, p.rest) := by
      unfold FutureSource at source
      rw [source]
      exact p.distanceRead
    have currentLength : (stream l bs).length = l.bits.toNat + 8 * bs.length := by
      simp only [stream, List.length_append, natBits_length, bytesBits_length]
    obtain ⟨localRest, localRead, suffix⟩ := readBits_restrict completeRead (by rw [currentLength, ← width]; exact enough)
    obtain ⟨regs, after, state, used, actual, usedBound, current, currentTables,
      currentBits, nextMode, frame, shape, rest, offset, stateEq, lo, hi,
      _noWrap, heap, cursor, _bits⟩ := DISTEXT_symbol_read_semantics
        (L.getD p.symbol 0 + lengthExtras.getD (p.symbol - 257) 0 + D.getD p.distanceSymbol 0)
        E.strm E.st good tables B p.distanceUpper base width back (by omega) localRead
    refine ⟨regs, after, state, used, actual, usedBound, current, currentTables,
      currentBits, ?_, ?_, shape, ?_, ?_, lo, hi, heap, cursor⟩
    · apply PendingSyntax.matching nextMode
      · rw [stateEq]
        change s.was.toNat = _
        rw [was, length]
      · rw [stateEq]
        change s.length.toNat ≤ s.was.toNat
        rw [was]
        exact Nat.le_refl _
      · exact offset
      · rw [stateEq]
        simp only [width]
    · unfold FutureSource
      rw [rest]
      exact suffix.symm
    · rw [stateEq]
    · rw [stateEq]
  · exact Or.inl (DISTEXT_fragment E B (by rw [width]; omega) (by omega) source)

#print axioms lenext_fields
#print axioms distext_fields
#print axioms length_base_extra_budget
#print axioms LENEXT_fragment_progress
#print axioms DISTEXT_fragment_progress
end Zlib.Inflate.Proofs.SlowExtraFragmentProgress
