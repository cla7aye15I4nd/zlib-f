import ZlibF.Proof.«inflate.c.default-foundation»
import ZlibF.Proof.«inflate.c.check-dispatch»
import ZlibF.Proof.«inflate.c.lenlens-table-safe»
import ZlibF.Proof.«inflate.c.validate-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Validation leaves raw recovery raw for every signed check argument. -/
theorem validateState_raw_wrap {s : InflateState} (wrap : s.wrap = 0) (check : Int32) :
    (validateState check s).wrap = 0 := by
  simp [validateState, wrap]

/-- A legal validation toggle preserves every clause of the default J,
including the raw state produced by recovery. The actual translated call
is executed, rather than admitted as a history-contract assumption. -/
theorem inflateValidate_default_J {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (invariant : DefaultDecodeJ h r zs z s) (check : Int32) :
    ∃ after state, C.run (inflateValidate (some r) check) h = .ok (Z_OK, after) ∧
      after = setI h zs state ∧ state = validateState check s ∧ DefaultDecodeJ after r zs z state := by
  obtain ⟨after, run, heap, current, _⟩ := inflateValidate_safe invariant.good check
  subst after
  let state := validateState check s
  have tables : DataTableInvariant (setI h zs state) state := by
    intro active
    have original := invariant.tables active
    constructor
    · obtain ⟨ref, off, array, ptr, get, safe⟩ := original.lengthTable
      exact ⟨ref, off, array, ptr, by rw [validate_code_views invariant.good.live.hs]; exact get, safe⟩
    · obtain ⟨ref, off, array, ptr, get, safe⟩ := original.distanceTable
      exact ⟨ref, off, array, ptr, by rw [validate_code_views invariant.good.live.hs]; exact get, safe⟩
  have wrapper : state.wrap = 0 ∨ state.wrap = 1 ∨ state.wrap = 5 := by
    rcases invariant.wrapper with raw | wrapped
    · exact Or.inl (validateState_raw_wrap raw check)
    · exact Or.inr (validateState_zlib_wrap wrapped check)
  refine ⟨setI h zs state, state, run, rfl, rfl, ⟨current, tables,
    ⟨invariant.pending.sane, invariant.pending.lenext, invariant.pending.dist,
      invariant.pending.distext, invariant.pending.matching⟩,
    invariant.lengths, invariant.headerLengths, invariant.held, ?_, wrapper,
    invariant.header, invariant.modes, ?_, invariant.globals, invariant.platform.with_istates _⟩⟩
  · rcases invariant.window with range | ⟨zero, null, unread, nonraw⟩
    · exact Or.inl range
    · refine Or.inr ⟨zero, null, unread, ?_⟩
      rcases invariant.wrapper with raw | zlib
      · exact absurd raw nonraw
      · rcases validateState_zlib_wrap zlib check with e | e <;> rw [e] <;> decide
  intro trailer
  rcases invariant.trailer trailer with raw | flags
  · exact Or.inl (validateState_raw_wrap raw check)
  · exact Or.inr flags

end Zlib.Inflate.Proofs
