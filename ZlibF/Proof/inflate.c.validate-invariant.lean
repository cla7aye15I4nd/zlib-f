import ZlibF.Proof.«inflate.c.header-default»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Validation toggles the checking bit without changing a zlib wrapper
into a raw or gzip wrapper. Both actual default-history values are kept. -/
theorem validateState_zlib_wrap {s : InflateState} (wrap : s.wrap = 1 ∨ s.wrap = 5) (check : Int32) :
    (validateState check s).wrap = 1 ∨ (validateState check s).wrap = 5 := by
  rcases wrap with wrap | wrap <;> by_cases zero : check = 0
  all_goals simp [validateState, wrap, zero]
  all_goals decide

/-- Toggling validation retains every actual code-array view. -/
theorem validate_code_views {h : Heap} {zs : Nat} {s : InflateState}
    (get : h.istates zs = some s) (check : Int32) (ref : CodeRef) :
    (Space.get (setI h zs (validateState check s)) ref : Option (Array Code)) = Space.get h ref := by
  cases ref with
  | istate_codes i =>
    by_cases same : i = zs
    · subst i
      simp only [Space.get, setI_istates_same, get, Option.map_some]
      rfl
    · simp [Space.get, setI, upd_ne _ _ _ _ same]
  | st_lenfix => rfl
  | st_distfix => rfl

/-- The real validation operation preserves the current safety clauses and
the zlib-only wrapper alternatives needed by the complete header proof.
This discharges this legal history transition without assuming its contract. -/
theorem inflateValidate_zlib_clauses {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (good : Good h r zs z s)
    (tables : DataTableInvariant h s) (lengths : CodeLengthInvariant zs s)
    (pending : DataPendingInvariant s) (wrap : s.wrap = 1 ∨ s.wrap = 5) (check : Int32) :
    ∃ after state,
      C.run (inflateValidate (some r) check) h = .ok (Z_OK, after) ∧
      after = setI h zs state ∧ state = validateState check s ∧ Good after r zs z state ∧
      DataTableInvariant after state ∧ CodeLengthInvariant zs state ∧ DataPendingInvariant state ∧
      (state.wrap = 1 ∨ state.wrap = 5) ∧ state.wbits = s.wbits ∧ state.head = s.head ∧
      state.hold = s.hold ∧ state.bits = s.bits ∧ after.static = h.static := by
  obtain ⟨after, run, heap, current, _⟩ := inflateValidate_safe good check
  subst after
  refine ⟨setI h zs (validateState check s), validateState check s, run, rfl, rfl, current,
    ?_, lengths, ?_, validateState_zlib_wrap wrap check, rfl, rfl, rfl, rfl, rfl⟩
  · intro active
    have original := tables active
    constructor
    · obtain ⟨ref, off, array, ptr, get, safe⟩ := original.lengthTable
      exact ⟨ref, off, array, ptr, by rw [validate_code_views good.live.hs]; exact get, safe⟩
    · obtain ⟨ref, off, array, ptr, get, safe⟩ := original.distanceTable
      exact ⟨ref, off, array, ptr, by rw [validate_code_views good.live.hs]; exact get, safe⟩
  · exact ⟨pending.sane, pending.lenext, pending.dist, pending.distext, pending.matching⟩

end Zlib.Inflate.Proofs
