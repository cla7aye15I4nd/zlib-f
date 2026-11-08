import ZlibF.Proof.«inffast.c.body»
import ZlibF.Proof.«inffast.c.input-frame»

namespace Zlib.Inffast.Proofs
open C Zlib.Inffast
set_option autoImplicit false

/-- A selected literal, linked-table, end, or invalid length code never
executes an input pull. This includes successful BAD exits. -/
theorem dolen_nobase_input_frame
    {c : Ctx} {l result : L} {h after : Heap} {entry : Code}
    (loaded : Ptr.load l.here h = .ok (entry, h))
    (width : entry.bits.toNat ≤ 15)
    (nobase : (entry.op.toUInt32 &&& 16 != 0) = false)
    (run : dolen c l h = .ok (result, after)) :
    result.in_ = l.in_ := by
  let count : UInt32 := entry.bits.toUInt32
  have shift : shr64 l.hold count.toUInt64 h =
      .ok (l.hold >>> count.toUInt64, h) := by
    apply shr64_ok
    rw [UInt32.toNat_toUInt64]
    have countNat : count.toNat = entry.bits.toNat := rfl
    omega
  rw [dolen_eq_len] at run
  rw [bind_ok loaded] at run
  rw [bind_ok shift] at run
  rw [bind_ok loaded] at run
  by_cases literal : (entry.op.toUInt32 == 0) = true
  · simp only [literal, ite_true] at run
    rw [bind_ok loaded] at run
    simp only [bind_app] at run
    cases stored : store8 l.out entry.val.toUInt8 h with
    | error fault => simp only [stored] at run; cases run
    | ok pair =>
      obtain ⟨unit, heap1⟩ := pair
      simp only [stored] at run
      cases moved : Ptr.add l.out 1 heap1 with
      | error fault => simp only [moved] at run; cases run
      | ok pair =>
        obtain ⟨out, heap2⟩ := pair
        simp only [moved, pure_app] at run
        cases run
        rfl
  · simp only [literal, Bool.false_eq_true, ite_false,
      nobase] at run
    by_cases linked : (entry.op.toUInt32 &&& 64 == 0) = true
    · simp only [linked, ite_true] at run
      rw [bind_ok loaded] at run
      simp only [bind_app] at run
      cases added : Ptr.add c.lcode entry.val.toNat h with
      | error fault => simp only [added] at run; cases run
      | ok pair =>
        obtain ⟨basePtr, heap1⟩ := pair
        simp only [added] at run
        cases shifted : shl32 1 entry.op.toUInt32 heap1 with
        | error fault => simp only [shifted] at run; cases run
        | ok pair =>
          obtain ⟨mask, heap2⟩ := pair
          simp only [shifted] at run
          cases added2 : Ptr.add basePtr
              (l.hold >>> count.toUInt64 &&& (mask - 1).toUInt64).toNat heap2 with
          | error fault => simp only [added2] at run; cases run
          | ok pair =>
            obtain ⟨target, heap3⟩ := pair
            simp only [added2, pure_app] at run
            cases run
            rfl
    · simp only [linked, Bool.false_eq_true, ite_false] at run
      by_cases endCode : (entry.op.toUInt32 &&& 32 != 0) = true
      · simp only [endCode, ite_true, bind_app] at run
        cases loadedState : ldInflateState c.state h with
        | error fault => simp only [loadedState] at run; cases run
        | ok pair =>
          obtain ⟨state, heap1⟩ := pair
          simp only [loadedState] at run
          cases storedState : stInflateState c.state { state with mode := TYPE } heap1 with
          | error fault => simp only [storedState] at run; cases run
          | ok pair =>
            obtain ⟨unit, heap2⟩ := pair
            simp only [storedState, pure_app] at run
            cases run
            rfl
      · simp only [endCode, Bool.false_eq_true, ite_false, bind_app] at run
        cases bad : badData c "invalid literal/length code" h with
        | error fault => simp only [bad] at run; cases run
        | ok pair =>
          obtain ⟨unit, heap1⟩ := pair
          simp only [bad, pure_app] at run
          cases run
          rfl

#print axioms dolen_nobase_input_frame
end Zlib.Inffast.Proofs
