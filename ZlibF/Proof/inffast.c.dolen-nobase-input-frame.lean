import ZlibF.Proof.«inffast.c.body»
import ZlibF.Proof.«inffast.c.input-frame»
import ZlibF.Proof.«inffast.c.dolen-input-frame»

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
      obtain ⟨ignoredUnit, heap1⟩ := pair
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
            obtain ⟨ignoredUnit, heap2⟩ := pair
            simp only [storedState, pure_app] at run
            cases run
            rfl
      · simp only [endCode, Bool.false_eq_true, ite_false, bind_app] at run
        cases bad : badData c "invalid literal/length code" h with
        | error fault => simp only [bad] at run; cases run
        | ok pair =>
          obtain ⟨ignoredUnit, heap1⟩ := pair
          simp only [bad, pure_app] at run
          cases run
          rfl

#print axioms dolen_nobase_input_frame

theorem dolen_two_pass_nobase_input_frame
    {c : Ctx} {l linked result : L} {h after : Heap} {entry : Code}
    (firstRun : dolen c l h = .ok (linked, h))
    (again : linked.againL = true)
    (loaded : Ptr.load linked.here h = .ok (entry, h))
    (width : entry.bits.toNat ≤ 15)
    (nobase : (entry.op.toUInt32 &&& 16 != 0) = false)
    (secondRun : dolen c linked h = .ok (result, after)) :
    result.in_ = l.in_ := by
  have first := dolen_continue_cursor c l h linked h firstRun again
  have second := dolen_nobase_input_frame loaded width nobase secondRun
  exact second.trans first

#print axioms dolen_two_pass_nobase_input_frame

/-- The one-pass loop result is the result of its actual first body call. -/
theorem dolen_one_pass_result
    {c : Ctx} {l first result : L} {h after : Heap}
    (firstRun : dolen c l h = .ok (first, after))
    (noAgain : first.againL = false)
    (loopRun : cdoWhile (dolen c)
      (fun current => pure (current.againL, current)) l h =
        .ok (result, after)) :
    result = first := by
  have equal : cdoWhile (dolen c)
      (fun current => pure (current.againL, current)) l h =
        .ok (first, after) := by
    apply cdoWhile_one firstRun
    simp [noAgain]
  rw [equal] at loopRun
  cases loopRun
  rfl

#print axioms dolen_one_pass_result

theorem dolen_one_pass_nobase_input_frame
    {c : Ctx} {l first result : L} {h after : Heap} {entry : Code}
    (loaded : Ptr.load l.here h = .ok (entry, h))
    (width : entry.bits.toNat ≤ 15)
    (nobase : (entry.op.toUInt32 &&& 16 != 0) = false)
    (firstRun : dolen c l h = .ok (first, after))
    (noAgain : first.againL = false)
    (loopRun : cdoWhile (dolen c)
      (fun current => pure (current.againL, current)) l h =
        .ok (result, after)) :
    result.in_ = l.in_ := by
  have same := dolen_one_pass_result firstRun noAgain loopRun
  rw [same]
  exact dolen_nobase_input_frame loaded width nobase firstRun

#print axioms dolen_one_pass_nobase_input_frame

theorem success_value_unique {α : Type} {program : M α}
    {h firstAfter secondAfter : Heap} {first second : α}
    (firstRun : program h = .ok (first, firstAfter))
    (secondRun : program h = .ok (second, secondAfter)) :
    first = second := by
  have pair : (first, firstAfter) = (second, secondAfter) := by
    simpa only [Except.ok.injEq] using firstRun.symm.trans secondRun
  exact congrArg Prod.fst pair

#print axioms success_value_unique
end Zlib.Inffast.Proofs
