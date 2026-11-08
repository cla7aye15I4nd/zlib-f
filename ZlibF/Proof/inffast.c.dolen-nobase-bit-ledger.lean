import ZlibF.Proof.«inffast.c.dolen-nobase-input-frame»
import ZlibF.Proof.«inffast.c.length-bit-ledger»

namespace Zlib.Inffast.Proofs
open C Zlib.Inffast
set_option autoImplicit false

/-- The actual non-base length branches retain precisely the bit subtraction
performed before their branch selection, including both broken exits. -/
theorem dolen_nobase_bits_frame
    {c : Ctx} {l result : L} {h after : Heap} {entry : Code}
    (loaded : Ptr.load l.here h = .ok (entry, h))
    (width : entry.bits.toNat ≤ 15)
    (nobase : (entry.op.toUInt32 &&& 16 != 0) = false)
    (run : dolen c l h = .ok (result, after)) :
    result.bits = l.bits - entry.bits.toUInt32 := by
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


/-- A selected non-base code charges its exact width and no input byte.
The caller obtains availability from its safe table and refill facts. -/
theorem dolen_nobase_input_bit_ledger
    {c : Ctx} {l result : L} {h after : Heap} {entry : Code}
    (loaded : Ptr.load l.here h = .ok (entry, h))
    (width : entry.bits.toNat ≤ 15)
    (available : entry.bits.toNat ≤ l.bits.toNat)
    (nobase : (entry.op.toUInt32 &&& 16 != 0) = false)
    (run : dolen c l h = .ok (result, after)) :
    result.in_ = l.in_ ∧
      result.bits.toNat + entry.bits.toNat = l.bits.toNat := by
  refine ⟨dolen_nobase_input_frame loaded width nobase run, ?_⟩
  rw [dolen_nobase_bits_frame loaded width nobase run]
  have cast : entry.bits.toUInt32.toNat = entry.bits.toNat := rfl
  rw [u32_toNat_sub (by rw [cast]; exact available), cast]
  omega

/-- Two actual linked-table passes retain their starting input cursor and
spend the two selected widths, including literal, end and invalid leaves. -/
theorem dolen_two_nobase_input_bit_ledger
    {c : Ctx} {l middle result : L} {h after : Heap}
    {root leaf : Code}
    (rootLoad : Ptr.load l.here h = .ok (root, h))
    (rootWidth : root.bits.toNat ≤ 15)
    (rootAvailable : root.bits.toNat ≤ l.bits.toNat)
    (rootNonbase : (root.op.toUInt32 &&& 16 != 0) = false)
    (firstRun : dolen c l h = .ok (middle, h))
    (leafLoad : Ptr.load middle.here h = .ok (leaf, h))
    (leafWidth : leaf.bits.toNat ≤ 15)
    (leafAvailable : leaf.bits.toNat ≤ middle.bits.toNat)
    (leafNonbase : (leaf.op.toUInt32 &&& 16 != 0) = false)
    (secondRun : dolen c middle h = .ok (result, after)) :
    result.in_ = l.in_ ∧
      result.bits.toNat + root.bits.toNat + leaf.bits.toNat = l.bits.toNat := by
  have first := dolen_nobase_input_bit_ledger
    rootLoad rootWidth rootAvailable rootNonbase firstRun
  have second := dolen_nobase_input_bit_ledger
    leafLoad leafWidth leafAvailable leafNonbase secondRun
  exact ⟨second.1.trans first.1, by omega⟩

/-- A terminal one-pass length loop has exactly the same source ledger
as its actual body call. This includes end-of-block and invalid codes. -/
theorem dolen_one_pass_nobase_input_bit_ledger
    {c : Ctx} {l first result : L} {h after : Heap} {entry : Code}
    (loaded : Ptr.load l.here h = .ok (entry, h))
    (width : entry.bits.toNat ≤ 15)
    (available : entry.bits.toNat ≤ l.bits.toNat)
    (nobase : (entry.op.toUInt32 &&& 16 != 0) = false)
    (firstRun : dolen c l h = .ok (first, after))
    (noAgain : first.againL = false)
    (loopRun : cdoWhile (dolen c)
      (fun current => pure (current.againL, current)) l h =
        .ok (result, after)) :
    result.in_ = l.in_ ∧
      result.bits.toNat + entry.bits.toNat = l.bits.toNat := by
  have same := dolen_one_pass_result firstRun noAgain loopRun
  rw [same]
  exact dolen_nobase_input_bit_ledger loaded width available nobase firstRun

#print axioms dolen_one_pass_nobase_input_bit_ledger

#print axioms dolen_nobase_bits_frame
#print axioms dolen_nobase_input_bit_ledger
#print axioms dolen_two_nobase_input_bit_ledger
end Zlib.Inffast.Proofs
