import ZlibF.Proof.«inffast.c.dist-two-pull-ledger»
import ZlibF.Proof.«inffast.c.again-d»

namespace Zlib.Inffast.Proofs
open C Zlib.Inffast Zlib.Inflate.Proofs
set_option autoImplicit false

/-- A safe selected distance-base entry charges its code and optional two-byte extra refill on the actual translated call. -/
theorem dodist_base_two_pull_bit_ledger
    {c : Ctx} {l result : L} {h after : Heap}
    {entry : Code}
    (loaded : Ptr.load l.here h = .ok (entry, h))
    (codeWidth : entry.bits.toNat ≤ 15)
    (held : entry.bits.toNat ≤ l.bits.toNat)
    (base : (entry.op.toUInt32 &&& 16 != 0) = true)
    (extra : (entry.op.toUInt32 &&& 15).toNat ≤ 13)
    (run : dodist c l h = .ok (result, after)) :
    ∃ pulled, pulled ≤ 2 ∧
      result.in_ = Zlib.Inflate.Proofs.inputAdvance l.in_ pulled ∧
      result.bits.toNat + entry.bits.toNat +
        (entry.op.toUInt32 &&& 15).toNat =
        l.bits.toNat + 8 * pulled := by
  let count : UInt32 := entry.bits.toUInt32
  let firstLocal : L := { l with againD := false, op := count }
  let afterCode : L := { firstLocal with
    hold := firstLocal.hold >>> count.toUInt64,
    bits := firstLocal.bits - count }
  let baseLocal : L := { afterCode with
    op := entry.op.toUInt32 &&& 15,
    dist := entry.val.toUInt32 }
  have countNat : count.toNat = entry.bits.toNat := rfl
  have countFits : count.toNat ≤ l.bits.toNat := by
    omega
  have countSmall : count.toNat < 64 := by
    omega
  have shift : shr64 l.hold count.toUInt64 h =
      .ok (l.hold >>> count.toUInt64, h) := by
    apply shr64_ok
    rw [UInt32.toNat_toUInt64]
    exact countSmall
  have runBase : dodistBase c baseLocal h = .ok (result, after) := by
    rw [dodist_eq_base] at run
    rw [bind_ok loaded] at run
    rw [bind_ok shift] at run
    rw [bind_ok loaded] at run
    simp only [base, ite_true] at run
    rw [bind_ok loaded] at run
    simpa only [baseLocal, afterCode, firstLocal, count] using run
  have bitsAfter : afterCode.bits.toNat + count.toNat = l.bits.toNat := by
    simp only [afterCode, firstLocal]
    rw [u32_toNat_sub countFits]
    omega
  obtain ⟨pulled, limit, cursor, ledger⟩ :=
    dodistBase_two_pull_bit_ledger c baseLocal
      (by simpa only [baseLocal] using extra)
      h result after runBase
  refine ⟨pulled, limit, ?_, ?_⟩
  · simpa only [baseLocal, afterCode, firstLocal] using cursor
  · simp only [baseLocal] at ledger
    omega


#print axioms dodist_base_two_pull_bit_ledger

/-- A selected link or invalid distance entry consumes only its own code bits.
Its actual translated branch does not pull input, including bad-data exits. -/
theorem dodist_nonbase_bit_ledger
    {c : Ctx} {l result : L} {h after : Heap} {entry : Code}
    (loaded : Ptr.load l.here h = .ok (entry, h))
    (held : entry.bits.toNat ≤ l.bits.toNat)
    (width : entry.bits.toNat ≤ 15)
    (nonbase : (entry.op.toUInt32 &&& 16 != 0) = false)
    (run : dodist c l h = .ok (result, after)) :
    result.in_ = l.in_ ∧
      result.bits.toNat + entry.bits.toNat = l.bits.toNat := by
  let count : UInt32 := entry.bits.toUInt32
  have countNat : count.toNat = entry.bits.toNat := rfl
  have shift : shr64 l.hold count.toUInt64 h =
      .ok (l.hold >>> count.toUInt64, h) := by
    apply shr64_ok
    rw [UInt32.toNat_toUInt64]
    omega
  rw [dodist_eq_base] at run
  rw [bind_ok loaded] at run
  rw [bind_ok shift] at run
  rw [bind_ok loaded] at run
  simp only [nonbase, Bool.false_eq_true, ite_false] at run
  have bitsAfter : (l.bits - count).toNat + count.toNat = l.bits.toNat := by
    rw [u32_toNat_sub (by omega : count.toNat ≤ l.bits.toNat)]
    omega
  by_cases linked : (entry.op.toUInt32 &&& 64 == 0) = true
  · simp only [linked, ite_true] at run
    rw [bind_ok loaded] at run
    simp only [bind_app] at run
    cases basePtr : Ptr.add c.dcode entry.val.toNat h with
    | error fault => simp only [basePtr] at run; cases run
    | ok pair =>
      obtain ⟨p, heap1⟩ := pair
      simp only [basePtr] at run
      cases mask : shl32 1 entry.op.toUInt32 heap1 with
      | error fault => simp only [mask] at run; cases run
      | ok pair =>
        obtain ⟨m, heap2⟩ := pair
        simp only [mask] at run
        cases target : Ptr.add p ((l.hold >>> count.toUInt64) &&& (m - 1).toUInt64).toNat heap2 with
        | error fault => simp only [target] at run; cases run
        | ok pair =>
          obtain ⟨pointer, heap3⟩ := pair
          simp only [target, pure_app] at run
          cases run
          exact ⟨rfl, by simpa only [countNat] using bitsAfter⟩
  · simp only [linked, Bool.false_eq_true, ite_false, bind_app] at run
    cases bad : badData c "invalid distance code" h with
    | error fault => simp only [bad] at run; cases run
    | ok pair =>
      obtain ⟨ignoredUnit, heap1⟩ := pair
      simp only [bad, pure_app] at run
      cases run
      exact ⟨rfl, by simpa only [countNat] using bitsAfter⟩

#print axioms dodist_nonbase_bit_ledger

/-- One actual selected distance-table step has a single cursor count and
an exact bit charge. The base branch may read two bytes; the link and invalid
branches read none. -/
theorem dodist_selected_bit_ledger
    {c : Ctx} {l result : L} {h after : Heap} {entry : Code}
    (loaded : Ptr.load l.here h = .ok (entry, h))
    (held : entry.bits.toNat ≤ l.bits.toNat)
    (width : entry.bits.toNat ≤ 15)
    (extra : (entry.op.toUInt32 &&& 15).toNat ≤ 13)
    (run : dodist c l h = .ok (result, after)) :
    ∃ pulled, pulled ≤ 2 ∧
      result.in_ = inputAdvance l.in_ pulled ∧
      ((entry.op.toUInt32 &&& 16 != 0) = true ∧
        result.bits.toNat + entry.bits.toNat +
          (entry.op.toUInt32 &&& 15).toNat =
          l.bits.toNat + 8 * pulled ∨
       (entry.op.toUInt32 &&& 16 != 0) = false ∧
        result.bits.toNat + entry.bits.toNat = l.bits.toNat) := by
  by_cases base : (entry.op.toUInt32 &&& 16 != 0) = true
  · obtain ⟨pulled, bound, cursor, bits⟩ :=
      dodist_base_two_pull_bit_ledger loaded width held base extra run
    exact ⟨pulled, bound, cursor, Or.inl ⟨base, bits⟩⟩
  · have nonbase : (entry.op.toUInt32 &&& 16 != 0) = false := by
      cases flag : (entry.op.toUInt32 &&& 16 != 0)
      · rfl
      · exact False.elim (base flag)
    obtain ⟨cursor, bits⟩ :=
      dodist_nonbase_bit_ledger loaded held width nonbase run
    exact ⟨0, by omega,
      by simpa only [inputAdvance_zero] using cursor,
      Or.inr ⟨nonbase, bits⟩⟩

#print axioms dodist_selected_bit_ledger

/-- A safe distance leaf spends its code bits and, for a base entry, at
most thirteen extra bits. The cursor and bit bound share one pull count. -/
theorem dodist_leaf_bit_budget
    {c : Ctx} {l result : L} {h after : Heap} {entry : Code}
    {dropped : Nat}
    (loaded : Ptr.load l.here h = .ok (entry, h))
    (held : entry.bits.toNat ≤ l.bits.toNat)
    (leaf : Zlib.Inffast.Spec.DistLeaf dropped entry)
    (run : dodist c l h = .ok (result, after)) :
    ∃ pulled, pulled ≤ 2 ∧
      result.in_ = inputAdvance l.in_ pulled ∧
      result.bits.toNat ≤ l.bits.toNat + 8 * pulled := by
  have width : entry.bits.toNat ≤ 15 := by omega
  rcases leaf.2 with base | invalid
  · have baseBool : (entry.op.toUInt32 &&& 16 != 0) = true := by
      rw [mask16]
      simp [base.1]
    have extra : (entry.op.toUInt32 &&& 15).toNat ≤ 13 := by
      rw [mask15]
      exact base.2.1
    obtain ⟨pulled, bound, cursor, bits⟩ :=
      dodist_base_two_pull_bit_ledger loaded width held baseBool extra run
    exact ⟨pulled, bound, cursor, by omega⟩
  · have nonbase : (entry.op.toUInt32 &&& 16 != 0) = false := by
      rw [mask16]
      simp [invalid.1]
    obtain ⟨cursor, bits⟩ :=
      dodist_nonbase_bit_ledger loaded held width nonbase run
    exact ⟨0, by omega,
      by simpa only [inputAdvance_zero] using cursor,
      by omega⟩

#print axioms dodist_leaf_bit_budget
end Zlib.Inffast.Proofs
