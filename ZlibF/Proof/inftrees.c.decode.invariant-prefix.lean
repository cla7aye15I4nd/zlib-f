import ZlibF.Proof.«inftrees.c.decode.short»
import ZlibF.Proof.«inftrees.c.decode.frame»
import ZlibF.Spec.InflateDecodeTableInvariant

set_option autoImplicit false

namespace Zlib.Inftrees.Proofs
open C Zlib.Inftrees Zlib.Inftrees.Spec ZlibF.Spec Zlib.Inffast.Spec
open Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeTableInvariant

theorem query_link_fields {type : UInt32} (entry : Code)
    (kind : type = LENS ∨ type = DISTS) (active : Subtable.IsLink type entry = true) :
    (type = LENS ∧ LenLink entry) ∨ (type = DISTS ∧ DistLink entry) := by
  rcases kind with type | type
  · simp only [Subtable.IsLink, type, ite_true, Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at active
    exact Or.inl ⟨type, active.1, ZlibF.Math.InflateLookup.high_zero_flags entry.op active.2⟩
  · simp only [Subtable.IsLink, type, show DISTS ≠ LENS by decide, ite_false, beq_iff_eq] at active
    exact Or.inr ⟨type, ZlibF.Math.InflateLookup.high_zero_flags entry.op active⟩

/-- An unchanged returned table extent retains its exact independent
meaning even when a later builder changes or grows the backing array. -/
theorem decode_table_invariant_of_prefix : DecodeTableInvariant.Goal.decode_table_invariant_of_prefix := by
  intro type before after offset root used lens invariant size cells
  have rootEnd := invariant.readExtent.2.2.1
  have rootCell : ∀ i, i < 2 ^ root → after[offset + i]? = before[offset + i]? := by
    intro i inside
    exact cells _ (by omega) (by omega)
  have query := decode_table_read_preserved type before after offset root used
    invariant.tableType invariant.readExtent cells
  have preservedExtent : TableReadExtent type after offset root used := by
    refine ⟨invariant.readExtent.1, invariant.readExtent.2.1, rootEnd, ?_⟩
    intro i inside
    have same : after.getD (offset + i) default = before.getD (offset + i) default := by
      simp only [Array.getD_eq_getD_getElem?]
      rw [rootCell i inside]
    rw [same]
    exact invariant.readExtent.2.2.2 i inside
  refine ⟨invariant.tableType, ?_, ?_, preservedExtent,
    invariant.acceptable, ?_, ?_⟩
  · obtain ⟨lo, hi, bound, entries⟩ := invariant.rootTable
    refine ⟨lo, hi, Nat.le_trans bound (by omega), ?_⟩
    intro i inside
    obtain ⟨entry, get, positive, fits⟩ := entries i inside
    exact ⟨entry, (rootCell i inside).trans get, positive, fits⟩
  · intro i entry inside get link
    have original : before[offset + i]? = some entry := (rootCell i inside).symm.trans get
    obtain ⟨bits, safe⟩ := invariant.subtables i entry inside original link
    obtain ⟨positive, opPositive, bitBound, capacity, entries⟩ := safe
    have getD : before.getD (offset + i) default = entry := by
      simp only [Array.getD_eq_getD_getElem?, original, Option.getD_some]
    have extent := invariant.readExtent.2.2.2 i inside
    rw [getD] at extent
    have finish := extent (query_link_fields entry invariant.tableType link)
    refine ⟨bits, positive, opPositive, bitBound, Nat.le_trans capacity size, ?_⟩
    intro j bound
    obtain ⟨leaf, getLeaf, leafPositive, leafBound⟩ := entries j bound
    exact ⟨leaf, (cells _ (by omega) (by omega)).trans getLeaf, leafPositive, leafBound⟩
  · intro inp entry consumed actual fits accepted
    rw [query] at actual
    exact invariant.short inp entry consumed actual fits accepted
  · intro inp enough
    obtain ⟨entry, consumed, actual, classification⟩ := invariant.classify inp enough
    exact ⟨entry, consumed, by rw [query]; exact actual, classification⟩

#print axioms decode_table_invariant_of_prefix

end Zlib.Inftrees.Proofs
