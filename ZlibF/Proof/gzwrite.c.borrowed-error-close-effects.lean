import ZlibF.Proof.«gzwrite.c.borrowed-error-refusal-entry»

/-! # Complete public close effects on both same error histories

These are instances of the original unchanged CloseEffects, on the actual
reachable heaps of the adjacent regressions. They do not prove the universal
public close goal for other histories or compression branches.
-/
namespace Zlib.Gzwrite.BorrowRegression
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib Zlib.Gzwrite
open ZlibF.Spec.Public

theorem error_close_frame (st : Statics) (hg : LibraryGlobals (callerHeap st)) :
    Frame (writtenHeap st) (finalHeap st) (GzOwned (writtenHeap st) 2 writtenState) := by
  refine ⟨rfl, rfl, rfl, by change 6 ≤ 8; decide, by change 3 ≤ 4; decide, ?_⟩
  intro b hl hn
  rw [written_owned] at hn
  by_cases hb : b < 6
  · have hc : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 := by omega
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
    all_goals exact False.elim (hn (by decide))
  · exact False.elim ((written_valid st hg).2.2.1 b (by change 6 ≤ b; omega) hl)

theorem refusal_error_close_frame (st : Statics) (hg : LibraryGlobals (callerHeap st)) :
    Frame (refusalWrittenHeap st) (refusalFinalHeap st)
      (GzOwned (refusalWrittenHeap st) 2 writtenState) := by
  refine ⟨rfl, rfl, rfl, by change 6 ≤ 6; decide, by change 3 ≤ 4; decide, ?_⟩
  intro b hl hn
  rw [refusal_written_owned] at hn
  by_cases hb : b < 6
  · have hc : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 := by omega
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
    all_goals exact False.elim (hn (by decide))
  · exact False.elim ((refusal_written_valid st hg).2.2.1 b (by change 6 ≤ b; omega) hl)

theorem final_world_valid : FileSystem finalFs := by
  refine ⟨by decide, ?_, ?_, ?_⟩
  · intro path node hm
    simp [finalFs, openedFs] at hm
    obtain ⟨rfl, rfl⟩ := hm
    decide
  · intro i file hi
    by_cases hs : i < 4
    · have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases hc with rfl | rfl | rfl | rfl
      all_goals simp [finalFs, openedFs] at hi
    · have he : finalFs.fds[i]? = none := by
        apply Array.getElem?_eq_none; change 4 ≤ i; omega
      rw [he] at hi
      contradiction
  · intro i node hi
    by_cases hs : i < 1
    · have he : i = 0 := by omega
      subst i
      have hn : node = { data := #[], isDir := false } := by
        simpa [finalFs, openedFs] using hi.symm
      subst node
      decide
    · have he : finalFs.nodes[i]? = none := by
        apply Array.getElem?_eq_none; change 1 ≤ i; omega
      rw [he] at hi
      contradiction

theorem final_other_fds (j : Nat) (hj : j ≠ 3) : finalFs.fds[j]? = openedFs.fds[j]? := by
  by_cases hs : j < 4
  · have hc : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hc with rfl | rfl | rfl <;> rfl
  · have hfin : finalFs.fds[j]? = none := by
      apply Array.getElem?_eq_none; change 4 ≤ j; omega
    have hopen : openedFs.fds[j]? = none := by
      apply Array.getElem?_eq_none; change 4 ≤ j; omega
    rw [hfin, hopen]

theorem opened_descriptor_present : DescriptorPresent openedFs writtenState.fd := by
  exact (entry_and_cleanup Heap.empty.static).2.2.1

private theorem final_world_effects :
    FileSystem finalFs ∧ finalFs.names = openedFs.names ∧ finalFs.fsizeLimit = openedFs.fsizeLimit ∧
    finalFs.fds.size = openedFs.fds.size ∧ finalFs.nodes.size = openedFs.nodes.size ∧
    (∀ j, j ≠ writtenState.fd.toInt.toNat → finalFs.fds[j]? = openedFs.fds[j]?) ∧
    (DescriptorPresent openedFs writtenState.fd → finalFs.fds[writtenState.fd.toInt.toNat]? = some none) ∧
    (¬ DescriptorPresent openedFs writtenState.fd → finalFs.fds = openedFs.fds) ∧
    (∀ file j, openedFs.fds[writtenState.fd.toInt.toNat]? = some (some file) → j ≠ file.node →
      finalFs.nodes[j]? = openedFs.nodes[j]?) ∧
    (writtenState.mode = GZ_READ → finalFs.nodes = openedFs.nodes) := by
  refine ⟨final_world_valid, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact final_other_fds
  · intro _; rfl
  · intro hn; exact False.elim (hn opened_descriptor_present)
  · intro file j _ _; rfl
  · intro _; rfl

/-- Every conjunct of the original public close-effects predicate holds on
this exact actual close, including the original no-new-live requirement. -/
theorem error_close_effects (st : Statics) (hg : LibraryGlobals (callerHeap st)) :
    CloseEffects (writtenHeap st) (finalHeap st) openedFs finalFs 2 writtenState := by
  exact ⟨rfl, error_close_frame st hg, close_live_ledger st hg, final_world_effects⟩

/-- The same original public effects also hold when allocation of the copied
message fails. No external text or owned storage remains live after close. -/
theorem refusal_error_close_effects (st : Statics) (hg : LibraryGlobals (callerHeap st)) :
    CloseEffects (refusalWrittenHeap st) (refusalFinalHeap st) openedFs finalFs 2 writtenState := by
  exact ⟨rfl, refusal_error_close_frame st hg, refusal_close_live_ledger st hg, final_world_effects⟩

#print axioms error_close_effects
#print axioms refusal_error_close_effects
end Zlib.Gzwrite.BorrowRegression
