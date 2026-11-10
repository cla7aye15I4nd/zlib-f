import Std
namespace ZlibF.Math.CovfHistogram
set_option autoImplicit false

/-- Complete level histograms with exactly `left` leaves from `slots`
current level nodes. A finished tree has no trailing zero levels. -/
inductive Complete : Nat → Nat → List Nat → Prop where
  | nil : Complete 0 0 []
  | cons {slots left c : Nat} {tail : List Nat}
      (positive : 0 < slots) (fit : c ≤ slots) (room : c ≤ left)
      (next : Complete (2*(slots-c)) (left-c) tail) : Complete slots left (c::tail)

/-- Exhaustive transparent finite level enumeration. Fuel bounds height;
the complete-height theorem below derives sufficient fuel from leaf count. -/
def enumerate (slots left : Nat) : Nat → List (List Nat)
  | 0 => if slots = 0 ∧ left = 0 then [[]] else []
  | fuel+1 => if slots = 0 then (if left = 0 then [[]] else []) else
      (List.range (min slots left+1)).flatMap (fun c =>
        (enumerate (2*(slots-c)) (left-c) fuel).map (c::·))

theorem Complete.zero {left : Nat} {h : List Nat} (complete : Complete 0 left h) :
    left = 0 ∧ h = [] := by
  cases complete with
  | nil => exact ⟨rfl,rfl⟩
  | cons positive => omega

/-- A complete histogram needs at least as many leaves as current slots.
Its nonzero level count is at most `left-slots+1`. No extra height assumption
is imposed by the certificate enumeration. -/
theorem Complete.capacity_height {slots left : Nat} {h : List Nat}
    (complete : Complete slots left h) :
    slots ≤ left ∧ (0 < slots → h.length+slots ≤ left+1) := by
  induction complete with
  | nil => simp
  | @cons slots left c tail positive fit room next ih =>
    refine ⟨by omega,?_⟩
    intro _
    by_cases zero : 2*(slots-c) = 0
    · have finished : Complete 0 (left-c) tail := by simpa only [zero] using next
      obtain ⟨endLeaves,endLevels⟩ := finished.zero
      subst tail
      simp only [List.length_cons,List.length_nil]
      omega
    · have height := ih.2 (by omega)
      simp only [List.length_cons]
      omega

/-- Every complete histogram whose level count fits the fuel occurs in
the exact executable enumerator. -/
theorem Complete.mem_enumerate {slots left fuel : Nat} {h : List Nat}
    (complete : Complete slots left h) (height : h.length ≤ fuel) :
    h ∈ enumerate slots left fuel := by
  induction complete generalizing fuel with
  | nil => cases fuel <;> simp [enumerate]
  | @cons slots left c tail positive fit room next ih =>
    cases fuel with
    | zero => simp only [List.length_cons] at height; omega
    | succ fuel =>
      have member := ih (fuel := fuel) (by simpa only [List.length_cons] using Nat.le_of_succ_le_succ height)
      simp only [enumerate,show ¬slots=0 by omega,ite_false]
      apply List.mem_flatMap.mpr
      refine ⟨c,List.mem_range.mpr (by omega),?_⟩
      exact List.mem_map.mpr ⟨tail,member,rfl⟩

/-- Every enumerated result is a complete histogram; no incomplete tree
or extra trailing level is admitted. -/
theorem enumerate_complete (slots left fuel : Nat) :
    ∀ h ∈ enumerate slots left fuel, Complete slots left h := by
  induction fuel generalizing slots left with
  | zero =>
    intro h member
    simp only [enumerate] at member
    split at member
    · rename_i ended
      obtain ⟨rfl,rfl⟩ := ended
      simp only [List.mem_singleton] at member
      subst h
      exact Complete.nil
    · simp at member
  | succ fuel ih =>
    intro h member
    simp only [enumerate] at member
    split at member
    · rename_i zero
      subst slots
      split at member
      · rename_i endLeaves
        subst left
        simp only [List.mem_singleton] at member
        subst h
        exact Complete.nil
      · simp at member
    · rename_i positive
      obtain ⟨c,bound,mappedMember⟩ := List.mem_flatMap.mp member
      obtain ⟨tail,leafMember,equal⟩ := List.mem_map.mp mappedMember
      subst h
      have range := List.mem_range.mp bound
      exact Complete.cons (by omega) (by omega) (by omega) (ih _ _ _ leafMember)

/-- Finite enumeration with `s-1` levels covers every complete full binary
root histogram with `s` leaves, in both directions. An actual-tree producer
still has to establish this Complete relation for its raw histogram. -/
theorem root_histogram_coverage (s : Nat) (h : List Nat) :
    Complete 2 s h ↔ h ∈ enumerate 2 s (s-1) := by
  constructor
  · intro complete
    have height := complete.capacity_height.2 (by decide)
    exact complete.mem_enumerate (by omega)
  · exact enumerate_complete 2 s (s-1) h

/-- The first certificate's histogram is genuinely complete and overflows
maximum seven. This checks the exact full-tree level recurrence. -/
theorem first_histogram_complete : Complete 2 9 [1,1,1,1,1,1,1,2] := by
  repeat first
    | exact Complete.nil
    | apply Complete.cons <;> try decide

#print axioms Complete.zero
#print axioms Complete.capacity_height
#print axioms Complete.mem_enumerate
#print axioms enumerate_complete
#print axioms root_histogram_coverage
#print axioms first_histogram_complete
end ZlibF.Math.CovfHistogram
