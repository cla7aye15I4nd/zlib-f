import Std
namespace ZlibF.Math.CovfSorting
set_option autoImplicit false

/-- Natural weighted cost with zero-based rank weights. -/
def weighted (w : Nat → Nat) : List Nat → Nat
  | [] => 0
  | x::xs => w 0*x+weighted (fun i => w (i+1)) xs

/-- Only the weights used by this list are required to be descending. -/
def Descending (w : Nat → Nat) (n : Nat) : Prop :=
  ∀ i, i+1<n → w (i+1) ≤ w i

def insert (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y::ys => if x≤y then x::y::ys else y::insert x ys

def sort : List Nat → List Nat
  | [] => []
  | x::xs => insert x (sort xs)

/-- Moving the smaller depth to the larger weight lowers the cost. -/
theorem exchange (a b x y : Nat) (weights : b≤a) (depths : y≤x) :
    a*y+b*x ≤ a*x+b*y := by
  obtain ⟨da,rfl⟩ := Nat.exists_eq_add_of_le weights
  obtain ⟨dx,rfl⟩ := Nat.exists_eq_add_of_le depths
  simp only [Nat.add_mul,Nat.mul_add]
  omega

theorem insert_perm (x : Nat) (ys : List Nat) : (insert x ys).Perm (x::ys) := by
  induction ys with
  | nil => exact List.Perm.refl _
  | cons y ys ih =>
    simp only [insert]
    split
    · exact List.Perm.refl _
    · exact (ih.cons y).trans (List.Perm.swap x y ys)

theorem sort_perm (xs : List Nat) : (sort xs).Perm xs := by
  induction xs with
  | nil => exact List.Perm.refl _
  | cons x xs ih => exact (insert_perm x (sort xs)).trans (ih.cons x)

theorem insert_sorted (x : Nat) {ys : List Nat} (sorted : ys.Pairwise (·≤·)) :
    (insert x ys).Pairwise (·≤·) := by
  induction ys with
  | nil => simp [insert]
  | cons y ys ih =>
    obtain ⟨head,tail⟩ := List.pairwise_cons.mp sorted
    by_cases before : x≤y
    · simp only [insert,ite_eq_left before,List.pairwise_cons]
      refine ⟨?_,head,tail⟩
      intro z member
      rcases List.mem_cons.mp member with same | member
      · subst z; exact before
      · exact Nat.le_trans before (head z member)
    · rw [insert,ite_eq_right before,List.pairwise_cons]
      refine ⟨?_,ih tail⟩
      intro z member
      have original := (insert_perm x ys).mem_iff.mp member
      rcases List.mem_cons.mp original with same | member
      · subst z; omega
      · exact head z member

theorem sort_sorted (xs : List Nat) : (sort xs).Pairwise (·≤·) := by
  induction xs with
  | nil => simp [sort]
  | cons x xs ih => exact insert_sorted x ih

/-- The insertion passes can only exchange inverted adjacent depths; no
positivity premise on depths and no weight beyond the list are needed. -/
theorem insert_weighted_le (x : Nat) (ys : List Nat) (w : Nat → Nat)
    (descending : Descending w (ys.length+1)) :
    weighted w (insert x ys) ≤ weighted w (x::ys) := by
  induction ys generalizing w with
  | nil => exact Nat.le_refl _
  | cons y ys ih =>
    by_cases before : x≤y
    · simp only [insert,ite_eq_left before]
      exact Nat.le_refl _
    · have shifted : Descending (fun i => w (i+1)) (ys.length+1) := by
        intro i fit
        exact descending (i+1) (by simp only [List.length_cons]; omega)
      have next := ih (fun i => w (i+1)) shifted
      have order : w 1≤w 0 := descending 0 (by simp only [List.length_cons]; omega)
      have swapped := exchange (w 0) (w 1) x y order (by omega)
      simp only [insert,ite_eq_right before,weighted]
      change w 0*y+weighted (fun i => w (i+1)) (insert x ys) ≤
        w 0*x+(w 1*y+weighted (fun i => w (i+1+1)) ys)
      change weighted (fun i => w (i+1)) (insert x ys) ≤
        w 1*x+weighted (fun i => w (i+1+1)) ys at next
      omega

/-- Ascending insertion sort minimizes weighted cost for descending
weights. Every sorting operation is a proved cost-decreasing exchange. -/
theorem sort_weighted_le (xs : List Nat) (w : Nat → Nat)
    (descending : Descending w xs.length) : weighted w (sort xs) ≤ weighted w xs := by
  induction xs generalizing w with
  | nil => exact Nat.le_refl _
  | cons x xs ih =>
    have shifted : Descending (fun i => w (i+1)) xs.length := by
      intro i fit
      exact descending (i+1) (by simp only [List.length_cons]; omega)
    have tail := ih (fun i => w (i+1)) shifted
    have length := (sort_perm xs).length_eq
    have first := insert_weighted_le x (sort xs) w (by rw [length]; exact descending)
    exact Nat.le_trans first (Nat.add_le_add_left tail (w 0*x))

/-- An arbitrary ascending permutation is the same sorted depth multiset,
so the theorem does not bind callers to this sorting implementation. -/
theorem sorted_permutation_weighted_le {xs ys : List Nat}
    (sorted : ys.Pairwise (·≤·)) (permutation : ys.Perm xs) (w : Nat → Nat)
    (descending : Descending w xs.length) : weighted w ys ≤ weighted w xs := by
  have same : ys=sort xs :=
    List.Perm.eq_of_pairwise (fun a b _ _ ab ba => Nat.le_antisymm ab ba)
      sorted (sort_sorted xs) (permutation.trans (sort_perm xs).symm)
  rw [same]
  exact sort_weighted_le xs w descending

/-- Sorting preserves exact total mass as well as every multiplicity. -/
theorem sort_mass (xs : List Nat) : (sort xs).sum=xs.sum := (sort_perm xs).sum_nat

#print axioms exchange
#print axioms insert_perm
#print axioms sort_perm
#print axioms insert_sorted
#print axioms sort_sorted
#print axioms insert_weighted_le
#print axioms sort_weighted_le
#print axioms sorted_permutation_weighted_le
#print axioms sort_mass
end ZlibF.Math.CovfSorting
