import Std
namespace ZlibF.Math.CovfCertificate
set_option autoImplicit false

/-- Integer scalar product over an explicit finite coordinate list. -/
def eval (cols : List Nat) (f : Nat → Int) (w : Nat → Nat) : Int :=
  (cols.map (fun j => f j * (w j : Int))).sum

/-- Nonnegative integral dual coefficients paired with integer constraint rows. -/
def combination (pairs : List (Nat × List Int)) (j : Nat) : Int :=
  (pairs.map (fun pair => (pair.1 : Int) * pair.2[j]?.getD 0)).sum

structure Data where
  raw : List Nat
  repaired : List Nat
  pairs : List (Nat × List Int)
  scale : Nat
  bound : Nat
  deriving Repr

/-- A completely decidable certificate check after clearing denominators.
Each input row has right-hand side zero. The residual bound is per unit mass. -/
def Checked (c : Data) : Prop :=
  0 < c.scale ∧ c.repaired.length = c.raw.length ∧
  (∀ pair ∈ c.pairs, pair.2.length = c.raw.length) ∧
  ∀ j : Fin c.raw.length,
    (c.scale : Int) * ((c.repaired[j.val]?.getD 0 : Int) - (c.raw[j.val]?.getD 0 : Int)) ≤
      (c.bound : Int) + combination c.pairs j.val

instance (c : Data) : Decidable (Checked c) := by unfold Checked; infer_instance

theorem eval_add (cols : List Nat) (f g : Nat → Int) (w : Nat → Nat) :
    eval cols (fun j => f j + g j) w = eval cols f w + eval cols g w := by
  unfold eval
  induction cols with
  | nil => rfl
  | cons j cols ih => simp only [List.map_cons,List.sum_cons,Int.add_mul] at ih ⊢; omega

theorem eval_sub (cols : List Nat) (f g : Nat → Int) (w : Nat → Nat) :
    eval cols (fun j => f j - g j) w = eval cols f w - eval cols g w := by
  unfold eval
  induction cols with
  | nil => rfl
  | cons j cols ih => simp only [List.map_cons,List.sum_cons,Int.sub_mul] at ih ⊢; omega

theorem eval_scale (cols : List Nat) (k : Int) (f : Nat → Int) (w : Nat → Nat) :
    eval cols (fun j => k*f j) w = k*eval cols f w := by
  unfold eval
  induction cols with
  | nil => simp
  | cons j cols ih =>
    simp only [List.map_cons,List.sum_cons,Int.mul_assoc] at ih ⊢
    rw [ih,Int.mul_add]

theorem eval_combination (cols : List Nat) (w : Nat → Nat) (pairs : List (Nat × List Int)) :
    eval cols (combination pairs) w =
      (pairs.map (fun pair => (pair.1 : Int)*eval cols (fun j => pair.2[j]?.getD 0) w)).sum := by
  induction pairs with
  | nil =>
    simp only [eval,combination,List.map_nil,List.sum_nil,Int.zero_mul]
    induction cols with
    | nil => rfl
    | cons j cols ih => simp only [List.map_cons,List.sum_cons,ih,Int.zero_add]
  | cons pair pairs ih =>
    have split : combination (pair::pairs) = fun j =>
        (pair.1 : Int)*pair.2[j]?.getD 0 + combination pairs j := by funext j; rfl
    rw [split,eval_add,eval_scale,ih]
    rfl

theorem eval_mono (cols : List Nat) (f g : Nat → Int) (w : Nat → Nat)
    (bound : ∀ j ∈ cols, f j ≤ g j) : eval cols f w ≤ eval cols g w := by
  unfold eval
  induction cols with
  | nil => simp
  | cons j cols ih =>
    have head := Int.mul_le_mul_of_nonneg_right (bound j (by simp)) (Int.natCast_nonneg (w j))
    have tail := ih (fun k member => bound k (by simp [member]))
    simp only [List.map_cons,List.sum_cons]
    omega

theorem combination_nonpositive (cols : List Nat) (pairs : List (Nat × List Int)) (w : Nat → Nat)
    (rows : ∀ pair ∈ pairs, eval cols (fun j => pair.2[j]?.getD 0) w ≤ 0) :
    (pairs.map (fun pair => (pair.1 : Int)*eval cols (fun j => pair.2[j]?.getD 0) w)).sum ≤ 0 := by
  induction pairs with
  | nil => simp
  | cons pair pairs ih =>
    have head := Int.mul_le_mul_of_nonneg_left (rows pair (by simp)) (Int.natCast_nonneg pair.1)
    have tail := ih (fun q member => rows q (by simp [member]))
    simp only [List.map_cons,List.sum_cons,Int.mul_zero] at head ⊢
    omega

/-- Kernel-checked integer Farkas soundness for the overflow objective.
Nonnegative arbitrary weights and valid comparison/order rows suffice.
No real Huffman execution or covf bound is assumed by this arithmetic lemma. -/
theorem certificate_sound (c : Data) (checked : Checked c) (w : Nat → Nat)
    (rows : ∀ pair ∈ c.pairs, eval (List.range c.raw.length) (fun j => pair.2[j]?.getD 0) w ≤ 0) :
    (c.scale : Int)*eval (List.range c.raw.length) (fun j => (c.repaired[j]?.getD 0 : Int)) w ≤
      (c.scale : Int)*eval (List.range c.raw.length) (fun j => (c.raw[j]?.getD 0 : Int)) w +
        (c.bound : Int)*eval (List.range c.raw.length) (fun _ => 1) w := by
  have point := checked.2.2.2
  have weighted := eval_mono (List.range c.raw.length)
    (fun j => (c.scale : Int)*((c.repaired[j]?.getD 0 : Int)-(c.raw[j]?.getD 0 : Int)))
    (fun j => (c.bound : Int)+combination c.pairs j) w
    (fun j member => point ⟨j,List.mem_range.mp member⟩)
  rw [eval_scale,eval_sub,eval_add,eval_combination] at weighted
  have constant : eval (List.range c.raw.length) (fun _ => (c.bound : Int)) w =
      (c.bound : Int)*eval (List.range c.raw.length) (fun _ => 1) w := by
    simpa only [Int.mul_one] using eval_scale (List.range c.raw.length) (c.bound : Int) (fun _ => 1) w
  rw [constant,Int.mul_sub] at weighted
  have nonpositive := combination_nonpositive (List.range c.raw.length) c.pairs w rows
  omega

#print axioms eval_add
#print axioms eval_sub
#print axioms eval_scale
#print axioms eval_combination
#print axioms eval_mono
#print axioms combination_nonpositive
#print axioms certificate_sound
end ZlibF.Math.CovfCertificate
