import ZlibF.Math.«overlay-lp»

/-!
# Weak duality for integer LPs given as rows over a column list

Generic lemma (step 6 of the memLevel 1–3 overlay LP, `docs/DEFLATE_OVERLAY.md` §8.4): the check
`verify.py` does with fractions, stated over `Int`.

An LP over column names `α` is a list of columns `cols` with upper bounds `ub`, inequality rows
`a·x ≤ b`, equality rows `e·x = b` and an objective `c`; a row is a coefficient function on `α`
and a right-hand side, and `a·x` is evaluated over `cols` (`evalR`). Rational duals are scaled to
integers with a common denominator `D > 0`. For `y ≥ 0` (one per inequality, paired by
position with `List.zip`) and any `z` (one per equality), with
`red v = D·c v − Σ y_i a_i v − Σ z_k e_k v`, every feasible `x` (`0 ≤ x ≤ ub` on `cols`) has

  `D · c·x ≤ Σ y_i b_i + Σ z_k b_k + Σ_{v ∈ cols} ub v · max(0, red v)`   (`weak_duality`).

The definitions (`Row`, `LPData`, `evalR`, `Feasible`, `dualBound`) are in
`Spec/trees/OverlayLP.lean`.
-/

namespace Zlib.Trees.OverlayLP

theorem evalR_add {α : Type} (cols : List α) (f g : α → Int) (x : α → Int) :
    evalR cols (fun v => f v + g v) x = evalR cols f x + evalR cols g x := by
  unfold evalR; induction cols with
  | nil => simp
  | cons v cs ih => simp only [List.map_cons, List.sum_cons, Int.add_mul] at ih ⊢; omega

theorem evalR_sub {α : Type} (cols : List α) (f g : α → Int) (x : α → Int) :
    evalR cols (fun v => f v - g v) x = evalR cols f x - evalR cols g x := by
  unfold evalR; induction cols with
  | nil => simp
  | cons v cs ih => simp only [List.map_cons, List.sum_cons, Int.sub_mul] at ih ⊢; omega

theorem evalR_smul {α : Type} (cols : List α) (k : Int) (f : α → Int) (x : α → Int) :
    evalR cols (fun v => k * f v) x = k * evalR cols f x := by
  unfold evalR; induction cols with
  | nil => simp
  | cons v cs ih => simp only [List.map_cons, List.sum_cons, Int.mul_assoc] at ih ⊢; rw [ih, Int.mul_add]

theorem sum_map_zero {α : Type} (cols : List α) : (cols.map fun _ => (0 : Int)).sum = 0 := by
  induction cols with
  | nil => rfl
  | cons v cs ih => simp only [List.map_cons, List.sum_cons, ih]; rfl

theorem evalR_comb {α : Type} (cols : List α) (x : α → Int) : ∀ ps : List (Int × Row α),
    evalR cols (comb ps) x = (ps.map fun p => p.1 * evalR cols p.2.coef x).sum
  | [] => by simp [evalR, comb, sum_map_zero]
  | p :: ps => by
    have e : comb (p :: ps) = fun v => p.1 * p.2.coef v + comb ps v := by
      funext v; simp [comb]
    rw [e, evalR_add, evalR_smul, evalR_comb cols x ps]; simp

theorem comb_ineq_le {α : Type} (cols : List α) (x : α → Int) (rows : List (Row α))
    (hr : ∀ r ∈ rows, evalR cols r.coef x ≤ r.rhs) : ∀ yu : List Int, (∀ y ∈ yu, 0 ≤ y) →
    ((yu.zip rows).map fun p => p.1 * evalR cols p.2.coef x).sum ≤ combRhs (yu.zip rows) := by
  induction rows with
  | nil => intro yu _; cases yu <;> simp [combRhs]
  | cons r rs ih =>
    intro yu hy
    cases yu with
    | nil => simp [combRhs]
    | cons y ys =>
      simp only [List.zip_cons_cons, List.map_cons, List.sum_cons, combRhs] at *
      have h1 := ih (fun r' h => hr r' (List.mem_cons_of_mem _ h)) ys (fun y' h => hy y' (List.mem_cons_of_mem _ h))
      have h2 : y * evalR cols r.coef x ≤ y * r.rhs :=
        Int.mul_le_mul_of_nonneg_left (hr r (by simp)) (hy y (by simp))
      omega

theorem comb_eq {α : Type} (cols : List α) (x : α → Int) (rows : List (Row α))
    (hr : ∀ r ∈ rows, evalR cols r.coef x = r.rhs) : ∀ ye : List Int,
    ((ye.zip rows).map fun p => p.1 * evalR cols p.2.coef x).sum = combRhs (ye.zip rows) := by
  induction rows with
  | nil => intro ye; cases ye <;> simp [combRhs]
  | cons r rs ih =>
    intro ye
    cases ye with
    | nil => simp [combRhs]
    | cons y ys =>
      simp only [List.zip_cons_cons, List.map_cons, List.sum_cons, combRhs] at *
      rw [hr r (by simp), ih (fun r' h => hr r' (List.mem_cons_of_mem _ h)) ys]

theorem evalR_le_box {α : Type} (cols : List α) (g ub x : α → Int)
    (hb : ∀ v ∈ cols, 0 ≤ x v ∧ x v ≤ ub v) :
    evalR cols g x ≤ (cols.map fun v => ub v * max 0 (g v)).sum := by
  unfold evalR; induction cols with
  | nil => simp
  | cons v cs ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 := ih (fun w hw => hb w (List.mem_cons_of_mem _ hw))
    obtain ⟨h0, hu⟩ := hb v (by simp)
    have h2 : g v * x v ≤ ub v * max 0 (g v) := by
      have hm : 0 ≤ max 0 (g v) := Int.le_max_left _ _
      have hg : g v ≤ max 0 (g v) := Int.le_max_right _ _
      calc g v * x v ≤ max 0 (g v) * x v := Int.mul_le_mul_of_nonneg_right hg h0
        _ ≤ max 0 (g v) * ub v := Int.mul_le_mul_of_nonneg_left hu hm
        _ = ub v * max 0 (g v) := Int.mul_comm _ _
    omega

/-- **Weak duality.** For a feasible `x`, `y ≥ 0` on the inequalities, any `z` on the
equalities and `D > 0` (not needed for the inequality itself; it is the common denominator of
a rational dual), `D·(c·x) ≤ dualBound`. -/
theorem weak_duality {α : Type} (P : LPData α) (x : α → Int) (hx : Feasible P x) (D : Int)
    (yu ye : List Int) (hy : ∀ y ∈ yu, 0 ≤ y) :
    D * evalR P.cols P.obj x ≤ dualBound P D yu ye := by
  have hred : D * evalR P.cols P.obj x = evalR P.cols (redCost P D yu ye) x +
      evalR P.cols (comb (yu.zip P.ineqs)) x + evalR P.cols (comb (ye.zip P.eqs)) x := by
    unfold redCost
    rw [evalR_sub, evalR_sub, evalR_smul]; omega
  rw [hred, evalR_comb, evalR_comb, comb_eq P.cols x P.eqs hx.eq ye]
  have h1 := comb_ineq_le P.cols x P.ineqs hx.ineq yu hy
  have h2 := evalR_le_box P.cols (redCost P D yu ye) P.ub x hx.box
  unfold dualBound; omega

end Zlib.Trees.OverlayLP
