import ZlibF.Math.«overlay-lp-dual»

/-!
# A kernel-checkable form of `dualBound` for the memLevel 1–3 overlay LP

`docs/DEFLATE_OVERLAY.md` §8.4. `OverlayLPDual.weak_duality` gives, for every feasible point `x`
of `theLP ml c p q cuts` (the LP of `lp2.py`, rows in `Spec/trees/OverlayLP.lean`),
`D · (hd + E) ≤ dualBound`. Evaluating `dualBound` literally visits every column (up to 27 652)
and, for each, every row (up to 189): far too much for kernel reduction. This file proves
`dualBound (theLP …) D yu ye = fastBound …` for a form that the kernel can evaluate:

* **sparse duals**: rows with a zero dual are dropped (`comb_filter`);
* **affine reduced costs**: every row coefficient of the column `x ti f l` is affine in the
  frequency `f` (`affX_theLP`), so the reduced cost of `x ti f l` is `R0 + f·(R1 − R0)` with `R0`,
  `R1` the reduced costs at `f = 0, 1` (computed once per type and length, `redCost_x`);
* **sums regrouped** by type and length instead of type and frequency (`sum_swap_filter`).

`cert_bound` then turns a certificate `(D, yu, ye, B)` with `0 < D`, `yu ≥ 0` and
`fastBound … ≤ D · B` (a closed Boolean check, `certOK`) into `x hd + x E ≤ B` at every
feasible point. The certificates themselves are in `OverlayLPCertData*.lean`.
-/

namespace Zlib.Trees.OverlayLP.Cert
open Zlib.Trees.OverlayLP

/-! ## Generic list sums -/

theorem sum_map_add {α : Type} (L : List α) (f g : α → Int) :
    (L.map fun a => f a + g a).sum = (L.map f).sum + (L.map g).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.sum_cons, ih]; omega

theorem sum_map_zero' {α : Type} (L : List α) : (L.map fun _ => (0 : Int)).sum = 0 := by
  induction L with
  | nil => rfl
  | cons a L ih => simp only [List.map_cons, List.sum_cons, ih]; rfl

theorem sum_flatMap {α β : Type} (L : List α) (g : α → List β) (h : β → Int) :
    ((L.flatMap g).map h).sum = (L.map fun a => ((g a).map h).sum).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
      List.sum_cons, ih]

theorem sum_filter {α : Type} (L : List α) (p : α → Bool) (h : α → Int) :
    ((L.filter p).map h).sum = (L.map fun a => if p a then h a else 0).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    by_cases hp : p a
    · simp [hp, ih]
    · simp [hp, ih]

theorem sum_comm {α β : Type} (F : List α) (L : List β) (k : α → β → Int) :
    (F.map fun f => (L.map fun l => k f l).sum).sum = (L.map fun l => (F.map fun f => k f l).sum).sum := by
  induction F with
  | nil => simp [sum_map_zero']
  | cons f F ih => simp only [List.map_cons, List.sum_cons, ih, sum_map_add]

/-- Swap a frequency/length double sum with a filter depending on both. -/
theorem sum_swap_filter {α β : Type} (F : List α) (L : List β) (ok : α → β → Bool) (k : α → β → Int) :
    (F.map fun f => ((L.filter (ok f)).map (k f)).sum).sum =
      (L.map fun l => ((F.filter fun f => ok f l).map fun f => k f l).sum).sum := by
  simp only [sum_filter]
  exact sum_comm F L (fun f l => if ok f l then k f l else 0)

/-! ## Sparse duals -/

/-- Drop the rows with a zero dual. -/
def nz {α : Type} (ps : List (Int × Row α)) : List (Int × Row α) := ps.filter fun p => p.1 != 0

theorem comb_filter {α : Type} (ps : List (Int × Row α)) (v : α) : comb (nz ps) v = comb ps v := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    by_cases h : p.1 = 0
    · have : nz (p :: ps) = nz ps := by simp [nz, h]
      rw [this, ih]; simp [comb, h]
    · have : nz (p :: ps) = p :: nz ps := by simp [nz, h]
      rw [this]; simp only [comb, List.map_cons, List.sum_cons] at ih ⊢; rw [ih]

/-- The reduced cost on the sparse rows. -/
def redS (D : Int) (ps qs : List (Int × Row Var)) (v : Var) : Int :=
  D * objHE v - comb ps v - comb qs v

theorem redS_eq (P : LPData Var) (hP : P.obj = objHE) (D : Int) (yu ye : List Int) (v : Var) :
    redS D (nz (yu.zip P.ineqs)) (nz (ye.zip P.eqs)) v = redCost P D yu ye v := by
  simp only [redS, redCost, comb_filter, hP]

/-! ## Affinity in the frequency -/

/-- The coefficient of `x ti f l` is affine in `f`. -/
def AffX (r : Row Var) : Prop :=
  ∀ ti f l, r.coef (.x ti f l) = r.coef (.x ti 0 l) + (f : Int) * (r.coef (.x ti 1 l) - r.coef (.x ti 0 l))

theorem affX_xrow (c : DCase) (gx : CType → Nat → Nat → Int) (g : Var → Int) (b : Int)
    (h : ∀ t f l, gx t f l = gx t 0 l + (f : Int) * (gx t 1 l - gx t 0 l)) : AffX (xrow c gx g b) :=
  fun ti f l => h (tyAt c ti) f l

/-- A coefficient that does not depend on `f`. -/
theorem affX_const (c : DCase) (gx : CType → Nat → Int) (g : Var → Int) (b : Int) :
    AffX (xrow c (fun t _ l => gx t l) g b) :=
  affX_xrow c _ g b (fun t f l => by simp)

theorem aff_lin (f : Nat) (a : Int) : (f : Int) * a = 0 * a + (f : Int) * (1 * a - 0 * a) := by
  simp

theorem affX_rowSize (c : DCase) (ti : Nat) (t : CType) : AffX (rowSize c ti t) := by
  intro ti' f l; simp [rowSize]

theorem affX_rowNsym (ml : Nat) (c : DCase) : AffX (rowNsym ml c) :=
  affX_xrow c _ _ _ (fun t f l => by split <;> simp)

theorem affX_rowM (c : DCase) : AffX (rowM c) :=
  affX_xrow c _ _ _ (fun t f l => by
    split
    · simp
    · split
      · simp
      · simp)

theorem affX_rowChoice (c : DCase) : AffX (rowChoice c) :=
  affX_xrow c _ _ _ (fun t f l => by
    split
    · simp
    · simp only [Int.natCast_zero, Int.zero_mul, Int.neg_zero, Int.zero_add, Int.sub_zero,
        Int.natCast_one, Int.one_mul, Int.mul_neg])

theorem affX_rowExc (c : DCase) (a : Nat) : AffX (rowExc c a) :=
  affX_xrow c _ _ _ (fun t f l => by
    split
    · simp only [Int.natCast_zero, Int.zero_mul, Int.neg_zero, Int.zero_add, Int.sub_zero,
        Int.natCast_one, Int.one_mul, Int.mul_neg]
    · split
      · simp only [Int.natCast_zero, Int.zero_mul, Int.neg_zero, Int.zero_add, Int.sub_zero,
          Int.natCast_one, Int.one_mul, Int.mul_neg]
      · simp)

theorem affX_rowKraftL (ml : Nat) (c : DCase) : AffX (rowKraftL ml c) := affX_const c _ _ _
theorem affX_rowKraftD (ml : Nat) (c : DCase) : AffX (rowKraftD ml c) := affX_const c _ _ _
theorem affX_rowKind (c : DCase) (k : Kind) (b : Int) : AffX (rowKind c k b) := affX_const c _ _ _
theorem affX_rowExc0 (c : DCase) : AffX (rowExc0 c) := affX_const c (fun _ _ => 0) _ _
theorem affX_rowZ (c : DCase) (R : Nat → Var) (w : Nat → Int) (inR : Kind → Bool) (s b : Int) :
    AffX (rowZ c R w inR s b) := affX_const c _ _ _
theorem affX_rowN0 (c : DCase) : AffX (rowN0 c) := affX_const c (fun _ _ => 0) _ _
theorem affX_rowN17 (c : DCase) : AffX (rowN17 c) := affX_const c (fun _ _ => 0) _ _
theorem affX_rowN18 (c : DCase) : AffX (rowN18 c) := affX_const c (fun _ _ => 0) _ _
theorem affX_rowN16 (c : DCase) : AffX (rowN16 c) := affX_const c (fun _ _ => 0) _ _
theorem affX_rowCntLe (c : DCase) (u : Nat) : AffX (rowCntLe c u) := affX_const c _ _ _
theorem affX_rowCntGe (c : DCase) (u : Nat) : AffX (rowCntGe c u) := affX_const c _ _ _
theorem affX_rowCut (c : DCase) (p q : Nat) (tau : List Nat) : AffX (rowCut c p q tau) :=
  affX_const c (fun _ _ => 0) _ _

theorem affX_ineqs (ml : Nat) (c : DCase) (p q : Nat) (cuts : List (List Nat)) :
    ∀ r ∈ (theLP ml c p q cuts).ineqs, AffX r := by
  intro r hr
  simp only [theLP, ineqsBase, List.mem_append, List.mem_map, List.mem_cons, List.mem_flatMap,
    List.not_mem_nil, or_false] at hr
  rcases hr with ((((⟨pp, _, rfl⟩ | rfl | rfl) | hr) | rfl | rfl | rfl | rfl | rfl) | ⟨u, _, rfl | rfl⟩) |
      ⟨tau, _, rfl⟩
  · exact affX_rowSize _ _ _
  · exact affX_rowNsym _ _
  · exact affX_rowChoice _
  · split at hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; exact affX_rowExc0 _
    · simp only [List.mem_map] at hr; obtain ⟨a, _, rfl⟩ := hr; exact affX_rowExc _ _
  all_goals first
    | exact affX_rowZ _ _ _ _ _ _
    | exact affX_rowCntLe _ _
    | exact affX_rowCntGe _ _
    | exact affX_rowCut _ _ _ _

theorem affX_eqs (ml : Nat) (c : DCase) (p q : Nat) (cuts : List (List Nat)) :
    ∀ r ∈ (theLP ml c p q cuts).eqs, AffX r := by
  intro r hr
  simp only [theLP, eqRows, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (((((rfl | hr) | hr) | rfl) | hr) | rfl | rfl | rfl | rfl)
  · exact affX_rowKraftL _ _
  · split at hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; exact affX_rowKraftD _ _
    · simp at hr
  · split at hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; exact affX_rowKind _ _ _
    · simp at hr
  · exact affX_rowKind _ _ _
  · split at hr
    · simp at hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; exact affX_rowM _
  · exact affX_rowN0 _
  · exact affX_rowN17 _
  · exact affX_rowN18 _
  · exact affX_rowN16 _

theorem comb_affX (ps : List (Int × Row Var)) (h : ∀ p ∈ ps, AffX p.2) (ti f l : Nat) :
    comb ps (.x ti f l) = comb ps (.x ti 0 l) + (f : Int) * (comb ps (.x ti 1 l) - comb ps (.x ti 0 l)) := by
  induction ps with
  | nil => simp [comb]
  | cons p ps ih =>
    have ih' := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    have hp := h p (by simp) ti f l
    simp only [comb, List.map_cons, List.sum_cons] at ih' ⊢
    rw [ih', hp]
    generalize p.2.coef (.x ti 0 l) = a0 at *
    generalize p.2.coef (.x ti 1 l) = a1 at *
    generalize (ps.map fun p => p.1 * p.2.coef (.x ti 0 l)).sum = c0 at *
    generalize (ps.map fun p => p.1 * p.2.coef (.x ti 1 l)).sum = c1 at *
    generalize (f : Int) = F
    generalize p.1 = y
    simp only [Int.mul_add, Int.mul_sub, Int.mul_left_comm y F]
    omega

theorem mem_zip_snd {α β : Type} : ∀ (as : List α) (bs : List β) (p : α × β), p ∈ as.zip bs → p.2 ∈ bs
  | [], _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | a :: as, b :: bs, p, h => by
    simp only [List.zip_cons_cons, List.mem_cons] at h
    rcases h with rfl | h
    · simp
    · exact List.mem_cons_of_mem _ (mem_zip_snd as bs p h)

theorem mem_nz {α : Type} {ps : List (Int × Row α)} {p : Int × Row α} (h : p ∈ nz ps) : p ∈ ps :=
  (List.mem_filter.mp h).1

/-- The reduced cost of `x ti f l` from its values at `f = 0` and `f = 1`. -/
theorem redS_x (ml : Nat) (c : DCase) (p q : Nat) (cuts : List (List Nat)) (D : Int) (yu ye : List Int)
    (ti f l : Nat) :
    let ps := nz (yu.zip (theLP ml c p q cuts).ineqs)
    let qs := nz (ye.zip (theLP ml c p q cuts).eqs)
    redS D ps qs (.x ti f l) =
      redS D ps qs (.x ti 0 l) + (f : Int) * (redS D ps qs (.x ti 1 l) - redS D ps qs (.x ti 0 l)) := by
  intro ps qs
  have h1 := comb_affX ps (fun r hr => affX_ineqs ml c p q cuts r.2 (mem_zip_snd _ _ _ (mem_nz hr))) ti f l
  have h2 := comb_affX qs (fun r hr => affX_eqs ml c p q cuts r.2 (mem_zip_snd _ _ _ (mem_nz hr))) ti f l
  simp only [redS, objHE]
  simp only [reduceCtorEq, or_self, ite_false, Int.mul_zero, Int.zero_sub]
  rw [h1, h2]
  generalize comb ps (.x ti 0 l) = a0
  generalize comb ps (.x ti 1 l) = a1
  generalize comb qs (.x ti 0 l) = b0
  generalize comb qs (.x ti 1 l) = b1
  generalize (f : Int) = F
  simp only [Int.mul_sub, Int.mul_neg]
  omega

/-! ## The fast bound -/

/-- Box term of one type `ti` and one length `l`, from the reduced costs `R0`, `R1` at
`f = 0, 1`: `Σ_f ub(x ti f l) · max(0, R0 + f (R1 − R0))` over the frequencies with a column. -/
def grpSum (ml : Nat) (c : DCase) (ti : Nat) (t : CType) (l : Nat) (R0 R1 : Int) : Int :=
  (((fRange ml t.kind).filter fun f => xColOK ml c t.kind f l).map fun f =>
    ub ml c (.x ti f l) * max 0 (R0 + (f : Int) * (R1 - R0))).sum

/-- The non-`x` columns. -/
def restCols : List Var :=
  [Var.hd, Var.E] ++ (List.range 19).map Var.N ++ (List.range' 1 15).map Var.N16 ++
    chunkKinds.map Var.A ++ chunkKinds.map Var.B

/-- The box term regrouped, for any reduced-cost function `red`. -/
def fastBox (ml : Nat) (c : DCase) (red : Var → Int) : Int :=
  ((types c).zipIdx.map fun pr => ((List.range' 1 (lmax ml)).map fun l =>
      grpSum ml c pr.2 pr.1 l (red (.x pr.2 0 l)) (red (.x pr.2 1 l))).sum).sum +
    (restCols.map fun v => ub ml c v * max 0 (red v)).sum

/-- `dualBound` in the kernel-friendly form. -/
def fastBound (ml : Nat) (c : DCase) (p q : Nat) (cuts : List (List Nat)) (D : Int) (yu ye : List Int) : Int :=
  combRhs (yu.zip (theLP ml c p q cuts).ineqs) + combRhs (ye.zip (theLP ml c p q cuts).eqs) +
    fastBox ml c (redS D (nz (yu.zip (theLP ml c p q cuts).ineqs)) (nz (ye.zip (theLP ml c p q cuts).eqs)))

theorem box_x_group (ml : Nat) (c : DCase) (ti : Nat) (t : CType) (h : Var → Int) :
    ((xColsOf ml c ti t).map h).sum =
      ((List.range' 1 (lmax ml)).map fun l =>
        (((fRange ml t.kind).filter fun f => xColOK ml c t.kind f l).map fun f => h (.x ti f l)).sum).sum := by
  unfold xColsOf
  rw [sum_flatMap]
  simp only [List.map_map]
  exact sum_swap_filter (fRange ml t.kind) (List.range' 1 (lmax ml)) (fun f l => xColOK ml c t.kind f l)
    (fun f l => h (.x ti f l))

theorem fastBound_eq (ml : Nat) (c : DCase) (p q : Nat) (cuts : List (List Nat)) (D : Int) (yu ye : List Int) :
    fastBound ml c p q cuts D yu ye = dualBound (theLP ml c p q cuts) D yu ye := by
  have hred : ∀ v, redS D (nz (yu.zip (theLP ml c p q cuts).ineqs)) (nz (ye.zip (theLP ml c p q cuts).eqs)) v =
      redCost (theLP ml c p q cuts) D yu ye v := redS_eq _ rfl D yu ye
  unfold fastBound dualBound
  congr 1
  rw [← funext hred]
  generalize hR : redS D (nz (yu.zip (theLP ml c p q cuts).ineqs)) (nz (ye.zip (theLP ml c p q cuts).eqs)) = R
  have hx : ∀ ti f l, R (.x ti f l) = R (.x ti 0 l) + (f : Int) * (R (.x ti 1 l) - R (.x ti 0 l)) := by
    intro ti f l; rw [← hR]; exact redS_x ml c p q cuts D yu ye ti f l
  show fastBox ml c R = ((cols ml c).map fun v => ub ml c v * max 0 (R v)).sum
  unfold fastBox cols
  rw [show ((types c).zipIdx.flatMap fun p => xColsOf ml c p.2 p.1) ++ [Var.hd, Var.E] ++
      (List.range 19).map Var.N ++ (List.range' 1 15).map Var.N16 ++ chunkKinds.map Var.A ++
      chunkKinds.map Var.B = ((types c).zipIdx.flatMap fun p => xColsOf ml c p.2 p.1) ++ restCols by
    simp [restCols, List.append_assoc]]
  rw [List.map_append, List.sum_append, sum_flatMap]
  congr 1
  congr 1
  apply List.map_congr_left
  intro pr _
  rw [box_x_group]
  unfold grpSum
  congr 1
  apply List.map_congr_left
  intro l _
  congr 1
  apply List.map_congr_left
  intro f _
  rw [hx pr.snd f l]

/-! ## From a certificate to the bound -/

/-- The objective `hd + E` at `x`. -/
theorem evalR_objHE (ml : Nat) (c : DCase) (x : Var → Int) :
    evalR (cols ml c) objHE x = x .hd + x .E := by
  have h0 : ∀ L : List Var, (∀ v ∈ L, objHE v = 0) → evalR L objHE x = 0 := by
    intro L hL
    unfold evalR
    induction L with
    | nil => rfl
    | cons v L ih =>
      simp only [List.map_cons, List.sum_cons, hL v (by simp), Int.zero_mul, Int.zero_add]
      exact ih (fun w hw => hL w (List.mem_cons_of_mem _ hw))
  have happ : ∀ L M : List Var, evalR (L ++ M) objHE x = evalR L objHE x + evalR M objHE x := by
    intro L M; simp [evalR, List.map_append, List.sum_append]
  unfold cols
  simp only [happ]
  have hX : evalR ((types c).zipIdx.flatMap fun p => xColsOf ml c p.2 p.1) objHE x = 0 := by
    apply h0
    intro v hv
    simp only [List.mem_flatMap, xColsOf, List.mem_map, List.mem_filter] at hv
    obtain ⟨_, _, _, _, l, _, rfl⟩ := hv
    simp [objHE]
  rw [hX, h0 ((List.range 19).map Var.N) (by intro v hv; simp only [List.mem_map] at hv; obtain ⟨_, _, rfl⟩ := hv; simp [objHE]),
    h0 ((List.range' 1 15).map Var.N16) (by intro v hv; simp only [List.mem_map] at hv; obtain ⟨_, _, rfl⟩ := hv; simp [objHE]),
    h0 (chunkKinds.map Var.A) (by intro v hv; simp only [List.mem_map] at hv; obtain ⟨_, _, rfl⟩ := hv; simp [objHE]), h0 (chunkKinds.map Var.B) (by intro v hv; simp only [List.mem_map] at hv; obtain ⟨_, _, rfl⟩ := hv; simp [objHE])]
  simp [evalR, objHE]

/-- The closed check of a certificate: `D > 0`, `yu ≥ 0`, `fastBound ≤ D · B`. -/
def certOK (ml : Nat) (c : DCase) (p q : Nat) (cuts : List (List Nat)) (D : Int) (yu ye : List Int)
    (B : Int) : Bool :=
  decide (0 < D) && yu.all (fun y => decide (0 ≤ y)) && decide (fastBound ml c p q cuts D yu ye ≤ D * B)

/-- **Certificate soundness.** A certificate that passes `certOK` bounds `hd + E` by `B` at every
feasible point of `theLP ml c p q cuts`. -/
theorem cert_bound (ml : Nat) (c : DCase) (p q : Nat) (cuts : List (List Nat)) (D : Int) (yu ye : List Int)
    (B : Int) (hc : certOK ml c p q cuts D yu ye B = true) (x : Var → Int)
    (hx : Feasible (theLP ml c p q cuts) x) : x .hd + x .E ≤ B := by
  simp only [certOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
  obtain ⟨⟨hD, hy⟩, hb⟩ := hc
  have hw := weak_duality (theLP ml c p q cuts) x hx D yu ye hy
  rw [← fastBound_eq] at hw
  have ho : evalR (theLP ml c p q cuts).cols (theLP ml c p q cuts).obj x = x .hd + x .E :=
    evalR_objHE ml c x
  rw [ho] at hw
  have : D * (x .hd + x .E) ≤ D * B := Int.le_trans hw hb
  exact Int.le_of_mul_le_mul_left this hD

/-- The cut codes are codes on the 19 bit-length symbols with lengths `1..15` satisfying
Kraft's inequality `Σ_t 2^(−τ_t) ≤ 1` (scaled by `2^15`), the condition under which a cut
row of `lp2.py` is valid (`verify.py`). -/
def cutsKraft (cuts : List (List Nat)) : Bool :=
  cuts.all fun tau => tau.length == 19 && tau.all (fun t => 1 ≤ t && t ≤ 15) &&
    decide ((tau.map fun t => 2 ^ (15 - t)).sum ≤ 2 ^ 15)

theorem cutsKraft_spec {cuts : List (List Nat)} (h : cutsKraft cuts = true) :
    ∀ tau ∈ cuts, tau.length = 19 ∧ (∀ t ∈ tau, 1 ≤ t ∧ t ≤ 15) ∧
      (tau.map fun t => 2 ^ (15 - t)).sum ≤ 2 ^ 15 := by
  intro tau ht
  simp only [cutsKraft, List.all_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h tau ht
  exact ⟨h1, h2, h3⟩

end Zlib.Trees.OverlayLP.Cert
