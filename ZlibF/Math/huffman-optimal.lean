import Std
import ZlibF.Math.HuffmanTree

/-!
# Kraft equality and optimality of the abstract Huffman merge

The pinned reference overlay analysis, properties (K) and (O), for the tree that `build_tree`'s
merge loop builds (`Merges`), stated without a length limit:

* `kraft_eq`: for any tree and any `H ≥ height`, `Σ_leaves 2^(H − d) = 2^H`.
* `merges_optimal`: for every assignment `t` of lengths to the symbols with
  `Σ 2^(K − t) ≤ 2^K` (Kraft), `Σ_leaves w·d ≤ Σ_symbols w·t`.

The proof is the classical exchange argument, by induction on the run. The merged pair
`n, m` can be given the two longest lengths without raising the cost (`swap_max`). The
longer one can then be cut to the shorter (`kraft_lower`). The two then merge into one item
one level up (`exchange`). Only the `Freq` part of `smaller` is used.
-/

namespace Zlib.Trees.HuffmanAbstract
open HTree

/-! ## Sums -/

theorem sum_map_add {β : Type _} (l : List β) (f g : β → Nat) :
    (l.map fun x => f x + g x).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.map_cons, List.sum_cons, ih]; omega

theorem sum_perm_map {β : Type _} {l₁ l₂ : List β} (f : β → Nat) (h : l₁.Perm l₂) :
    (l₁.map f).sum = (l₂.map f).sum := (h.map f).sum_nat

/-! ## Tree facts -/

theorem leaves_w_sum (l : List LeafInfo) :
    ((l.map fun x => ({ x with d := x.d + 1 } : LeafInfo)).map fun x => x.w * x.d).sum =
      (l.map fun x => x.w * x.d).sum + (l.map (·.w)).sum := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.map_cons, List.sum_cons, ih, Nat.mul_add]; omega

theorem weight_eq_sum : ∀ t : HTree, t.weight = (t.leaves.map (·.w)).sum
  | leaf _ w => by simp [weight, leaves]
  | node a b => by
    simp only [weight, leaves, List.map_map, List.map_append, List.sum_append]
    rw [weight_eq_sum a, weight_eq_sum b]; rfl

theorem leafCost_leaf (s w : Nat) : (leaf s w).leafCost = 0 := by simp [leafCost, leaves]

theorem leafCost_node (a b : HTree) :
    (node a b).leafCost = a.leafCost + b.leafCost + a.weight + b.weight := by
  simp only [leafCost, leaves]
  rw [leaves_w_sum, List.map_append, List.sum_append, List.map_append, List.sum_append,
    weight_eq_sum a, weight_eq_sum b]
  omega

theorem depth_le_height : ∀ (t : HTree), ∀ x ∈ t.leaves, x.d ≤ t.height
  | leaf _ _, x, hx => by simp only [leaves, List.mem_singleton] at hx; subst hx; simp [height]
  | node a b, x, hx => by
    simp only [leaves, List.mem_map, List.mem_append] at hx
    obtain ⟨y, hy | hy, rfl⟩ := hx
    · have := depth_le_height a y hy; simp only [height]; omega
    · have := depth_le_height b y hy; simp only [height]; omega

theorem kraft_shift (l : List LeafInfo) (H : Nat) :
    ((l.map fun x => ({ x with d := x.d + 1 } : LeafInfo)).map fun x => 2 ^ (H + 1 - x.d)).sum =
      (l.map fun x => 2 ^ (H - x.d)).sum := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    congr 2; omega

/-- **Kraft equality** (property (K)). For every `H ≥ height`, `Σ_leaves 2^(H − d) = 2^H`.
In other words the leaf depths of every tree, merge tree or not, satisfy
`Σ 2^(−d) = 1`. -/
theorem kraft_eq : ∀ (t : HTree) (H : Nat), t.height ≤ H → (t.leaves.map fun x => 2 ^ (H - x.d)).sum = 2 ^ H
  | leaf _ _, H, _ => by simp [leaves]
  | node a b, H, hH => by
    simp only [height] at hH
    obtain ⟨H', rfl⟩ : ∃ H', H = H' + 1 := ⟨H - 1, by omega⟩
    simp only [leaves, List.map_append, List.sum_append]
    rw [kraft_shift, kraft_shift,
      kraft_eq a H' (by omega), kraft_eq b H' (by omega), Nat.pow_succ]
    omega

/-! ## Exchange on weighted length lists -/

section exchange
variable {α : Type _} (wt : α → Nat)

/-- `Σ wt(x)·t` over a list of (item, length) pairs. -/
def costW (ps : List (α × Nat)) : Nat := (ps.map fun p => wt p.1 * p.2).sum

/-- The Kraft sum `Σ 2^(K − t)`. -/
def kraftS (K : Nat) (ts : List Nat) : Nat := (ts.map fun t => 2 ^ (K - t)).sum

theorem exch_ineq {wx wy a c : Nat} (hw : wx ≤ wy) (hac : a ≤ c) :
    wx * c + wy * a ≤ wx * a + wy * c := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hac
  obtain ⟨f, rfl⟩ := Nat.exists_eq_add_of_le hw
  simp only [Nat.mul_add, Nat.add_mul]
  omega

/-- Swap a longest length onto the light item `x`. The rest keeps its items in the same
order, the lengths are permuted, `x`'s new length `a'` is at least every remaining
length, and the cost does not grow. -/
theorem swap_max (x : α) : ∀ (a : Nat) (rest : List (α × Nat)), (∀ p ∈ rest, wt x ≤ wt p.1) →
    ∃ a' rest', rest'.map Prod.fst = rest.map Prod.fst ∧
      (a' :: rest'.map Prod.snd).Perm (a :: rest.map Prod.snd) ∧ (∀ p ∈ rest', p.2 ≤ a') ∧
      wt x * a' + costW wt rest' ≤ wt x * a + costW wt rest
  | a, [], _ => ⟨a, [], rfl, List.Perm.refl _, by simp, Nat.le_refl _⟩
  | a, (y, c) :: rest, hmin => by
    obtain ⟨a1, rest1, hf, hp, hmax, hc⟩ :=
      swap_max x a rest (fun p hp => hmin p (List.mem_cons_of_mem _ hp))
    have hy : wt x ≤ wt y := hmin (y, c) (by simp)
    have hperm : ∀ u v : Nat, u + v = a1 + c → min u v = min a1 c →
        (u :: v :: rest1.map Prod.snd).Perm (a :: (c :: rest.map Prod.snd)) := by
      intro u v h1 h2
      have : (u = a1 ∧ v = c) ∨ (u = c ∧ v = a1) := by omega
      rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]; exact (List.Perm.swap c a1 _).trans ((hp.cons c).trans (List.Perm.swap a c _))
      · rw [h1, h2]; exact (hp.cons c).trans (List.Perm.swap a c _)
    rcases Nat.le_total c a1 with hle | hlt
    · refine ⟨a1, (y, c) :: rest1, by simp [hf], hperm a1 c rfl rfl, ?_, ?_⟩
      · intro p hp'
        simp only [List.mem_cons] at hp'
        rcases hp' with rfl | hp'
        · exact hle
        · exact hmax p hp'
      · simp only [costW, List.map_cons, List.sum_cons] at hc ⊢; omega
    · refine ⟨c, (y, a1) :: rest1, by simp [hf], hperm c a1 (by omega) (by omega), ?_, ?_⟩
      · intro p hp'
        simp only [List.mem_cons] at hp'
        rcases hp' with rfl | hp'
        · exact hlt
        · exact Nat.le_trans (hmax p hp') hlt
      · have := exch_ineq hy hlt
        simp only [costW, List.map_cons, List.sum_cons] at hc ⊢; omega

theorem dvd_kraftS (K b : Nat) : ∀ ts : List Nat, (∀ t ∈ ts, t ≤ b) → 2 ^ (K - b) ∣ kraftS K ts
  | [], _ => by simp [kraftS]
  | t :: ts, h => by
    simp only [kraftS, List.map_cons, List.sum_cons]
    exact Nat.dvd_add (Nat.pow_dvd_pow 2 (by have := h t (by simp); omega))
      (dvd_kraftS K b ts fun u hu => h u (List.mem_cons_of_mem _ hu))

theorem add_le_of_dvd {u X Y : Nat} (hX : u ∣ X) (hY : u ∣ Y) (hlt : X < Y) : X + u ≤ Y := by
  obtain ⟨p, rfl⟩ := hX
  obtain ⟨q, rfl⟩ := hY
  have hpq : p < q := by
    rcases Nat.lt_or_ge p q with h | h
    · exact h
    · exact absurd (Nat.mul_le_mul_left u h) (by omega)
  have := Nat.mul_le_mul_left u (show p + 1 ≤ q by omega)
  rw [Nat.mul_add, Nat.mul_one] at this; exact this

/-- Changing one length `a` to `b` keeps Kraft when every other length is at most `b`
(used with `a ≥ b`: cutting the unique longest length down to the next one). -/
theorem kraft_lower (K a b : Nat) (ts : List Nat) (hts : ∀ t ∈ ts, t ≤ b)
    (h : 2 ^ (K - a) + 2 ^ (K - b) + kraftS K ts ≤ 2 ^ K) :
    2 ^ (K - b) + 2 ^ (K - b) + kraftS K ts ≤ 2 ^ K := by
  have hd1 : 2 ^ (K - b) ∣ 2 ^ (K - b) + kraftS K ts :=
    Nat.dvd_add (Nat.dvd_refl _) (dvd_kraftS K b ts hts)
  have hd2 : 2 ^ (K - b) ∣ 2 ^ K := Nat.pow_dvd_pow 2 (by omega)
  have hpos : 1 ≤ 2 ^ (K - a) := Nat.one_le_two_pow
  have := add_le_of_dvd hd1 hd2 (by omega)
  omega

/-- Lift a permutation of the first components. -/
theorem perm_map_cons {β : Type _} (f : β → α) {l : List β} {x : α} {r : List α}
    (h : (l.map f).Perm (x :: r)) : ∃ y rest, f y = x ∧ l.Perm (y :: rest) ∧ (rest.map f).Perm r := by
  have hx : x ∈ l.map f := h.mem_iff.2 (by simp)
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
  obtain ⟨s, t, rfl⟩ := List.append_of_mem hy
  refine ⟨y, s ++ t, rfl, List.perm_middle, ?_⟩
  have h2 : ((s ++ y :: t).map f).Perm (f y :: (s ++ t).map f) := by
    simp
  exact (h2.symm.trans h).cons_inv

theorem kraftS_perm {K : Nat} {l₁ l₂ : List Nat} (h : l₁.Perm l₂) : kraftS K l₁ = kraftS K l₂ :=
  sum_perm_map _ h

/-- **Exchange step.** The two lightest items `n, m` of a Kraft-valid assignment `ps`
can be given one common length `ℓ ≥ 1`. The rest becomes `qs`, with the same items and
lengths still `≤ K`. Merging `n, m` into one item of length `ℓ − 1` keeps Kraft, and the
cost does not grow. -/
theorem exchange (K : Nat) (ps : List (α × Nat)) (n m : α) (r : List α)
    (hps : (ps.map Prod.fst).Perm (n :: m :: r))
    (hn : ∀ x ∈ m :: r, wt n ≤ wt x) (hm : ∀ x ∈ r, wt m ≤ wt x)
    (hK : ∀ p ∈ ps, p.2 ≤ K) (hkr : kraftS K (ps.map Prod.snd) ≤ 2 ^ K) :
    ∃ ℓ qs, 1 ≤ ℓ ∧ ℓ ≤ K ∧ (qs.map Prod.fst).Perm r ∧ (∀ q ∈ qs, q.2 ≤ K) ∧
      2 ^ (K - (ℓ - 1)) + kraftS K (qs.map Prod.snd) ≤ 2 ^ K ∧
      wt n * ℓ + wt m * ℓ + costW wt qs ≤ costW wt ps := by
  -- lift the two items out of `ps`
  obtain ⟨pn, rest0, hpn, hp0, hr0⟩ := perm_map_cons Prod.fst hps
  obtain ⟨pm, rest, hpm, hp1, hr1⟩ := perm_map_cons Prod.fst hr0
  obtain ⟨n', a⟩ := pn
  obtain ⟨m', b⟩ := pm
  simp only at hpn hpm; subst hpn; subst hpm
  have hpsP : ps.Perm ((n', a) :: (m', b) :: rest) := hp0.trans (hp1.cons _)
  have memr : ∀ p ∈ rest, p.1 ∈ r := fun p hp => hr1.mem_iff.1 (List.mem_map_of_mem hp)
  -- step 1: longest length onto n
  obtain ⟨a1, rest1, hf1, hP1, hmax1, hc1⟩ := swap_max wt n' a ((m', b) :: rest) (by
    intro p hp
    simp only [List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact hn _ (by simp)
    · exact hn _ (List.mem_cons_of_mem _ (memr p hp)))
  obtain ⟨⟨m'', b1⟩, rest1', rfl⟩ : ∃ q rest1', rest1 = q :: rest1' := by
    cases rest1 with
    | nil => simp at hf1
    | cons q rest1' => exact ⟨q, rest1', rfl⟩
  simp only [List.map_cons, List.cons.injEq] at hf1
  obtain ⟨rfl, hf1'⟩ := hf1
  -- step 2: longest remaining length onto m
  obtain ⟨b2, rest2, hf2, hP2, hmax2, hc2⟩ := swap_max wt m'' b1 rest1' (by
    intro p hp
    have : p.1 ∈ rest.map Prod.fst := by rw [← hf1']; exact List.mem_map_of_mem hp
    obtain ⟨q, hq, hqe⟩ := List.mem_map.1 this
    rw [← hqe]; exact hm _ (memr q hq))
  have hb2a1 : b2 ≤ a1 := by
    have : b2 ∈ b1 :: rest1'.map Prod.snd := hP2.mem_iff.1 (by simp)
    simp only [List.mem_cons, List.mem_map] at this
    rcases this with h | ⟨q, hq, hqe⟩
    · rw [h]; exact hmax1 (m'', b1) List.mem_cons_self
    · rw [← hqe]; exact hmax1 q (List.mem_cons_of_mem _ hq)
  -- the length multiset is unchanged
  have hLen : (a1 :: b2 :: rest2.map Prod.snd).Perm (a :: b :: rest.map Prod.snd) :=
    (hP2.cons a1).trans hP1
  have hLenPs : (ps.map Prod.snd).Perm (a :: b :: rest.map Prod.snd) := by
    simpa using hpsP.map Prod.snd
  have hkr' : 2 ^ (K - a1) + 2 ^ (K - b2) + kraftS K (rest2.map Prod.snd) ≤ 2 ^ K := by
    have := kraftS_perm (K := K) (hLen.trans hLenPs.symm)
    simp only [kraftS, List.map_cons, List.sum_cons] at this
    simp only [kraftS] at hkr ⊢; omega
  have hlenK : ∀ t ∈ a1 :: b2 :: rest2.map Prod.snd, t ≤ K := by
    intro t ht
    have : t ∈ ps.map Prod.snd := hLenPs.mem_iff.2 (hLen.mem_iff.1 ht)
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 this
    exact hK p hp
  have ha1K : a1 ≤ K := hlenK a1 (by simp)
  have hb2K : b2 ≤ K := hlenK b2 (by simp)
  -- step 3: cut n down to b2
  have hlow := kraft_lower K a1 b2 (rest2.map Prod.snd)
    (by intro t ht; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ht; exact hmax2 p hp) hkr'
  have hb2pos : 1 ≤ b2 := by
    rcases Nat.lt_or_ge b2 1 with h | h
    · have : b2 = 0 := by omega
      subst this
      have : (1 : Nat) ≤ 2 ^ K := Nat.one_le_two_pow
      simp only [Nat.sub_zero] at hlow; omega
    · exact h
  refine ⟨b2, rest2, hb2pos, hb2K, ?_, ?_, ?_, ?_⟩
  · rw [hf2, hf1']; exact hr1
  · intro q hq; exact hlenK q.2 (by simp [List.mem_map_of_mem (f := Prod.snd) hq])
  · have : K - (b2 - 1) = (K - b2) + 1 := by omega
    rw [this, Nat.pow_succ]; omega
  · have hcostPs : costW wt ps = wt n' * a + wt m'' * b + costW wt rest := by
      have := sum_perm_map (fun p : α × Nat => wt p.1 * p.2) hpsP
      simp only [costW, List.map_cons, List.sum_cons] at this ⊢; omega
    have hna : wt n' * b2 ≤ wt n' * a1 := Nat.mul_le_mul_left _ hb2a1
    simp only [costW, List.map_cons, List.sum_cons] at hc1
    simp only [costW] at hc2 hcostPs ⊢
    omega

end exchange

/-! ## Optimality of the merge -/

/-- **Optimality on forests.** Let `ps` assign a length to every tree of the forest `s`
(Kraft-valid, lengths `≤ K`). Then the tree the run builds has leaf cost at most
`Σ (leafCost + weight·length)` over `ps`. -/
theorem merges_opt_forest {s tr : List HTree} {T : HTree} (h : Merges s tr T) :
    ∀ (K : Nat) (ps : List (HTree × Nat)), (ps.map Prod.fst).Perm s → (∀ p ∈ ps, p.2 ≤ K) →
      kraftS K (ps.map Prod.snd) ≤ 2 ^ K →
      T.leafCost ≤ (ps.map fun p => p.1.leafCost + p.1.weight * p.2).sum := by
  induction h with
  | done t =>
    intro K ps hps _ _
    have : ps.map Prod.fst = [t] := List.Perm.eq_singleton hps
    obtain ⟨p, rfl⟩ : ∃ p, ps = [p] := by
      cases ps with
      | nil => simp at this
      | cons p ps' => cases ps' with
        | nil => exact ⟨p, rfl⟩
        | cons _ _ => simp at this
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at this
    subst this; simp
  | @step s s' n m tr T hst _ ih =>
    intro K ps hps hK hkr
    obtain ⟨r, hp, hn, hm, rfl⟩ := hst
    obtain ⟨ℓ, qs, hℓ1, hℓK, hqs, hqK, hqkr, hqc⟩ := exchange HTree.weight K ps n m r (hps.trans hp)
      (fun x hx => smaller_weight' (hn x hx)) (fun x hx => smaller_weight' (hm x hx)) hK hkr
    have ih' := ih K ((node n m, ℓ - 1) :: qs) (by simpa using hqs.cons (node n m))
      (by
        intro p hp'
        simp only [List.mem_cons] at hp'
        rcases hp' with rfl | hp'
        · simp only; omega
        · exact hqK p hp')
      (by simp only [kraftS, List.map_cons, List.sum_cons] at hqkr ⊢; exact hqkr)
    have hlc : (ps.map fun p => p.1.leafCost).sum = n.leafCost + m.leafCost +
        (qs.map fun p => p.1.leafCost).sum := by
      have h1 := sum_perm_map HTree.leafCost (hps.trans hp)
      have h2 := sum_perm_map HTree.leafCost hqs
      simp only [List.map_map, List.map_cons, List.sum_cons] at h1 h2
      rw [show (fun p : HTree × Nat => p.1.leafCost) = HTree.leafCost ∘ Prod.fst from rfl, h1, ← h2]
      omega
    rw [sum_map_add] at ih' ⊢
    simp only [List.map_cons, List.sum_cons, leafCost_node] at ih'
    have hwnm : (node n m).weight = n.weight + m.weight := rfl
    rw [hwnm] at ih'
    rw [hlc]
    obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
    simp only [Nat.add_sub_cancel, Nat.add_mul, Nat.mul_add, Nat.mul_one] at ih' hqc
    simp only [costW] at hqc
    omega
where
  smaller_weight' {a b : HTree} (h : smaller a b) : a.weight ≤ b.weight := by
    rcases h with h | ⟨h, _⟩ <;> omega

/-- **Optimality** (property (O), DEFLATE_OVERLAY.md §3). Let a merge run start from the
symbols `syms` (pairs `(symbol, weight)`). For every length assignment `t` with
`t j ≤ K` and Kraft `Σ 2^(K − t j) ≤ 2^K` over `syms`, the code given by the leaf depths
costs at most as much: `Σ_leaves w·d ≤ Σ_syms w·t`. No length limit applies here: the
leaf depths are the Huffman depths before `gen_bitlen` clamps them. -/
theorem merges_optimal {syms : List (Nat × Nat)} {tr : List HTree} {T : HTree}
    (h : Merges (initForest syms) tr T) (K : Nat) (t : Nat → Nat)
    (hK : ∀ p ∈ syms, t p.1 ≤ K) (hkr : (syms.map fun p => 2 ^ (K - t p.1)).sum ≤ 2 ^ K) :
    T.leafCost ≤ (syms.map fun p => p.2 * t p.1).sum := by
  have eA : ∀ l : List (Nat × Nat), ((l.map fun p => (HTree.leaf p.1 p.2, t p.1)).map
      fun p => p.1.leafCost + p.1.weight * p.2).sum = (l.map fun p => p.2 * t p.1).sum := by
    intro l; induction l with
    | nil => rfl
    | cons p l ih => simp only [List.map_cons, List.sum_cons, ih, leafCost_leaf, weight]; omega
  have eB : ∀ l : List (Nat × Nat), kraftS K ((l.map fun p => (HTree.leaf p.1 p.2, t p.1)).map
      Prod.snd) = (l.map fun p => 2 ^ (K - t p.1)).sum := by
    intro l; induction l with
    | nil => rfl
    | cons p l ih => simp only [kraftS, List.map_cons, List.sum_cons] at ih ⊢; rw [ih]
  have eC : ((syms.map fun p => (HTree.leaf p.1 p.2, t p.1)).map Prod.fst) = initForest syms := by
    simp only [initForest, List.map_map]; rfl
  have := merges_opt_forest h K (syms.map fun p => (HTree.leaf p.1 p.2, t p.1))
    (by rw [eC])
    (by intro p hp; simp only [List.mem_map] at hp; obtain ⟨q, hq, rfl⟩ := hp; exact hK q hq)
    (by rw [eB]; exact hkr)
  rw [eA] at this; exact this

end Zlib.Trees.HuffmanAbstract

#print axioms Zlib.Trees.HuffmanAbstract.kraft_eq
#print axioms Zlib.Trees.HuffmanAbstract.merges_opt_forest
#print axioms Zlib.Trees.HuffmanAbstract.merges_optimal
