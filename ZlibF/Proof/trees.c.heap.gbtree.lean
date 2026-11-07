import ZlibF.Proof.«trees.c.heap.gbmath»

/-!
# The tree layout of `build_tree` and its clamped depths (pure)

`PShape H hm J elems maxc` is the layout `build_tree` leaves in
`heap[hm .. HEAP_SIZE)`; `Clamped … cl` says `cl` is the clamped depth that the
first pass of `gen_bitlen` computes. Proved: the clamped Kraft identity
(`kraft_clamped`), `bl_count[L] = exact + overflow/2` (`blC_top`), some node has
exact depth `L` when `overflow > 0` (`exactC_pos`), and the fix-up round facts.
-/

namespace Zlib.Trees.Proofs.GB

/-- The `Dad` of the node at heap position `p`: positions `572-2j` and `571-2j`
hold the two children of node `elems + j`. -/
def dadP (elems p : Nat) : Nat := elems + (572 - p) / 2

/-- Pure shape of the tree that `build_tree` leaves in `heap[hm .. 573)`: `J ≥ 1`
internal nodes `elems .. elems+J-1`, root `elems+J-1` at `hm = 572 - 2J`, node
`elems+j` placed below its children `572-2j`, `571-2j`, all other entries symbols
`≤ maxc < elems`, all entries distinct. -/
structure PShape (H : Nat → Nat) (hm J elems maxc : Nat) : Prop where
  hm_eq : hm + 2 * J + 1 = 573
  J1 : 1 ≤ J
  maxc_lt : maxc < elems
  inj : ∀ q q', hm ≤ q → q < 573 → hm ≤ q' → q' < 573 → H q = H q' → q = q'
  kind : ∀ q, hm ≤ q → q < 573 → H q ≤ maxc ∨ (elems ≤ H q ∧ H q < elems + J)
  root : H hm = elems + J - 1
  appears : ∀ j < J, ∃ q, hm ≤ q ∧ q < 571 - 2 * j ∧ H q = elems + j

/-- `cl` is the clamped depth: `0` at the root, `min (cl dad + 1) L` elsewhere. -/
structure Clamped (H : Nat → Nat) (hm J elems L : Nat) (cl : Nat → Nat) : Prop where
  root : cl (H hm) = 0
  step : ∀ i < 2 * J, cl (H (hm + 1 + i)) = min (cl (dadP elems (hm + 1 + i)) + 1) L

section tree
variable {H : Nat → Nat} {hm J elems maxc L : Nat} {cl : Nat → Nat}

theorem PShape.dadP_eq (S : PShape H hm J elems maxc) (i : Nat) (hi : i < 2 * J) :
    dadP elems (hm + 1 + i) = elems + (2 * J - 1 - i) / 2 := by
  have := S.hm_eq; unfold dadP; congr 2; omega

theorem Clamped.le_all (S : PShape H hm J elems maxc) (C : Clamped H hm J elems L cl) (q : Nat)
    (h1 : hm ≤ q) (h2 : q < 573) : cl (H q) ≤ L := by
  by_cases e : q = hm
  · subst e; rw [C.root]; omega
  · have := C.step (q - hm - 1) (by have := S.hm_eq; omega)
    rw [show hm + 1 + (q - hm - 1) = q by omega] at this
    rw [this]; exact Nat.min_le_right _ _

theorem Clamped.dad_le (S : PShape H hm J elems maxc) (C : Clamped H hm J elems L cl) (i : Nat)
    (hi : i < 2 * J) : cl (dadP elems (hm + 1 + i)) ≤ L := by
  rw [S.dadP_eq i hi]
  obtain ⟨q, h1, h2, e⟩ := S.appears ((2 * J - 1 - i) / 2) (by omega)
  rw [← e]; exact C.le_all S q h1 (by omega)

/-- The internal nodes, counted through the heap positions, are `elems .. elems+J-1`. -/
theorem PShape.internal_sum (S : PShape H hm J elems maxc) (F : Nat → Nat) :
    rs (fun i => if elems ≤ H (hm + i) then F (H (hm + i)) else 0) (2 * J + 1) =
      rs (fun j => F (elems + j)) J := by
  have hm_eq := S.hm_eq
  have hP : ∀ i < 2 * J + 1, H (hm + i) < elems + J := by
    intro i hi
    rcases S.kind (hm + i) (by omega) (by omega) with h | h
    · have := S.maxc_lt; omega
    · exact h.2
  have := rs_image (fun i => H (hm + i)) (fun v => if elems ≤ v then F v else 0) (2 * J + 1) (elems + J) hP
  rw [this, rs_split]
  rw [rs_eq_zero (fun v hv => by rw [ite_eq_right (by omega), Nat.mul_zero])]
  rw [Nat.zero_add]
  apply rs_congr
  intro j hj
  rw [ite_eq_left (by omega)]
  obtain ⟨q, h1, h2, e⟩ := S.appears j hj
  have c1 := cnt_pos (P := fun i => H (hm + i)) (m := 2 * J + 1) (i := q - hm) (by omega)
    (by show H (hm + (q - hm)) = _; rw [show hm + (q - hm) = q by omega, e])
  have c2 := cnt_le_one (fun i => H (hm + i)) (2 * J + 1) (elems + j)
    (fun a b ha hb e => by have := S.inj (hm + a) (hm + b) (by omega) (by omega) (by omega) (by omega) e; omega)
  rw [show cnt (fun i => H (hm + i)) (2 * J + 1) (elems + j) = 1 by omega, Nat.one_mul]

/-- Weight of one open child slot below a node of clamped depth `x` (scaled by `2^(L+1)`). -/
def slot (L x : Nat) : Nat := if x < L then 2 ^ (L - x) else 1

theorem local_leaf (L d : Nat) (hL : 1 ≤ L) (hd : d ≤ L) :
    2 * 2 ^ (L - min (d + 1) L) = slot L d + ind (d = L) := by
  by_cases e : d = L
  · rw [show min (d + 1) L = L by omega]
    unfold slot ind
    rw [ite_eq_right (show ¬ d < L by omega), ite_eq_left e, Nat.sub_self]
  · rw [show min (d + 1) L = d + 1 by omega]
    unfold slot ind
    rw [ite_eq_left (show d < L by omega), ite_eq_right e]
    rw [show L - d = (L - (d + 1)) + 1 by omega, Nat.pow_succ]; omega

theorem local_int (L d : Nat) (hL : 1 ≤ L) (hd : d ≤ L) :
    2 * slot L (min (d + 1) L) = slot L d + ind (d = L) := by
  by_cases e : d = L
  · rw [show min (d + 1) L = L by omega]
    unfold slot ind
    rw [ite_eq_right (Nat.lt_irrefl _), ite_eq_right (show ¬ d < L by omega), ite_eq_left e]
  · by_cases e2 : d + 1 = L
    · rw [show min (d + 1) L = L by omega]
      unfold slot ind
      rw [ite_eq_right (Nat.lt_irrefl _), ite_eq_left (show d < L by omega), ite_eq_right e, show L - d = 1 by omega]
    · rw [show min (d + 1) L = d + 1 by omega]
      unfold slot ind
      rw [ite_eq_left (show d + 1 < L by omega), ite_eq_left (show d < L by omega), ite_eq_right e]
      rw [show L - d = (L - (d + 1)) + 1 by omega, Nat.pow_succ]; omega

/-- Clamped Kraft sum of the leaves, scaled by `2^L`. -/
def kraftC (H : Nat → Nat) (hm J maxc L : Nat) (cl : Nat → Nat) : Nat :=
  rs (fun i => if H (hm + 1 + i) ≤ maxc then 2 ^ (L - cl (H (hm + 1 + i))) else 0) (2 * J)

/-- Number of nodes whose (clamped) parent depth is already `L`: `gen_bitlen`'s `overflow`. -/
def ovfC (H : Nat → Nat) (hm J elems L : Nat) (cl : Nat → Nat) : Nat :=
  rs (fun i => if cl (dadP elems (hm + 1 + i)) = L then 1 else 0) (2 * J)

theorem PShape.internal_tail (S : PShape H hm J elems maxc) (C : Clamped H hm J elems L cl) (F : Nat → Nat) :
    F 0 + rs (fun i => if elems ≤ H (hm + 1 + i) then F (cl (H (hm + 1 + i))) else 0) (2 * J) =
      rs (fun j => F (cl (elems + j))) J := by
  have hint := S.internal_sum (fun v => F (cl v))
  rw [show 2 * J + 1 = 1 + 2 * J by omega, rs_split] at hint
  simp only [rs_succ, rs_zero, Nat.add_zero, Nat.zero_add] at hint
  rw [S.root, ite_eq_left (by have := S.J1; omega)] at hint
  rw [show elems + J - 1 = H hm by rw [S.root], C.root] at hint
  rw [← hint]
  congr 1
  apply rs_congr; intro i _; rw [Nat.add_assoc]

/-- **Clamped Kraft identity.** `2 · Σ_leaves 2^(L - cl) = 2^(L+1) + overflow`. -/
theorem kraft_clamped (S : PShape H hm J elems maxc) (C : Clamped H hm J elems L cl) (hL : 1 ≤ L) :
    2 * kraftC H hm J maxc L cl = 2 ^ (L + 1) + ovfC H hm J elems L cl := by
  have hm_eq := S.hm_eq
  have hloc : ∀ i < 2 * J,
      (if H (hm + 1 + i) ≤ maxc then 2 * 2 ^ (L - cl (H (hm + 1 + i))) else 0) +
        2 * (if elems ≤ H (hm + 1 + i) then slot L (cl (H (hm + 1 + i))) else 0) =
      slot L (cl (dadP elems (hm + 1 + i))) + (if cl (dadP elems (hm + 1 + i)) = L then 1 else 0) := by
    intro i hi
    have hd := C.dad_le S i hi
    rw [C.step i hi]
    have hk := S.kind (hm + 1 + i) (by omega) (by omega)
    have := S.maxc_lt
    by_cases hl : H (hm + 1 + i) ≤ maxc
    · rw [ite_eq_left hl, ite_eq_right (by omega)]
      have := local_leaf L _ hL hd; unfold ind at this; omega
    · rw [ite_eq_right hl, ite_eq_left (by omega)]
      have := local_int L _ hL hd; unfold ind at this; omega
  have hsum := rs_congr hloc
  rw [rs_add, rs_add, rs_mul] at hsum
  have hpair : rs (fun i => slot L (cl (dadP elems (hm + 1 + i)))) (2 * J) =
      2 * rs (fun j => slot L (cl (elems + j))) J := by
    rw [rs_congr (G := fun i => (fun j => slot L (cl (elems + j))) ((2 * J - 1 - i) / 2))
      (fun i hi => by simp only; rw [S.dadP_eq i hi])]
    exact rs_pair (fun j => slot L (cl (elems + j))) J
  have hint := S.internal_tail C (slot L)
  have hs0 : slot L 0 = 2 ^ L := by unfold slot; rw [ite_eq_left (show 0 < L by omega), Nat.sub_zero]
  rw [hs0] at hint
  have hleaf : rs (fun i => if H (hm + 1 + i) ≤ maxc then 2 * 2 ^ (L - cl (H (hm + 1 + i))) else 0) (2 * J) =
      2 * kraftC H hm J maxc L cl := by
    unfold kraftC; rw [← rs_mul]; apply rs_congr; intro i _; split <;> simp
  unfold ovfC
  rw [Nat.pow_succ]
  omega

/-- Nodes at exact depth `L`: their parent has clamped depth `L - 1`. -/
def exactC (H : Nat → Nat) (hm J elems L : Nat) (cl : Nat → Nat) : Nat :=
  rs (fun i => if cl (dadP elems (hm + 1 + i)) + 1 = L then 1 else 0) (2 * J)

/-- Leaves of clamped depth `b` (`bl_count[b]` after the first pass). -/
def blC (H : Nat → Nat) (hm J maxc : Nat) (cl : Nat → Nat) (b : Nat) : Nat :=
  rs (fun i => if H (hm + 1 + i) ≤ maxc ∧ cl (H (hm + 1 + i)) = b then 1 else 0) (2 * J)

/-- `bl_count[L] = #(nodes of exact depth L) + overflow / 2`, and `overflow` is even. -/
theorem blC_top (S : PShape H hm J elems maxc) (C : Clamped H hm J elems L cl) (hL : 1 ≤ L) :
    ovfC H hm J elems L cl % 2 = 0 ∧
    blC H hm J maxc cl L = exactC H hm J elems L cl + ovfC H hm J elems L cl / 2 := by
  have hm_eq := S.hm_eq
  have hloc : ∀ i < 2 * J,
      (if H (hm + 1 + i) ≤ maxc ∧ cl (H (hm + 1 + i)) = L then 1 else 0) +
        (if elems ≤ H (hm + 1 + i) then (if cl (H (hm + 1 + i)) = L then 1 else 0) else 0) =
      (if cl (dadP elems (hm + 1 + i)) + 1 = L then 1 else 0) +
        (if cl (dadP elems (hm + 1 + i)) = L then 1 else 0) := by
    intro i hi
    have hd := C.dad_le S i hi
    have hk := S.kind (hm + 1 + i) (by omega) (by omega)
    have := S.maxc_lt
    rw [C.step i hi]
    by_cases hl : H (hm + 1 + i) ≤ maxc
    · rw [ite_eq_right (show ¬ elems ≤ H (hm + 1 + i) by omega)]
      by_cases a : cl (dadP elems (hm + 1 + i)) + 1 = L
      · rw [ite_eq_left ⟨hl, by omega⟩, ite_eq_left a, ite_eq_right (by omega)]
      · by_cases b : cl (dadP elems (hm + 1 + i)) = L
        · rw [ite_eq_left ⟨hl, by omega⟩, ite_eq_right a, ite_eq_left b]
        · rw [ite_eq_right (fun h => by omega), ite_eq_right a, ite_eq_right b]
    · rw [ite_eq_right (fun h => hl h.1), ite_eq_left (by omega)]
      by_cases a : cl (dadP elems (hm + 1 + i)) + 1 = L
      · rw [ite_eq_left (by omega), ite_eq_left a, ite_eq_right (by omega)]
      · by_cases b : cl (dadP elems (hm + 1 + i)) = L
        · rw [ite_eq_left (by omega), ite_eq_right a, ite_eq_left b]
        · rw [ite_eq_right (by omega), ite_eq_right a, ite_eq_right b]
  have hsum := rs_congr hloc
  rw [rs_add, rs_add] at hsum
  have hpair : rs (fun i => if cl (dadP elems (hm + 1 + i)) = L then 1 else 0) (2 * J) =
      2 * rs (fun j => if cl (elems + j) = L then 1 else 0) J := by
    rw [rs_congr (G := fun i => (fun j => if cl (elems + j) = L then 1 else 0) ((2 * J - 1 - i) / 2))
      (fun i hi => by simp only; rw [S.dadP_eq i hi])]
    exact rs_pair (fun j => if cl (elems + j) = L then 1 else 0) J
  have hint := S.internal_tail C (fun x => if x = L then 1 else 0)
  rw [ite_eq_right (by omega), Nat.zero_add] at hint
  unfold blC exactC ovfC
  constructor <;> omega

/-- If some node overflows, some node has exact depth `L`. -/
theorem exactC_pos (S : PShape H hm J elems maxc) (C : Clamped H hm J elems L cl) (hL : 1 ≤ L)
    (hov : 0 < ovfC H hm J elems L cl) : 0 < exactC H hm J elems L cl := by
  have hm_eq := S.hm_eq
  have key0 : ∀ n i, i < n → i < 2 * J → cl (dadP elems (hm + 1 + i)) = L →
      ∃ i' < 2 * J, cl (dadP elems (hm + 1 + i')) + 1 = L := by
    intro n
    induction n with
    | zero => intro i hi; omega
    | succ n ihn =>
      intro i hin hi hcl
      have ih : ∀ i', i' < i → i' < 2 * J → cl (dadP elems (hm + 1 + i')) = L →
          ∃ i' < 2 * J, cl (dadP elems (hm + 1 + i')) + 1 = L :=
        fun i' h1 => ihn i' (by omega)
      rw [S.dadP_eq i hi] at hcl
      obtain ⟨q, h1, h2, e⟩ := S.appears ((2 * J - 1 - i) / 2) (by omega)
      rw [← e] at hcl
      have hq : q ≠ hm := by intro e'; subst e'; rw [C.root] at hcl; omega
      obtain ⟨i', rfl⟩ : ∃ i', q = hm + 1 + i' := ⟨q - hm - 1, by omega⟩
      have hq' : i' < i := by omega
      have := C.step i' (by omega)
      rw [hcl] at this
      have hd := C.dad_le S i' (by omega)
      by_cases a : cl (dadP elems (hm + 1 + i')) + 1 = L
      · exact ⟨i', by omega, a⟩
      · exact ih i' hq' (by omega) (by omega)
  obtain ⟨i, hi, hcl⟩ : ∃ i < 2 * J, cl (dadP elems (hm + 1 + i)) = L := by
    by_cases hx : ∃ i < 2 * J, cl (dadP elems (hm + 1 + i)) = L
    · exact hx
    · have := rs_eq_zero (F := fun i => if cl (dadP elems (hm + 1 + i)) = L then 1 else 0) (n := 2 * J)
        (fun i hi => by rw [ite_eq_right (fun e => hx ⟨i, hi, e⟩)])
      unfold ovfC at hov; omega
  obtain ⟨i', hi', e'⟩ := key0 (i + 1) i (by omega) hi hcl
  have := le_rs (F := fun i => if cl (dadP elems (hm + 1 + i)) + 1 = L then 1 else 0) hi'
  simp only [e', ite_true] at this
  unfold exactC; omega

/-- No leaf has clamped depth `0`. -/
theorem blC_zero (S : PShape H hm J elems maxc) (C : Clamped H hm J elems L cl) (hL : 1 ≤ L) :
    blC H hm J maxc cl 0 = 0 := by
  unfold blC
  apply rs_eq_zero; intro i hi
  rw [ite_eq_right]; rintro ⟨-, e⟩; rw [C.step i hi] at e; omega

theorem blC_high (S : PShape H hm J elems maxc) (C : Clamped H hm J elems L cl) (b : Nat) (hb : L < b) :
    blC H hm J maxc cl b = 0 := by
  have hm_eq := S.hm_eq
  unfold blC
  apply rs_eq_zero; intro i hi
  rw [ite_eq_right]; rintro ⟨-, e⟩; have := C.le_all S (hm + 1 + i) (by omega) (by omega); omega

/-- The clamped Kraft sum regrouped by length. -/
theorem kraftC_eq (S : PShape H hm J elems maxc) (C : Clamped H hm J elems L cl) :
    kraftC H hm J maxc L cl = rs (fun b => blC H hm J maxc cl b * 2 ^ (L - b)) (L + 1) := by
  have hm_eq := S.hm_eq
  unfold kraftC blC
  exact rs_regroup (fun i => H (hm + 1 + i) ≤ maxc) (fun i => cl (H (hm + 1 + i))) (fun b => 2 ^ (L - b))
    (2 * J) (L + 1) (fun i hi _ => by have := C.le_all S (hm + 1 + i) (by omega) (by omega); omega)

/-- Number of leaves. -/
def nLeaves (H : Nat → Nat) (hm J maxc : Nat) : Nat :=
  rs (fun i => if H (hm + 1 + i) ≤ maxc then 1 else 0) (2 * J)

theorem blC_total (S : PShape H hm J elems maxc) (C : Clamped H hm J elems L cl) :
    rs (fun b => blC H hm J maxc cl b) (L + 1) = nLeaves H hm J maxc := by
  have hm_eq := S.hm_eq
  have := rs_regroup (fun i => H (hm + 1 + i) ≤ maxc) (fun i => cl (H (hm + 1 + i))) (fun _ => 1)
    (2 * J) (L + 1) (fun i hi _ => by have := C.le_all S (hm + 1 + i) (by omega) (by omega); omega)
  unfold nLeaves blC
  rw [this]; apply rs_congr; intro b _; simp

/-- Summing over the leaves (by position) is summing over the symbols in the tree. -/
theorem PShape.leaf_sum (S : PShape H hm J elems maxc) (T : Nat → Prop) [DecidablePred T]
    (hT : ∀ v ≤ maxc, T v ↔ ∃ q, hm < q ∧ q < 573 ∧ H q = v) (F : Nat → Nat) :
    rs (fun i => if H (hm + 1 + i) ≤ maxc then F (H (hm + 1 + i)) else 0) (2 * J) =
      rs (fun v => if T v then F v else 0) (maxc + 1) := by
  have hm_eq := S.hm_eq
  have hlt := S.maxc_lt
  have hP : ∀ i < 2 * J, H (hm + 1 + i) < elems + J := by
    intro i hi
    rcases S.kind (hm + 1 + i) (by omega) (by omega) with h | h
    · omega
    · exact h.2
  have := rs_image (fun i => H (hm + 1 + i)) (fun v => if v ≤ maxc then F v else 0) (2 * J) (elems + J) hP
  rw [this, show elems + J = (maxc + 1) + (elems + J - (maxc + 1)) by omega, rs_split]
  rw [rs_eq_zero (F := fun i => cnt (fun i => H (hm + 1 + i)) (2 * J) (maxc + 1 + i) *
      (if maxc + 1 + i ≤ maxc then F (maxc + 1 + i) else 0)) (fun v _ => by rw [ite_eq_right (by omega), Nat.mul_zero]),
    Nat.add_zero]
  apply rs_congr
  intro v hv
  rw [ite_eq_left (by omega)]
  have hinj : ∀ a b, a < 2 * J → b < 2 * J → H (hm + 1 + a) = H (hm + 1 + b) → a = b :=
    fun a b ha hb e => by
      have := S.inj (hm + 1 + a) (hm + 1 + b) (by omega) (by omega) (by omega) (by omega) e; omega
  have c2 := cnt_le_one (fun i => H (hm + 1 + i)) (2 * J) v hinj
  by_cases ht : T v
  · rw [ite_eq_left ht]
    obtain ⟨q, h1, h2, e⟩ := (hT v (by omega)).mp ht
    have c1 := cnt_pos (P := fun i => H (hm + 1 + i)) (m := 2 * J) (i := q - hm - 1) (by omega)
      (by show H (hm + 1 + (q - hm - 1)) = _; rw [show hm + 1 + (q - hm - 1) = q by omega, e])
    rw [show cnt (fun i => H (hm + 1 + i)) (2 * J) v = 1 by omega, Nat.one_mul]
  · rw [ite_eq_right ht]
    have : cnt (fun i => H (hm + 1 + i)) (2 * J) v = 0 := cnt_zero (fun i hi e =>
      ht ((hT v (by omega)).mpr ⟨hm + 1 + i, by omega, by omega, e⟩))
    rw [this, Nat.zero_mul]

theorem nLeaves_le (S : PShape H hm J elems maxc) : nLeaves H hm J maxc ≤ maxc + 1 := by
  classical
  have hl := S.leaf_sum (fun v => ∃ q, hm < q ∧ q < 573 ∧ H q = v) (fun _ _ => Iff.rfl) (fun _ => 1)
  unfold nLeaves
  rw [hl]
  have := rs_le (n := maxc + 1) (F := fun v => if (∃ q, hm < q ∧ q < 573 ∧ H q = v) then 1 else 0)
    (G := fun _ => 1) (fun v _ => by split <;> omega)
  rw [rs_const] at this; omega

end tree

/-! ## One round of the overflow fix-up -/

/-- Kraft sum of the counts `c b` (`b = 0 .. L`), scaled by `2^L`. -/
def kc (c : Nat → Nat) (L : Nat) : Nat := rs (fun b => c b * 2 ^ (L - b)) (L + 1)

theorem ind_mul (p : Prop) [Decidable p] (x : Nat) : ind p * x = if p then x else 0 := by
  unfold ind; split <;> simp

theorem rs_ind_eq (k n : Nat) (hk : k < n) : rs (fun x => ind (x = k)) n = 1 := by
  rw [rs_congr (F := fun x => ind (x = k)) (G := fun x => if x = k then 1 else 0) (fun x _ => rfl),
    rs_single, ite_eq_left hk]

/-- One round: `c[b]--`, `c[b+1] += 2`, `c[L]--` lowers the Kraft sum by one
and keeps the total. -/
theorem round_kraft (c c' : Nat → Nat) (L b : Nat) (hb : b + 1 ≤ L)
    (h : ∀ x ≤ L, c' x + ind (x = b) + ind (x = L) = c x + 2 * ind (x = b + 1)) :
    kc c' L + 1 = kc c L ∧ rs c' (L + 1) = rs c (L + 1) := by
  have e1 := rs_congr (n := L + 1) (F := fun x => (c' x + ind (x = b) + ind (x = L)) * 2 ^ (L - x))
    (G := fun x => (c x + 2 * ind (x = b + 1)) * 2 ^ (L - x)) (fun x hx => by rw [h x (by omega)])
  simp only [Nat.add_mul, Nat.mul_assoc] at e1
  rw [rs_add, rs_add, rs_add] at e1
  simp only [ind_mul] at e1
  rw [rs_single _ _ _, rs_single _ _ _, ite_eq_left (by omega), ite_eq_left (by omega)] at e1
  have e3 : rs (fun i => 2 * (if i = b + 1 then 2 ^ (L - i) else 0)) (L + 1) = 2 * 2 ^ (L - (b + 1)) := by
    rw [rs_mul, rs_single, ite_eq_left (by omega)]
  rw [e3] at e1
  have e4 : 2 ^ (L - b) = 2 * 2 ^ (L - (b + 1)) := by
    rw [show L - b = (L - (b + 1)) + 1 by omega, Nat.pow_succ]; omega
  rw [e4, Nat.sub_self, Nat.pow_zero] at e1
  refine ⟨by unfold kc; omega, ?_⟩
  have e2 := rs_congr (n := L + 1) (F := fun x => c' x + ind (x = b) + ind (x = L))
    (G := fun x => c x + 2 * ind (x = b + 1)) (fun x hx => h x (by omega))
  rw [rs_add, rs_add, rs_add, rs_mul] at e2
  rw [rs_ind_eq b _ (by omega), rs_ind_eq L _ (by omega), rs_ind_eq (b + 1) _ (by omega)] at e2
  omega

/-- While the Kraft sum exceeds `2^L` and there are at most `2^L` leaves, some
length `1 ≤ b < L` is in use. -/
theorem exists_short (c : Nat → Nat) (L R : Nat) (hR : 1 ≤ R) (hk : kc c L = 2 ^ L + R)
    (htot : rs c (L + 1) ≤ 2 ^ L) (h0 : c 0 = 0) : ∃ b, 1 ≤ b ∧ b < L ∧ c b ≠ 0 := by
  by_cases hx : ∃ b, 1 ≤ b ∧ b < L ∧ c b ≠ 0
  · exact hx
  · exfalso
    have z : rs (fun b => c b * 2 ^ (L - b)) L = 0 := rs_eq_zero (fun b hb => by
      by_cases e : b = 0
      · subst e; rw [h0, Nat.zero_mul]
      · have : c b = 0 := by
          by_cases e' : c b = 0
          · exact e'
          · exact absurd ⟨b, by omega, hb, e'⟩ hx
        rw [this, Nat.zero_mul])
    unfold kc at hk
    rw [rs_succ, z, Nat.sub_self, Nat.pow_zero, Nat.mul_one, Nat.zero_add] at hk
    have := le_rs (F := c) (n := L + 1) (i := L) (by omega)
    omega

end Zlib.Trees.Proofs.GB
