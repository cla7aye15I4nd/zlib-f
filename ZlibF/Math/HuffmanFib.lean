import ZlibF.Math.HuffmanTree

/-!
Pure Huffman mathematics adapted from the pinned zlib-formal reference
`0f1428677ebf5b1614ff77f4702bbb382b2bf3c6`; see docs/history/references.md.
The mathematical statements and proof bodies are retained. Imports use this
project. No result here alone establishes refinement of the translated C.
-/

/-!
# Fibonacci depth bound of the abstract Huffman merge (`FibPlus`)

The reference overlay analysis, §7.2, Lemmas 1–2. A leaf of weight `w` at depth `d` in a tree that
the merge loop builds (`Merges`) satisfies `w·F(d+1) + F(d) ≤ W` when all weights are
positive (`fibPlus_of_merges`). The same fact is also given on a bare ancestor chain
(`fibChain_bound`), which the refinement proof applies directly to the C heap layout.

The proofs use only the `Freq` part of `smaller`: each merge removes two nodes of least
weight.
-/

namespace Zlib.Trees.HuffmanAbstract
open HTree

/-! ## Fibonacci numbers -/

theorem fib_zero : fib 0 = 0 := rfl
theorem fib_one : fib 1 = 1 := rfl
theorem fib_two : fib 2 = 1 := rfl

theorem fib_succ_eq (n : Nat) : fib (n + 1) = (fibPair n).2 := rfl

theorem fib_add_two (n : Nat) : fib (n + 2) = fib n + fib (n + 1) := rfl

theorem fib_le_succ : ∀ n, fib n ≤ fib (n + 1)
  | 0 => by decide
  | n + 1 => by rw [fib_add_two]; omega

theorem fib_mono {m n : Nat} (h : m ≤ n) : fib m ≤ fib n := by
  induction n with
  | zero => have : m = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ n ih =>
    rcases Nat.lt_or_ge m (n + 1) with h' | h'
    · exact Nat.le_trans (ih (by omega)) (fib_le_succ n)
    · have : m = n + 1 := by omega
      subst this; exact Nat.le_refl _

theorem fib_pos {n : Nat} (h : 1 ≤ n) : 1 ≤ fib n :=
  Nat.le_trans (by decide : 1 ≤ fib 1) (fib_mono h)

/-- `g w d = w·F(d+1) + F(d)`, the least possible weight above a leaf of weight `w` at
depth `d`. -/
def gF (w d : Nat) : Nat := w * fib (d + 1) + fib d

theorem gF_zero (w : Nat) : gF w 0 = w := by simp [gF, fib_zero, fib_one]
theorem gF_one (w : Nat) : gF w 1 = w + 1 := by simp [gF, fib_two, fib_one]
theorem gF_add_two (w d : Nat) : gF w (d + 2) = gF w d + gF w (d + 1) := by
  simp only [gF, fib_add_two]; rw [Nat.mul_add]; omega

/-! ## Lemma 2 on an ancestor chain -/

/-- **Lemma 2 on an ancestor chain** (the reference overlay analysis §7.2). Take a leaf of weight `w`
with ancestors `a_0 = leaf, …, a_δ`, weights `p i = w(a_i)`, and siblings `b_i` of `a_i`
with weights `s i`. Assume `p (i+1) = p i + s i`, `s 0 ≥ 1`, and `s (i+1) ≥ p i`. The last
holds because the sibling `b_{i+1}` of `a_{i+1}` is removed after `a_i` (Lemma 1(c)). Then
`w·F(δ+1) + F(δ) ≤ p δ`. -/
theorem fibChain_bound (p s : Nat → Nat) (w δ : Nat) (h0 : p 0 = w)
    (hstep : ∀ i, i < δ → p (i + 1) = p i + s i) (hs0 : 0 < δ → 1 ≤ s 0)
    (hs : ∀ i, i + 1 < δ → p i ≤ s (i + 1)) :
    w * fib (δ + 1) + fib δ ≤ p δ := by
  have key : ∀ i, i ≤ δ → gF w i ≤ p i ∧ (i + 1 ≤ δ → gF w (i + 1) ≤ p (i + 1)) := by
    intro i
    induction i with
    | zero =>
      intro _
      refine ⟨by rw [gF_zero, h0]; exact Nat.le_refl _, fun h1 => ?_⟩
      rw [gF_one, hstep 0 (by omega), h0]; have := hs0 (by omega); omega
    | succ i ih =>
      intro hi
      have ⟨h1, h2⟩ := ih (by omega)
      refine ⟨h2 hi, fun h3 => ?_⟩
      rw [gF_add_two, hstep (i + 1) (by omega)]
      have := hs i (by omega); have := h2 hi; omega
  exact (key δ (Nat.le_refl _)).1

/-! ## Lemma 2 on the tree model -/

/-- Every leaf weight is at least 1, so every subtree weighs at least 1. -/
def PosT : HTree → Prop
  | leaf _ w => 1 ≤ w
  | node a b => PosT a ∧ PosT b

/-- The **sibling property**. At every node `node a b`, each son of `a` weighs at most `b`,
and each son of `b` weighs at most `a`. In a merge tree the sibling of a parent was removed
no earlier than the child (Lemma 1(c)). -/
def SibOK : HTree → Prop
  | leaf _ _ => True
  | node a b => SibOK a ∧ SibOK b ∧ (∀ c ∈ a.sons, c.weight ≤ b.weight) ∧
      (∀ c ∈ b.sons, c.weight ≤ a.weight)

theorem PosT.weight_pos : ∀ {t : HTree}, PosT t → 1 ≤ t.weight
  | leaf _ _, h => h
  | node a _, h => by have := PosT.weight_pos h.1; simp only [weight]; omega

theorem mem_leaves_node {a b : HTree} {x : LeafInfo} :
    x ∈ (node a b).leaves ↔ ∃ y, (y ∈ a.leaves ∨ y ∈ b.leaves) ∧ x = ⟨y.sym, y.w, y.d + 1⟩ := by
  simp only [leaves, List.mem_map, List.mem_append]
  constructor
  · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩

theorem weight_of_depth_zero : ∀ {t : HTree} {x : LeafInfo}, x ∈ t.leaves → x.d = 0 → t.weight = x.w
  | leaf s w, x, hx, _ => by
    simp only [leaves, List.mem_singleton] at hx; subst hx; rfl
  | node a b, x, hx, hd => by
    obtain ⟨y, _, rfl⟩ := mem_leaves_node.mp hx; simp at hd

/-- One side of the node case: the leaf lies under son `a`, whose sibling is `b`. -/
theorem gF_le_side (d : Nat)
    (ih : ∀ e, e < d + 2 → ∀ (t : HTree) (x : LeafInfo), SibOK t → PosT t → x ∈ t.leaves →
      x.d = e → gF x.w e ≤ t.weight)
    (a b : HTree) (hSa : SibOK a) (hPa : PosT a) (hsons : ∀ c ∈ a.sons, c.weight ≤ b.weight)
    (y : LeafInfo) (hy : y ∈ a.leaves) (hyd : y.d = d + 1) :
    gF y.w (d + 2) ≤ a.weight + b.weight := by
  cases a with
  | leaf s w =>
    simp only [leaves, List.mem_singleton] at hy; subst hy; simp at hyd
  | node a1 a2 =>
    obtain ⟨z, hz, rfl⟩ := mem_leaves_node.mp hy
    simp only at hyd ⊢
    have hzd : z.d = d := by omega
    have h1 := ih (d + 1) (by omega) _ _ hSa hPa hy (by simp [hzd])
    simp only at h1
    rw [gF_add_two]
    rcases hz with hz | hz
    · have h2 := ih d (by omega) a1 z hSa.1 hPa.1 hz hzd
      have h3 := hsons a1 (by simp [sons])
      omega
    · have h2 := ih d (by omega) a2 z hSa.2.1 hPa.2 hz hzd
      have h3 := hsons a2 (by simp [sons])
      omega

/-- **Lemma 2 (tree form).** In a tree with the sibling property and positive weights, a
leaf of weight `w` at depth `d` has `w·F(d+1) + F(d) ≤ weight`. -/
theorem gF_le_weight : ∀ (d : Nat) (t : HTree) (x : LeafInfo), SibOK t → PosT t → x ∈ t.leaves →
    x.d = d → gF x.w d ≤ t.weight := by
  intro d
  induction d using Nat.strongRecOn with
  | ind d ih =>
    intro t x hS hP hx hd
    match d, t with
    | 0, t => rw [gF_zero, weight_of_depth_zero hx hd]; exact Nat.le_refl _
    | _ + 1, leaf s w =>
      simp only [leaves, List.mem_singleton] at hx; subst hx; simp at hd
    | 1, node a b =>
      obtain ⟨y, hy, rfl⟩ := mem_leaves_node.mp hx
      simp only at hd ⊢
      rw [gF_one]; simp only [weight]
      rcases hy with hy | hy
      · rw [weight_of_depth_zero hy (by omega)]; have := PosT.weight_pos hP.2; omega
      · rw [weight_of_depth_zero hy (by omega)]; have := PosT.weight_pos hP.1; omega
    | d + 2, node a b =>
      obtain ⟨y, hy, rfl⟩ := mem_leaves_node.mp hx
      simp only at hd ⊢; simp only [weight]
      rcases hy with hy | hy
      · exact gF_le_side d ih a b hS.1 hP.1 hS.2.2.1 y hy (by omega)
      · have := gF_le_side d ih b a hS.2.1 hP.2 hS.2.2.2 y hy (by omega); omega

/-! ## Lemma 1: the merge loop keeps the sibling property -/

theorem smaller_weight {a b : HTree} (h : smaller a b) : a.weight ≤ b.weight := by
  rcases h with h | ⟨h, _⟩ <;> omega

/-- Forest invariant of the merge loop. Every tree has the sibling property and positive
weights, and every son of a tree in the forest weighs at most every tree in the forest:
nodes removed earlier are no heavier than nodes still in the heap (Lemma 1(a)). -/
def FInv (s : List HTree) : Prop :=
  (∀ X ∈ s, SibOK X ∧ PosT X) ∧ ∀ X ∈ s, ∀ c ∈ X.sons, ∀ Y ∈ s, c.weight ≤ Y.weight

theorem FInv.step {s s' : List HTree} {n m : HTree} (hst : Step s s' n m) (hI : FInv s) : FInv s' := by
  obtain ⟨r, hp, hn, hm, rfl⟩ := hst
  have mem : ∀ x, x ∈ s ↔ x ∈ n :: m :: r := fun x => hp.mem_iff
  have hn_s : n ∈ s := (mem n).2 (by simp)
  have hm_s : m ∈ s := (mem m).2 (by simp)
  have hr_s : ∀ x ∈ r, x ∈ s := fun x hx => (mem x).2 (by simp [hx])
  obtain ⟨hA, hB⟩ := hI
  have hnw : ∀ x ∈ r, n.weight ≤ x.weight := fun x hx => smaller_weight (hn x (by simp [hx]))
  have hmw : ∀ x ∈ r, m.weight ≤ x.weight := fun x hx => smaller_weight (hm x hx)
  refine ⟨?_, ?_⟩
  · intro X hX
    simp only [List.mem_cons] at hX
    rcases hX with rfl | hX
    · refine ⟨⟨(hA n hn_s).1, (hA m hm_s).1, ?_, ?_⟩, (hA n hn_s).2, (hA m hm_s).2⟩
      · intro c hc; exact hB n hn_s c hc m hm_s
      · intro c hc; exact hB m hm_s c hc n hn_s
    · exact hA X (hr_s X hX)
  · intro X hX c hc Y hY
    simp only [List.mem_cons] at hX hY
    rcases hX with rfl | hX
    · simp only [sons, List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with rfl | rfl
      · rcases hY with rfl | hY
        · simp only [weight]; omega
        · exact hnw Y hY
      · rcases hY with rfl | hY
        · simp only [weight]; omega
        · exact hmw Y hY
    · rcases hY with rfl | hY
      · have := hB X (hr_s X hX) c hc n hn_s; simp only [weight]; omega
      · exact hB X (hr_s X hX) c hc Y (hr_s Y hY)

theorem FInv.merges {s tr : List HTree} {T : HTree} (h : Merges s tr T) (hI : FInv s) :
    SibOK T ∧ PosT T := by
  induction h with
  | done t => exact hI.1 t (by simp)
  | step hst _ ih => exact ih (hI.step hst)

theorem FInv.init (syms : List (Nat × Nat)) (hpos : ∀ p ∈ syms, 1 ≤ p.2) :
    FInv (initForest syms) := by
  refine ⟨?_, ?_⟩
  · intro X hX
    simp only [initForest, List.mem_map] at hX
    obtain ⟨p, hp, rfl⟩ := hX
    exact ⟨trivial, hpos p hp⟩
  · intro X hX c hc
    simp only [initForest, List.mem_map] at hX
    obtain ⟨p, _, rfl⟩ := hX
    simp [sons] at hc

/-- **`FibPlus` for the abstract merge** (the reference overlay analysis §7.2, Lemma 2). If every
symbol weight is at least 1, every leaf `x` of the tree a merge run builds satisfies
`x.w · F(x.d + 1) + F(x.d) ≤ W`, with `W = T.weight` the total weight. -/
theorem fibPlus_of_merges {syms : List (Nat × Nat)} {tr : List HTree} {T : HTree}
    (h : Merges (initForest syms) tr T) (hpos : ∀ p ∈ syms, 1 ≤ p.2) :
    ∀ x ∈ T.leaves, x.w * fib (x.d + 1) + fib x.d ≤ T.weight := by
  have ⟨hS, hP⟩ := (FInv.init syms hpos).merges h
  intro x hx
  exact gF_le_weight x.d T x hS hP hx rfl

/-- Every leaf of a positive tree has weight at least 1. -/
theorem PosT.leaf_w : ∀ {t : HTree}, PosT t → ∀ x ∈ t.leaves, 1 ≤ x.w
  | leaf s w, h, x, hx => by simp only [leaves, List.mem_singleton] at hx; subst hx; exact h
  | node a b, h, x, hx => by
    obtain ⟨y, hy, rfl⟩ := mem_leaves_node.mp hx
    rcases hy with hy | hy
    · exact PosT.leaf_w h.1 y hy
    · exact PosT.leaf_w h.2 y hy

/-- **No overflow below `F(L+3)`.** If the total weight is below `F(L+3)`, every leaf
depth is at most `L`. For `L = 15`, `F(18) = 2584`. -/
theorem depth_le_of_merges {syms : List (Nat × Nat)} {tr : List HTree} {T : HTree}
    (h : Merges (initForest syms) tr T) (hpos : ∀ p ∈ syms, 1 ≤ p.2) (L : Nat)
    (hW : T.weight < fib (L + 3)) : ∀ x ∈ T.leaves, x.d ≤ L := by
  have ⟨_, hP⟩ := (FInv.init syms hpos).merges h
  intro x hx
  have h1 := fibPlus_of_merges h hpos x hx
  have hw := PosT.leaf_w hP x hx
  refine Nat.le_of_not_lt fun hlt => ?_
  have h2 : fib (x.d + 1) ≤ x.w * fib (x.d + 1) := Nat.le_mul_of_pos_left _ hw
  have h3 : fib (L + 3) ≤ fib (x.d + 2) := fib_mono (by omega)
  have h4 := fib_add_two x.d
  omega

end Zlib.Trees.HuffmanAbstract
