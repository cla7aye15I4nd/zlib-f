import ZlibF.Proof.«trees.c.heap.base»

/-!
# Binary heaps ordered by `smaller` (pure)

Migrated from the earlier attempt (its `Spec/trees/Build.lean`), unchanged except for the namespace. The heap is
`heap[1 .. heap_len]` (children of `p` are `2p`, `2p+1`), ordered by zlib's `smaller` macro: `key a b` iff
`Freq[a] < Freq[b]`, or equal frequencies and `depth[a] ≤ depth[b]` (a total preorder). `HeapOK key H len k`: the
heap property holds for every parent `> k`; `HoleInv` is the invariant of the sift-down loop.
-/

namespace Zlib.Trees.Proofs

/-- zlib's `smaller(tree, n, m, depth)` on node values. -/
def smallerB (fr : Nat → UInt16) (dp : Nat → UInt8) (a b : Int32) : Bool :=
  decide (fr a.toInt.toNat < fr b.toInt.toNat) ||
    (fr a.toInt.toNat == fr b.toInt.toNat && decide (dp a.toInt.toNat ≤ dp b.toInt.toNat))

/-- A total preorder. -/
structure KeyOK (key : Int32 → Int32 → Bool) : Prop where
  total : ∀ a b, key a b = true ∨ key b a = true
  trans : ∀ a b c, key a b = true → key b c = true → key a c = true

theorem smallerB_ok (fr : Nat → UInt16) (dp : Nat → UInt8) : KeyOK (smallerB fr dp) := by
  constructor
  · intro a b
    simp only [smallerB, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq,
      UInt16.lt_iff_toNat_lt, ← UInt16.toNat_inj, UInt8.le_iff_toNat_le]
    omega
  · intro a b c
    simp only [smallerB, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq,
      UInt16.lt_iff_toNat_lt, ← UInt16.toNat_inj, UInt8.le_iff_toNat_le]
    omega

/-- Heap property for every parent `p > k` (in `1 .. len`). -/
def HeapOK (key : Int32 → Int32 → Bool) (H : Nat → Int32) (len k : Nat) : Prop :=
  ∀ c, 2 ≤ c → c ≤ len → k < c / 2 → key (H (c / 2)) (H c) = true

/-- `H'` on `1 .. len` is a permutation of `H` on `1 .. len`. -/
def PermOn (H' H : Nat → Int32) (len : Nat) : Prop :=
  ∃ σ : Nat → Nat, (∀ i, 1 ≤ i → i ≤ len → 1 ≤ σ i ∧ σ i ≤ len) ∧
    (∀ i i', 1 ≤ i → i ≤ len → 1 ≤ i' → i' ≤ len → σ i = σ i' → i = i') ∧
    ∀ i, 1 ≤ i → i ≤ len → H' i = H (σ i)

theorem PermOn.refl (H : Nat → Int32) (len : Nat) : PermOn H H len :=
  ⟨id, fun i a b => ⟨a, b⟩, fun i i' _ _ _ _ e => e, fun _ _ _ => rfl⟩

/-- Swap positions `a`, `b`. -/
def swapAt (A : Nat → Int32) (a b : Nat) : Nat → Int32 :=
  fun i => if i = a then A b else if i = b then A a else A i

theorem PermOn.swap {A H : Nat → Int32} {len : Nat} (hp : PermOn A H len) {a b : Nat}
    (ha : 1 ≤ a ∧ a ≤ len) (hb : 1 ≤ b ∧ b ≤ len) : PermOn (swapAt A a b) H len := by
  obtain ⟨σ, hr, hi, he⟩ := hp
  let τ : Nat → Nat := fun i => if i = a then b else if i = b then a else i
  refine ⟨σ ∘ τ, ?_, ?_, ?_⟩
  · intro i h1 h2; simp only [Function.comp, τ]; split
    · exact hr b hb.1 hb.2
    · split
      · exact hr a ha.1 ha.2
      · exact hr i h1 h2
  · intro i i' h1 h2 h3 h4 e
    simp only [Function.comp, τ] at e
    have hτ : ∀ x, 1 ≤ x → x ≤ len → 1 ≤ τ x ∧ τ x ≤ len := by
      intro x h1 h2; simp only [τ]; split
      · exact hb
      · split
        · exact ha
        · exact ⟨h1, h2⟩
    have := hi _ _ (hτ i h1 h2).1 (hτ i h1 h2).2 (hτ i' h3 h4).1 (hτ i' h3 h4).2 e
    simp only [τ] at this
    split at this <;> split at this <;> (try split at this) <;> (try split at this) <;> omega
  · intro i h1 h2; simp only [Function.comp, τ, swapAt]; split
    · exact he b hb.1 hb.2
    · split
      · exact he a ha.1 ha.2
      · exact he i h1 h2

/-- Sift-down hole invariant: `A` is the array with the pending value at the
hole `K`; all parent/child pairs with parent `≥ k0` not touching `K` hold, and
the parent of the hole is `≤` the hole value and the hole's children. -/
def HoleInv (key : Int32 → Int32 → Bool) (A : Nat → Int32) (len k0 K : Nat) : Prop :=
  (∀ c, 2 ≤ c → c ≤ len → k0 ≤ c / 2 → c / 2 ≠ K → c ≠ K → key (A (c / 2)) (A c) = true) ∧
  (k0 < K → key (A (K / 2)) (A K) = true ∧
    ∀ c, c / 2 = K → 2 ≤ c → c ≤ len → key (A (K / 2)) (A c) = true)

theorem hole_init {key : Int32 → Int32 → Bool} {A : Nat → Int32} {len k0 : Nat}
    (h : HeapOK key A len k0) : HoleInv key A len k0 k0 :=
  ⟨fun c a b d e _ => h c a b (by omega), fun h => absurd h (Nat.lt_irrefl _)⟩

/-- `j'` is a minimal child of `K`. -/
def MinChild (key : Int32 → Int32 → Bool) (A : Nat → Int32) (len K j' : Nat) : Prop :=
  j' / 2 = K ∧ 2 ≤ j' ∧ j' ≤ len ∧ ∀ c, c / 2 = K → 2 ≤ c → c ≤ len → key (A j') (A c) = true

theorem hole_break {key : Int32 → Int32 → Bool} (hk : KeyOK key) {A : Nat → Int32} {len k0 K j' : Nat}
    (hK : 1 ≤ k0 ∧ k0 ≤ K) (hI : HoleInv key A len k0 K) (hm : MinChild key A len K j')
    (hv : key (A K) (A j') = true) : HeapOK key A len (k0 - 1) := by
  intro c h2 hl hp
  by_cases e1 : c / 2 = K
  · rw [e1]; exact hk.trans _ _ _ hv (hm.2.2.2 c e1 h2 hl)
  · by_cases e2 : c = K
    · subst e2; exact (hI.2 (by omega)).1
    · exact hI.1 c h2 hl (by omega) e1 e2

theorem hole_leaf {key : Int32 → Int32 → Bool} {A : Nat → Int32} {len k0 K : Nat}
    (hK : 1 ≤ k0 ∧ k0 ≤ K) (hI : HoleInv key A len k0 K) (hleaf : len < 2 * K) :
    HeapOK key A len (k0 - 1) := by
  intro c h2 hl hp
  by_cases e1 : c / 2 = K
  · omega
  · by_cases e2 : c = K
    · subst e2; exact (hI.2 (by omega)).1
    · exact hI.1 c h2 hl (by omega) e1 e2

theorem hole_step {key : Int32 → Int32 → Bool} (hk : KeyOK key) {A : Nat → Int32} {len k0 K j' : Nat}
    (hK : 1 ≤ k0 ∧ k0 ≤ K) (hI : HoleInv key A len k0 K) (hm : MinChild key A len K j')
    (hv : key (A K) (A j') = false) : HoleInv key (swapAt A K j') len k0 j' := by
  obtain ⟨hj2, hj2', hjl, hmin⟩ := hm
  have hjK : K < j' := by omega
  have hkey : key (A j') (A K) = true := by
    rcases hk.total (A K) (A j') with h | h
    · rw [hv] at h; cases h
    · exact h
  refine ⟨?_, ?_⟩
  · intro c h2 hl hp e1 e2
    simp only [swapAt]
    by_cases f1 : c / 2 = K
    · rw [ite_eq_left f1, ite_eq_right (by omega), ite_eq_right e2]
      exact hmin c f1 h2 hl
    · by_cases f2 : c = K
      · rw [ite_eq_right f1, ite_eq_right (by omega), ite_eq_left f2]
        subst f2
        exact (hI.2 (by omega)).2 j' hj2 hj2' hjl
      · rw [ite_eq_right f1, ite_eq_right e1, ite_eq_right f2, ite_eq_right e2]
        exact hI.1 c h2 hl hp f1 f2
  · intro _
    have hne : j' ≠ K := by omega
    refine ⟨?_, ?_⟩
    · simp only [swapAt, hj2, hne, ite_true, ite_false]; exact hkey
    · intro c hc h2 hl
      have n1 : c ≠ K := by omega
      have n2 : c ≠ j' := by omega
      simp only [swapAt, hj2, n1, n2, ite_true, ite_false]
      have := hI.1 c h2 hl (by omega) (by omega) n1; rwa [hc] at this

end Zlib.Trees.Proofs
