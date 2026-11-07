import ZlibF.Proof.«trees.c.heap.ord»
import ZlibF.Proof.«trees.c.heap.gbmath»

/-!
# Finite permutations of binary-heap entries

The existing `PermOn` and finite-range pigeonhole theorem are reused here.
These lemmas concern functions and bounded indices; they do not execute or
modify a heap.
-/

namespace Zlib.Trees.Proofs

/-- Compose permutations of the same populated heap interval. -/
theorem PermOn.trans' {A B D : Nat → Int32} {len : Nat}
    (h1 : PermOn A B len) (h2 : PermOn B D len) : PermOn A D len := by
  obtain ⟨σ, hr, hi, he⟩ := h1
  obtain ⟨τ, hr', hi', he'⟩ := h2
  refine ⟨τ ∘ σ, fun i a b => hr' _ (hr i a b).1 (hr i a b).2,
    fun i i' a b c d e => ?_, fun i a b => ?_⟩
  · exact hi i i' a b c d (hi' _ _ (hr i a b).1 (hr i a b).2 (hr i' c d).1 (hr i' c d).2 e)
  · simp only [Function.comp]; rw [he i a b, he' _ (hr i a b).1 (hr i a b).2]

/-- A bounded injective reindexing also preserves every old entry. -/
theorem PermOn.preimage {A H : Nat → Int32} {len : Nat} (hp : PermOn A H len)
    (i : Nat) (hi1 : 1 ≤ i) (hi2 : i ≤ len) :
    ∃ j : Nat, 1 ≤ j ∧ j ≤ len ∧ A j = H i := by
  obtain ⟨σ, hr, hj, he⟩ := hp
  let P : Nat → Nat := fun q => σ (q + 1) - 1
  have hP : ∀ q < len, P q < len := by
    intro q hq
    have := hr (q + 1) (by omega) (by omega)
    dsimp only [P]; omega
  have hPi : ∀ q q', q < len → q' < len → P q = P q' → q = q' := by
    intro q q' hq hq' heq
    have ha := hr (q + 1) (by omega) (by omega)
    have hb := hr (q' + 1) (by omega) (by omega)
    have hs : σ (q + 1) = σ (q' + 1) := by dsimp only [P] at heq; omega
    have := hj (q + 1) (q' + 1) (by omega) (by omega) (by omega) (by omega) hs
    omega
  obtain ⟨q, hq, heq⟩ := GB.inj_surj P len hP hPi (i - 1) (by omega)
  refine ⟨q + 1, by omega, by omega, ?_⟩
  rw [he (q + 1) (by omega) (by omega)]
  have := hr (q + 1) (by omega) (by omega)
  have hs : σ (q + 1) = i := by dsimp only [P] at heq; omega
  rw [hs]

/-- Every populated entry is above the root in the comparison preorder. -/
theorem HeapOK.root_min {key : Int32 → Int32 → Bool} {H : Nat → Int32} {len : Nat}
    (hk : KeyOK key) (ho : HeapOK key H len 0) :
    ∀ q, 1 ≤ q → q ≤ len → key (H 1) (H q) = true := by
  intro q
  induction q using Nat.strongRecOn with
  | _ q ih =>
    intro hq1 hq2
    by_cases heq : q = 1
    · subst q
      rcases hk.total (H 1) (H 1) with h | h <;> exact h
    · have hq : 2 ≤ q := by omega
      have hp : key (H 1) (H (q / 2)) = true :=
        ih (q / 2) (by omega) (by omega) (by omega)
      exact hk.trans _ _ _ hp (ho q hq hq2 (by omega))

end Zlib.Trees.Proofs
