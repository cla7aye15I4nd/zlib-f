import ZlibF.Proof.«trees.c.heap.gbtree»

/-!
# Pure facts for the first pass of `gen_bitlen`

`clK H hm elems L k` is the clamped depth after `k` non-root positions were processed; `blP`, `ovP`, `costP` are
the counts the first pass has accumulated. Copied from the earlier attempt (`GenBitlenBase.lean`,
`GenBitlenPass1.lean`), unchanged except for the namespace.
-/

namespace Zlib.Trees.Proofs.GB

/-- Clamped depths after processing the first `k` non-root positions. -/
def clK (H : Nat → Nat) (hm elems L : Nat) : Nat → Nat → Nat
  | 0 => fun _ => 0
  | k + 1 => fun v => if v = H (hm + 1 + k) then min (clK H hm elems L k (dadP elems (hm + 1 + k)) + 1) L
      else clK H hm elems L k v

section cl
variable {H : Nat → Nat} {hm J elems maxc L : Nat}

theorem clK_stable (S : PShape H hm J elems maxc) (q k : Nat) (hq1 : hm ≤ q) (hq2 : q ≤ hm + k) :
    ∀ k', k ≤ k' → k' ≤ 2 * J → clK H hm elems L k' (H q) = clK H hm elems L k (H q) := by
  have := S.hm_eq
  intro k'
  induction k' with
  | zero => intro h1 _; rw [show k = 0 by omega]
  | succ k' ih =>
    intro h1 h2
    by_cases e : k = k' + 1
    · subst e; rfl
    · simp only [clK]; rw [if_neg (fun e' => by have := S.inj q (hm + 1 + k') hq1 (by omega) (by omega) (by omega) e'; omega)]
      exact ih (by omega) (by omega)

theorem dad_pos (S : PShape H hm J elems maxc) (i : Nat) (hi : i < 2 * J) :
    ∃ q, hm ≤ q ∧ q ≤ hm + i ∧ H q = dadP elems (hm + 1 + i) := by
  have := S.hm_eq
  obtain ⟨q, h1, h2, e⟩ := S.appears ((2 * J - 1 - i) / 2) (by omega)
  exact ⟨q, h1, by omega, by rw [e, S.dadP_eq i hi]⟩

theorem clK_clamped (S : PShape H hm J elems maxc) : Clamped H hm J elems L (clK H hm elems L (2 * J)) := by
  have := S.hm_eq
  refine ⟨?_, ?_⟩
  · rw [clK_stable S hm 0 (Nat.le_refl _) (by omega) (2 * J) (by omega) (Nat.le_refl _)]; rfl
  · intro i hi
    rw [clK_stable S (hm + 1 + i) (i + 1) (by omega) (by omega) (2 * J) (by omega) (Nat.le_refl _)]
    simp only [clK, if_true]
    obtain ⟨q, h1, h2, e⟩ := dad_pos S i hi
    rw [← e, clK_stable S q i h1 h2 (2 * J) (by omega) (Nat.le_refl _)]

end cl

/-- Leaves of length `b` among the first `k` non-root positions. -/
def blP (H : Nat → Nat) (hm maxc : Nat) (len : Nat → Nat) (k b : Nat) : Nat :=
  rs (fun i => if H (hm + 1 + i) ≤ maxc ∧ len (H (hm + 1 + i)) = b then 1 else 0) k

/-- Clamped nodes among the first `k` non-root positions. -/
def ovP (H : Nat → Nat) (hm elems L : Nat) (cl : Nat → Nat) (k : Nat) : Nat :=
  rs (fun i => if cl (dadP elems (hm + 1 + i)) = L then 1 else 0) k

/-- `Σ f · (len + xbits)` over the leaves among the first `k` non-root positions. -/
def costP (H : Nat → Nat) (hm maxc : Nat) (fr len xb : Nat → Nat) (k : Nat) : Nat :=
  rs (fun i => if H (hm + 1 + i) ≤ maxc then fr (H (hm + 1 + i)) * (len (H (hm + 1 + i)) + xb (H (hm + 1 + i)))
    else 0) k

theorem blP_succ (H : Nat → Nat) (hm maxc : Nat) (len : Nat → Nat) (k b : Nat) :
    blP H hm maxc len (k + 1) b = blP H hm maxc len k b +
      (if H (hm + 1 + k) ≤ maxc ∧ len (H (hm + 1 + k)) = b then 1 else 0) := rfl

theorem costP_succ (H : Nat → Nat) (hm maxc : Nat) (fr len xb : Nat → Nat) (k : Nat) :
    costP H hm maxc fr len xb (k + 1) = costP H hm maxc fr len xb k +
      (if H (hm + 1 + k) ≤ maxc then fr (H (hm + 1 + k)) * (len (H (hm + 1 + k)) + xb (H (hm + 1 + k))) else 0) :=
  rfl

theorem blP_le (H : Nat → Nat) (hm maxc : Nat) (len : Nat → Nat) (k b : Nat) : blP H hm maxc len k b ≤ k := by
  have := rs_le (n := k) (F := fun i => if H (hm + 1 + i) ≤ maxc ∧ len (H (hm + 1 + i)) = b then 1 else 0)
    (G := fun _ => 1) (fun i _ => by split <;> omega)
  rw [rs_const] at this; unfold blP; omega

theorem ovP_le (H : Nat → Nat) (hm elems L : Nat) (cl : Nat → Nat) (k : Nat) : ovP H hm elems L cl k ≤ k := by
  have := rs_le (n := k) (F := fun i => if cl (dadP elems (hm + 1 + i)) = L then 1 else 0)
    (G := fun _ => 1) (fun i _ => by split <;> omega)
  rw [rs_const] at this; unfold ovP; omega


end Zlib.Trees.Proofs.GB
