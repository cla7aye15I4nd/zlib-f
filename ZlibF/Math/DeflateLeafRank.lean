import ZlibF.Proof.«trees.c.heap.gbmath»
import ZlibF.Math.HuffmanRank

/-!
Pure leaf-rank mathematics adapted from the pinned zlib-formal reference
`0f1428677ebf5b1614ff77f4702bbb382b2bf3c6`; see docs/history/references.md.
The proof bodies are retained. Imports and namespace use this project's
finite sums. These facts do not assume execution of any translated callee.
-/

/-!
# Ranks of the leaves in the heap

The leaves among the heap positions `hm + 1 + i` (`i < n`, predicate `lf`) are numbered from
below: the leaf at index `i` has rank `cntL lf (i + 1)` (rank `1` = lowest position = removed
last, the convention of `HuffmanAbstract`). `idxR` is the inverse. Sums over leaf positions
are sums over ranks (`sum_reindex`). Pure.
-/

namespace Zlib.Trees.Proofs.GB


/-- Number of leaves among the indices `< n`. -/
def cntL (lf : Nat → Bool) (n : Nat) : Nat := rs (fun i => if lf i then 1 else 0) n

section
variable (lf : Nat → Bool)

theorem cntL_succ (n : Nat) : cntL lf (n + 1) = cntL lf n + (if lf n then 1 else 0) := rfl

theorem sum_reindex (g : Nat → Nat) : ∀ n,
    rs (fun i => if lf i then g (cntL lf (i + 1)) else 0) n = HuffmanAbstract.sumR g (cntL lf n)
  | 0 => rfl
  | n + 1 => by
    rw [rs_succ, sum_reindex g n, cntL_succ]
    by_cases e : lf n
    · rw [if_pos e, if_pos e]; rfl
    · rw [if_neg e, if_neg e]; rfl

theorem cntL_mono {i i' : Nat} (h : i ≤ i') : cntL lf i ≤ cntL lf i' := by
  unfold cntL; rw [show i' = i + (i' - i) by omega, rs_split]; omega

theorem cntL_lt {i i' : Nat} (hl : lf i' = true) (h : i < i') : cntL lf (i + 1) < cntL lf (i' + 1) := by
  have := cntL_mono lf (show i + 1 ≤ i' by omega)
  rw [cntL_succ lf i', if_pos hl]; omega

theorem rank_inj {i i' : Nat} (hl : lf i = true) (hl' : lf i' = true) (e : cntL lf (i + 1) = cntL lf (i' + 1)) :
    i = i' := by
  rcases Nat.lt_trichotomy i i' with h | h | h
  · have := cntL_lt lf hl' h; omega
  · exact h
  · have := cntL_lt lf hl h; omega

theorem rank_ex : ∀ n r, 1 ≤ r → r ≤ cntL lf n → ∃ i, i < n ∧ lf i = true ∧ cntL lf (i + 1) = r
  | 0, r, h1, h2 => by simp [cntL] at h2; omega
  | n + 1, r, h1, h2 => by
    rw [cntL_succ] at h2
    by_cases hr : r ≤ cntL lf n
    · obtain ⟨i, a, b, c⟩ := rank_ex n r h1 hr; exact ⟨i, by omega, b, c⟩
    · by_cases e : lf n
      · rw [if_pos e] at h2; exact ⟨n, by omega, e, by rw [cntL_succ, if_pos e]; omega⟩
      · rw [if_neg e] at h2; omega

theorem rank_bounds {n i : Nat} (hi : i < n) (hl : lf i = true) : 1 ≤ cntL lf (i + 1) ∧ cntL lf (i + 1) ≤ cntL lf n :=
  ⟨by rw [cntL_succ, if_pos hl]; omega, cntL_mono lf (by omega)⟩

open Classical in
/-- The index of the leaf of rank `r`. -/
noncomputable def idxR (n r : Nat) : Nat :=
  if h : ∃ i, i < n ∧ lf i = true ∧ cntL lf (i + 1) = r then Classical.choose h else 0

theorem idxR_spec {n r : Nat} (h1 : 1 ≤ r) (h2 : r ≤ cntL lf n) :
    idxR lf n r < n ∧ lf (idxR lf n r) = true ∧ cntL lf (idxR lf n r + 1) = r := by
  have hx := rank_ex lf n r h1 h2
  unfold idxR; rw [dif_pos hx]; exact Classical.choose_spec hx

theorem idxR_rank {n i : Nat} (hi : i < n) (hl : lf i = true) : idxR lf n (cntL lf (i + 1)) = i := by
  obtain ⟨b1, b2⟩ := rank_bounds lf hi hl
  obtain ⟨-, a2, a3⟩ := idxR_spec lf b1 b2
  exact rank_inj lf a2 hl a3

theorem idxR_mono {n y r : Nat} (h1 : 1 ≤ y) (hyr : y ≤ r) (h2 : r ≤ cntL lf n) : idxR lf n y ≤ idxR lf n r := by
  obtain ⟨-, a2, a3⟩ := idxR_spec lf (n := n) h1 (by omega)
  obtain ⟨-, b2, b3⟩ := idxR_spec lf (n := n) (by omega) h2
  refine Classical.byContradiction (fun h => ?_)
  have := cntL_lt lf a2 (show idxR lf n r < idxR lf n y by omega)
  omega

/-- A count over ranks is a count over leaf positions. -/
theorem countR_reindex (p : Nat → Bool) (n : Nat) :
    HuffmanAbstract.countR p (cntL lf n) = rs (fun i => if lf i ∧ p (cntL lf (i + 1)) then 1 else 0) n := by
  unfold HuffmanAbstract.countR
  rw [← sum_reindex]
  apply rs_congr; intro i _
  by_cases a : lf i <;> by_cases b : p (cntL lf (i + 1)) <;> simp [a, b]

end

end Zlib.Trees.Proofs.GB
