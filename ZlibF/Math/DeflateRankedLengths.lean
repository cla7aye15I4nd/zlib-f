import ZlibF.Math.DeflateLeafRank
import ZlibF.Math.HuffmanFibPush
import ZlibF.Proof.«trees.c.heap.gbclk»

/-! # Final leaf histograms and sorted lengths identify rank lengths -/

namespace Zlib.Trees.Proofs.GB.LeafRank
set_option autoImplicit false

def selected (H : Nat → Nat) (hm maxc : Nat) (i : Nat) : Bool := decide (H (hm + 1 + i) ≤ maxc)

def count (H : Nat → Nat) (hm J maxc : Nat) : Nat := cntL (selected H hm maxc) (2 * J)

noncomputable def index (H : Nat → Nat) (hm J maxc r : Nat) : Nat := idxR (selected H hm maxc) (2 * J) r

noncomputable def value (H f : Nat → Nat) (hm J maxc r : Nat) : Nat := f (H (hm + 1 + index H hm J maxc r))

theorem index_spec {H : Nat → Nat} {hm J maxc r : Nat}
    (lower : 1 ≤ r) (upper : r ≤ count H hm J maxc) :
    index H hm J maxc r < 2 * J ∧ H (hm + 1 + index H hm J maxc r) ≤ maxc ∧
      cntL (selected H hm maxc) (index H hm J maxc r + 1) = r := by
  obtain ⟨bound, leaf, rank⟩ := idxR_spec (selected H hm maxc) lower upper
  exact ⟨bound, by simpa only [index, selected, decide_eq_true_eq] using leaf, rank⟩

/-- Counting final lengths over actual leaf ranks is exactly the full
histogram over retained heap positions. Internal nodes add nothing. -/
theorem value_counts (H f : Nat → Nat) (hm J maxc x : Nat) :
    Zlib.Trees.HuffmanAbstract.countR (fun r => value H f hm J maxc r == x) (count H hm J maxc) =
      blP H hm maxc f (2 * J) x := by
  unfold count
  rw [countR_reindex]
  unfold blP
  apply rs_congr
  intro i bound
  by_cases leaf : H (hm + 1 + i) ≤ maxc
  · have same := idxR_rank (selected H hm maxc) bound (by simp only [selected, leaf, decide_true])
    simp only [value, index, selected, leaf, decide_true, true_and] at same ⊢
    rw [same]
    by_cases equal : f (H (hm + 1 + i)) = x <;> simp only [equal, beq_iff_eq, decide_eq_true_eq, and_true, and_false, ite_true, ite_false, true_and]
  · simp [selected, leaf]

/-- Heap-position order becomes rank order because the inverse index is
monotone. The proof only needs the actual leaf predicate. -/
theorem value_sorted {H f : Nat → Nat} {hm J maxc : Nat}
    (ordered : ∀ q q', hm + 1 ≤ q → q ≤ q' → q' < 573 → H q ≤ maxc → H q' ≤ maxc → f (H q) ≤ f (H q'))
    (geometry : hm + 2 * J = 572) :
    ∀ y r, 1 ≤ y → y ≤ r → r ≤ count H hm J maxc → value H f hm J maxc y ≤ value H f hm J maxc r := by
  intro y r lower between upper
  have yspec := index_spec lower (by omega : y ≤ count H hm J maxc)
  have rspec := index_spec (by omega : 1 ≤ r) upper
  have order := idxR_mono (selected H hm maxc) lower between upper
  simp only [index] at yspec rspec
  unfold value index
  exact ordered _ _ (by omega) (by omega) (by omega) yspec.2.1 rspec.2.1

/-- Exact final counts and sorted lengths characterize the rank assignment
used by the pinned repair model. This pure statement is instantiated by
the source execution's final scan/count results. -/
theorem value_eq_lenOfRank {H f c : Nat → Nat} {hm J maxc : Nat}
    (ordered : ∀ q q', hm + 1 ≤ q → q ≤ q' → q' < 573 → H q ≤ maxc → H q' ≤ maxc → f (H q) ≤ f (H q'))
    (geometry : hm + 2 * J = 572)
    (lengths : ∀ r, 1 ≤ r → r ≤ count H hm J maxc → value H f hm J maxc r ≤ 15)
    (histogram : ∀ j, j ≤ 15 → c j = blP H hm maxc f (2 * J) j) :
    ∀ r, 1 ≤ r → r ≤ count H hm J maxc →
      value H f hm J maxc r = Zlib.Trees.HuffmanAbstract.lenOfRank 15 c r := by
  exact Zlib.Trees.HuffmanAbstract.lenOfRank_of_sorted (count H hm J maxc) (value H f hm J maxc) c
    (value_sorted ordered geometry) lengths (fun j bound => (histogram j bound).trans (value_counts H f hm J maxc j).symm)

end Zlib.Trees.Proofs.GB.LeafRank
