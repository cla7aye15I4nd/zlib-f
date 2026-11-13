import ZlibF.Math.HuffmanRepairCost

/-!
# Per-rank Fibonacci caps for the repair term (H2b, common part)

A leaf at true depth `δ` in a Huffman tree of weight `W` has `w·F(δ+1) + F(δ) ≤ W`. With weights
nonincreasing in rank, the rank `r` therefore weighs at most `fibCap W d`, where `d` is the
`r`-th smallest clamped depth `lenOfRank 15 (histL L δ N) r` (`rank_cap`). The certificate
modules bound `repairExtra 7 w M c` histogram by histogram with these caps.

`cv a` reads a count vector from a list (zero beyond it); `RepairShape` collects the facts that the
first pass of `gen_bitlen` gives for the clamped histogram at the limit 7.
-/

namespace Zlib.Trees.HuffmanAbstract
set_option autoImplicit false

/-- The weight cap of a rank at clamped depth `d` in a tree of weight `W`. -/
def fibCap (W d : Nat) : Nat := (W - fib d) / fib (d + 1)

/-- A count vector given by a list. -/
def cv (a : List Nat) (j : Nat) : Nat := a.getD j 0

/-- The histogram facts at the limit 7: no leaf at level 0, nothing above 7, `N` leaves, clamped
Kraft sum `128 + M` and at least `M + 1` leaves at level 7. -/
structure RepairShape (c : Nat → Nat) (N M : Nat) : Prop where
  zero : c 0 = 0
  high : ∀ j, 7 < j → c j = 0
  leaves : c 1 + c 2 + c 3 + c 4 + c 5 + c 6 + c 7 = N
  kraft : 64 * c 1 + 32 * c 2 + 16 * c 3 + 8 * c 4 + 4 * c 5 + 2 * c 6 + c 7 = 128 + M
  top : M + 1 ≤ c 7

/-- The caps on the ranks `1 .. N` of the histogram `c`. -/
def RankCaps (c w : Nat → Nat) (W N : Nat) : Prop :=
  ∀ r, 1 ≤ r → r ≤ N → w r ≤ fibCap W (lenOfRank 15 c r)

theorem le_fibCap {w W d : Nat} (h : w * fib (d + 1) + fib d ≤ W) : w ≤ fibCap W d := by
  unfold fibCap
  have pos : 0 < fib (d + 1) := fib_pos (by omega)
  exact (Nat.le_div_iff_mul_le pos).mpr (by omega)

/-- **Rank caps.** -/
theorem rank_cap (L : Nat) (N W : Nat) (w δ : Nat → Nat)
    (hw : ∀ y r, 1 ≤ y → y ≤ r → r ≤ N → w r ≤ w y)
    (hfib : ∀ y, 1 ≤ y → y ≤ N → w y * fib (δ y + 1) + fib (δ y) ≤ W) :
    RankCaps (histL L δ N) w W N := by
  intro r hr1 hr2
  apply le_fibCap
  generalize hd : lenOfRank 15 (histL L δ N) r = d
  rcases Nat.eq_zero_or_pos d with h0 | h0
  · subst h0
    have := hfib r hr1 hr2
    have : fib 1 ≤ fib (δ r + 1) := fib_mono (by omega)
    have : w r * fib 1 ≤ w r * fib (δ r + 1) := Nat.mul_le_mul_left _ this
    show w r * fib 1 + 0 ≤ W
    omega
  · have hbel := lenOfRank_below (histL L δ N) r (d - 1) (by omega)
    unfold histL at hbel
    rw [cumC_hist (fun r => min (δ r) L) N] at hbel
    obtain ⟨y, hy1, hy2, hy3⟩ :=
      exists_not_of_countR_lt (fun r => decide (min (δ r) L ≤ d - 1)) r
        (Nat.lt_of_le_of_lt (countR_mono _ hr2) hbel)
    have hy3' : ¬ (min (δ y) L ≤ d - 1) := by simpa using hy3
    have hδy : d ≤ δ y := by omega
    have h1 : w r * fib (d + 1) ≤ w y * fib (δ y + 1) :=
      Nat.mul_le_mul (hw y r hy1 hy2 hr2) (fib_mono (by omega))
    have h2 : fib d ≤ fib (δ y) := fib_mono hδy
    have := hfib y hy1 (by omega)
    omega

theorem RepairShape.eq_cv {c : Nat → Nat} {N M a1 a2 a3 a4 a5 a6 a7 : Nat} (shape : RepairShape c N M)
    (h1 : c 1 = a1) (h2 : c 2 = a2) (h3 : c 3 = a3) (h4 : c 4 = a4) (h5 : c 5 = a5) (h6 : c 6 = a6)
    (h7 : c 7 = a7) : c = cv [0, a1, a2, a3, a4, a5, a6, a7] := by
  funext j
  match j with
  | 0 => exact shape.zero
  | 1 => exact h1
  | 2 => exact h2
  | 3 => exact h3
  | 4 => exact h4
  | 5 => exact h5
  | 6 => exact h6
  | 7 => exact h7
  | j + 8 => rw [shape.high (j + 8) (by omega)]; rfl

end Zlib.Trees.HuffmanAbstract
