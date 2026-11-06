import ZlibF.Proof.«inftrees.c.canon»

/-!
# Kraft tiles of a canonical code

Pure arithmetic over the canonical model (`Zlib.Inftrees.Canon`). The code word of the `j`-th symbol in allocation
order owns the *tile* `[K j, K j + 2^(15 - L j))` of `[0, 2^15)`. For a code that is not over-subscribed the tiles
are disjoint and consecutive, so they cover exactly `[0, K nz)`. A point `z` is in the tile of `j` exactly when
`z / 2^(15 - L j) = cv j`, i.e. when the code word of `j` is a prefix of the 15-bit word `z`.
-/
set_option autoImplicit false

namespace Zlib.Inftrees.Proofs.Cover
open Zlib.Inftrees.Canon

/-- The code is not over-subscribed (`Σ 2^(15 - l) ≤ 2^15`). -/
abbrev Fit (ls : List Nat) : Prop := K ls (nz ls) ≤ 2 ^ 15

/-- `z` lies in the tile of the `j`-th code. -/
abbrev InTile (ls : List Nat) (j z : Nat) : Prop := K ls j ≤ z ∧ z < K ls (j + 1)

theorem two_pow_pos' (n : Nat) : 0 < 2 ^ n := Nat.two_pow_pos n

theorem inTile_iff_div (ls : List Nat) {j : Nat} (hj : j < nz ls) (z : Nat) :
    InTile ls j z ↔ z / 2 ^ (15 - L ls j) = cv ls j := by
  have hm := cv_mul ls hj
  have hp := two_pow_pos' (15 - L ls j)
  unfold InTile
  rw [K_succ]
  constructor
  · rintro ⟨h1, h2⟩
    apply Nat.le_antisymm
    · apply Nat.le_of_lt_succ
      rw [Nat.div_lt_iff_lt_mul hp]
      rw [Nat.succ_mul]; omega
    · rw [Nat.le_div_iff_mul_le hp]; omega
  · intro h
    have h1 := Nat.div_mul_le_self z (2 ^ (15 - L ls j))
    have h2 := Nat.lt_div_mul_add (a := z) hp
    rw [h] at h1 h2
    omega

/-- A point of `[0, K nz)` is in exactly one tile. -/
theorem tile_exists (ls : List Nat) {z : Nat} (hz : z < K ls (nz ls)) :
    ∃ j, j < nz ls ∧ InTile ls j z := by
  have : ∀ n, n ≤ nz ls → z < K ls n → ∃ j, j < nz ls ∧ InTile ls j z := by
    intro n
    induction n with
    | zero => intro _ h; exact absurd h (by simp [K_zero])
    | succ n ih =>
      intro hn h
      by_cases hz' : z < K ls n
      · exact ih (by omega) hz'
      · exact ⟨n, by omega, by omega, h⟩
  exact this _ (Nat.le_refl _) hz

theorem tile_unique (ls : List Nat) {j j' z : Nat}
    (h : InTile ls j z) (h' : InTile ls j' z) : j = j' := by
  by_cases hlt : j < j'
  · have := K_mono ls (show j + 1 ≤ j' by omega); omega
  · by_cases hgt : j' < j
    · have := K_mono ls (show j' + 1 ≤ j by omega); omega
    · omega

/-- Outside `[0, K nz)` there is no tile. -/
theorem not_inTile_of_ge (ls : List Nat) {j z : Nat} (hj : j < nz ls) (hz : K ls (nz ls) ≤ z) :
    ¬ InTile ls j z := by
  intro h
  have := K_mono ls (show j + 1 ≤ nz ls by omega)
  omega

/-- No code of a non-over-subscribed set reaches `2^15`. -/
theorem cv_lt {ls : List Nat} (hF : Fit ls) {j : Nat} (hj : j < nz ls) : cv ls j < 2 ^ L ls j := by
  have h := cv_succ_le ls hj (Nat.le_trans (K_mono ls (show j + 1 ≤ nz ls by omega)) hF)
  omega

theorem K_lt {ls : List Nat} (hF : Fit ls) {j : Nat} (hj : j < nz ls) : K ls j < 2 ^ 15 := by
  have := K_strict ls (show j < nz ls by omega)
  omega

/-- The first `R` bits of a code that is longer than `R` (the group of the root table). -/
theorem grp_lt' {ls : List Nat} (hF : Fit ls) {R : Nat} (hR : R ≤ 15) {j : Nat} (hj : j < nz ls) :
    grp ls R j < 2 ^ R := by
  have hk := K_lt hF hj
  have hp : 2 ^ 15 = 2 ^ R * 2 ^ (15 - R) := by rw [← Nat.pow_add]; congr 1; omega
  unfold grp
  rw [Nat.div_lt_iff_lt_mul (two_pow_pos' _), ← hp]
  exact hk

end Zlib.Inftrees.Proofs.Cover
