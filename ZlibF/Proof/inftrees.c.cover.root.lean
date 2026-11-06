import ZlibF.Proof.«inftrees.c.cover.tile»

/-!
# Covering of the root table

Pure arithmetic over the canonical model. A root cell `y < 2^R` is read with the next `R` input bits, the first bit
being the lowest bit of `y`. The 15-bit word that starts with those bits is `z = rev R y * 2^(15 - R)`, so the cell is
decided by the tile of `[0, 2^15)` that contains `z`: a code of length `l ≤ R` whose tile contains `z` fills `y`
(`y % 2^l = H j`, the cells `H j + 2^l * k` that the C writes with `drop = 0`); a code with `l > R` places a link at
`y = H j % 2^R` (`low` in the C).
-/
set_option autoImplicit false

namespace Zlib.Inftrees.Proofs.Cover
open Zlib.Inftrees.Canon

/-- The `j`-th code (allocation order) is short and fills the root cell `y`. -/
def ShortAt (ls : List Nat) (R y j : Nat) : Prop := j < nz ls ∧ L ls j ≤ R ∧ y % 2 ^ L ls j = H ls j

/-- The `j`-th code is longer than the root and its link sits at the root cell `y`. -/
def LongAt (ls : List Nat) (R y j : Nat) : Prop := j < nz ls ∧ R < L ls j ∧ H ls j % 2 ^ R = y

theorem rev_div_short (R l y : Nat) (hl : l ≤ R) :
    Canon.rev R y / 2 ^ (R - l) = Canon.rev l (y % 2 ^ l) := by
  have hs := rev_split (R - l) l y
  rw [show R - l + l = R by omega] at hs
  rw [hs, Nat.add_mul_div_right _ _ (two_pow_pos' _), Nat.div_eq_of_lt (rev_lt _ _)]
  simp

/-- The word `z` of a root cell, seen at the length of a short code. -/
theorem short_div {R l y : Nat} (hR : R ≤ 15) (hl : l ≤ R) :
    Canon.rev R y * 2 ^ (15 - R) / 2 ^ (15 - l) = Canon.rev l (y % 2 ^ l) := by
  have hp : 2 ^ (15 - l) = 2 ^ (15 - R) * 2 ^ (R - l) := by rw [← Nat.pow_add]; congr 1; omega
  rw [hp, ← Nat.div_div_eq_div_mul, Nat.mul_div_cancel _ (two_pow_pos' _), rev_div_short R l y hl]

/-- A short code covers the root cell `y` exactly when its tile contains the word of `y`. -/
theorem short_iff {ls : List Nat} (hF : Fit ls) {R y j : Nat} (hR : R ≤ 15) (hj : j < nz ls) (hl : L ls j ≤ R) :
    InTile ls j (Canon.rev R y * 2 ^ (15 - R)) ↔ y % 2 ^ L ls j = H ls j := by
  rw [inTile_iff_div ls hj, short_div hR hl]
  have hc := cv_lt hF hj
  unfold H
  constructor
  · intro h
    rw [← h, rev_rev, Nat.mod_mod]
  · intro h
    rw [h, rev_rev, Nat.mod_eq_of_lt hc]

/-- A tile of a code longer than the root lies inside the block of `2^(15 - R)` points that contains it: the group
`grp` of the code is the block number of any point of its tile. -/
theorem long_grp {ls : List Nat} {R j z : Nat} (hj : j < nz ls) (hR : R < L ls j) (h : InTile ls j z) :
    grp ls R j = z / 2 ^ (15 - R) := by
  have h15 := (L_interval ls hj).2.1
  have hd := (inTile_iff_div ls hj z).mp h
  have hp : 2 ^ (15 - R) = 2 ^ (15 - L ls j) * 2 ^ (L ls j - R) := by
    rw [← Nat.pow_add]; congr 1; omega
  unfold grp
  rw [hp, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, hd]
  unfold cv; rfl

/-- The bounds of the tile of a short code in units of the root cell. -/
theorem short_units {ls : List Nat} {R j : Nat} (hR : R ≤ 15) (hj : j < nz ls) (hl : L ls j ≤ R) :
    K ls j = (cv ls j * 2 ^ (R - L ls j)) * 2 ^ (15 - R) ∧
    K ls (j + 1) = (cv ls j * 2 ^ (R - L ls j) + 2 ^ (R - L ls j)) * 2 ^ (15 - R) := by
  have hp : 2 ^ (15 - L ls j) = 2 ^ (R - L ls j) * 2 ^ (15 - R) := by
    rw [← Nat.pow_add]; congr 1; omega
  have hm := cv_mul ls hj
  rw [hp] at hm
  refine ⟨by rw [← hm, Nat.mul_assoc], ?_⟩
  rw [K_succ, ← hm, hp, Nat.add_mul, Nat.mul_assoc]

/-- A long code whose link is at `y` belongs to the block `rev R y`. -/
theorem long_grp_eq {ls : List Nat} (hF : Fit ls) {R y j : Nat} (hR : R ≤ 15) (h : LongAt ls R y j) :
    grp ls R j = Canon.rev R y := by
  obtain ⟨hj, hl, hy⟩ := h
  rw [← hy, H_mod_root ls hj (by omega), rev_rev, Nat.mod_eq_of_lt (grp_lt' hF hR hj)]

/-- **Root covering.** Every cell `y < 2^R` of the root table is, for a code that is not over-subscribed, in
exactly one of three states: filled by exactly one short code (and no link at `y`); a link of the group of long codes
`rev R y` (and no short code fills it); or not written at all, which happens only beyond the Kraft sum
(`K nz ≤ rev R y * 2^(15 - R)`, impossible for a complete code). -/
inductive RootCell (ls : List Nat) (R y : Nat) : Prop
  | short (j : Nat) : ShortAt ls R y j → (∀ j', ShortAt ls R y j' → j' = j) → (∀ j', ¬ LongAt ls R y j') →
      RootCell ls R y
  | long (j : Nat) : LongAt ls R y j → (∀ j', ¬ ShortAt ls R y j') → RootCell ls R y
  | free : (∀ j', ¬ ShortAt ls R y j') → (∀ j', ¬ LongAt ls R y j') → K ls (nz ls) ≤ Canon.rev R y * 2 ^ (15 - R) →
      RootCell ls R y

/-- **Root covering (list model).** For lengths that are not over-subscribed (`Fit`) and `R ≤ 15`, every root cell
`y < 2^R` is in one of the three states of `RootCell`. -/
theorem root_cover {ls : List Nat} (hF : Fit ls) {R : Nat} (hR : R ≤ 15) {y : Nat} (hy : y < 2 ^ R) :
    RootCell ls R y := by
  generalize hr : Canon.rev R y = r
  have hrlt : r < 2 ^ R := hr ▸ rev_lt _ _
  have hshort : ∀ j, ShortAt ls R y j ↔ j < nz ls ∧ L ls j ≤ R ∧ InTile ls j (r * 2 ^ (15 - R)) := by
    intro j
    constructor
    · rintro ⟨hj, hl, h⟩; exact ⟨hj, hl, hr ▸ (short_iff hF hR hj hl).mpr h⟩
    · rintro ⟨hj, hl, h⟩; exact ⟨hj, hl, (short_iff hF hR hj hl).mp (hr ▸ h)⟩
  by_cases hz : r * 2 ^ (15 - R) < K ls (nz ls)
  · obtain ⟨j, hj, hjt⟩ := tile_exists ls hz
    have t1 := hjt.1
    have t2 := hjt.2
    by_cases hl : L ls j ≤ R
    · refine RootCell.short j ⟨hj, hl, (short_iff hF hR hj hl).mp (hr ▸ hjt)⟩ ?_ ?_
      · intro j' hj'
        obtain ⟨hj1, hl1, h1⟩ := (hshort j').mp hj'
        exact tile_unique ls h1 hjt
      · intro j' hlong
        have hg := long_grp_eq hF hR hlong
        obtain ⟨hj', hRl, _⟩ := hlong
        have hk1 : r * 2 ^ (15 - R) ≤ K ls j' := by
          rw [hr] at hg; rw [← hg]; exact Nat.div_mul_le_self _ _
        have hk2 : K ls j' < (r + 1) * 2 ^ (15 - R) := by
          rw [hr] at hg; rw [← hg, Nat.succ_mul]; exact Nat.lt_div_mul_add (two_pow_pos' _)
        obtain ⟨u1, u2⟩ := short_units (ls := ls) hR hj hl
        have hb := hjt.1
        have hb2 := hjt.2
        rw [u1] at hb; rw [u2] at hb2
        have e1 : cv ls j * 2 ^ (R - L ls j) ≤ r := Nat.le_of_mul_le_mul_right hb (two_pow_pos' _)
        have e2 : r < cv ls j * 2 ^ (R - L ls j) + 2 ^ (R - L ls j) :=
          Nat.lt_of_mul_lt_mul_right hb2
        have e3 : (r + 1) * 2 ^ (15 - R) ≤ K ls (j + 1) := by
          rw [u2]; exact Nat.mul_le_mul_right _ e2
        by_cases hjj : j' < j
        · have := K_strict ls hjj; omega
        · by_cases hje : j' = j
          · subst hje; omega
          · have := K_mono ls (show j + 1 ≤ j' by omega); omega
    · refine RootCell.long j ⟨hj, by omega, ?_⟩ ?_
      · have hg := long_grp (R := R) hj (by omega) hjt
        rw [Nat.mul_div_cancel _ (two_pow_pos' _)] at hg
        rw [H_mod_root ls hj (by omega), hg, ← hr, rev_rev, Nat.mod_eq_of_lt hy]
      · intro j' hj'
        obtain ⟨hj1, hl1, h1⟩ := (hshort j').mp hj'
        have := tile_unique ls h1 hjt
        subst this
        omega
  · refine RootCell.free ?_ ?_ (by rw [hr]; omega)
    · intro j' hj'
      obtain ⟨hj1, hl1, h1⟩ := (hshort j').mp hj'
      exact not_inTile_of_ge ls hj1 (by omega) h1
    · intro j' hlong
      have hg := long_grp_eq hF hR hlong
      have hj' := hlong.1
      have hk1 : r * 2 ^ (15 - R) ≤ K ls j' := by
        rw [hr] at hg; rw [← hg]; exact Nat.div_mul_le_self _ _
      have := K_strict ls (show j' < nz ls from hj')
      omega

end Zlib.Inftrees.Proofs.Cover
