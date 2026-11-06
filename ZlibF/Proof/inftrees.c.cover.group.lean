import ZlibF.Proof.«inftrees.c.cover.root»

/-!
# Covering of a sub-table

Pure arithmetic over the canonical model. The long codes whose first `R` bits are the block `p` (`grp = p`) form the
group of one root link. For a complete code they tile the block `[p * 2^(15-R), (p+1) * 2^(15-R))`. A sub-table with
`2^c` cells is read with the `c` bits that follow the root bits; the cell `t` is decided by the tile that contains
`z = p * 2^(15-R) + rev c t * 2^(15-R-c)`. The code `j` of the group (`e = L j - R ≤ c`) fills the cells
`t = H j / 2^R + 2^e * t'`, `t' < 2^(c - e)`, which is what the C writes (`next[(huff >> drop) + fill]`).
-/
set_option autoImplicit false

namespace Zlib.Inftrees.Proofs.Cover
open Zlib.Inftrees.Canon

/-- The `j`-th code is longer than the root and in the group of block `p`. -/
def Group (ls : List Nat) (R p j : Nat) : Prop := j < nz ls ∧ R < L ls j ∧ grp ls R j = p

theorem z_div (R c p t e : Nat) (hRc : R + c ≤ 15) (hec : e ≤ c) :
    (p * 2 ^ (15 - R) + Canon.rev c t * 2 ^ (15 - R - c)) / 2 ^ (15 - R - e) =
      p * 2 ^ e + Canon.rev e (t % 2 ^ e) := by
  have h1 : 2 ^ (15 - R - e) = 2 ^ (15 - R - c) * 2 ^ (c - e) := by
    rw [← Nat.pow_add]; congr 1; omega
  have h2 : p * 2 ^ (15 - R) = (p * 2 ^ e) * 2 ^ (15 - R - e) := by
    rw [Nat.mul_assoc, ← Nat.pow_add]; congr 2; omega
  rw [h2, h1, show (p * 2 ^ e) * (2 ^ (15 - R - c) * 2 ^ (c - e)) =
      (2 ^ (15 - R - c) * 2 ^ (c - e)) * (p * 2 ^ e) from Nat.mul_comm _ _,
    Nat.mul_add_div (Nat.mul_pos (two_pow_pos' _) (two_pow_pos' _)),
    Nat.mul_comm (Canon.rev c t), Nat.mul_div_mul_left _ _ (two_pow_pos' _), rev_div_short c e t hec]

theorem z_lt (R c p t : Nat) (hRc : R + c ≤ 15) :
    p * 2 ^ (15 - R) + Canon.rev c t * 2 ^ (15 - R - c) < (p + 1) * 2 ^ (15 - R) := by
  have h : Canon.rev c t * 2 ^ (15 - R - c) < 2 ^ (15 - R) := by
    have hp : 2 ^ (15 - R) = 2 ^ c * 2 ^ (15 - R - c) := by rw [← Nat.pow_add]; congr 1; omega
    rw [hp]
    exact Nat.mul_lt_mul_of_pos_right (rev_lt _ _) (two_pow_pos' _)
  rw [Nat.succ_mul]; omega

theorem z_div_root (R c p t : Nat) (hRc : R + c ≤ 15) :
    (p * 2 ^ (15 - R) + Canon.rev c t * 2 ^ (15 - R - c)) / 2 ^ (15 - R) = p := by
  have h := z_lt R c p t hRc
  have := two_pow_pos' (15 - R)
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ this, Nat.div_eq_of_lt]
  · simp
  · rw [Nat.succ_mul] at h; omega

/-- `cv` of a code of the group, split at the root. -/
theorem cv_group {ls : List Nat} {R p j : Nat} (hg : Group ls R p j) :
    cv ls j = p * 2 ^ (L ls j - R) + cv ls j % 2 ^ (L ls j - R) := by
  obtain ⟨hj, hl, hp⟩ := hg
  have h15 := (L_interval ls hj).2.1
  have hq : cv ls j / 2 ^ (L ls j - R) = p := by
    rw [← hp]; unfold grp cv
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
    congr 2; omega
  have := Nat.div_add_mod (cv ls j) (2 ^ (L ls j - R))
  rw [hq, Nat.mul_comm (2 ^ (L ls j - R)) p] at this
  omega

/-- **Group covering (list model, residue form).** For a complete code, a group `p` of long codes (`j0` is one) and a
width `c` with `R + c ≤ 15` that holds every code of the group, every cell `t` of the sub-table is covered by exactly
one code `j` of the group: `t % 2^(L j - R) = H j / 2^R`. -/
theorem group_cover {ls : List Nat} (hcomp : K ls (nz ls) = 2 ^ 15) {R p j0 : Nat} (hR : R ≤ 15)
    (hg0 : Group ls R p j0) {c : Nat} (hRc : R + c ≤ 15) (hcl : ∀ j, Group ls R p j → L ls j ≤ R + c)
    (t : Nat) :
    ∃ j, Group ls R p j ∧ t % 2 ^ (L ls j - R) = H ls j / 2 ^ R ∧
      ∀ j', Group ls R p j' → t % 2 ^ (L ls j' - R) = H ls j' / 2 ^ R → j' = j := by
  have hF : Fit ls := by show K ls (nz ls) ≤ 2 ^ 15; omega
  obtain ⟨hj0, hl0, hp0⟩ := hg0
  have hplt : p < 2 ^ R := hp0 ▸ grp_lt' hF hR hj0
  generalize hz : p * 2 ^ (15 - R) + Canon.rev c t * 2 ^ (15 - R - c) = z
  have hzlt : z < (p + 1) * 2 ^ (15 - R) := hz ▸ z_lt R c p t hRc
  have hzdiv : z / 2 ^ (15 - R) = p := hz ▸ z_div_root R c p t hRc
  have hzge : p * 2 ^ (15 - R) ≤ z := by rw [← hz]; omega
  have hpow : 2 ^ 15 = 2 ^ R * 2 ^ (15 - R) := by rw [← Nat.pow_add]; congr 1; omega
  have hzK : z < K ls (nz ls) := by
    rw [hcomp, hpow]
    have : (p + 1) * 2 ^ (15 - R) ≤ 2 ^ R * 2 ^ (15 - R) := Nat.mul_le_mul_right _ hplt
    omega
  obtain ⟨j, hj, hjt⟩ := tile_exists ls hzK
  have t1 := hjt.1
  have t2 := hjt.2
  have hlong : R < L ls j := by
    refine Classical.byContradiction fun hl => ?_
    have hl' : L ls j ≤ R := by omega
    obtain ⟨u1, u2⟩ := short_units (ls := ls) hR hj hl'
    have hk0a : p * 2 ^ (15 - R) ≤ K ls j0 := by rw [← hp0]; exact Nat.div_mul_le_self _ _
    have hk0b : K ls j0 < (p + 1) * 2 ^ (15 - R) := by
      rw [← hp0, Nat.succ_mul]; exact Nat.lt_div_mul_add (two_pow_pos' _)
    rw [u1] at t1; rw [u2] at t2
    have e1 : cv ls j * 2 ^ (R - L ls j) ≤ p := by
      have : (cv ls j * 2 ^ (R - L ls j)) * 2 ^ (15 - R) < (p + 1) * 2 ^ (15 - R) := by omega
      have := Nat.lt_of_mul_lt_mul_right this
      omega
    have e2 : p < cv ls j * 2 ^ (R - L ls j) + 2 ^ (R - L ls j) := by
      have : p * 2 ^ (15 - R) < (cv ls j * 2 ^ (R - L ls j) + 2 ^ (R - L ls j)) * 2 ^ (15 - R) := by omega
      exact Nat.lt_of_mul_lt_mul_right this
    have e3 : K ls j ≤ K ls j0 := by
      rw [u1]; exact Nat.le_trans (Nat.mul_le_mul_right _ e1) hk0a
    have e4 : K ls j0 < K ls (j + 1) := by
      rw [u2]
      exact Nat.lt_of_lt_of_le hk0b (Nat.mul_le_mul_right _ e2)
    by_cases hjj : j0 < j
    · have := K_strict ls hjj; omega
    · by_cases hje : j0 = j
      · subst hje; omega
      · have := K_mono ls (show j + 1 ≤ j0 by omega); omega
  have hgrp : grp ls R j = p := by rw [long_grp hj hlong hjt, hzdiv]
  have hgj : Group ls R p j := ⟨hj, hlong, hgrp⟩
  have h15 := (L_interval ls hj).2.1
  have hec := hcl j hgj
  have hzval : ∀ j', Group ls R p j' → z / 2 ^ (15 - L ls j') = p * 2 ^ (L ls j' - R) +
      Canon.rev (L ls j' - R) (t % 2 ^ (L ls j' - R)) := by
    intro j' hj'
    have hl := hcl j' hj'
    have hl15 := (L_interval ls hj'.1).2.1
    have hRl := hj'.2.1
    rw [← hz, show 15 - L ls j' = 15 - R - (L ls j' - R) by omega]
    exact z_div R c p t (L ls j' - R) hRc (by omega)
  have hHdiv : ∀ j', Group ls R p j' → H ls j' / 2 ^ R = Canon.rev (L ls j' - R) (cv ls j' % 2 ^ (L ls j' - R)) :=
    fun j' hj' => H_div_root ls hj'.1 (by have := hj'.2.1; omega)
  refine ⟨j, hgj, ?_, ?_⟩
  · rw [hHdiv j hgj]
    have hcv := (inTile_iff_div ls hj z).mp hjt
    rw [hzval j hgj] at hcv
    have hm : cv ls j % 2 ^ (L ls j - R) = Canon.rev (L ls j - R) (t % 2 ^ (L ls j - R)) := by
      rw [← hcv, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (rev_lt _ _)]
    rw [hm, rev_rev, Nat.mod_mod]
  · intro j' hj' heq
    have e1 : Canon.rev (L ls j' - R) (t % 2 ^ (L ls j' - R)) = cv ls j' % 2 ^ (L ls j' - R) := by
      rw [heq, hHdiv j' hj', rev_rev, Nat.mod_mod]
    refine tile_unique ls ((inTile_iff_div ls hj'.1 z).mpr ?_) hjt
    rw [hzval j' hj', e1]; exact (cv_group hj').symm

/-- The first entry index of a code of the group inside its sub-table is below `2^(L j - R)`. -/
theorem first_lt {ls : List Nat} {R p j : Nat} (hg : Group ls R p j) : H ls j / 2 ^ R < 2 ^ (L ls j - R) := by
  obtain ⟨hj, hl, _⟩ := hg
  have h15 := (L_interval ls hj).2.1
  rw [Nat.div_lt_iff_lt_mul (two_pow_pos' _), ← Nat.pow_add, show L ls j - R + R = L ls j by omega]
  exact H_lt ls j

/-- The cells that a code of the group writes lie inside the sub-table of `2^c` cells. -/
theorem cell_lt {ls : List Nat} {R p j c : Nat} (hg : Group ls R p j) (hl : L ls j ≤ R + c) {t' : Nat}
    (ht' : t' < 2 ^ (R + c - L ls j)) : H ls j / 2 ^ R + 2 ^ (L ls j - R) * t' < 2 ^ c := by
  have h1 := first_lt hg
  have hR := hg.2.1
  have hp : 2 ^ c = 2 ^ (L ls j - R) * 2 ^ (R + c - L ls j) := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [hp]
  have : 2 ^ (L ls j - R) * (t' + 1) ≤ 2 ^ (L ls j - R) * 2 ^ (R + c - L ls j) :=
    Nat.mul_le_mul_left _ ht'
  rw [Nat.mul_succ] at this
  omega

/-- **Group covering, in the index form of the C.** For a complete code, a group `p` of long codes (one of them is
`j0`) and a sub-table width `c` with `R + c ≤ 15` that holds every code of the group (`L j ≤ R + c`, which
`inflate_table` ensures with `look`), every cell `t < 2^c` of the sub-table is written by exactly one code `j` of the
group, as `next[H j / 2^R + 2^(L j - R) * t']` with `t' < 2^(R + c - L j)`. (`H j / 2^R` is `huff >> drop` of the
code at the time it is written.) -/
theorem group_cover_idx {ls : List Nat} (hcomp : K ls (nz ls) = 2 ^ 15) {R p j0 : Nat} (hR : R ≤ 15)
    (hg0 : Group ls R p j0) {c : Nat} (hRc : R + c ≤ 15) (hcl : ∀ j, Group ls R p j → L ls j ≤ R + c)
    {t : Nat} (ht : t < 2 ^ c) :
    ∃ j, Group ls R p j ∧ (∃ t', t' < 2 ^ (R + c - L ls j) ∧ t = H ls j / 2 ^ R + 2 ^ (L ls j - R) * t') ∧
      ∀ j' t', Group ls R p j' → t = H ls j' / 2 ^ R + 2 ^ (L ls j' - R) * t' → j' = j := by
  obtain ⟨j, hg, hm, hu⟩ := group_cover hcomp hR hg0 hRc hcl t
  have hmodeq : ∀ j' t', Group ls R p j' → (H ls j' / 2 ^ R + 2 ^ (L ls j' - R) * t') % 2 ^ (L ls j' - R) =
      H ls j' / 2 ^ R := by
    intro j' t' hj'
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (first_lt hj')]
  refine ⟨j, hg, ⟨t / 2 ^ (L ls j - R), ?_, ?_⟩, ?_⟩
  · have hl := hcl j hg
    have hR' := hg.2.1
    have hp : 2 ^ c = 2 ^ (L ls j - R) * 2 ^ (R + c - L ls j) := by
      rw [← Nat.pow_add]; congr 1; omega
    rw [hp] at ht
    exact Nat.div_lt_of_lt_mul ht
  · have := Nat.mod_add_div t (2 ^ (L ls j - R))
    rw [hm] at this; omega
  · intro j' t' hj' heq
    apply hu j' hj'
    rw [heq, hmodeq j' t' hj']

end Zlib.Inftrees.Proofs.Cover
