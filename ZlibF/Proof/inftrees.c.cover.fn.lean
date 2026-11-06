import ZlibF.Proof.«inftrees.c.cover.group»
import ZlibF.Proof.«inftrees.c.canonbridge»

/-!
# The covering lemmas in the model of the main proof

`inftrees.c.canonbridge` identifies the canonical model (`ls = lensOf f n`: `Canon.L`, `Canon.K`, `Canon.H`,
`Canon.grp`) with the model that the main loop of `inflate_table` is proved in (`lenAt`, `val`, `pre`, `Tc`, `Kc`).
This module restates the covering lemmas of `inftrees.c.cover.root` and `.group` in that model.
-/
set_option autoImplicit false

namespace Zlib.Inftrees.Proofs.Cover

theorem nz_eq_Tc (f : Nat → Nat) (n : Nat) : Canon.nz (lensOf f n) = Tc f n 15 := by
  unfold Canon.nz; rw [ord_eq]; exact wsAux_length 15

/-- Last tile of a code that is not over-subscribed. -/
theorem K_top {f : Nat → Nat} {n : Nat} (hpos : 0 < Tc f n 15) :
    ∃ m, Tc f n 15 = m + 1 ∧
      Canon.K (lensOf f n) (Tc f n 15) = (val f n m + 1) * 2 ^ (15 - lenAt f n m) := by
  obtain ⟨m, hm⟩ : ∃ m, Tc f n 15 = m + 1 := ⟨Tc f n 15 - 1, by omega⟩
  refine ⟨m, hm, ?_⟩
  have hlt : m < Tc f n 15 := by omega
  rw [hm, Canon.K_succ, K_eq f n m hlt, L_eq f n hlt, Nat.add_mul, Nat.one_mul]

theorem fit_of_fits {f : Nat → Nat} {n : Nat} (hfit : Fits f n) : Fit (lensOf f n) := by
  show Canon.K (lensOf f n) (Canon.nz (lensOf f n)) ≤ 2 ^ 15
  rw [nz_eq_Tc]
  by_cases hpos : 0 < Tc f n 15
  · obtain ⟨m, hm, hK⟩ := K_top hpos
    rw [hK]
    have hlt : m < Tc f n 15 := by omega
    have h1 := val_lt hfit hlt
    obtain ⟨b1, b2⟩ := lenAt_bounds (f := f) (n := n) hlt
    have hp : 2 ^ 15 = 2 ^ lenAt f n m * 2 ^ (15 - lenAt f n m) := by rw [← Nat.pow_add]; congr 1; omega
    rw [hp]
    exact Nat.mul_le_mul_right _ h1
  · have : Tc f n 15 = 0 := by omega
    rw [this]; simp [Canon.K_zero]

theorem complete_of_Kc {f : Nat → Nat} {n : Nat} (hc : Kc f n 15 = 2 ^ 15) :
    Canon.K (lensOf f n) (Canon.nz (lensOf f n)) = 2 ^ 15 := by
  rw [nz_eq_Tc]
  have hpos : 0 < Tc f n 15 := by
    refine Classical.byContradiction fun h => ?_
    have h0 : Tc f n 15 = 0 := by omega
    have : Kc f n 15 = 0 := by
      have := Kc_gap (f := f) (n := n) 0 15 (by simpa [Tc] using h0)
      simpa [Kc] using this
    have : (2 : Nat) ^ 15 = 0 := by omega
    exact absurd this (by decide)
  obtain ⟨m, hm, hK⟩ := K_top hpos
  rw [hK, val_last hc hm]
  have hlt : m < Tc f n 15 := by omega
  obtain ⟨b1, b2⟩ := lenAt_bounds (f := f) (n := n) hlt
  rw [← Nat.pow_add]; congr 1; omega

/-! ### The three predicates in the model of the main proof -/

/-- The `j`-th symbol in sorted order fills the root cell `y` (a code of at most `R` bits whose bit-reversed value
`rev l v` is `y` modulo `2^l`; the C writes `table[huff + k * 2^l]`, `k < 2^(R - l)`). -/
def ShortAtF (f : Nat → Nat) (n R y j : Nat) : Prop :=
  j < Tc f n 15 ∧ lenAt f n j ≤ R ∧ y % 2 ^ lenAt f n j = rev (lenAt f n j) (val f n j)

/-- The `j`-th symbol is longer than `R` bits and its link sits at the root cell `y = rev R (pre j)` (the `low` of
the C). -/
def LongAtF (f : Nat → Nat) (n R y j : Nat) : Prop :=
  j < Tc f n 15 ∧ R < lenAt f n j ∧ rev R (pre f n R j) = y

/-- The `j`-th symbol is longer than `R` bits and belongs to the group `p` of the root link `rev R p`
(`pre j = val j / 2^(l - R)`, `e.p j` in the main loop). -/
def GroupF (f : Nat → Nat) (n R p j : Nat) : Prop := j < Tc f n 15 ∧ R < lenAt f n j ∧ pre f n R j = p

theorem grp_eq_pre {f : Nat → Nat} {n R j : Nat} (hj : j < Tc f n 15) (hR : R ≤ lenAt f n j) :
    Canon.grp (lensOf f n) R j = pre f n R j := by
  obtain ⟨b1, b2⟩ := lenAt_bounds (f := f) (n := n) hj
  unfold Canon.grp pre
  rw [K_eq f n j hj]
  have hp : 2 ^ (15 - R) = 2 ^ (15 - lenAt f n j) * 2 ^ (lenAt f n j - R) := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [hp, ← Nat.div_div_eq_div_mul, Nat.mul_div_cancel _ (two_pow_pos' _)]

theorem shortAt_iff (f : Nat → Nat) (n R y j : Nat) : ShortAt (lensOf f n) R y j ↔ ShortAtF f n R y j := by
  unfold ShortAt ShortAtF
  rw [nz_eq_Tc]
  constructor
  · rintro ⟨hj, hl, h⟩
    rw [L_eq f n hj] at hl h
    rw [H_eq f n hj] at h
    exact ⟨hj, hl, h⟩
  · rintro ⟨hj, hl, h⟩
    refine ⟨hj, by rw [L_eq f n hj]; exact hl, ?_⟩
    rw [L_eq f n hj, H_eq f n hj]; exact h

theorem longAt_iff (f : Nat → Nat) (n R y j : Nat) : LongAt (lensOf f n) R y j ↔ LongAtF f n R y j := by
  unfold LongAt LongAtF
  rw [nz_eq_Tc]
  constructor
  · rintro ⟨hj, hl, h⟩
    rw [L_eq f n hj] at hl
    refine ⟨hj, hl, ?_⟩
    rw [← h, Canon.H_mod_root _ (by rw [nz_eq_Tc]; exact hj) (by rw [L_eq f n hj]; omega),
      grp_eq_pre hj (by omega), canon_rev_eq]
  · rintro ⟨hj, hl, h⟩
    refine ⟨hj, by rw [L_eq f n hj]; exact hl, ?_⟩
    rw [Canon.H_mod_root _ (by rw [nz_eq_Tc]; exact hj) (by rw [L_eq f n hj]; omega),
      grp_eq_pre hj (by omega), canon_rev_eq, h]

theorem group_iff (f : Nat → Nat) (n R p j : Nat) : Group (lensOf f n) R p j ↔ GroupF f n R p j := by
  unfold Group GroupF
  rw [nz_eq_Tc]
  constructor
  · rintro ⟨hj, hl, h⟩
    rw [L_eq f n hj] at hl
    exact ⟨hj, hl, by rw [← grp_eq_pre hj (by omega)]; exact h⟩
  · rintro ⟨hj, hl, h⟩
    exact ⟨hj, by rw [L_eq f n hj]; exact hl, by rw [grp_eq_pre hj (by omega)]; exact h⟩

/-! ### Root covering -/

/-- A root cell of a complete code: filled by exactly one short code, or the link of a group of long codes (and then
filled by no short code). -/
def RootCellC (f : Nat → Nat) (n R y : Nat) : Prop :=
  (∃ j, ShortAtF f n R y j ∧ (∀ j', ShortAtF f n R y j' → j' = j) ∧ ∀ j', ¬ LongAtF f n R y j') ∨
  ((∃ j, LongAtF f n R y j) ∧ ∀ j', ¬ ShortAtF f n R y j')

/-- **Root covering (translation model).** For lengths that are not over-subscribed (`Fits`), every root cell
`y < 2^R` (`R ≤ 15`) is covered as in `RootCellC`, or by nothing at all. -/
theorem root_cover_fn {f : Nat → Nat} {n R y : Nat} (hfit : Fits f n) (hR : R ≤ 15) (hy : y < 2 ^ R) :
    RootCellC f n R y ∨ ((∀ j, ¬ ShortAtF f n R y j) ∧ ∀ j, ¬ LongAtF f n R y j) := by
  have hs := fun j => shortAt_iff f n R y j
  have hl := fun j => longAt_iff f n R y j
  rcases root_cover (fit_of_fits hfit) hR hy with ⟨j, h1, h2, h3⟩ | ⟨j, h1, h2⟩ | ⟨h1, h2, _⟩
  · exact Or.inl (Or.inl ⟨j, (hs j).mp h1, fun j' h => h2 j' ((hs j').mpr h), fun j' h => h3 j' ((hl j').mpr h)⟩)
  · exact Or.inl (Or.inr ⟨⟨j, (hl j).mp h1⟩, fun j' h => h2 j' ((hs j').mpr h)⟩)
  · exact Or.inr ⟨fun j' h => h1 j' ((hs j').mpr h), fun j' h => h2 j' ((hl j').mpr h)⟩

/-- **Root covering of a complete code (translation model).** No root cell stays unwritten. -/
theorem root_cover_complete_fn {f : Nat → Nat} {n R y : Nat} (hfit : Fits f n) (hc : Kc f n 15 = 2 ^ 15)
    (hR : R ≤ 15) (hy : y < 2 ^ R) : RootCellC f n R y := by
  have hs := fun j => shortAt_iff f n R y j
  have hl := fun j => longAt_iff f n R y j
  rcases root_cover (fit_of_fits hfit) hR hy with ⟨j, h1, h2, h3⟩ | ⟨j, h1, h2⟩ | ⟨h1, h2, h3⟩
  · exact Or.inl ⟨j, (hs j).mp h1, fun j' h => h2 j' ((hs j').mpr h), fun j' h => h3 j' ((hl j').mpr h)⟩
  · exact Or.inr ⟨⟨j, (hl j).mp h1⟩, fun j' h => h2 j' ((hs j').mpr h)⟩
  · exfalso
    rw [complete_of_Kc hc] at h3
    have h4 : Canon.rev R y * 2 ^ (15 - R) < 2 ^ 15 := by
      have hp : 2 ^ 15 = 2 ^ R * 2 ^ (15 - R) := by rw [← Nat.pow_add]; congr 1; omega
      rw [hp]
      exact Nat.mul_lt_mul_of_pos_right (Canon.rev_lt _ _) (two_pow_pos' _)
    omega

/-- The link of a long code is at a cell below `2^R`, and the codes of one group share the cell. -/
theorem longAtF_lt {f : Nat → Nat} {n R y j : Nat} (h : LongAtF f n R y j) : y < 2 ^ R := h.2.2 ▸ rev_lt _ _

/-! ### Group covering -/

/-- **Group covering (translation model, residue form).** For a complete code, a group `p` of long codes (`j0` is
one) and a sub-table width `c` with `R + c ≤ 15` that holds every code of the group (`lenAt j ≤ R + c`), every cell
`t` of the sub-table is covered by exactly one code `j` of the group: `t % 2^(lenAt j - R)` is `rev (lenAt j) (val j) >> R`. -/
theorem group_cover_fn {f : Nat → Nat} {n R p j0 : Nat} (hc : Kc f n 15 = 2 ^ 15) (hR : R ≤ 15)
    (hg0 : GroupF f n R p j0) {c : Nat} (hRc : R + c ≤ 15) (hcl : ∀ j, GroupF f n R p j → lenAt f n j ≤ R + c)
    (t : Nat) :
    ∃ j, GroupF f n R p j ∧ t % 2 ^ (lenAt f n j - R) = rev (lenAt f n j) (val f n j) / 2 ^ R ∧
      ∀ j', GroupF f n R p j' → t % 2 ^ (lenAt f n j' - R) = rev (lenAt f n j') (val f n j') / 2 ^ R → j' = j := by
  have hcl' : ∀ j, Group (lensOf f n) R p j → Canon.L (lensOf f n) j ≤ R + c := by
    intro j hj
    have := (group_iff f n R p j).mp hj
    rw [L_eq f n this.1]; exact hcl j this
  have hH : ∀ j, GroupF f n R p j → Canon.H (lensOf f n) j = rev (lenAt f n j) (val f n j) :=
    fun j hj => H_eq f n hj.1
  obtain ⟨j, hj, hm, hu⟩ := group_cover (complete_of_Kc hc) hR ((group_iff f n R p j0).mpr hg0) hRc hcl' t
  have hjF := (group_iff f n R p j).mp hj
  refine ⟨j, hjF, ?_, ?_⟩
  · rw [← hH j hjF, ← L_eq f n hjF.1]; exact hm
  · intro j' hj' heq
    refine hu j' ((group_iff f n R p j').mpr hj') ?_
    rw [hH j' hj', L_eq f n hj'.1]; exact heq

/-- **Group covering, index form (translation model).** Same hypotheses, and `t < 2^c`: the cell `t` is written
by exactly one code `j` of the group, as `next[(huff >> drop) + 2^(lenAt j - R) * t']` with `huff = rev (lenAt j) (val j)`,
`drop = R`, `t' < 2^(R + c - lenAt j)` (the fill loop of the C). -/
theorem group_cover_idx_fn {f : Nat → Nat} {n R p j0 : Nat} (hc : Kc f n 15 = 2 ^ 15) (hR : R ≤ 15)
    (hg0 : GroupF f n R p j0) {c : Nat} (hRc : R + c ≤ 15) (hcl : ∀ j, GroupF f n R p j → lenAt f n j ≤ R + c)
    {t : Nat} (ht : t < 2 ^ c) :
    ∃ j, GroupF f n R p j ∧
      (∃ t', t' < 2 ^ (R + c - lenAt f n j) ∧
        t = rev (lenAt f n j) (val f n j) / 2 ^ R + 2 ^ (lenAt f n j - R) * t') ∧
      ∀ j' t', GroupF f n R p j' →
        t = rev (lenAt f n j') (val f n j') / 2 ^ R + 2 ^ (lenAt f n j' - R) * t' → j' = j := by
  have hcl' : ∀ j, Group (lensOf f n) R p j → Canon.L (lensOf f n) j ≤ R + c := by
    intro j hj
    have := (group_iff f n R p j).mp hj
    rw [L_eq f n this.1]; exact hcl j this
  have hH : ∀ j, GroupF f n R p j → Canon.H (lensOf f n) j = rev (lenAt f n j) (val f n j) :=
    fun j hj => H_eq f n hj.1
  obtain ⟨j, hj, ⟨t', ht', he⟩, hu⟩ :=
    group_cover_idx (complete_of_Kc hc) hR ((group_iff f n R p j0).mpr hg0) hRc hcl' ht
  have hjF := (group_iff f n R p j).mp hj
  have hLj := L_eq f n hjF.1
  refine ⟨j, hjF, ⟨t', by rw [← hLj]; exact ht', ?_⟩, ?_⟩
  · rw [← hH j hjF, ← hLj]; exact he
  · intro j' t'' hj' heq
    refine hu j' t'' ((group_iff f n R p j').mpr hj') ?_
    rw [hH j' hj', L_eq f n hj'.1]; exact heq

/-- The cell index `rev l v >> R + 2^(l - R) * t'` that a code of the group writes is inside the sub-table. -/
theorem cell_lt_fn {f : Nat → Nat} {n R p j c : Nat} (hg : GroupF f n R p j) (hl : lenAt f n j ≤ R + c) {t' : Nat}
    (ht' : t' < 2 ^ (R + c - lenAt f n j)) :
    rev (lenAt f n j) (val f n j) / 2 ^ R + 2 ^ (lenAt f n j - R) * t' < 2 ^ c := by
  have hG := (group_iff f n R p j).mpr hg
  have hLj := L_eq f n hg.1
  have := cell_lt (c := c) hG (by rw [hLj]; exact hl) (t' := t') (by rw [hLj]; exact ht')
  rw [H_eq f n hg.1, hLj] at this
  exact this

/-! ### The incomplete code that the main loop accepts -/

/-- **The single code of length 1** (the only incomplete code with symbols that `inflate_table` builds a table
for: `Tc = 1`, `lenAt 0 = 1`, hence `R = 1`): the root cell `0` is filled by it and cell `1` is covered by no code,
neither short nor long. The C writes cell `1` after the loop, the entry `op = 64, bits = len - drop = 1, val = 0`
(`invalid_leaf`). Every other incomplete code makes `inflate_table` return `-1` before the first write, and the empty
code (`max = 0`) is handled before the loop (two entries `op = 64, bits = 1, val = 0`). -/
theorem root_single_fn {f : Nat → Nat} {n : Nat} (hT : Tc f n 15 = 1) (hl : lenAt f n 0 = 1) :
    ShortAtF f n 1 0 0 ∧ (∀ j, ¬ ShortAtF f n 1 1 j) ∧ ∀ y j, ¬ LongAtF f n 1 y j := by
  have h0 : val f n 0 = 0 := val_zero (by omega)
  refine ⟨⟨by omega, by omega, by rw [hl, h0]; simp [rev]⟩, ?_, ?_⟩
  · rintro j ⟨hj, _, h⟩
    have : j = 0 := by omega
    subst this
    rw [hl, h0] at h
    simp [rev] at h
  · rintro y j ⟨hj, hR, _⟩
    have : j = 0 := by omega
    subst this
    omega

end Zlib.Inftrees.Proofs.Cover
