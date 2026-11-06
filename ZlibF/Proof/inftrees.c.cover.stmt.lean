import ZlibF.Proof.«inftrees.c.cover.fn»
import ZlibF.Proof.«inftrees.c.cover.leaf»

/-!
# inflate_table: what the written cells are (statements for the content invariant)

Heap-free lemmas about the table that the main loop of `inflate_table` builds. The model is that of the main proof
(`f s` the length of symbol `s`, `n` the number of symbols, `Tc f n 15` the number of coded symbols, `lenAt f n j`
and `val f n j` the length and canonical value of the `j`-th coded symbol in sorted order, `pre f n R j` the first
`R` bits of its code, `rev` the bit reversal of `huff`); `R` is the root width. The lemmas are proved in the modules
`inftrees.c.cover.tile` (Kraft tiles of `[0, 2^15)`), `.root`, `.group` (in the list model `ls = lensOf f n` of
`inftrees.c.canon`), `.fn` (translated to the model of the main proof) and `.leaf` (the values of `here`).

## Root table (`inftrees.c.cover.fn`)

* `ShortAtF f n R y j`: the `j`-th symbol has `lenAt j ≤ R` and `y % 2^(lenAt j) = rev (lenAt j) (val j)`, i.e. `y` is
  one of the cells `huff + k * 2^len` (`k < 2^(R - len)`, `drop = 0`) that the fill loop writes for it.
* `LongAtF f n R y j`: `lenAt j > R` and `y = rev R (pre f n R j)`, the cell `low` where the link of its group is
  written.
* `GroupF f n R p j`: `lenAt j > R` and `pre f n R j = p` (`e.p j = p` of the main loop).
* `root_cover_fn` (`Fits`, `R ≤ 15`, `y < 2^R`): the cell is covered as `RootCellC f n R y` (exactly one short code
  and no link, or a link and no short code), or by nothing. `root_cover_complete_fn` (also `Kc f n 15 = 2^15`): always
  `RootCellC`.
* `root_single_fn`: the single code of length 1 (`Tc = 1`, `lenAt 0 = 1`, `R = 1`): cell 0 is `ShortAtF`, cell 1 is
  covered by nothing (the C writes the invalid entry there after the loop). Every other incomplete set makes the call
  return `-1` before any write, and the empty set returns before the loop.
* `longAtF_lt`: `LongAtF f n R y j → y < 2^R`.

## Sub-table (`inftrees.c.cover.fn`)

* `group_cover_fn`: complete code, `R ≤ 15`, a group `p` (`GroupF f n R p j0`), a width `c` with `R + c ≤ 15` and
  `∀ j, GroupF f n R p j → lenAt j ≤ R + c` (which `TabSt` has): every cell `t` has exactly one code `j` of the group
  with `t % 2^(lenAt j - R) = rev (lenAt j) (val j) / 2^R` (`/ 2^R` is `huff >> drop`).
* `group_cover_idx_fn` (also `t < 2^c`): `t = rev (lenAt j) (val j) / 2^R + 2^(lenAt j - R) * t'` with
  `t' < 2^(R + c - lenAt j)`, for exactly one code `j` of the group (the index of the C).
* `cell_lt_fn`: every such index is `< 2^c`, so the fill loop of a group stays in its sub-table.

## Values written (`inftrees.c.cover.leaf`)

* `lenLeaf_of d w`, `w < 288`: an entry `e` whose `op`, `val` are the C values for symbol `w` (literal `op = 0` for
  `w < 256`; `op = 96` for `w = 256`; `op = lext[w-257]`, `val = lbase[w-257]` for `w ≥ 257`) and with
  `e.bits + d ≤ 15` is a `LenLeaf d e` (`inffast.c.tableok`).
* `distLeaf_of d w`, `w < 32`: the same with `dext[w]`, `dbase[w]` gives `DistLeaf d e`.
* `invalid_leaf d b`: `⟨64, b, 0⟩` is both a `LenLeaf d` and a `DistLeaf d` (empty code; the cell after a single
  length-1 code).
* `bits_toNat`, `bits_add_drop`: `(len - drop).toUInt8` is `len - drop`, and bits plus `drop` is at most `15`.

## Size

`used ≤ ENOUGH_LENS / ENOUGH_DISTS / 128` is the `tooBig` check of the C together with `2^R ≤ 128` for `CODES`
(`R = mxl ≤ 7`): it is already `TabSt`'s `s.used.toNat ≤ e.cap`, which the main loop keeps; nothing more is needed.
-/

namespace Zlib.Inftrees.Proofs.Cover

/-! ### Non-vacuity: the lengths `1, 2, 3, 3` with root width 2

The code is complete; the codes of length 3 (`110`, `111`) form the group `p = 3` of the link at the root cell
`rev 2 3 = 3` and fill the two cells of a sub-table of width 1. -/

private def f4 : Nat → Nat := fun s => [1, 2, 3, 3].getD s 0

private theorem f4_T : Tc f4 4 15 = 4 := by decide +kernel
private theorem f4_K : Kc f4 4 15 = 2 ^ 15 := by decide +kernel
private theorem f4_fits : Fits f4 4 := by
  intro l h1 h2
  exact (by decide +kernel : ∀ l, l < 16 → Kc f4 4 l ≤ 2 ^ l) l (by omega)

example (y : Nat) (hy : y < 2 ^ 2) : RootCellC f4 4 2 y :=
  root_cover_complete_fn f4_fits f4_K (by omega) hy

example (t : Nat) (ht : t < 2 ^ 1) :
    ∃ j, GroupF f4 4 2 3 j ∧
      (∃ t', t' < 2 ^ (2 + 1 - lenAt f4 4 j) ∧
        t = rev (lenAt f4 4 j) (val f4 4 j) / 2 ^ 2 + 2 ^ (lenAt f4 4 j - 2) * t') ∧
      ∀ j' t', GroupF f4 4 2 3 j' →
        t = rev (lenAt f4 4 j') (val f4 4 j') / 2 ^ 2 + 2 ^ (lenAt f4 4 j' - 2) * t' → j' = j :=
  group_cover_idx_fn (j0 := 2) f4_K (by omega)
    (by unfold GroupF; rw [f4_T]; decide +kernel) (c := 1) (by omega)
    (by
      intro j hj
      have h : ∀ j, j < 4 → GroupF f4 4 2 3 j → lenAt f4 4 j ≤ 2 + 1 := by
        unfold GroupF; rw [f4_T]; decide +kernel
      exact h j (by have := hj.1; rw [f4_T] at this; exact this) hj)
    ht

end Zlib.Inftrees.Proofs.Cover
