import ZlibF.Proof.«inffast.c.tableok»
import ZlibF.Zlib.«inftrees.c»

/-!
# The leaves that `inflate_table` writes

`inflate_table` stores, for the symbol `w` of a code, the entry `here` with `op` and `val` taken from `lbase` / `lext`
(`LENS`: `match = 257`) or `dbase` / `dext` (`DISTS`: `match = 0`) or the literal/end-of-block cases, and
`bits = len - drop`. `LenLeaf` and `DistLeaf` (`inffast.c.tableok`) are the shapes `inflate_fast` needs. This module
proves them for every symbol that the call can read (`w < 288` for `LENS`, `w < 32` for `DISTS`) by kernel
evaluation of the tables of the translation, and that `bits + drop ≤ 15`.
-/
set_option autoImplicit false

namespace Zlib.Inftrees.Proofs.Cover
open C Zlib.Inffast.Spec

set_option maxRecDepth 100000 in
/-- All the `LENS` symbols `257 ≤ w < 288` get a length base (`w ≤ 285`: extra bits `≤ 5`, base `≥ 3`, base plus
the largest extra at most 258) or an invalid code (`286`, `287`). -/
theorem lext_lbase_shape : ∀ w, w < 288 → 257 ≤ w →
    let op := (Zlib.Inftrees.lext.getD (w - 257) 0).toUInt8
    let v := Zlib.Inftrees.lbase.getD (w - 257) 0
    (op &&& 16 ≠ 0 ∧ (op &&& 15).toNat ≤ 5 ∧ 3 ≤ v.toNat ∧ v.toNat + 2 ^ (op &&& 15).toNat ≤ 259) ∨
    (op &&& 16 = 0 ∧ op &&& 64 ≠ 0) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- All the `DISTS` symbols `w < 32`: a distance base (`w ≤ 29`: extra bits `≤ 13`, base `≥ 1`) or an invalid code
(`30`, `31`). -/
theorem dext_dbase_shape : ∀ w, w < 32 →
    let op := (Zlib.Inftrees.dext.getD w 0).toUInt8
    let v := Zlib.Inftrees.dbase.getD w 0
    (op &&& 16 ≠ 0 ∧ (op &&& 15).toNat ≤ 13 ∧ 1 ≤ v.toNat) ∨ (op &&& 16 = 0 ∧ op &&& 64 ≠ 0) := by
  decide +kernel

/-- The leaf stored for a symbol `w < 288` of a `LENS` code is a `LenLeaf` after `d` dropped bits: a literal
(`w < 256`, `op = 0`), the end of block (`w = 256`, `op = 96`), or `op = lext[w - 257]`, `val = lbase[w - 257]` for
`257 ≤ w < 288`; the stored `bits` plus `d` is at most 15. -/
theorem lenLeaf_of (d w : Nat) (hw : w < 288) (e : Code) (hb : e.bits.toNat + d ≤ 15)
    (h0 : w < 256 → e.op = 0) (h1 : w = 256 → e.op = 96)
    (h2 : 257 ≤ w → e.op = (Zlib.Inftrees.lext.getD (w - 257) 0).toUInt8 ∧
      e.val = Zlib.Inftrees.lbase.getD (w - 257) 0) : LenLeaf d e := by
  refine ⟨hb, ?_⟩
  by_cases a : w < 256
  · exact Or.inl (h0 a)
  · by_cases b : w = 256
    · have := h1 b; right; right; rw [this]; decide
    · obtain ⟨ho, hv⟩ := h2 (by omega)
      have := lext_lbase_shape w hw (by omega)
      simp only at this
      rw [ho, hv]
      exact Or.inr this

/-- The leaf stored for a symbol `w < 32` of a `DISTS` code is a `DistLeaf`: `op = dext[w]`, `val = dbase[w]`. -/
theorem distLeaf_of (d w : Nat) (hw : w < 32) (e : Code) (hb : e.bits.toNat + d ≤ 15)
    (h : e.op = (Zlib.Inftrees.dext.getD w 0).toUInt8 ∧ e.val = Zlib.Inftrees.dbase.getD w 0) : DistLeaf d e := by
  refine ⟨hb, ?_⟩
  have := dext_dbase_shape w hw
  simp only at this
  rw [h.1, h.2]
  exact this

/-- The entry `op = 64, val = 0` (invalid code) written for the empty code, and for the unused second cell of the
single-symbol code, is a leaf of both tables. -/
theorem invalid_leaf (d : Nat) (b : UInt8) (hb : b.toNat + d ≤ 15) :
    LenLeaf d ⟨64, b, 0⟩ ∧ DistLeaf d ⟨64, b, 0⟩ :=
  have h1 : (64 : UInt8) &&& 16 = 0 := by decide
  have h2 : (64 : UInt8) &&& 64 ≠ 0 := by decide
  ⟨⟨hb, Or.inr (Or.inr ⟨h1, h2⟩)⟩, ⟨hb, Or.inr ⟨h1, h2⟩⟩⟩

/-- `here.bits = (unsigned char)(len - drop)`: with `drop ≤ len ≤ 15` it is `len - drop`, so that bits plus the bits
`drop` already consumed is `len ≤ 15`. -/
theorem bits_toNat {len drop : UInt32} (h1 : drop.toNat ≤ len.toNat) (h2 : len.toNat ≤ 15) :
    (len - drop).toUInt8.toNat = len.toNat - drop.toNat := by
  rw [UInt32.toNat_toUInt8, UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; exact h1)]
  omega

/-- The bits stored plus the bits already dropped are at most 15 (`LenLeaf`/`DistLeaf` first conjunct). -/
theorem bits_add_drop {len drop : UInt32} (h1 : drop.toNat ≤ len.toNat) (h2 : len.toNat ≤ 15) :
    (len - drop).toUInt8.toNat + drop.toNat ≤ 15 := by
  rw [bits_toNat h1 h2]; omega

end Zlib.Inftrees.Proofs.Cover
