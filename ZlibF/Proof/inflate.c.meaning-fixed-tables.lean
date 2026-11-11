import ZlibF.Proof.«inffixed.h.input-meaning»
import ZlibF.Proof.«inftrees.c.decode.short»
import ZlibF.Spec.InflateDecodeTableInvariant
import ZlibF.Proof.«inffast.c.tableok»

/-!
# inflate.c: the fixed tables have the decode-table meaning

`inflate_fixed` installs the static tables `lenfix` (root 9) and `distfix`
(root 5) of `inffixed.h`. They are not the output of `inflate_table`, so the
constructor results do not cover them. Here they get the same invariant
`DecodeTableInvariant.Inv` as a constructed table, with the fixed code
lengths of the format. The proof uses the per-cell checks of
`inffixed.h.meaning` and the full-input lookups of `inffixed.h.input-meaning`.

`Inv.of_full_input` is the general step: a table whose root lookups of full
width decode the canonical code of an acceptable alphabet, with no links,
has the whole invariant, short (zero-padded) lookups included.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Zlib.Inflate.Proofs.MeaningFixed
open C ZlibF.Spec Zlib.Inffast.Proofs
open Zlib.Inftrees Zlib.Inftrees.Spec Zlib.Inftrees.Proofs
open Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness
open Zlib.Inftrees.Spec.DecodeTableInvariant

/-- Full-width root lookups that decode the canonical code of `lens`. -/
def FullInput (type : UInt32) (ca : Array Code) (root : Nat) (lens : List Nat) : Prop :=
  ∀ inp : List Bool, root ≤ inp.length →
    ∃ (symbol : Nat) (rest : List Bool) (entry : Code),
      decodeSym lens inp = some (symbol, rest) ∧
      tableRead type ca 0 root inp = some (entry, entry.bits.toNat) ∧
      entry.bits.toNat = lens.getD symbol 0 ∧
      rest = inp.drop entry.bits.toNat ∧
      SymbolEntry type symbol entry ∧
      (LeafAccepted type entry ↔ ValidSymbol type symbol)

/-- A table with full-width meaning has the short-lookup and classification
fields of `Inv`; the shape fields are given. -/
theorem Inv.of_full_input {type : UInt32} {ca : Array Code} {root used : Nat}
    {lens : List Nat}
    (kind : type = LENS ∨ type = DISTS)
    (rootTable : RootTable.Safe ca 0 root)
    (subtables : ∀ i entry, i < 2 ^ root → ca[0 + i]? = some entry →
      Subtable.IsLink type entry = true →
      entry.bits.toNat = root ∧ Subtable.Safe ca 0 entry)
    (readExtent : TableReadExtent type ca 0 root used)
    (acceptable : Acceptable (kindOf type) lens)
    (full : FullInput type ca root lens) :
    Inv type ca 0 root used lens := by
  have root15 : root ≤ 15 := rootTable.2.1
  refine ⟨kind, rootTable, subtables, readExtent, acceptable, ?_, ?_⟩
  · intro inp entry consumed query fits accepted
    have enough : root ≤ (DecodeShort.padded inp).length := by
      simp only [DecodeShort.padded, List.length_append, List.length_replicate]
      omega
    obtain ⟨symbol, rest, entry', decoded, query', length, _restEq, meaning, classified⟩ :=
      full _ enough
    obtain ⟨entries, consumedEq⟩ := Prod.mk.inj (Option.some.inj (query.symm.trans query'))
    subst entry'
    subst consumedEq
    have original : decodeSym lens inp = some (symbol, inp.drop entry.bits.toNat) :=
      decode_unpad acceptable decoded length fits
    refine ⟨symbol, classified.mp accepted, meaning, length, original, ?_⟩
    intro more
    exact ZlibF.Spec.Proofs.ext_acceptable acceptable inp symbol _ more original
  · intro inp enough
    obtain ⟨symbol, rest, entry, decoded, query, _length, _restEq, _meaning, classified⟩ :=
      full inp (by omega)
    refine ⟨entry, entry.bits.toNat, query, ?_⟩
    constructor
    · intro accepted
      exact ⟨symbol, rest, decoded, classified.mp accepted⟩
    · rintro ⟨symbol', rest', decoded', valid⟩
      have same := Option.some.inj (decoded.symm.trans decoded')
      obtain ⟨symbols, _⟩ := Prod.mk.inj same
      subst symbols
      exact classified.mpr valid

/-! ## Finite facts about the static arrays -/

theorem lenfix_size : Zlib.InffixedH.lenfix.size = 512 := by decide

theorem distfix_size : Zlib.InffixedH.distfix.size = 32 := by decide

theorem lenfix_root_bits : ∀ i : Fin 512,
    1 ≤ (Zlib.InffixedH.lenfix.getD i.val default).bits.toNat ∧
      (Zlib.InffixedH.lenfix.getD i.val default).bits.toNat ≤ 9 := by
  decide +kernel

theorem distfix_root_bits : ∀ i : Fin 32,
    1 ≤ (Zlib.InffixedH.distfix.getD i.val default).bits.toNat ∧
      (Zlib.InffixedH.distfix.getD i.val default).bits.toNat ≤ 5 := by
  decide +kernel

theorem lenfix_no_len_link : ∀ i : Fin 512,
    ¬ Zlib.Inffast.Spec.LenLink (Zlib.InffixedH.lenfix.getD i.val default) := by
  decide +kernel

theorem distfix_no_dist_link : ∀ i : Fin 32,
    ¬ Zlib.Inffast.Spec.DistLink (Zlib.InffixedH.distfix.getD i.val default) := by
  decide +kernel

theorem lenfix_no_subtable : ∀ i : Fin 512,
    Subtable.IsLink LENS (Zlib.InffixedH.lenfix.getD i.val default) = false := by
  decide +kernel

theorem distfix_no_subtable : ∀ i : Fin 32,
    Subtable.IsLink DISTS (Zlib.InffixedH.distfix.getD i.val default) = false := by
  decide +kernel

theorem fixedLit_acceptable : Acceptable .litLen fixedLitLens := by decide

theorem fixedDist_acceptable : Acceptable .dist fixedDistLens := by decide

/-- A cell of a static array, read with `getElem?`, is its `getD` value. -/
theorem get_of_lt {ca : Array Code} {i : Nat} (inside : i < ca.size) :
    ca[i]? = some (ca.getD i default) := by
  simp [Array.getD, inside]

/-! ## The two invariants -/

/-- `lenfix` is the root-9 decoding table of the fixed literal/length code. -/
theorem lenfix_inv :
    Inv LENS Zlib.InffixedH.lenfix 0 9 512 fixedLitLens := by
  have size := lenfix_size
  refine Inv.of_full_input (Or.inl rfl) ?_ ?_ ?_ ?_ ?_
  · refine ⟨by decide, by decide, by simp [size], ?_⟩
    intro i inside
    have i512 : i < 512 := by simpa using inside
    refine ⟨_, ?_, (lenfix_root_bits ⟨i, i512⟩).1, (lenfix_root_bits ⟨i, i512⟩).2⟩
    simpa using get_of_lt (ca := Zlib.InffixedH.lenfix) (by omega)
  · intro i entry inside get link
    have i512 : i < 512 := by simpa using inside
    have cell : entry = Zlib.InffixedH.lenfix.getD i default := by
      have := get_of_lt (ca := Zlib.InffixedH.lenfix) (i := i) (by omega)
      simp only [Nat.zero_add] at get
      exact Option.some.inj (get.symm.trans this)
    rw [cell, lenfix_no_subtable ⟨i, i512⟩] at link
    cases link
  · refine ⟨by decide, by decide, by simp, ?_⟩
    intro i inside entry link
    have i512 : i < 512 := by simpa using inside
    rcases link with ⟨_, leaf⟩ | ⟨wrong, _⟩
    · exact (lenfix_no_len_link ⟨i, i512⟩ (by simpa [entry] using leaf)).elim
    · exact absurd wrong (by decide)
  · exact fixedLit_acceptable
  · intro inp enough
    exact Zlib.InffixedH.Proofs.lenfix_full_input inp enough

/-- `distfix` is the root-5 decoding table of the fixed distance code. -/
theorem distfix_inv :
    Inv DISTS Zlib.InffixedH.distfix 0 5 32 fixedDistLens := by
  have size := distfix_size
  refine Inv.of_full_input (Or.inr rfl) ?_ ?_ ?_ ?_ ?_
  · refine ⟨by decide, by decide, by simp [size], ?_⟩
    intro i inside
    have i32 : i < 32 := by simpa using inside
    refine ⟨_, ?_, (distfix_root_bits ⟨i, i32⟩).1, (distfix_root_bits ⟨i, i32⟩).2⟩
    simpa using get_of_lt (ca := Zlib.InffixedH.distfix) (by omega)
  · intro i entry inside get link
    have i32 : i < 32 := by simpa using inside
    have cell : entry = Zlib.InffixedH.distfix.getD i default := by
      have := get_of_lt (ca := Zlib.InffixedH.distfix) (i := i) (by omega)
      simp only [Nat.zero_add] at get
      exact Option.some.inj (get.symm.trans this)
    rw [cell, distfix_no_subtable ⟨i, i32⟩] at link
    cases link
  · refine ⟨by decide, by decide, by simp, ?_⟩
    intro i inside entry link
    have i32 : i < 32 := by simpa using inside
    rcases link with ⟨wrong, _⟩ | ⟨_, leaf⟩
    · exact absurd wrong (by decide)
    · exact (distfix_no_dist_link ⟨i, i32⟩ (by simpa [entry] using leaf)).elim
  · exact fixedDist_acceptable
  · intro inp enough
    exact Zlib.InffixedH.Proofs.distfix_full_input inp enough

end Zlib.Inflate.Proofs.MeaningFixed
