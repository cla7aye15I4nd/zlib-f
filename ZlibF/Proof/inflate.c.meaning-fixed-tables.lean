import ZlibF.Proof.«inffixed.h.input-meaning»
import ZlibF.Proof.«inftrees.c.decode.short»
import ZlibF.Spec.InflateDecodeTableInvariant
import ZlibF.Spec.InflateDecodeTableStability
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

/-! ## Suffix stability of the fixed tables -/

namespace Zlib.Inflate.Proofs.MeaningFixed
open C ZlibF.Spec Zlib.Inffast.Proofs
open Zlib.Inftrees Zlib.Inftrees.Spec Zlib.Inftrees.Proofs
open Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeTableStability

/-- Two bit lists with the same first `b` bits give root values with the
same low `b` bits. -/
theorem read_mod_of_take {n b : Nat} {x y : List Bool} {v w : Nat} {rx ry : List Bool}
    (le : b ≤ n) (vx : x = bitsOfNat v n ++ rx) (wy : y = bitsOfNat w n ++ ry)
    (same : x.take b = y.take b) : v % 2 ^ b = w % 2 ^ b := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
  by_cases small : j < b
  · have jn : j < n := by omega
    have atX : x[j]? = some (v.testBit j) := by
      rw [vx, List.getElem?_append_left (by simpa [bitsOfNat_length] using jn)]
      simp [bitsOfNat, jn]
    have atY : y[j]? = some (w.testBit j) := by
      rw [wy, List.getElem?_append_left (by simpa [bitsOfNat_length] using jn)]
      simp [bitsOfNat, jn]
    have takeX : (x.take b)[j]? = some (v.testBit j) := by
      rw [List.getElem?_take]; simp [small, atX]
    have takeY : (y.take b)[j]? = some (w.testBit j) := by
      rw [List.getElem?_take]; simp [small, atY]
    rw [same, takeY] at takeX
    have := Option.some.inj takeX
    simp [small, this]
  · simp [small]

/-- A root table without links whose cells are replicated over every index
with the same low code bits has suffix-stable queries. -/
theorem stable_of_replicated {type : UInt32} {ca : Array Code} {root : Nat}
    (root15 : root ≤ 15) (size : 2 ^ root ≤ ca.size)
    (noLink : ∀ i, i < 2 ^ root → Subtable.IsLink type (ca.getD i default) = false)
    (rep : ∀ i, i < 2 ^ root → ∀ w, w < 2 ^ root →
      w % 2 ^ (ca.getD i default).bits.toNat = i % 2 ^ (ca.getD i default).bits.toNat →
      ca.getD w default = ca.getD i default) :
    StableQuery type ca 0 root := by
  have read : ∀ inp : List Bool, root ≤ inp.length →
      ∃ v rest, ZlibF.Spec.readBits root inp = some (v, rest) ∧ v < 2 ^ root ∧
        inp = bitsOfNat v root ++ rest ∧
        tableRead type ca 0 root inp =
          some (ca.getD v default, (ca.getD v default).bits.toNat) := by
    intro inp enough
    obtain ⟨v, rest, readEq, bound, source⟩ := ZlibF.Math.InflateDecode.read_total root inp enough
    refine ⟨v, rest, readEq, bound, source, ?_⟩
    have get : ca[0 + v]? = some (ca.getD v default) := by
      simp [Array.getD, show v < ca.size by omega]
    have link := noLink v bound
    unfold Subtable.IsLink at link
    simp only [tableRead, readEq, get, bind, Option.bind, link, Bool.false_eq_true, ite_false]
    rfl
  intro inp entry consumed query fits more
  have padLen : ∀ x : List Bool, root ≤ (DecodeShort.padded x).length := by
    intro x
    simp only [DecodeShort.padded, List.length_append, List.length_replicate]
    omega
  obtain ⟨v, rx, _, vb, vx, qv⟩ := read _ (padLen inp)
  obtain ⟨w, ry, _, wb, wy, qw⟩ := read _ (padLen (inp ++ more))
  rw [qv] at query
  obtain ⟨entryEq, consumedEq⟩ := Prod.mk.inj (Option.some.inj query)
  subst entryEq consumedEq
  have bitsLe : (ca.getD v default).bits.toNat ≤ inp.length := fits
  have takes : (DecodeShort.padded inp).take (ca.getD v default).bits.toNat =
      (DecodeShort.padded (inp ++ more)).take (ca.getD v default).bits.toNat := by
    simp only [DecodeShort.padded, List.append_assoc]
    rw [List.take_append_of_le_length bitsLe, List.take_append_of_le_length bitsLe]
  by_cases rootLe : (ca.getD v default).bits.toNat ≤ root
  · have modEq := read_mod_of_take rootLe vx wy takes
    rw [qw, rep v vb w wb modEq.symm]
  · -- a cell longer than the root reads the whole root index from `inp`
    have takesRoot : (DecodeShort.padded inp).take root =
        (DecodeShort.padded (inp ++ more)).take root := by
      have rl : root ≤ inp.length := by omega
      simp only [DecodeShort.padded, List.append_assoc]
      rw [List.take_append_of_le_length rl, List.take_append_of_le_length rl]
    have modEq := read_mod_of_take (Nat.le_refl root) vx wy takesRoot
    rw [Nat.mod_eq_of_lt vb, Nat.mod_eq_of_lt wb] at modEq
    subst modEq
    exact qw

/-- Field-wise equality of two table cells. -/
def codeEq (a b : Code) : Bool := a.op == b.op && a.bits == b.bits && a.val == b.val

theorem codeEq_eq {a b : Code} (same : codeEq a b = true) : a = b := by
  cases a; cases b
  simp only [codeEq, Bool.and_eq_true, beq_iff_eq] at same
  obtain ⟨⟨op, bits⟩, val⟩ := same
  subst op bits val
  rfl

/-- The replication pattern of `lenfix`, checked cell by cell. -/
def lenfixReplicated : Bool :=
  (List.range 512).all fun i =>
    let b := (Zlib.InffixedH.lenfix.getD i default).bits.toNat
    (List.range (2 ^ (9 - b))).all fun k =>
      codeEq (Zlib.InffixedH.lenfix.getD (i % 2 ^ b + k * 2 ^ b) default)
        (Zlib.InffixedH.lenfix.getD i default)

/-- The replication pattern of `distfix`. -/
def distfixReplicated : Bool :=
  (List.range 32).all fun i =>
    let b := (Zlib.InffixedH.distfix.getD i default).bits.toNat
    (List.range (2 ^ (5 - b))).all fun k =>
      codeEq (Zlib.InffixedH.distfix.getD (i % 2 ^ b + k * 2 ^ b) default)
        (Zlib.InffixedH.distfix.getD i default)

theorem lenfixReplicated_true : lenfixReplicated = true := by decide +kernel

theorem distfixReplicated_true : distfixReplicated = true := by decide +kernel

/-- From the cell check: an index with the same low code bits is a copy. -/
theorem rep_of_check {ca : Array Code} {root : Nat}
    (check : ((List.range (2 ^ root)).all fun i =>
      let b := (ca.getD i default).bits.toNat
      (List.range (2 ^ (root - b))).all fun k =>
        codeEq (ca.getD (i % 2 ^ b + k * 2 ^ b) default) (ca.getD i default)) = true)
    (bitsLe : ∀ i, i < 2 ^ root → (ca.getD i default).bits.toNat ≤ root) :
    ∀ i, i < 2 ^ root → ∀ w, w < 2 ^ root →
      w % 2 ^ (ca.getD i default).bits.toNat = i % 2 ^ (ca.getD i default).bits.toNat →
      ca.getD w default = ca.getD i default := by
  intro i ib w wb modEq
  have cell := List.all_eq_true.mp check i (List.mem_range.mpr ib)
  simp only at cell
  generalize hb : (ca.getD i default).bits.toNat = b at cell modEq
  have bLe : b ≤ root := hb ▸ bitsLe i ib
  have kLt : w / 2 ^ b < 2 ^ (root - b) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos b), ← Nat.pow_add, Nat.sub_add_cancel bLe]
    exact wb
  have copy := List.all_eq_true.mp cell (w / 2 ^ b) (List.mem_range.mpr kLt)
  have split : i % 2 ^ b + w / 2 ^ b * 2 ^ b = w := by
    rw [← modEq, Nat.mod_add_div' w (2 ^ b)]
  rw [split] at copy
  exact codeEq_eq copy

theorem lenfix_stable : StableQuery LENS Zlib.InffixedH.lenfix 0 9 := by
  have bitsLe : ∀ i, i < 2 ^ 9 → (Zlib.InffixedH.lenfix.getD i default).bits.toNat ≤ 9 :=
    fun i ib => (lenfix_root_bits ⟨i, ib⟩).2
  refine stable_of_replicated (by decide) (by simp [lenfix_size]) ?_
    (rep_of_check lenfixReplicated_true bitsLe)
  intro i ib
  exact lenfix_no_subtable ⟨i, ib⟩

theorem distfix_stable : StableQuery DISTS Zlib.InffixedH.distfix 0 5 := by
  have bitsLe : ∀ i, i < 2 ^ 5 → (Zlib.InffixedH.distfix.getD i default).bits.toNat ≤ 5 :=
    fun i ib => (distfix_root_bits ⟨i, ib⟩).2
  refine stable_of_replicated (by decide) (by simp [distfix_size]) ?_
    (rep_of_check distfixReplicated_true bitsLe)
  intro i ib
  exact distfix_no_subtable ⟨i, ib⟩

end Zlib.Inflate.Proofs.MeaningFixed
