import ZlibF.Proof.«inflate.c.lookup-subtable»
import ZlibF.Proof.«inftrees.c.decode.stability-rejection»
import ZlibF.Spec.InflateDecodeTableInvariant
import ZlibF.Spec.InflateDecodeTableStability

/-!
# inflate.c: the meaning of a slow table lookup

`lookup1` reads `table[BITS(root)]` and `lookup2` reads
`table[last.val + (BITS(last.bits + last.op) >> last.bits)]`, refilling the
bit buffer until the selected entry fits the held bits. The existing lookup
modules give the selected cell (`codeLookupValue`, `subLookupValue`) and the
bit stream. This module connects the cell to the independent decoder:

* the cell is the result of `tableRead` on the held bits, zero padded to
  fifteen bits (`tableRead_root`, `tableRead_link`), for any number of held
  bits, also fewer than the root width;
* on a table with `Inv` and `StableQuery`, a fitted accepted leaf is the
  canonical symbol of the held bits for every continuation of the input, and
  a fitted rejected leaf rules out a valid symbol on every continuation
  (`fitted_leaf_meaning`).

Nothing here fixes a table width or a window size.
-/

set_option autoImplicit false

namespace Zlib.Inflate.Proofs.MeaningLookup
open C Zlib.Inflate Zlib.Inflate.Proofs ZlibF.Spec
open Zlib.Inftrees Zlib.Inftrees.Spec Zlib.Inftrees.Proofs
open Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness
open Zlib.Inftrees.Spec.DecodeTableInvariant Zlib.Inftrees.Spec.DecodeTableStability

/-! ## Reading the held bits -/

theorem readBits_natBits_append : ∀ (k v : Nat) (r : List Bool),
    readBits k (natBits k v ++ r) = some (v % 2 ^ k, r)
  | 0, v, r => by simp [readBits, natBits, Nat.mod_one]
  | k + 1, v, r => by
    simp only [natBits, List.cons_append, readBits, readBits_natBits_append k (v / 2) r]
    congr 2
    have split : v % (2 * 2 ^ k) = v % 2 + 2 * (v / 2 % 2 ^ k) := Nat.mod_mul
    have bit : (v % 2 == 1) = true ↔ v % 2 = 1 := by simp
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, split]
    by_cases odd : v % 2 = 1
    · rw [if_pos (bit.mpr odd)]
      omega
    · rw [if_neg (by simpa [bit] using odd)]
      omega

theorem natBits_zero : ∀ k : Nat, natBits k 0 = List.replicate k false
  | 0 => rfl
  | k + 1 => by simp [natBits, natBits_zero k, List.replicate_succ]

/-- Held bits, zero padded to fifteen, are the low bits of the hold value. -/
theorem padded_natBits {n v : Nat} (lt : v < 2 ^ n) :
    DecodeShort.padded (natBits n v) = natBits (n + (15 - n)) v := by
  rw [natBits_add, Nat.div_eq_of_lt lt, natBits_zero]
  simp [DecodeShort.padded, natBits_length]

theorem readBits_natBits_prefix {k n v : Nat} (le : k ≤ n) :
    ∃ rest, readBits k (natBits n v) = some (v % 2 ^ k, rest) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le le
  rw [natBits_add]
  exact ⟨_, readBits_natBits_append k v _⟩

theorem natBits_drop {k n v : Nat} (le : k ≤ n) :
    (natBits n v).drop k = natBits (n - k) (v / 2 ^ k) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le le
  rw [natBits_add, List.drop_left' (natBits_length k v)]
  simp

/-! ## The selected cell is `tableRead` of the padded held bits -/

/-- The second-level index of `lookup2` as a function of the hold value. -/
def subLookupIndexNat (last : Code) (hold : Nat) : Nat :=
  hold % 2 ^ (last.bits.toNat + last.op.toNat) / 2 ^ last.bits.toNat

theorem subLookupIndex_eq (last : Code) (l : IL) :
    subLookupIndex last l = subLookupIndexNat last l.hold.toNat := rfl

/-- A root cell that is not a link. -/
theorem tableRead_root {type : UInt32} {ca : Array Code} {offset root bits hold : Nat}
    (lt : hold < 2 ^ bits) (root15 : root ≤ 15)
    (inside : offset + hold % 2 ^ root < ca.size)
    (leaf : Subtable.IsLink type (ca.getD (offset + hold % 2 ^ root) default) = false) :
    tableRead type ca offset root (DecodeShort.padded (natBits bits hold)) =
      some (ca.getD (offset + hold % 2 ^ root) default,
        (ca.getD (offset + hold % 2 ^ root) default).bits.toNat) := by
  rw [padded_natBits lt]
  obtain ⟨rest, read⟩ := readBits_natBits_prefix (v := hold) (show root ≤ bits + (15 - bits) by omega)
  have get : ca[offset + hold % 2 ^ root]? = some (ca.getD (offset + hold % 2 ^ root) default) := by
    simp [Array.getD, inside]
  unfold Subtable.IsLink at leaf
  simp only [tableRead, read, get, bind, Option.bind, leaf, Bool.false_eq_true, ite_false]
  rfl

/-- A root link and the second-level cell it selects. -/
theorem tableRead_link {type : UInt32} {ca : Array Code} {offset root bits hold : Nat}
    (lt : hold < 2 ^ bits) (root15 : root ≤ 15)
    (inside : offset + hold % 2 ^ root < ca.size)
    (link : Subtable.IsLink type (ca.getD (offset + hold % 2 ^ root) default) = true)
    (width : (ca.getD (offset + hold % 2 ^ root) default).bits.toNat +
      (ca.getD (offset + hold % 2 ^ root) default).op.toNat ≤ 15)
    (inside2 : offset + (ca.getD (offset + hold % 2 ^ root) default).val.toNat +
      subLookupIndexNat (ca.getD (offset + hold % 2 ^ root) default) hold < ca.size) :
    tableRead type ca offset root (DecodeShort.padded (natBits bits hold)) =
      some (ca.getD (offset + (ca.getD (offset + hold % 2 ^ root) default).val.toNat +
          subLookupIndexNat (ca.getD (offset + hold % 2 ^ root) default) hold) default,
        (ca.getD (offset + hold % 2 ^ root) default).bits.toNat +
          (ca.getD (offset + (ca.getD (offset + hold % 2 ^ root) default).val.toNat +
            subLookupIndexNat (ca.getD (offset + hold % 2 ^ root) default) hold)
            default).bits.toNat) := by
  generalize hfirst : ca.getD (offset + hold % 2 ^ root) default = first at *
  rw [padded_natBits lt]
  obtain ⟨rest, read⟩ := readBits_natBits_prefix (v := hold) (show root ≤ bits + (15 - bits) by omega)
  have get : ca[offset + hold % 2 ^ root]? = some first := by
    rw [← hfirst]; simp [Array.getD, inside]
  have drop := natBits_drop (v := hold) (show first.bits.toNat ≤ bits + (15 - bits) by omega)
  obtain ⟨rest2, read2⟩ := readBits_natBits_prefix (v := hold / 2 ^ first.bits.toNat)
    (show first.op.toNat ≤ bits + (15 - bits) - first.bits.toNat by omega)
  have index : hold / 2 ^ first.bits.toNat % 2 ^ first.op.toNat = subLookupIndexNat first hold := by
    unfold subLookupIndexNat
    rw [ZlibF.Math.InflateLookup.slice_eq]
  rw [index] at read2
  have get2 : ca[offset + first.val.toNat + subLookupIndexNat first hold]? =
      some (ca.getD (offset + first.val.toNat + subLookupIndexNat first hold) default) := by
    simp [Array.getD, inside2]
  unfold Subtable.IsLink at link
  simp only [tableRead, read, get, bind, Option.bind, link, ite_true, drop, read2, get2]
  rfl

/-! ## Meaning of a fitted leaf -/

/-- A leaf selected by the held bits `inp` that fits them. Accepted: it is
the canonical symbol of `inp` on every continuation. Rejected: no
continuation has a valid symbol. -/
theorem fitted_leaf_meaning {type : UInt32} {ca : Array Code} {offset root used : Nat}
    {lens : List Nat} (inv : Inv type ca offset root used lens)
    (stable : StableQuery type ca offset root) {inp : List Bool} {entry : Code} {consumed : Nat}
    (query : tableRead type ca offset root (DecodeShort.padded inp) = some (entry, consumed))
    (fits : consumed ≤ inp.length) :
    (LeafAccepted type entry → ∃ symbol, ValidSymbol type symbol ∧ SymbolEntry type symbol entry ∧
      consumed = lens.getD symbol 0 ∧
      ∀ more : List Bool, decodeSym lens (inp ++ more) = some (symbol, inp.drop consumed ++ more)) ∧
    (¬ LeafAccepted type entry → ∀ more : List Bool,
      ¬ ∃ (symbol : Nat) (rest : List Bool),
        decodeSym lens (inp ++ more) = some (symbol, rest) ∧ ValidSymbol type symbol) := by
  constructor
  · intro accepted
    obtain ⟨symbol, valid, meaning, length, _decoded, extend⟩ :=
      inv.short inp entry consumed query fits accepted
    exact ⟨symbol, valid, meaning, length, extend⟩
  · intro rejected more
    exact short_rejected_leaf_stays_invalid type ca offset root used lens inv stable inp entry
      consumed query fits rejected more

end Zlib.Inflate.Proofs.MeaningLookup

namespace Zlib.Inflate.Proofs.MeaningLookup

/-- Refilling the bit buffer after the root entry fits does not change the
root index: the new hold value keeps the low bits. -/
theorem root_index_stable {root b1 hold1 hold2 : Nat} (le : root ≤ b1)
    (keep : hold2 % 2 ^ b1 = hold1 % 2 ^ b1) : hold2 % 2 ^ root = hold1 % 2 ^ root := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le le
  rw [Nat.pow_add] at keep
  have h2 := Nat.mod_mul_right_mod hold2 (2 ^ root) (2 ^ m)
  have h1 := Nat.mod_mul_right_mod hold1 (2 ^ root) (2 ^ m)
  rw [← h2, ← h1, keep]

end Zlib.Inflate.Proofs.MeaningLookup
