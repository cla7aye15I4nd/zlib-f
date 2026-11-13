import ZlibF.Runtime.Schema
import ZlibF.Zlib.«inffixed.h»

/-!
# inffast.c: the shape of the decoding tables (`TableOK` for `inflate_fast`)

`inflate_fast` reads the literal/length table `lencode` and the distance table `distcode` without checking them. What
it needs is the shape that `inflate_table` gives (`proof/inftrees.md`, theorem T2) and that the static tables `lenfix`
and `distfix` have. `LenTableSafe` and `DistTableSafe` state it for a table `ca[o ..]` with root width `R`:

* the root has `2^R` entries inside the array and `R ≤ 15`;
* a root entry is a leaf (literal, base value, end of block, invalid code) or a link to a second level that lies inside
  the array, with `1 ≤ op ≤ 15` bits, and whose entries are leaves;
* the bits of a root entry plus those of the second-level entry reached from it are at most 15;
* a length base has at most 5 extra bits and a base value of at least 3 whose largest value, with the extra bits, is
  258; a distance base has at most 13 extra bits and a base value of at least 1.

`inflate_table` must establish `LenTableSafe` for the table it builds for `LENS` and `DistTableSafe` for `DISTS`
(the table pointer and `*bits` it returns being `o` and `R`). The static tables are proved below.
-/

namespace Zlib.Inffast.Spec
open C

/-- A leaf of the literal/length table that is read after `d` bits of the same code were dropped (`d = 0` in the root,
`d = ` the root width in a second-level table): `bits + d ≤ 15`; a literal (`op = 0`); a length base (`op & 16`)
with at most 5 extra bits and a base value in `3 .. 258` with the extra bits included; or an end of block or an
invalid code (`op & 16 = 0`, `op & 64`). -/
abbrev LenLeaf (d : Nat) (e : Code) : Prop :=
  e.bits.toNat + d ≤ 15 ∧
  (e.op = 0 ∨
   (e.op &&& 16 ≠ 0 ∧ (e.op &&& 15).toNat ≤ 5 ∧ 3 ≤ e.val.toNat ∧ e.val.toNat + 2 ^ (e.op &&& 15).toNat ≤ 259) ∨
   (e.op &&& 16 = 0 ∧ e.op &&& 64 ≠ 0))

/-- A leaf of the distance table: `bits + d ≤ 15`; a distance base (`op & 16`) with at most 13 extra bits and a base
value of at least 1; or an invalid code (`op & 16 = 0`, `op & 64`). -/
abbrev DistLeaf (d : Nat) (e : Code) : Prop :=
  e.bits.toNat + d ≤ 15 ∧
  ((e.op &&& 16 ≠ 0 ∧ (e.op &&& 15).toNat ≤ 13 ∧ 1 ≤ e.val.toNat) ∨
   (e.op &&& 16 = 0 ∧ e.op &&& 64 ≠ 0))

/-- The entry is a link to a second-level table in `inflate_fast` for the literal/length table (the tests of the C:
`op != 0`, `op & 16 == 0`, `op & 64 == 0`). -/
abbrev LenLink (e : Code) : Prop := e.op ≠ 0 ∧ e.op &&& 16 = 0 ∧ e.op &&& 64 = 0

/-- The same for the distance table (`op` may be 0 there). -/
abbrev DistLink (e : Code) : Prop := e.op &&& 16 = 0 ∧ e.op &&& 64 = 0

/-- The second level that a link entry `e` of a table `ca[o ..]` describes: it has between 2 and `2^15` entries, lies
inside the array, and its entries are leaves that are read after `e.bits` bits were dropped. -/
abbrev LinkOK (P : Nat → Code → Prop) (ca : Array Code) (o : Nat) (e : Code) : Prop :=
  e.bits.toNat ≤ 15 ∧ 1 ≤ e.op.toNat ∧ e.op.toNat ≤ 15 ∧ o + e.val.toNat + 2 ^ e.op.toNat ≤ ca.size ∧
  ∀ j, j < 2 ^ e.op.toNat → P e.bits.toNat (ca.getD (o + e.val.toNat + j) default)

/-- The shape of a table `ca[o ..]` with root width `R`, leaves described by `P`, links by `L`: every root entry is
either a link with `LinkOK`, or a leaf (`P 0`). -/
def TableSafe (P : Nat → Code → Prop) (L : Code → Prop) [DecidablePred L] (ca : Array Code) (o R : Nat) : Prop :=
  R ≤ 15 ∧ o + 2 ^ R ≤ ca.size ∧
  ∀ i, i < 2 ^ R →
    (if L (ca.getD (o + i) default) then LinkOK P ca o (ca.getD (o + i) default) else P 0 (ca.getD (o + i) default))

/-- `TableSafe` of the literal/length table. -/
abbrev LenTableSafe (ca : Array Code) (o R : Nat) : Prop := TableSafe LenLeaf LenLink ca o R
/-- `TableSafe` of the distance table. -/
abbrev DistTableSafe (ca : Array Code) (o R : Nat) : Prop := TableSafe DistLeaf DistLink ca o R

/-- Every leaf of the literal/length table reads at least one bit beyond the dropped root: a root leaf has
`1 ≤ bits`, a second-level leaf `1 ≤ bits` (its bits count after the root). -/
def LenLeavesPositive (ca : Array Code) (o R : Nat) : Prop :=
  ∀ i, i < 2 ^ R →
    (if LenLink (ca.getD (o + i) default) then
      ∀ j, j < 2 ^ (ca.getD (o + i) default).op.toNat →
        1 ≤ (ca.getD (o + (ca.getD (o + i) default).val.toNat + j) default).bits.toNat
    else 1 ≤ (ca.getD (o + i) default).bits.toNat)

end Zlib.Inffast.Spec

namespace Zlib.Inffast.Proofs
open C Zlib.Inffast.Spec

set_option maxRecDepth 100000 in
/-- The static literal/length table `lenfix` (inffixed.h), root width 9, has the shape `LenTableSafe` (kernel
evaluation of all 512 entries). -/
theorem lenfix_tableSafe : LenTableSafe Zlib.InffixedH.lenfix 0 9 := by
  unfold LenTableSafe TableSafe
  refine ⟨by decide, by decide +kernel, ?_⟩
  decide +kernel

set_option maxRecDepth 100000 in
/-- Every leaf of the static literal/length table `lenfix` reads at least one bit (kernel evaluation of all 512
entries). -/
theorem lenfix_leavesPositive : LenLeavesPositive Zlib.InffixedH.lenfix 0 9 := by
  unfold LenLeavesPositive
  decide +kernel

set_option maxRecDepth 100000 in
/-- The static distance table `distfix`, root width 5, has the shape `DistTableSafe`. -/
theorem distfix_tableSafe : DistTableSafe Zlib.InffixedH.distfix 0 5 := by
  unfold DistTableSafe TableSafe
  refine ⟨by decide, by decide +kernel, ?_⟩
  decide +kernel

end Zlib.Inffast.Proofs
