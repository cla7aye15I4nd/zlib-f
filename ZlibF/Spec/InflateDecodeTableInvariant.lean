import ZlibF.Spec.InflateSubtable
import ZlibF.Spec.InflateDecodeTableShort
import ZlibF.Spec.InflateDecodeTableRejection
import ZlibF.Spec.InflateDecodeTableFrame

/-!
# The shape and meaning of an installed decoding table

The logical alphabet remains fixed when a later constructor writes another
table in the same array. Every field below is a property of the current
array. The constructor goal establishes these properties by executing the
translated function; it does not assume a callee contract.
-/

namespace Zlib.Inftrees.Spec.DecodeTableInvariant
open C Zlib.Inftrees Zlib.Inftrees.Proofs
open Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness

/-- Shape, actual read extent and independent symbol semantics at one
installed table. Empty and singleton alphabets are retained. No assumption
is made about whether the future compressed input will be valid. -/
structure Inv (type : UInt32) (ca : Array Code) (offset root used : Nat)
    (lens : List Nat) : Prop where
  tableType : type = LENS ∨ type = DISTS
  rootTable : RootTable.Safe ca offset root
  subtables : ∀ i entry, i < 2 ^ root → ca[offset + i]? = some entry →
    Subtable.IsLink type entry = true →
    entry.bits.toNat = root ∧ Subtable.Safe ca offset entry
  readExtent : TableReadExtent type ca offset root used
  acceptable : ZlibF.Spec.Acceptable (kindOf type) lens
  short : ∀ (inp : List Bool) (entry : Code) (consumed : Nat),
    tableRead type ca offset root (DecodeShort.padded inp) = some (entry, consumed) →
    consumed ≤ inp.length → LeafAccepted type entry →
    ∃ symbol,
      ValidSymbol type symbol ∧ SymbolEntry type symbol entry ∧
      consumed = lens.getD symbol 0 ∧
      ZlibF.Spec.decodeSym lens inp = some (symbol, inp.drop consumed) ∧
      ∀ more : List Bool,
        ZlibF.Spec.decodeSym lens (inp ++ more) =
          some (symbol, inp.drop consumed ++ more)
  classify : ∀ inp : List Bool, 15 ≤ inp.length →
    ∃ (entry : Code) (consumed : Nat),
      tableRead type ca offset root inp = some (entry, consumed) ∧
      (LeafAccepted type entry ↔ ∃ (symbol : Nat) (rest : List Bool),
        ZlibF.Spec.decodeSym lens inp = some (symbol, rest) ∧ ValidSymbol type symbol)

/-- Actual construction establishes the invariant with its original
alphabet and its returned extent. The existing heap frame and all rejected
results are retained. This is a local constructor result, not a public
decoder theorem or a claim about fixed static tables. -/
def Goal.constructor_establishes_decode_table_invariant : Prop :=
  ∀ (h : Heap) (type : UInt32) (rl : WRef) (ol : Nat) (codes : UInt32)
    (rc : CodeRef) (oc : Nat) (bits : UInt32) (rw : WRef) (ow : Nat)
    (pre : CallPre h type rl ol codes rc oc bits rw ow),
    (type = LENS ∨ type = DISTS) →
    ∃ (r : Int32 × CodePtr × UInt32) (after : Heap),
      C.run (inflate_table type (.ref rl ol) codes (.ref rc oc) bits (.ref rw ow)) h =
        .ok (r, after) ∧
      Result h rw rc ow oc (capOf type) codes.toNat pre.wa pre.ca (.ref rc oc) bits r after ∧
      (r.1 = 0 → ∃ (ca : Array Code) (used : Nat),
        Space.get after rc = some ca ∧ r.2.1 = .ref rc (oc + used) ∧
        used ≤ capOf type ∧
        Inv type ca oc r.2.2.toNat used (lensOf pre.f codes.toNat))

/-- A later builder preserves the whole invariant when its actual frame
preserves this table's returned extent. Array growth is harmless. A mere
capacity bound does not supply the required pointwise frame. -/
def Goal.decode_table_invariant_of_prefix : Prop :=
  ∀ (type : UInt32) (before after : Array Code) (offset root used : Nat)
    (lens : List Nat),
    Inv type before offset root used lens →
    before.size ≤ after.size →
    (∀ i, offset ≤ i → i < offset + used → after[i]? = before[i]?) →
    Inv type after offset root used lens

end Zlib.Inftrees.Spec.DecodeTableInvariant
