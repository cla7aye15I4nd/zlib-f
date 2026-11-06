import ZlibF.Spec.InflateDecodeTableFrame
import ZlibF.Spec.InflateDecodeTableSoundness

/-!
# Leaf flags shared by slow and fast decoding

The fast decoder tests bit 16 before bit 64. The slow decoder tests the
invalid flag before interpreting a length or distance. Their existing
safety predicates alone do not rule out both bits being set. This extra
data property must follow from actual construction, not a public caller
restriction or an assumed callee contract.
-/

namespace Zlib.Inftrees.Spec.FastTableFlags
open C Zlib.Inftrees Zlib.Inftrees.Proofs
open Zlib.Inftrees.Spec.DecodeSemantics

/-- A length or distance marker is never also an invalid marker. EOB 96
and the actual reserved markers remain allowed. -/
def Compatible (entry : Code) : Prop :=
  entry.op &&& 16 ≠ 0 → entry.op &&& 64 = 0

/-- Every full-width table query returns compatible flags. The fifteen
bits describe an internal table query, not a public input-buffer minimum.
Actual fast decoding must establish the available-bit bound separately. -/
def QueryCompatible (type : UInt32) (ca : Array Code) (offset root : Nat) : Prop :=
  ∀ (inp : List Bool) (entry : Code) (consumed : Nat),
    15 ≤ inp.length →
    tableRead type ca offset root inp = some (entry, consumed) → Compatible entry

/-- The fast branch order after a final leaf is selected. Links are not
final leaves; the shape premise in the next goal excludes them. -/
def FastLeafAccepted (type : UInt32) (entry : Code) : Prop :=
  if type = LENS then
    entry.op = 0 ∨ entry.op &&& 16 ≠ 0 ∨
      (entry.op &&& 64 ≠ 0 ∧ entry.op &&& 32 ≠ 0)
  else entry.op &&& 16 ≠ 0

/-- Compatible flags and the existing leaf shape reconcile the two branch
orders. This is a data lemma; actual table selection and independent symbol
meaning remain separate obligations. -/
def Goal.leaf_classification_agrees : Prop :=
  ∀ (type : UInt32) (entry : Code),
    (type = LENS ∨ type = DISTS) → Compatible entry →
    ((type = LENS → Zlib.Inffast.Spec.LenLeaf 0 entry) ∧
     (type = DISTS → Zlib.Inffast.Spec.DistLeaf 0 entry)) →
    (FastLeafAccepted type entry ↔ DecodeSoundness.LeafAccepted type entry)

/-- Actual table construction establishes flag compatibility, retaining
the existing execution and result. Rejected constructions are retained.
This does not assert independent decoding correctness of inflate_fast. -/
def Goal.constructor_establishes_fast_leaf_flags : Prop :=
  ∀ (h : Heap) (type : UInt32) (rl : WRef) (ol : Nat) (codes : UInt32)
    (rc : CodeRef) (oc : Nat) (bits : UInt32) (rw : WRef) (ow : Nat)
    (pre : CallPre h type rl ol codes rc oc bits rw ow),
    (type = LENS ∨ type = DISTS) →
    ∃ (r : Int32 × CodePtr × UInt32) (after : Heap),
      C.run (inflate_table type (.ref rl ol) codes (.ref rc oc) bits (.ref rw ow)) h =
        .ok (r, after) ∧
      Result h rw rc ow oc (capOf type) codes.toNat pre.wa pre.ca (.ref rc oc) bits r after ∧
      (r.1 = 0 → ∀ ca : Array Code, Space.get after rc = some ca →
        QueryCompatible type ca oc r.2.2.toNat)

/-- A later builder preserves the property through the actual extent and
cell frame. Equal capacities alone do not establish the frame. -/
def Goal.fast_leaf_flags_of_prefix : Prop :=
  ∀ (type : UInt32) (before after : Array Code) (offset root used : Nat),
    (type = LENS ∨ type = DISTS) →
    TableReadExtent type before offset root used →
    QueryCompatible type before offset root →
    (∀ i, offset ≤ i → i < offset + used → after[i]? = before[i]?) →
    QueryCompatible type after offset root

/-- The actual default static tables provide the same property. Their
reserved markers are checked as stored, without replacing their values. -/
def Goal.fixed_tables_have_fast_leaf_flags : Prop :=
  QueryCompatible LENS Zlib.InffixedH.lenfix 0 9 ∧
  QueryCompatible DISTS Zlib.InffixedH.distfix 0 5

end Zlib.Inftrees.Spec.FastTableFlags
