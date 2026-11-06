import ZlibF.Spec.InflateDecodeTableInvariant

/-!
# A fitted query is independent of unread input

Both accepted and rejected entries must be stable under later input. The
fit check alone is not enough for an arbitrary range-safe table: its cells
must have the replication pattern established by the actual constructor.
This obligation is separate from accepted-symbol soundness.
-/

namespace Zlib.Inftrees.Spec.DecodeTableStability
open C Zlib.Inftrees Zlib.Inftrees.Proofs
open Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness

/-- Once the returned code length fits the available prefix, every future
suffix selects the very same entry and consumed length. Zero padding is
only a mathematical query convention, never input that may be consumed. -/
def StableQuery (type : UInt32) (ca : Array Code) (offset root : Nat) : Prop :=
  ∀ (inp : List Bool) (entry : Code) (consumed : Nat),
    tableRead type ca offset root (DecodeShort.padded inp) = some (entry, consumed) →
    consumed ≤ inp.length →
    ∀ more : List Bool,
      tableRead type ca offset root (DecodeShort.padded (inp ++ more)) =
        some (entry, consumed)

/-- The actual accepted constructor supplies suffix stability, including
invalid singleton padding, empty tables and reserved symbols. This says
nothing about the validity of the compressed input. -/
def Goal.constructor_establishes_query_stability : Prop :=
  ∀ (h : Heap) (type : UInt32) (rl : WRef) (ol : Nat) (codes : UInt32)
    (rc : CodeRef) (oc : Nat) (bits : UInt32) (rw : WRef) (ow : Nat)
    (pre : CallPre h type rl ol codes rc oc bits rw ow),
    (type = LENS ∨ type = DISTS) →
    ∃ (r : Int32 × CodePtr × UInt32) (after : Heap),
      C.run (inflate_table type (.ref rl ol) codes (.ref rc oc) bits (.ref rw ow)) h =
        .ok (r, after) ∧
      (r.1 = 0 → ∀ ca : Array Code, Space.get after rc = some ca →
        StableQuery type ca oc r.2.2.toNat)

/-- An actual cell frame also transports suffix stability. The extent is
supplied by the first constructor, and the equality by the following one. -/
def Goal.query_stability_of_prefix : Prop :=
  ∀ (type : UInt32) (before after : Array Code) (offset root used : Nat),
    (type = LENS ∨ type = DISTS) →
    TableReadExtent type before offset root used →
    StableQuery type before offset root →
    (∀ i, offset ≤ i → i < offset + used → after[i]? = before[i]?) →
    StableQuery type after offset root

/-- A fitted rejected entry rules out a valid independent symbol on every
future extension. Full-width classification alone does not justify this
early error path; the constructor's suffix stability is used explicitly. -/
def Goal.short_rejected_leaf_stays_invalid : Prop :=
  ∀ (type : UInt32) (ca : Array Code) (offset root used : Nat) (lens : List Nat),
    DecodeTableInvariant.Inv type ca offset root used lens →
    StableQuery type ca offset root →
    ∀ (inp : List Bool) (entry : Code) (consumed : Nat),
      tableRead type ca offset root (DecodeShort.padded inp) = some (entry, consumed) →
      consumed ≤ inp.length → ¬ LeafAccepted type entry →
      ∀ more : List Bool,
        ¬ ∃ (symbol : Nat) (rest : List Bool),
          ZlibF.Spec.decodeSym lens (inp ++ more) = some (symbol, rest) ∧
          ValidSymbol type symbol

end Zlib.Inftrees.Spec.DecodeTableStability
