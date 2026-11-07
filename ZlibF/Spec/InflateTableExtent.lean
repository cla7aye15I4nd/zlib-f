import ZlibF.Spec.InflateTableSafety

/-!
# The returned extent of a decoding table

The constructor returns a pointer just past the storage it used. A later table may be
built in the same array at that pointer. Decoder safety must therefore depend only on
cells before the returned pointer, rather than on the size of the backing array.
-/

namespace Zlib.Inftrees.Spec
open C Zlib.Inftrees Zlib.Inftrees.Proofs

/-- All root cells and every second-level cell that the decoder may read lie before the
returned end. This is a property of a successful constructor result, not an input
assumption. -/
def TableReadExtent (type : UInt32) (ca : Array Code) (offset root used : Nat) : Prop :=
  1 ≤ root ∧ root ≤ 15 ∧ offset + 2 ^ root ≤ offset + used ∧
    ∀ i, i < 2 ^ root →
      let entry := ca.getD (offset + i) default
      ((type = LENS ∧ Zlib.Inffast.Spec.LenLink entry) ∨
       (type = DISTS ∧ Zlib.Inffast.Spec.DistLink entry)) →
      offset + entry.val.toNat + 2 ^ entry.op.toNat ≤ offset + used

/-- The actual builder bounds its returned extent and establishes both the decoder
predicate and the extent needed when a following table reuses the same array. Accepted
empty and single-symbol codes are included. -/
def Goal.inflate_table_read_extent : Prop :=
  ∀ (h : Heap) (type : UInt32) (rl : WRef) (ol : Nat) (codes : UInt32)
    (rc : CodeRef) (oc : Nat) (bits : UInt32) (rw : WRef) (ow : Nat)
    (pre : CallPre h type rl ol codes rc oc bits rw ow),
    ∃ r after,
      C.run (inflate_table type (.ref rl ol) codes (.ref rc oc) bits (.ref rw ow)) h =
        .ok (r, after) ∧
      Result h rw rc ow oc (capOf type) codes.toNat pre.wa pre.ca (.ref rc oc) bits r after ∧
      (r.1 = 0 → ∃ (ca : Array Code) (used : Nat),
        Space.get after rc = some ca ∧
        r.2.1 = .ref rc (oc + used) ∧ used ≤ capOf type ∧
        TableReadExtent type ca oc r.2.2.toNat used ∧
        (type = CODES → CodeLengthTableSafe ca oc r.2.2.toNat) ∧
        (type = LENS → Zlib.Inffast.Spec.LenTableSafe ca oc r.2.2.toNat) ∧
        (type = DISTS → Zlib.Inffast.Spec.DistTableSafe ca oc r.2.2.toNat))

end Zlib.Inftrees.Spec
