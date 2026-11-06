import ZlibF.Spec.InflateTableContent

/-!
# Positive code lengths in a constructed root table

Array bounds alone do not ensure that a lookup consumes a positive number
of bits. This local predicate is established by the actual constructor,
including empty and singleton-invalid entries.
-/
namespace Zlib.Inftrees.Spec.RootTable
open C Zlib.Inftrees Zlib.Inftrees.Proofs

def Safe (ca : Array Code) (offset root : Nat) : Prop :=
  1 ≤ root ∧ root ≤ 15 ∧ offset + 2 ^ root ≤ ca.size ∧
    ∀ i, i < 2 ^ root →
      ∃ entry, ca[offset + i]? = some entry ∧
        1 ≤ entry.bits.toNat ∧ entry.bits.toNat ≤ root

/-- Every successful actual table construction gives the root-entry bounds
needed by lookup1. No validity of the compressed input is assumed. -/
def Goal.constructor_root_bits : Prop :=
  ∀ (h : Heap) (type : UInt32) (rl : WRef) (ol : Nat) (codes : UInt32)
    (rc : CodeRef) (oc : Nat) (bits : UInt32) (rw : WRef) (ow : Nat)
    (pre : CallPre h type rl ol codes rc oc bits rw ow),
    ∃ r after,
      C.run (inflate_table type (.ref rl ol) codes (.ref rc oc) bits (.ref rw ow)) h =
        .ok (r, after) ∧
      (r.1 = 0 → ∃ ca : Array Code,
        Space.get after rc = some ca ∧ Safe ca oc r.2.2.toNat)

end Zlib.Inftrees.Spec.RootTable
