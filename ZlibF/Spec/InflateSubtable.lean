import ZlibF.Spec.InflateRootTable

/-!
# Bounds of a root link and its second-level entries

These facts are outputs of actual table construction. The slow decoder uses
bits+op to index the subtable and bits+leaf.bits for its fit test.
-/
namespace Zlib.Inftrees.Spec.Subtable
open C Zlib.Inftrees Zlib.Inftrees.Proofs

def IsLink (type : UInt32) (entry : Code) : Bool :=
  if type = LENS then entry.op != 0 && (entry.op &&& 0xf0) == 0
  else (entry.op &&& 0xf0) == 0

def Safe (ca : Array Code) (offset : Nat) (link : Code) : Prop :=
  1 ≤ link.bits.toNat ∧ 1 ≤ link.op.toNat ∧
    link.bits.toNat + link.op.toNat ≤ 15 ∧
    offset + link.val.toNat + 2 ^ link.op.toNat ≤ ca.size ∧
    ∀ j, j < 2 ^ link.op.toNat →
      ∃ entry, ca[offset + link.val.toNat + j]? = some entry ∧
        1 ≤ entry.bits.toNat ∧ entry.bits.toNat ≤ link.op.toNat

/-- Each actual root link has a bounded subtable of positive-length leaves.
Empty and singleton tables are included and must not invent links. -/
def Goal.constructor_subtable_bits : Prop :=
  ∀ (h : Heap) (type : UInt32) (rl : WRef) (ol : Nat) (codes : UInt32)
    (rc : CodeRef) (oc : Nat) (bits : UInt32) (rw : WRef) (ow : Nat)
    (pre : CallPre h type rl ol codes rc oc bits rw ow),
    (type = LENS ∨ type = DISTS) →
    ∃ r after,
      C.run (inflate_table type (.ref rl ol) codes (.ref rc oc) bits (.ref rw ow)) h =
        .ok (r, after) ∧
      (r.1 = 0 → ∃ ca : Array Code,
        Space.get after rc = some ca ∧ RootTable.Safe ca oc r.2.2.toNat ∧
        ∀ i entry, i < 2 ^ r.2.2.toNat → ca[oc + i]? = some entry →
          IsLink type entry = true → entry.bits.toNat = r.2.2.toNat ∧ Safe ca oc entry)

end Zlib.Inftrees.Spec.Subtable
