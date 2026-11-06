import ZlibF.Spec.InflateTableContent
import ZlibF.Proof.«inffast.c.tableok»

/-!
# Table predicates established by the actual constructor

This obligation connects construction to the predicates used by the decoder. Every root
entry must be covered, including invalid entries in empty or single-symbol codes. A result
about the leaves and links that were written is insufficient by itself.
-/

namespace Zlib.Inftrees.Spec
open C Zlib.Inftrees Zlib.Inftrees.Proofs

/-- The code-length table has no second level. Every lookup reads a nonzero number of bits
and yields a code-length alphabet symbol or an invalid marker. -/
def CodeLengthTableSafe (ca : Array Code) (offset root : Nat) : Prop :=
  1 ≤ root ∧ root ≤ 7 ∧ offset + 2 ^ root ≤ ca.size ∧
    ∀ i, i < 2 ^ root →
      let entry := ca.getD (offset + i) default
      1 ≤ entry.bits.toNat ∧ entry.bits.toNat ≤ root ∧
        ((entry.op = 0 ∧ entry.val.toNat < 19) ∨ entry.op = 64)

/-- Successful construction establishes every table predicate that the slow and fast
decoders use. The real call and existing safety frame remain explicit. The input lengths
may be empty, incomplete, oversubscribed or too large for the capacity; error returns are
allowed. No table property or callee contract is an input hypothesis. -/
def Goal.inflate_table_decoder_safe : Prop :=
  ∀ (h : Heap) (type : UInt32) (rl : WRef) (ol : Nat) (codes : UInt32)
    (rc : CodeRef) (oc : Nat) (bits : UInt32) (rw : WRef) (ow : Nat)
    (pre : CallPre h type rl ol codes rc oc bits rw ow),
    ∃ r after,
      C.run (inflate_table type (.ref rl ol) codes (.ref rc oc) bits (.ref rw ow)) h =
        .ok (r, after) ∧
      Result h rw rc ow oc (capOf type) codes.toNat pre.wa pre.ca (.ref rc oc) bits r after ∧
      (r.1 = 0 → ∃ ca : Array Code, Space.get after rc = some ca ∧
        1 ≤ r.2.2.toNat ∧ r.2.2.toNat ≤ 15 ∧
        (type = CODES → CodeLengthTableSafe ca oc r.2.2.toNat) ∧
        (type = LENS → Zlib.Inffast.Spec.LenTableSafe ca oc r.2.2.toNat) ∧
        (type = DISTS → Zlib.Inffast.Spec.DistTableSafe ca oc r.2.2.toNat))

end Zlib.Inftrees.Spec
