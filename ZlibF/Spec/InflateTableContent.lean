import ZlibF.Proof.«inftrees.c.main»

/-!
# Contents of the table built by the actual `inflate_table`

The execution, frame and return classification are retained from the existing safety proof.
The extra obligation retains every leaf and subtable link written by the main loop. Its
environment is tied to the input lengths, table location, kind and returned root width.
No geometry condition or callee contract is assumed by the caller.
-/

namespace Zlib.Inftrees.Spec
open C Zlib.Inftrees Zlib.Inftrees.Proofs

/-- A successful empty code writes two one-bit invalid entries. A successful nonempty code
writes the canonical leaves and links associated with the supplied lengths. The internal
environment is an existential result of the execution, not an input assumption. -/
def TableContent (type : UInt32) (f : Nat → Nat) (n : Nat) (rc : CodeRef) (oc : Nat)
    (r : Int32 × CodePtr × UInt32) (after : Heap) : Prop :=
  r.1 = 0 →
    (Tc f n 15 = 0 ∧ r.2.2 = 1 ∧ r.2.1 = .ref rc (oc + 2) ∧
      ∃ ca : Array Code, Space.get after rc = some ca ∧
        ca[oc]? = some ⟨64, 1, 0⟩ ∧ ca[oc + 1]? = some ⟨64, 1, 0⟩) ∨
    (0 < Tc f n 15 ∧ ∃ (e : Env) (ca : Array Code),
      e.f = f ∧ e.n = n ∧ e.R = r.2.2.toNat ∧ e.rc = rc ∧ e.oc = oc ∧
      e.c.type = type ∧ Space.get after rc = some ca ∧
      Written e e.m ca ∧ Links e e.m ca)

/-- On every existing `CallPre`, the real translated function returns and retains both the
safety result and its constructed table contents. Rejected and oversized tables are allowed.
This is an internal table-builder obligation; it does not by itself establish decoder safety. -/
def Goal.inflate_table_content : Prop :=
  ∀ (h : Heap) (type : UInt32) (rl : WRef) (ol : Nat) (codes : UInt32)
    (rc : CodeRef) (oc : Nat) (bits : UInt32) (rw : WRef) (ow : Nat)
    (pre : CallPre h type rl ol codes rc oc bits rw ow),
    ∃ r after,
      C.run (inflate_table type (.ref rl ol) codes (.ref rc oc) bits (.ref rw ow)) h =
        .ok (r, after) ∧
      Result h rw rc ow oc (capOf type) codes.toNat pre.wa pre.ca (.ref rc oc) bits r after ∧
      RetInfo type pre.f codes.toNat r ∧ TableContent type pre.f codes.toNat rc oc r after

end Zlib.Inftrees.Spec
