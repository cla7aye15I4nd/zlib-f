import ZlibF.Spec.InflateDecodeTableSoundness

/-!
# Classifying valid and rejected full-width input

This combines the independent-to-table and table-to-independent directions.
The existence of a valid independent decode below does not depend on the
returned table entry's meaning. Thus a rejected entry rules out a valid
independent symbol, including empty and singleton-padding cases.
-/

namespace Zlib.Inftrees.Spec.DecodeRejection
open C Zlib.Inftrees Zlib.Inftrees.Proofs
open Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness

/-- Actual full-width table lookup accepts exactly the inputs with a valid
independent Huffman symbol. This local classification still needs a bridge
to actual input refill and early lookup on shorter prefixes. -/
def Goal.decode_table_classifies_input : Prop :=
  ∀ (h : Heap) (type : UInt32) (rl : WRef) (ol : Nat) (codes : UInt32)
    (rc : CodeRef) (oc : Nat) (bits : UInt32) (rw : WRef) (ow : Nat)
    (pre : CallPre h type rl ol codes rc oc bits rw ow),
    (type = LENS ∨ type = DISTS) →
    ∃ (r : Int32 × CodePtr × UInt32) (after : Heap),
      C.run (inflate_table type (.ref rl ol) codes (.ref rc oc) bits (.ref rw ow)) h =
        .ok (r, after) ∧
      (r.1 = 0 → ∀ (inp : List Bool), 15 ≤ inp.length →
        ∃ (ca : Array Code) (entry : Code) (used : Nat),
          Space.get after rc = some ca ∧
          tableRead type ca oc r.2.2.toNat inp = some (entry, used) ∧
          (LeafAccepted type entry ↔ ∃ (symbol : Nat) (rest : List Bool),
            ZlibF.Spec.decodeSym (lensOf pre.f codes.toNat) inp = some (symbol, rest) ∧
            ValidSymbol type symbol))

end Zlib.Inftrees.Spec.DecodeRejection
