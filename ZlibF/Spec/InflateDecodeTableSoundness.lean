import ZlibF.Spec.InflateDecodeTableSemantics

/-!
# Soundness of accepted decoding-table leaves

The literal/length decoder tests the end-of-block flag before the invalid
flag. EOB therefore remains accepted even though its op is 96. Reserved
symbols and incomplete-table padding are rejected. This internal goal still
uses fifteen available bits; it does not restrict public input splits.
-/

namespace Zlib.Inftrees.Spec.DecodeSoundness
open C Zlib.Inftrees Zlib.Inftrees.Proofs
open Zlib.Inftrees.Spec.DecodeSemantics

/-- The branch condition by which the actual slow decoder accepts a final
leaf. LENS tests bit 32 before bit 64; DISTS rejects bit 64 directly. -/
def LeafAccepted (type : UInt32) (entry : Code) : Prop :=
  if type = LENS then (entry.op &&& 32) != 0 ∨ (entry.op &&& 64) = 0
  else (entry.op &&& 64) = 0

/-- Valid format symbols, excluding the reserved literal/length and distance
symbols that can have canonical codes in fixed or generic accepted tables. -/
def ValidSymbol (type : UInt32) (symbol : Nat) : Prop :=
  if type = LENS then symbol ≤ 285 else symbol ≤ 29

/-- Every full-width read of an actual successful LENS/DISTS constructor
result exists. Its leaf is accepted exactly when it is the independent
decoder's valid symbol, with the same code length and leaf meaning. Empty
alphabets, singleton padding and reserved symbols remain in the domain. -/
def Goal.decode_table_leaf_sound : Prop :=
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
          (LeafAccepted type entry ↔
            ∃ (symbol : Nat) (rest : List Bool),
              ZlibF.Spec.decodeSym (lensOf pre.f codes.toNat) inp = some (symbol, rest) ∧
              ValidSymbol type symbol ∧
              used = (lensOf pre.f codes.toNat).getD symbol 0 ∧
              rest = inp.drop used ∧ SymbolEntry type symbol entry))

end Zlib.Inftrees.Spec.DecodeSoundness
