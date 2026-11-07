import ZlibF.Spec.InflateDecodeTableSoundness

/-!
# A successful table lookup on a short bit prefix

BITS observes zero in unavailable high positions of a normalized hold value.
A lookup may return only when the selected code length fits the available
bits. The padding below supplies a full-width mathematical table query; it
does not permit consuming bits from the padding. Actual refill execution is
a separate bridge.
-/

namespace Zlib.Inftrees.Spec.DecodeShort
open C Zlib.Inftrees Zlib.Inftrees.Proofs
open Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness

/-- Complete a short query to fifteen bits with zeros. Longer queries are
unchanged. The selected consumed length must fit the original prefix. -/
def padded (inp : List Bool) : List Bool :=
  inp ++ List.replicate (15 - inp.length) false

/-- An accepted leaf selected by a zero-padded query is justified by the
available prefix when its consumed length fits. Appending future input does
not change the selected independent symbol. Constructor acceptance supplies
the prefix-free alphabet; it is not assumed as a callee contract. -/
def Goal.short_decode_table_leaf_sound : Prop :=
  ∀ (h : Heap) (type : UInt32) (rl : WRef) (ol : Nat) (codes : UInt32)
    (rc : CodeRef) (oc : Nat) (bits : UInt32) (rw : WRef) (ow : Nat)
    (pre : CallPre h type rl ol codes rc oc bits rw ow),
    (type = LENS ∨ type = DISTS) →
    ∃ (r : Int32 × CodePtr × UInt32) (after : Heap),
      C.run (inflate_table type (.ref rl ol) codes (.ref rc oc) bits (.ref rw ow)) h =
        .ok (r, after) ∧
      (r.1 = 0 → ∀ (inp : List Bool) (ca : Array Code) (entry : Code) (used : Nat),
        Space.get after rc = some ca →
        tableRead type ca oc r.2.2.toNat (padded inp) = some (entry, used) →
        used ≤ inp.length → LeafAccepted type entry →
        ∃ symbol,
          ValidSymbol type symbol ∧ SymbolEntry type symbol entry ∧
          used = (lensOf pre.f codes.toNat).getD symbol 0 ∧
          ZlibF.Spec.decodeSym (lensOf pre.f codes.toNat) inp =
            some (symbol, inp.drop used) ∧
          ∀ more : List Bool,
            ZlibF.Spec.decodeSym (lensOf pre.f codes.toNat) (inp ++ more) =
              some (symbol, inp.drop used ++ more))

end Zlib.Inftrees.Spec.DecodeShort
