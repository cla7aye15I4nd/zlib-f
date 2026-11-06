import ZlibF.Spec.InflateDecodeTableStability
import ZlibF.Spec.InflateFastTableFlags
import ZlibF.Proof.«inffast.c.lp»

/-!
# The fast distance lookup selects an independent Huffman symbol

DistLook is already produced by the actual distance lookup proof. Its
fast link tests must agree with the two-level format query. Final leaves
need the actual constructor's flags as well as the old safety shape.
-/

namespace Zlib.Inffast.Spec.DistanceSemantics
open C Zlib.Inffast Zlib.Inffast.Proofs
open Zlib.Inftrees Zlib.Inftrees.Spec

/-- A selected fast leaf has the exact query, consumed code length and
independent symbol meaning, or rejects every future extension. This is
a lookup-data bridge, not complete extra-bit or copy execution. -/
def Goal.distance_lookup_matches_format : Prop :=
  ∀ (e : Env) (hold bits input tableUsed : Nat) (lens : List Nat)
    (entry : Code) (consumed : Nat),
    DecodeTableInvariant.Inv DISTS e.DCA e.od e.s0.distbits.toNat tableUsed lens →
    DecodeTableStability.StableQuery DISTS e.DCA e.od e.s0.distbits.toNat →
    FastTableFlags.QueryCompatible DISTS e.DCA e.od e.s0.distbits.toNat →
    hold < 2 ^ bits → 15 ≤ bits →
    DistLook e hold (hold % 2 ^ e.s0.distbits.toNat) entry consumed →
    let stream := Sg e hold bits input
    DecodeSemantics.tableRead DISTS e.DCA e.od e.s0.distbits.toNat stream = some (entry, consumed) ∧
    1 ≤ consumed ∧ consumed ≤ 15 ∧ DistLeaf 0 entry ∧
    ((entry.op &&& 16 = 0 ∧
      ∀ more : List Bool,
        ¬ ∃ (symbol : Nat) (rest : List Bool),
          ZlibF.Spec.decodeSym lens (stream ++ more) = some (symbol, rest) ∧ symbol ≤ 29) ∨
     (entry.op &&& 16 ≠ 0 ∧
      ∃ symbol, symbol ≤ 29 ∧ DecodeSemantics.SymbolEntry DISTS symbol entry ∧
        consumed = lens.getD symbol 0 ∧
        ZlibF.Spec.decodeSym lens stream = some (symbol, stream.drop consumed) ∧
        ∀ more : List Bool,
          ZlibF.Spec.decodeSym lens (stream ++ more) =
            some (symbol, stream.drop consumed ++ more)))

end Zlib.Inffast.Spec.DistanceSemantics
