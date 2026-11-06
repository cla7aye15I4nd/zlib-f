import ZlibF.Spec.InflateDecodeTableStability
import ZlibF.Spec.InflateFastTableFlags
import ZlibF.Spec.InflateFast

/-!
# Fast literal/length selection and independent symbols

The selected leaf must be connected to the independent Huffman decoder.
Source-bit origin and range-safe tables alone do not establish this fact.
The table predicates below are internal data obligations for construction.
-/

namespace Zlib.Inffast.Spec.LengthSemantics
open C Zlib.Inffast Zlib.Inffast.Proofs
open Zlib.Inftrees Zlib.Inftrees.Spec

/-- The final entry selected by the actual fast root/link branch order.
The second index uses the hold value after dropping the root code bits. -/
def Look (e : Env) (hold index : Nat) (entry : Code) (consumed : Nat) : Prop :=
  (e.LCA.getD (e.ol + index) default = entry ∧
    consumed = entry.bits.toNat ∧ ¬ LenLink entry) ∨
  (∃ first next,
    e.LCA.getD (e.ol + index) default = first ∧ LenLink first ∧
    next < 2 ^ first.op.toNat ∧
    next = (hold / 2 ^ first.bits.toNat) % 2 ^ first.op.toNat ∧
    e.LCA.getD (e.ol + first.val.toNat + next) default = entry ∧
    consumed = first.bits.toNat + entry.bits.toNat ∧
    first.bits.toNat + entry.bits.toNat ≤ 15 ∧ ¬ LenLink entry)

/-- A selected fast leaf has the independent symbol meaning and exact
code length, or rejects every future extension. This includes reserved
symbols and incomplete-table padding. It does not assume valid input or
assert that the main decoder has established the table predicates. -/
def Goal.length_lookup_matches_format : Prop :=
  ∀ (e : Env) (hold bits input tableUsed : Nat) (lens : List Nat)
    (entry : Code) (consumed : Nat),
    DecodeTableInvariant.Inv LENS e.LCA e.ol e.s0.lenbits.toNat tableUsed lens →
    DecodeTableStability.StableQuery LENS e.LCA e.ol e.s0.lenbits.toNat →
    FastTableFlags.QueryCompatible LENS e.LCA e.ol e.s0.lenbits.toNat →
    hold < 2 ^ bits → 15 ≤ bits →
    Look e hold (hold % 2 ^ e.s0.lenbits.toNat) entry consumed →
    let stream := Sg e hold bits input
    DecodeSemantics.tableRead LENS e.LCA e.ol e.s0.lenbits.toNat stream =
      some (entry, consumed) ∧
    1 ≤ consumed ∧ consumed ≤ 15 ∧ LenLeaf 0 entry ∧
    ((¬ FastTableFlags.FastLeafAccepted LENS entry ∧
      ∀ more : List Bool,
        ¬ ∃ (symbol : Nat) (rest : List Bool),
          ZlibF.Spec.decodeSym lens (stream ++ more) = some (symbol, rest) ∧ symbol ≤ 285) ∨
     (FastTableFlags.FastLeafAccepted LENS entry ∧
      ∃ symbol, symbol ≤ 285 ∧ DecodeSemantics.SymbolEntry LENS symbol entry ∧
        consumed = lens.getD symbol 0 ∧
        ZlibF.Spec.decodeSym lens stream = some (symbol, stream.drop consumed) ∧
        ∀ more : List Bool,
          ZlibF.Spec.decodeSym lens (stream ++ more) =
            some (symbol, stream.drop consumed ++ more)))

end Zlib.Inffast.Spec.LengthSemantics
