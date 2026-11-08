import ZlibF.Proof.«inftrees.c.decode.install»
import ZlibF.Proof.«inffast.c.tableok»

set_option autoImplicit false

namespace Zlib.InffixedH.Proofs
open C ZlibF.Spec
open Zlib.Inffast.Proofs
open Zlib.Inftrees Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeSoundness

/-- A finite cell check against the independent fixed distance alphabet.
The lookup index is the low five bits in the order read by the decoder. -/
def fixedDistCellCorrect (i : Fin 32) : Prop :=
  match decodeSym fixedDistLens (bitsOfNat i.val 5), Zlib.InffixedH.distfix[i.val]? with
  | some (symbol, rest), some entry =>
      rest = (bitsOfNat i.val 5).drop entry.bits.toNat ∧
      entry.bits.toNat = fixedDistLens.getD symbol 0 ∧
      SymbolEntry DISTS symbol entry ∧
      (LeafAccepted DISTS entry ↔ ValidSymbol DISTS symbol)
  | _, _ => False

instance (i : Fin 32) : Decidable (fixedDistCellCorrect i) := by
  unfold fixedDistCellCorrect
  split
  · unfold SymbolEntry LeafAccepted ValidSymbol
    infer_instance
  · infer_instance

set_option maxRecDepth 100000 in
theorem fixedDistCellCorrect_all : ∀ i : Fin 32, fixedDistCellCorrect i := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem distfix_no_links : ∀ i : Fin 32,
    ((Zlib.InffixedH.distfix[i.val]!).op &&& 0xf0) != 0 := by
  decide +kernel

/-- A finite cell check against the independent fixed literal/length alphabet.
This includes the four static cells that differ from `inflate_table` output. -/
def fixedLitCellCorrect (i : Fin 512) : Prop :=
  match decodeSym fixedLitLens (bitsOfNat i.val 9), Zlib.InffixedH.lenfix[i.val]? with
  | some (symbol, rest), some entry =>
      rest = (bitsOfNat i.val 9).drop entry.bits.toNat ∧
      entry.bits.toNat = fixedLitLens.getD symbol 0 ∧
      SymbolEntry LENS symbol entry ∧
      (LeafAccepted LENS entry ↔ ValidSymbol LENS symbol)
  | _, _ => False

instance (i : Fin 512) : Decidable (fixedLitCellCorrect i) := by
  unfold fixedLitCellCorrect
  split
  · unfold SymbolEntry LeafAccepted ValidSymbol
    infer_instance
  · infer_instance

set_option maxRecDepth 100000 in
theorem fixedLitCellCorrect_all : ∀ i : Fin 512, fixedLitCellCorrect i := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem lenfix_no_links : ∀ i : Fin 512,
    ¬ ((Zlib.InffixedH.lenfix[i.val]!).op != 0 &&
      ((Zlib.InffixedH.lenfix[i.val]!).op &&& 0xf0) == 0) := by
  decide +kernel

end Zlib.InffixedH.Proofs
