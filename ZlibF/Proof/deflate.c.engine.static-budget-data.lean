import ZlibF.Proof.«deflate.c.engine.symbol-excess»
import ZlibF.Proof.«deflate.c.engine.fixed-payload»
import ZlibF.Math.DeflateStaticBudget

/-! # The original real symbol ledger bounds the natural fixed-code cost -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Trees.Proofs (fixedLiteralWords fixedDistanceWords)
open Zlib.Trees.Proofs.Out (payloadSymBits dcodeN)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

def staticLiteralCost (v : Nat) : Nat :=
  (fixedLiteralWords v).2.toNat + if v < 257 then 0 else sourceLiteralExtra (v - 257)

def staticDistanceCost (v : Nat) : Nat := (fixedDistanceWords v).2.toNat + sourceDistanceExtra v

def staticDistanceSymbolCost (s : Symbol) : Nat :=
  match s.distanceKey dcodeN with
  | none => 0
  | some v => staticDistanceCost v

/-- The fixed tree's length and extra-bit coefficients equal the bit cost
of the actual fixed-symbol wire model, for either kind of stored symbol. -/
theorem static_symbol_cost (s : Symbol) (valid : s.Valid) :
    staticLiteralCost (s.literalKey symbolLengthCode) + staticDistanceSymbolCost s =
      (payloadSymBits fixedLiteralWords fixedDistanceWords (s.distance, s.value)).length := by
  by_cases zero : s.distance = 0
  · have small : s.value < 257 := by have := valid.2; omega
    simp only [Symbol.literalKey, zero, ite_true, staticDistanceSymbolCost, Symbol.distanceKey,
      staticLiteralCost, small, Nat.add_zero, payloadSymBits, Zlib.Trees.Proofs.Out.codeBits,
      Zlib.Trees.Proofs.Out.natBits_length]
  · have above : ¬ (symbolLengthCode s.value + 257 < 257) := by omega
    simp only [Symbol.literalKey, zero, ite_false, staticDistanceSymbolCost, Symbol.distanceKey,
      staticLiteralCost, above, staticDistanceCost, Nat.add_sub_cancel, payloadSymBits,
      List.length_append, Zlib.Trees.Proofs.Out.codeBits, Zlib.Trees.Proofs.Out.natBits_length,
      sourceLiteralExtra, sourceDistanceExtra, symbolLengthCode, Zlib.Trees.Proofs.Out.lcodeN, Nat.add_assoc]
    split <;> omega

set_option maxRecDepth 10000 in
/-- The real ledger's original leaf frequencies have at most 31 fixed
bits per stored symbol plus the seven-bit END_BLOCK. This is a natural
histogram budget; the actual unsigned cost-counter update is separate. -/
theorem ledger_static_cost_budget {buf : Array UInt8} {d : DeflateState} {xs : List Symbol}
    (ledger : SymbolLedger buf d xs) :
    mass (fun v => d.dyn_ltree[v]!.fc.toNat * staticLiteralCost v) 286 +
      mass (fun v => d.dyn_dtree[v]!.fc.toNat * staticDistanceCost v) 30 ≤ 31 * xs.length + 7 := by
  have literal : mass (fun v => d.dyn_ltree[v]!.fc.toNat * staticLiteralCost v) 286 =
      7 + (xs.map (fun s => staticLiteralCost (s.literalKey symbolLengthCode))).sum := by
    rw [mass_congr (fun v fit => by rw [ledger.literal v fit]),
      literal_frequency_cost symbolLengthCode xs staticLiteralCost 286 (by decide +kernel)
        (fun s member => valid_literal_key (ledger.valid s member))]
    rfl
  have distance : mass (fun v => d.dyn_dtree[v]!.fc.toNat * staticDistanceCost v) 30 =
      (xs.map staticDistanceSymbolCost).sum := by
    rw [mass_congr (fun v fit => by rw [ledger.distance v fit])]
    exact weighted_optional_key (Symbol.distanceKey dcodeN) 30 staticDistanceCost
      (fun s member _ selected => valid_distance_key (ledger.valid s member) selected)
  have bound := paired_symbol_cost_bound xs (fun s => staticLiteralCost (s.literalKey symbolLengthCode))
    staticDistanceSymbolCost 31 (fun s member => by
      rw [static_symbol_cost s (ledger.valid s member)]
      exact Zlib.Trees.Proofs.fixed_payload_symbol_length s.distance s.value (ledger.valid s member).1 (ledger.valid s member).2)
  rw [literal, distance]
  omega

end Zlib.Deflate.Engine.Proofs
