import ZlibF.Proof.«deflate.c.engine.dynamic-header»
import ZlibF.Proof.«trees.c.compress-dynamic»

/-! # Real packed symbols instantiate the complete dynamic payload loop -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs (sourceWords dynamicPayloadPrefix SourceCodeFacts DynamicPayloadData)
open Zlib.Trees.Proofs.Out (TreesInvAt payloadSymBits dcodeN)
open ZlibF.Math.DeflateSymbols
open ZlibF.Math.DeflatePush
set_option autoImplicit false

theorem dynamic_symbol_bits_length (d : DeflateState) (s : Symbol) :
    (payloadSymBits (sourceWords d .lit) (sourceWords d .dist) (s.distance, s.value)).length =
      symbolCost (Zlib.Trees.Proofs.curL d.dyn_ltree) (Zlib.Trees.Proofs.curL d.dyn_dtree)
        sourceLiteralExtra sourceDistanceExtra symbolLengthCode dcodeN s := by
  simp only [payloadSymBits, symbolCost]
  split <;> simp only [List.length_append, Zlib.Trees.Proofs.Out.codeBits,
    Zlib.Trees.Proofs.Out.natBits_length, sourceWords, Zlib.Trees.Proofs.PayloadTree.words,
    Zlib.Trees.Proofs.PayloadTree.arr, Zlib.Trees.Proofs.TK.arr, Zlib.Trees.Proofs.curL,
    sourceLiteralExtra, sourceDistanceExtra, symbolLengthCode, Zlib.Trees.Proofs.Out.lcodeN]

/-- Prefix bit length is exactly the sum of the original logical symbol
costs, in their actual packed order. The unread bytes need no extra value
assumptions beyond the established packing and legal symbol ranges. -/
theorem packed_dynamic_prefix_length {buf : Array UInt8} {d : DeflateState} {xs : List Symbol}
    (packed : PackedSymbols buf d.lit_bufsize.toNat xs) (valid : ∀ s ∈ xs, s.Valid)
    (k : Nat) (fit : k ≤ xs.length) :
    (dynamicPayloadPrefix d buf k).length = ((dynamicSymbolCosts d xs).take k).sum := by
  induction k with
  | zero => simp [dynamicPayloadPrefix, Zlib.Trees.Proofs.Out.payloadPrefixBits]
  | succ k ih =>
    have bound : k < xs.length := by omega
    have previous := ih (by omega)
    have read := packed_payload_symbol packed valid k xs[k] (List.getElem?_eq_getElem bound)
    have appended : (dynamicSymbolCosts d xs).take (k + 1) = (dynamicSymbolCosts d xs).take k ++
        [symbolCost (Zlib.Trees.Proofs.curL d.dyn_ltree) (Zlib.Trees.Proofs.curL d.dyn_dtree)
          sourceLiteralExtra sourceDistanceExtra symbolLengthCode dcodeN xs[k]] := by
      rw [List.take_succ_eq_append_getElem (by simpa only [dynamicSymbolCosts, List.length_map] using bound)]
      simp only [dynamicSymbolCosts, List.getElem_map]
    rw [Zlib.Trees.Proofs.dynamicPayloadPrefix_succ, List.length_append, read, dynamic_symbol_bits_length,
      appended, List.sum_append, List.sum_singleton, previous]

/-- All actual code-fit and loop-space premises follow from the original
ledger, the constructed code words and the header's retained payload room.
The default memory equation is established at the default init boundary. -/
theorem dynamic_payload_data {h : Heap} {ds pb : Nat} {original d : DeflateState}
    {originalBuf buf : Array UInt8} {xs : List Symbol}
    (trees : TreesInvAt h ds d pb buf) (ledger : SymbolLedger originalBuf original xs)
    (codes : SourceCodeFacts original d) (packed : PackedSymbols buf d.lit_bufsize.toNat xs)
    (room : DynamicPayloadRoom d xs) (memory : d.lit_bufsize.toNat = 16384) :
    DynamicPayloadData d buf xs.length := by
  constructor
  · exact packed_payload_legal packed ledger.valid
  · intro i bound
    have selected : xs[i]? = some xs[i] := List.getElem?_eq_getElem bound
    have member := List.mem_of_getElem? selected
    rw [packed_payload_symbol packed ledger.valid i xs[i] selected]
    have key : Zlib.Trees.Proofs.dynamicLiteralKey (xs[i].distance, xs[i].value) =
        xs[i].literalKey symbolLengthCode := rfl
    rw [key]
    exact codes.literal _ (valid_literal_key (ledger.valid xs[i] member)) (ledger.literal_used member)
  · intro i bound nonzero
    have selected : xs[i]? = some xs[i] := List.getElem?_eq_getElem bound
    have member := List.mem_of_getElem? selected
    have read := packed_payload_symbol packed ledger.valid i xs[i] selected
    rw [read] at nonzero ⊢
    have selectedKey : xs[i].distanceKey dcodeN = some (dcodeN (xs[i].distance - 1)) := by
      simp only [Symbol.distanceKey, nonzero, ite_false]
    exact codes.distance _ (valid_distance_key (ledger.valid xs[i] member) selectedKey)
      (ledger.distance_used member nonzero)
  · exact codes.literal 256 (by decide +kernel) ledger.end_marker
  · intro k fit
    rw [packed_dynamic_prefix_length packed ledger.valid k fit]
    exact room.prefix_room k
  · rw [packed_dynamic_prefix_length packed ledger.valid xs.length (Nat.le_refl _)]
    have length : (dynamicSymbolCosts d xs).length = xs.length := by simp only [dynamicSymbolCosts, List.length_map]
    rw [← length, List.take_length]
    have size := trees.base.size
    have bound := room.block_room
    omega

end Zlib.Deflate.Engine.Proofs
