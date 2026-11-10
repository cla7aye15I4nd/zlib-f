import ZlibF.Proof.«deflate.c.engine.memory-dynamic-header»
import ZlibF.Proof.«deflate.c.engine.dynamic-payload-data»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs (sourceWords dynamicPayloadPrefix SourceCodeFacts DynamicPayloadData)
open Zlib.Trees.Proofs.Out (TreesInvAt payloadSymBits dcodeN)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

theorem memory_dynamic_payload_data {h : Heap} {ds pb : Nat} {original d : DeflateState}
    {originalBuf buf : Array UInt8} {xs : List Symbol}
    (trees : TreesInvAt h ds d pb buf) (ledger : SymbolLedger originalBuf original xs)
    (codes : SourceCodeFacts original d) (packed : PackedSymbols buf d.lit_bufsize.toNat xs)
    (room : MemoryDynamicPayloadRoom d xs) :
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
    have pendingSize := trees.base.psize
    have bound := room.block_room
    omega

end Zlib.Deflate.Engine.Proofs
#print axioms Zlib.Deflate.Engine.Proofs.memory_dynamic_payload_data
