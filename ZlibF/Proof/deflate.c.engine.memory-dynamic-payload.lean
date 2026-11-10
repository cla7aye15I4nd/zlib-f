import ZlibF.Proof.«deflate.c.engine.memory-dynamic-payload-data»
import ZlibF.Proof.«deflate.c.engine.dynamic-payload»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs (sourceWords SourceCodeFacts dynamicPayloadPrefix)
open Zlib.Trees.Proofs.Out (TreesInvAt BitsDiff payloadSymBits codeBits)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

theorem memory_dynamic_payload_ready {h : Heap} {r : ZStreamRef} {ds pb ob : Nat}
    {z : ZStream} {original d : DeflateState} {originalBuf buf : Array UInt8} {xs : List Symbol}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (cursor : d.pending_out = d.pending_buf)
    (ledger : SymbolLedger originalBuf original xs) (codes : SourceCodeFacts original d)
    (packed : PackedSymbols buf d.lit_bufsize.toNat xs) (room : MemoryDynamicPayloadRoom d xs)
    (count : d.sym_next.toNat = 3 * xs.length) :
    ∃ next result,
      let after := setD (Zlib.Trees.Proofs.Out.setB h pb next) ds result
      Zlib.Trees.compress_block (some (.tab ds)) (.ref (Zlib.Trees.Proofs.TK.lit.ref ds) 0)
        (.ref (Zlib.Trees.Proofs.TK.dist.ref ds) 0) h = .ok ((), after) ∧
      DGood after r ds z result ∧ TreesInvAt after ds result pb next ∧ StreamBuffers after r ∧
      ByteSizes h after ∧ OutputStorage h after r ds pb ob ∧ BitsDiff d result ∧ next.size = buf.size ∧
      result.pending_out = result.pending_buf ∧ SourceCodeFacts original result ∧
      8 * result.pending.toNat + result.bi_valid.toInt.toNat + 7 ≤ 8 * result.pending_buf_size.toNat ∧
      Zlib.Trees.Proofs.Out.outBits next result = Zlib.Trees.Proofs.Out.outBits buf d ++
        (xs.flatMap (fun s => payloadSymBits (sourceWords d .lit) (sourceWords d .dist) (s.distance, s.value)) ++
          codeBits (sourceWords d .lit) 256) := by
  have data := memory_dynamic_payload_data trees ledger codes packed room
  obtain ⟨next, result, run, treesA, output, size, _frame, _lower, _upper, diff⟩ :=
    Zlib.Trees.Proofs.compress_block_dynamic_emit trees xs.length count data
  have goodA := output_bits_good good cursor trees.base.bytes size diff treesA
  have buffersA := output_bits_buffers good buffers cursor trees.base.bytes size diff treesA
  have sizes := output_bits_sizes good trees.base.bytes size diff
  have storage := output_bits_storage (r := r) (ob := ob) (result := result) (next := next)
    good.live.hs trees.base.bytes
  have bitCount := congrArg List.length output
  simp only [Zlib.Trees.Proofs.Out.outBits_length, List.length_append, codeBits,
    Zlib.Trees.Proofs.Out.natBits_length] at bitCount
  have prefixLength := packed_dynamic_prefix_length packed ledger.valid xs.length (Nat.le_refl _)
  have costLength : (dynamicSymbolCosts d xs).length = xs.length := by simp only [dynamicSymbolCosts, List.length_map]
  have allCosts : (dynamicSymbolCosts d xs).take xs.length = dynamicSymbolCosts d xs := by
    rw [← costLength, List.take_length]
  rw [allCosts] at prefixLength
  have pendingSize : result.pending_buf_size = d.pending_buf_size := by
    obtain ⟨p, word, valid, used, fields⟩ := diff
    rw [fields]
  have completeRoom : 8 * result.pending.toNat + result.bi_valid.toInt.toNat + 7 ≤ 8 * result.pending_buf_size.toNat := by
    rw [pendingSize]
    have codeBound := data.end_marker.1
    have blockRoom := room.block_room
    omega
  have sizeA : next.size = buf.size := size
  have cursorA : result.pending_out = result.pending_buf := by
    obtain ⟨p, word, valid, used, fields⟩ := diff
    rw [fields]
    exact cursor
  rw [packed_dynamic_payload_bits packed ledger.valid] at output
  exact ⟨next, result, run, goodA, treesA, buffersA, sizes, storage, diff,
    sizeA, cursorA, codes.bitsDiff diff, completeRoom, output⟩

end Zlib.Deflate.Engine.Proofs
#print axioms Zlib.Deflate.Engine.Proofs.memory_dynamic_payload_ready
