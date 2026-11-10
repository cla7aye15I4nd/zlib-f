import ZlibF.Proof.«deflate.c.engine.memory-dynamic-data»
import ZlibF.Proof.«deflate.c.engine.dynamic-header»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs (dynamicHeaderBits dynamicTag PreparedHeaderData)
open Zlib.Trees.Proofs.Out (TreesInvAt BitsDiff)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

structure MemoryDynamicPayloadRoom (d : DeflateState) (xs : List Symbol) : Prop where
  prefix_room : ∀ k, 8 * d.pending.toNat + d.bi_valid.toInt.toNat +
    ((dynamicSymbolCosts d xs).take k).sum + 15 ≤ 8 * (d.lit_bufsize.toNat + 3 * k)
  block_room : 8 * d.pending.toNat + d.bi_valid.toInt.toNat +
    (dynamicSymbolCosts d xs).sum + 15 + 7 ≤ 8 * d.pending_buf_size.toNat

/-- Actual dynamic-header emission derives its room from construction.
Output writes cannot reach the packed symbols. The same concrete heap
retains the engine, caller storage, code data and payload prefix budget.
No header-emitter contract or separate capacity bound is assumed. -/
theorem memory_dynamic_header_engine {h : Heap} {r : ZStreamRef} {ds pb ob : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol} {mb : Int32}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (cursor : d.pending_out = d.pending_buf) (write : MemoryDynamicWriteData d mb xs)
    (packed : PackedSymbols buf d.lit_bufsize.toNat xs) (last : Bool) :
    ∃ next result,
      let after := setD (Zlib.Trees.Proofs.Out.setB h pb next) ds result
      Zlib.Trees.Proofs.dynamicBlockHeader (some (.tab ds)) (if last then 1 else 0) mb h = .ok ((), after) ∧
      DGood after r ds z result ∧ TreesInvAt after ds result pb next ∧ StreamBuffers after r ∧
      ByteSizes h after ∧ OutputStorage h after r ds pb ob ∧ BitsDiff d result ∧ next.size = buf.size ∧
      result.pending_out = result.pending_buf ∧ PackedSymbols next result.lit_bufsize.toNat xs ∧
      PreparedHeaderData result mb ∧ MemoryDynamicPayloadRoom result xs ∧
      Zlib.Trees.Proofs.Out.outBits next result = Zlib.Trees.Proofs.Out.outBits buf d ++
        (dynamicTag last ++ dynamicHeaderBits d mb) := by
  have initialRoom := write.prefix_room 0
  simp only [List.take_zero, List.sum_nil, Nat.add_zero, Nat.mul_zero] at initialRoom
  have room : 8 * d.pending.toNat + d.bi_valid.toInt.toNat + 3 +
      (dynamicHeaderBits d mb).length ≤ 8 * buf.size := by
    have size := trees.base.size
    omega
  obtain ⟨next, result, run, treesA, output, size, frame, _lower, _upper, diff⟩ :=
    Zlib.Trees.Proofs.dynamic_block_header_emit trees write.header last room
  have goodA := output_bits_good good cursor trees.base.bytes size diff treesA
  have buffersA := output_bits_buffers good buffers cursor trees.base.bytes size diff treesA
  have sizes := output_bits_sizes good trees.base.bytes size diff
  have storage := output_bits_storage (r := r) (ob := ob) (result := result) (next := next)
    good.live.hs trees.base.bytes
  have bitCount := congrArg List.length output
  simp only [Zlib.Trees.Proofs.Out.outBits_length, List.length_append,
    dynamicTag, Zlib.Trees.Proofs.Out.natBits_length] at bitCount
  have capacity : result.lit_bufsize = d.lit_bufsize := by
    obtain ⟨p, word, valid, used, fields⟩ := diff
    rw [fields]
  have cursorA : result.pending_out = result.pending_buf := by
    obtain ⟨p, word, valid, used, fields⟩ := diff
    rw [fields]
    exact cursor
  have packedA : PackedSymbols next result.lit_bufsize.toNat xs := by
    rw [capacity]
    intro i s selected
    obtain ⟨low, high, value⟩ := packed i s selected
    have untouched (j : Nat) (bound : d.lit_bufsize.toNat ≤ j) : bfn next j = bfn buf j := by
      exact frame j (Or.inr (by omega))
    exact ⟨(untouched _ (by omega)).trans low, (untouched _ (by omega)).trans high,
      (untouched _ (by omega)).trans value⟩
  have costs := dynamicSymbolCosts_bitsDiff xs diff
  have pendingSize : result.pending_buf_size = d.pending_buf_size := by
    obtain ⟨p, word, valid, used, fields⟩ := diff
    rw [fields]
  have payload : MemoryDynamicPayloadRoom result xs := by
    constructor
    · intro k
      rw [costs, capacity]
      have before := write.prefix_room k
      omega
    · rw [costs, pendingSize]
      have before := write.block_room
      omega
  exact ⟨next, result, run, goodA, treesA, buffersA, sizes, storage, diff, size,
    cursorA, packedA, write.header.bitsDiff diff, payload, output⟩

end Zlib.Deflate.Engine.Proofs
#print axioms Zlib.Deflate.Engine.Proofs.memory_dynamic_header_engine
