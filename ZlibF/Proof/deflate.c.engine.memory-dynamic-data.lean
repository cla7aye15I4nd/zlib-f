import ZlibF.Proof.«deflate.c.engine.memory-dynamic-budget»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs (PreparedHeaderData dynamicHeaderBits)
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

structure MemoryDynamicWriteData (d : DeflateState) (mb : Int32) (xs : List Symbol) : Prop where
  header : PreparedHeaderData d mb
  header_size : (dynamicHeaderBits d mb).length ≤ 2283
  prefix_room : ∀ k, 8 * d.pending.toNat + d.bi_valid.toInt.toNat + 3 +
    (dynamicHeaderBits d mb).length + ((dynamicSymbolCosts d xs).take k).sum + 15 ≤
      8 * (d.lit_bufsize.toNat + 3 * k)
  block_room : 8 * d.pending.toNat + d.bi_valid.toInt.toNat + 3 +
    (dynamicHeaderBits d mb).length + (dynamicSymbolCosts d xs).sum + 15 + 7 ≤ 8 * d.pending_buf_size.toNat

/-- Default-memory construction derives the writer's header and space data
on the same actual heap. The original ledger supplies END_BLOCK. The
BL-zero fact comes from the retained init/reset boundary. -/
theorem memory_all_trees_dynamic_data_engine {memory : Nat} {h : Heap} {r : ZStreamRef} {ds pb ob : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (ledger : SymbolLedger buf d xs)
    (clear : BlockInit.BlockClear d)
    (count : d.sym_next.toNat ≤ d.sym_end.toNat) (capacity : d.lit_bufsize.toNat = 2 ^ (memory + 6))
    (memoryLow : 5 ≤ memory) (memoryHigh : memory ≤ 9)
    (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7) :
    ∃ (mb : Int32) (result : DeflateState),
      (do Zlib.Trees.Proofs.blPrepare (some (.tab ds)); Zlib.Trees.build_bl_tree (some (.tab ds))) h =
        .ok (mb, setD h ds result) ∧
      DGood (setD h ds result) r ds z result ∧ TreesInvAt (setD h ds result) ds result pb buf ∧
      StreamBuffers (setD h ds result) r ∧ ByteSizes h (setD h ds result) ∧
      OutputStorage h (setD h ds result) r ds pb ob ∧ TreePreparationFrame d result ∧
      Zlib.Trees.Proofs.Out.outBits buf result = Zlib.Trees.Proofs.Out.outBits buf d ∧
      MemoryDynamicWriteData result mb xs := by
  obtain ⟨mb, result, run, goodA, treesA, buffersA, sizes, storage,
    _lower, _upper, _guards, fields, output, headerSize, prefixRoom, blockRoom⟩ :=
    memory_all_trees_dynamic_budget_engine (ob := ob) good trees buffers ledger count capacity memoryLow memoryHigh pending bits
  obtain ⟨otherMb, other, dataRun, data⟩ :=
    Zlib.Trees.Proofs.prepare_header_data trees ledger.end_marker clear.bl
  have same : other = result := Zlib.Trees.Proofs.same_record_of_runs dataRun run
  have sameIndex : otherMb = mb := (Prod.mk.inj (Except.ok.inj (dataRun.symm.trans run))).1
  subst other
  subst otherMb
  exact ⟨mb, result, run, goodA, treesA, buffersA, sizes, storage,
    fields, output, data, headerSize, prefixRoom, blockRoom⟩

end Zlib.Deflate.Engine.Proofs
#print axioms Zlib.Deflate.Engine.Proofs.memory_all_trees_dynamic_data_engine
