import ZlibF.Math.DeflateMemoryBounds
import ZlibF.Proof.«deflate.c.engine.dynamic-data»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs (dynamicHeaderBits PreparedHeaderData)
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Actual three-tree preparation derives every unread-symbol prefix
and complete pending-buffer budget at memory five through nine. -/
theorem memory_all_trees_dynamic_budget_engine {memory : Nat} {h : Heap} {r : ZStreamRef} {ds pb ob : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (ledger : SymbolLedger buf d xs)
    (count : d.sym_next.toNat ≤ d.sym_end.toNat) (capacity : d.lit_bufsize.toNat = 2 ^ (memory + 6))
    (memoryLow : 5 ≤ memory) (memoryHigh : memory ≤ 9)
    (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7) :
    ∃ (mb : Int32) (result : DeflateState),
      (do Zlib.Trees.Proofs.blPrepare (some (.tab ds)); Zlib.Trees.build_bl_tree (some (.tab ds))) h =
        .ok (mb, setD h ds result) ∧
      DGood (setD h ds result) r ds z result ∧ TreesInvAt (setD h ds result) ds result pb buf ∧
      StreamBuffers (setD h ds result) r ∧ ByteSizes h (setD h ds result) ∧
      OutputStorage h (setD h ds result) r ds pb ob ∧
      2 ≤ mb.toInt ∧ mb.toInt ≤ 18 ∧ Zlib.Trees.Proofs.SourceGuards result ∧
      TreePreparationFrame d result ∧
      Zlib.Trees.Proofs.Out.outBits buf result = Zlib.Trees.Proofs.Out.outBits buf d ∧
      (dynamicHeaderBits result mb).length ≤ 2283 ∧
      (∀ k, 8 * result.pending.toNat + result.bi_valid.toInt.toNat + 3 +
        (dynamicHeaderBits result mb).length + ((dynamicSymbolCosts result xs).take k).sum + 15 ≤
          8 * (result.lit_bufsize.toNat + 3 * k)) ∧
      8 * result.pending.toNat + result.bi_valid.toInt.toNat + 3 + (dynamicHeaderBits result mb).length +
        (dynamicSymbolCosts result xs).sum + 15 + 7 ≤ 8 * result.pending_buf_size.toNat := by
  obtain ⟨mb, result, run, goodA, treesA, buffersA, sizes, storage,
    lower, upper, guards, fields, output, excess⟩ :=
    all_trees_symbol_excess_engine (ob := ob) good trees buffers ledger count
  obtain ⟨_literal, ready, prepare, _goodR, treesR, _buffersR, _sizesR, _storageR,
    input, _frameL, _frameD, _outputR⟩ := source_trees_engine (ob := ob) good trees buffers
  obtain ⟨mb2, other, build, header⟩ := Zlib.Trees.Proofs.build_bl_tree_header_budget treesR input
  have complete : (do
        Zlib.Trees.Proofs.blPrepare (some (.tab ds))
        Zlib.Trees.build_bl_tree (some (.tab ds))) h = .ok (mb2, setD h ds other) := by
    rw [bind_app, prepare]
    change Zlib.Trees.build_bl_tree (some (.tab ds)) (setD h ds ready) =
      .ok (mb2, setD (setD h ds ready) ds other) at build
    simpa only [setD_setD] using build
  have sameResult : result = other := Zlib.Trees.Proofs.same_record_of_runs run complete
  have sameIndex : mb = mb2 := (Prod.mk.inj (Except.ok.inj (run.symm.trans complete))).1
  rw [← sameResult, ← sameIndex] at header
  have actualPending : result.pending = 0 := by rw [fields]; exact pending
  have actualBits : result.bi_valid.toInt.toNat ≤ 7 := by
    have same : result.bi_valid = d.bi_valid := by rw [fields]
    rw [same]
    omega
  have actualCapacity : result.lit_bufsize.toNat = 2 ^ (memory + 6) := by rw [fields]; exact capacity
  have symbolsFit : (dynamicSymbolCosts result xs).length + 1 ≤ ZlibF.Math.DeflateMemLevel.symbolSlots memory := by
    have entries := ledger.count
    have end_ := trees.base.sym_end
    have slotsPositive := Nat.two_pow_pos (memory + 6)
    simp only [dynamicSymbolCosts, List.length_map]
    unfold ZlibF.Math.DeflateMemLevel.symbolSlots
    omega
  have excessFit : 1000 * Zlib.Trees.Overlay.bitExcess (dynamicSymbolCosts result xs) ≤
      6257 * ((dynamicSymbolCosts result xs).length + 3) := by
    simpa only [dynamicSymbolCosts, List.length_map] using excess
  have pendingCapacity : result.pending_buf_size.toNat = ZlibF.Math.DeflateMemLevel.pendingBytes memory := by
    rw [treesA.base.psize, treesA.base.size, actualCapacity]
    rfl
  refine ⟨mb, result, run, goodA, treesA, buffersA, sizes, storage, lower, upper, guards,
    fields, output, header, ?_, ?_⟩
  · intro k
    have bound := ZlibF.Math.DeflateMemLevel.dynamic_overlay_prefix_from_memory_five
      memoryLow memoryHigh (dynamicSymbolCosts result xs) actualBits header symbolsFit excessFit k
    simpa only [actualPending, actualCapacity, ZlibF.Math.DeflateMemLevel.symbolSlots,
      show (0 : UInt64).toNat = 0 from rfl, Nat.mul_zero, Nat.zero_add] using bound
  · have bound := ZlibF.Math.DeflateMemLevel.dynamic_pending_room_from_memory_five
      memoryLow memoryHigh (dynamicSymbolCosts result xs) actualBits header symbolsFit excessFit
    simpa only [actualPending, pendingCapacity, show (0 : UInt64).toNat = 0 from rfl,
      Nat.mul_zero, Nat.zero_add] using bound

end Zlib.Deflate.Engine.Proofs
#print axioms Zlib.Deflate.Engine.Proofs.memory_all_trees_dynamic_budget_engine
