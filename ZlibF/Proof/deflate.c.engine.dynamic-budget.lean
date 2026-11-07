import ZlibF.Proof.«deflate.c.engine.bl-symbol-excess»
import ZlibF.Proof.«trees.c.header-budget»

/-! # Default pending and unread-symbol room from actual tree construction -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs (dynamicHeaderBits)
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The actual three constructors and sentinel scans establish both the
dynamic header bound and every unread-symbol prefix bound for default
memLevel 8. The internal entry is an empty pending buffer with at most
seven held bits; symbol frequencies and bytes come from the actual ledger.
This result establishes room, not execution of the dynamic writer. -/
theorem all_trees_dynamic_budget_engine {h : Heap} {r : ZStreamRef} {ds pb ob : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (ledger : SymbolLedger buf d xs)
    (count : d.sym_next.toNat ≤ d.sym_end.toNat) (capacity : d.lit_bufsize.toNat = 16384)
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
        (dynamicSymbolCosts result xs).sum + 15 + 7 ≤ 8 * 63488 := by
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
  have actualCapacity : result.lit_bufsize.toNat = 16384 := by rw [fields]; exact capacity
  have symbolsFit : (dynamicSymbolCosts result xs).length + 1 ≤ 16384 := by
    have entries := ledger.count
    have end_ := trees.base.sym_end
    simp only [dynamicSymbolCosts, List.length_map]
    omega
  have excessFit : 1000 * Zlib.Trees.Overlay.bitExcess (dynamicSymbolCosts result xs) ≤
      6257 * ((dynamicSymbolCosts result xs).length + 3) := by
    simpa only [dynamicSymbolCosts, List.length_map] using excess
  refine ⟨mb, result, run, goodA, treesA, buffersA, sizes, storage, lower, upper, guards,
    fields, output, header, ?_, ?_⟩
  · intro k
    have bound := Zlib.Trees.Overlay.large_overlay_prefix_coarse 16384 result.bi_valid.toInt.toNat
      (dynamicHeaderBits result mb).length (dynamicSymbolCosts result xs)
      (by decide +kernel) actualBits header symbolsFit excessFit k
    simpa only [actualPending, actualCapacity, show (0 : UInt64).toNat = 0 from rfl,
      Nat.mul_zero, Nat.zero_add] using bound
  · have bound := Zlib.Trees.Overlay.default_block_room_coarse result.bi_valid.toInt.toNat
      (dynamicHeaderBits result mb).length (dynamicSymbolCosts result xs)
      actualBits header symbolsFit excessFit
    simpa only [actualPending, show (0 : UInt64).toNat = 0 from rfl,
      Nat.mul_zero, Nat.zero_add] using bound

end Zlib.Deflate.Engine.Proofs
