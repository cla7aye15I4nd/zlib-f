import ZlibF.Proof.«deflate.c.engine.static-budget-data»
import ZlibF.Proof.«deflate.c.engine.block-initial»
import ZlibF.Proof.«deflate.c.engine.block-prepare»
import ZlibF.Proof.«trees.c.static-counter»
import ZlibF.Math.DeflateBlockSelection

/-! # The actual branch-selection counter is bounded by the original symbols -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

def originalStaticCost (d : DeflateState) : Nat :=
  mass (fun v => d.dyn_ltree[v]!.fc.toNat * staticLiteralCost v) 286 +
    mass (fun v => d.dyn_dtree[v]!.fc.toNat * staticDistanceCost v) 30

set_option maxRecDepth 10000 in
/-- Real source-tree calls produce the original weighted fixed cost, then
both scans and the entire BL call preserve it. Frequencies are measured
before their unions are reused for canonical words. -/
theorem all_trees_static_budget_engine {h : Heap} {r : ZStreamRef} {ds pb ob : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (ledger : SymbolLedger buf d xs) (clear : BlockInit.BlockClear d) :
    ∃ (mb : Int32) (result : DeflateState),
      (do Zlib.Trees.Proofs.blPrepare (some (.tab ds)); Zlib.Trees.build_bl_tree (some (.tab ds))) h =
        .ok (mb, setD h ds result) ∧
      DGood (setD h ds result) r ds z result ∧ TreesInvAt (setD h ds result) ds result pb buf ∧
      StreamBuffers (setD h ds result) r ∧ ByteSizes h (setD h ds result) ∧
      OutputStorage h (setD h ds result) r ds pb ob ∧ TreePreparationFrame d result ∧
      result.static_len = UInt64.ofNat (originalStaticCost d) ∧
      result.static_len.toNat ≤ 31 * xs.length + 7 := by
  obtain ⟨literal, ready, prepare, goodR, treesR, buffersR, _sizesR, _storageR,
    input, _frameL, _frameD, _outputR⟩ := source_trees_engine (ob := ob) good trees buffers
  obtain ⟨otherReady, otherPrepare, cost⟩ := Zlib.Trees.Proofs.bl_prepare_static_cost trees
  have sameReady : otherReady = ready := Zlib.Trees.Proofs.same_record_of_runs otherPrepare prepare
  subst otherReady
  change ready.static_len = d.static_len + UInt64.ofNat (originalStaticCost d) at cost
  rw [clear.fixed, UInt64.zero_add] at cost
  obtain ⟨mb, result, finish, static⟩ := Zlib.Trees.Proofs.build_bl_tree_static_cost treesR input
  change Zlib.Trees.build_bl_tree (some (.tab ds)) (setD h ds ready) =
    .ok (mb, setD (setD h ds ready) ds result) at finish
  rw [setD_setD] at finish
  have complete : (do
      Zlib.Trees.Proofs.blPrepare (some (.tab ds))
      Zlib.Trees.build_bl_tree (some (.tab ds))) h = .ok (mb, setD h ds result) := by
    rw [bind_app, prepare]
    exact finish
  obtain ⟨otherMb, lit, prepared, scanned, built, other, B, run, goodA, treesA, buffersA,
    sizes, storage, _input, frameL, frameD, scans, frame, finishFields, _lower, _upper,
    _guards, _codes, _output⟩ := all_trees_engine (ob := ob) good trees buffers
  have same : result = other := Zlib.Trees.Proofs.same_record_of_runs complete run
  have fullFrame := all_tree_frames frameL frameD scans frame finishFields
  rw [← same] at goodA treesA buffersA sizes storage fullFrame
  have exactCost : result.static_len = UInt64.ofNat (originalStaticCost d) := static.trans cost
  have budget : originalStaticCost d ≤ 31 * xs.length + 7 := ledger_static_cost_budget ledger
  have bound : result.static_len.toNat ≤ 31 * xs.length + 7 := by
    rw [exactCost, UInt64.toNat_ofNat']
    exact Nat.le_trans (Nat.mod_le _ _) budget
  exact ⟨mb, result, complete, goodA, treesA, buffersA, sizes, storage,
    fullFrame, exactCost, bound⟩

/-- The actual public data-type hint statements precede the same cost
proof. Neither branch selection nor an assumed constructor contract is
used to establish the final counter bound. -/
theorem block_prepare_static_budget_engine {h : Heap} {r : ZStreamRef} {ds pb ob : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (ledger : SymbolLedger buf d xs) (clear : BlockInit.BlockClear d) :
    ∃ (mb : Int32) (z' : ZStream) (result : DeflateState),
      blockPrepare (some (.tab ds)) h = .ok (mb, setD (r.put h z') ds result) ∧
      DGood (setD (r.put h z') ds result) r ds z' result ∧
      TreesInvAt (setD (r.put h z') ds result) ds result pb buf ∧
      StreamBuffers (setD (r.put h z') ds result) r ∧ StreamAccounting z z' 0 0 ∧
      ByteSizes h (setD (r.put h z') ds result) ∧
      OutputStorage h (setD (r.put h z') ds result) r ds pb ob ∧ TreePreparationFrame d result ∧
      result.static_len = UInt64.ofNat (originalStaticCost d) ∧
      result.static_len.toNat ≤ 31 * xs.length + 7 := by
  obtain ⟨z', hint, goodZ, treesZ, buffersZ, account, sizesZ, storageZ, _fields, _unknown, _known⟩ :=
    block_data_type_engine (ob := ob) good trees buffers
  obtain ⟨mb, result, run, goodA, treesA, buffersA, sizesA, storageA, frame, exactCost, budget⟩ :=
    all_trees_static_budget_engine (ob := ob) goodZ treesZ buffersZ ledger clear
  refine ⟨mb, z', result, ?_, goodA, treesA, buffersA, account,
    sizesZ.trans sizesA, storageZ.trans storageA, frame, exactCost, budget⟩
  unfold blockPrepare
  rw [bind_app, hint]
  exact run

/-- The actual default-memory symbol range and constructed counter bound
supply the stored branch's pending-space inequality. The stored-word bound
is explicit here; the strategy's signed position calculation must supply
it at the call boundary. This is a branch-data result, not its execution. -/
theorem default_stored_selection_room {h : Heap} {ds pb : Nat}
    {d prepared : DeflateState} {buf : Array UInt8} {xs : List Symbol} {stored : UInt64}
    (trees : TreesInvAt h ds d pb buf) (ledger : SymbolLedger buf d xs)
    (memory : d.lit_bufsize.toNat = 16384) (count : d.sym_next.toNat ≤ d.sym_end.toNat)
    (budget : prepared.static_len.toNat ≤ 31 * xs.length + 7)
    (storedWord : stored.toNat ≤ 4294967296)
    (selected : stored + (4 : UInt64) ≤ ZlibF.Math.DeflateSelection.selectedCost
      (((prepared.opt_len + 3 + 7) >>> 3)) (((prepared.static_len + 3 + 7) >>> 3))
      (prepared.strategy == Z_FIXED)) :
    stored.toNat + 6 ≤ 63488 := by
  have end_ := trees.base.sym_end
  have symbols := ledger.count
  have bound : xs.length ≤ 16383 := by omega
  exact ZlibF.Math.DeflateSelection.stored_default_room bound budget storedWord selected

end Zlib.Deflate.Engine.Proofs
