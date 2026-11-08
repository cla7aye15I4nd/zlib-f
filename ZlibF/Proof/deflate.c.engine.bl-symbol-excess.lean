import ZlibF.Proof.«deflate.c.engine.symbol-excess»
import ZlibF.Proof.«deflate.c.engine.block-prepare»

/-! # The symbol budget survives the actual BL sentinel writes -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs (SourceLengthFacts)
open Zlib.Trees.Proofs.Out (TreesInvAt dcodeN)
open ZlibF.Math.DeflateSymbols
open ZlibF.Math.DeflatePush
set_option autoImplicit false

/-- Every stored symbol has a positive original literal/length frequency. -/
theorem SymbolLedger.literal_used {buf : Array UInt8} {d : DeflateState} {xs : List Symbol}
    (ledger : SymbolLedger buf d xs) {s : Symbol} (member : s ∈ xs) :
    d.dyn_ltree[s.literalKey symbolLengthCode]!.fc ≠ 0 := by
  have positive := count_key_positive (fun s => some (s.literalKey symbolLengthCode)) member rfl
  have frequency := ledger.literal _ (valid_literal_key (ledger.valid s member))
  intro zero
  rw [zero] at frequency
  unfold literalFrequency at frequency
  change 0 = _ at frequency
  omega

/-- A stored match also has a positive original distance frequency. -/
theorem SymbolLedger.distance_used {buf : Array UInt8} {d : DeflateState} {xs : List Symbol}
    (ledger : SymbolLedger buf d xs) {s : Symbol} (member : s ∈ xs)
    (match_ : s.distance ≠ 0) :
    d.dyn_dtree[dcodeN (s.distance - 1)]!.fc ≠ 0 := by
  have selected : s.distanceKey dcodeN = some (dcodeN (s.distance - 1)) := by
    simp only [Symbol.distanceKey, match_, ite_false]
  have positive := count_key_positive (Symbol.distanceKey dcodeN) member selected
  have frequency := ledger.distance _ (valid_distance_key (ledger.valid s member) selected)
  intro zero
  rw [zero] at frequency
  change 0 = _ at frequency
  unfold distanceFrequency at frequency
  omega

/-- A sentinel is outside every original used symbol. Agreement below the
actual descriptor maxima therefore retains every stored symbol's cost.
Unused lengths, including the sentinel itself, need not agree. -/
theorem dynamicSymbolCosts_live_congr {buf : Array UInt8} {original before after : DeflateState}
    {xs : List Symbol} (ledger : SymbolLedger buf original xs) (facts : SourceLengthFacts original before)
    (literal : ∀ i ≤ before.l_desc.max_code.toInt.toNat, after.dyn_ltree[i]! = before.dyn_ltree[i]!)
    (distance : ∀ i ≤ before.d_desc.max_code.toInt.toNat, after.dyn_dtree[i]! = before.dyn_dtree[i]!) :
    dynamicSymbolCosts after xs = dynamicSymbolCosts before xs := by
  apply List.map_congr_left
  intro s member
  have literalSame := literal _ (facts.literal_used _ (valid_literal_key (ledger.valid s member))
    (ledger.literal_used member))
  by_cases lit : s.distance = 0
  · have key : s.literalKey symbolLengthCode = s.value := by simp only [Symbol.literalKey, lit, ite_true]
    rw [key] at literalSame
    simp only [symbolCost, lit, ite_true, Zlib.Trees.Proofs.curL, literalSame]
  · have selected : s.distanceKey dcodeN = some (dcodeN (s.distance - 1)) := by
      simp only [Symbol.distanceKey, lit, ite_false]
    have distanceSame := distance _ (facts.distance_used _
      (valid_distance_key (ledger.valid s member) selected) (ledger.distance_used member lit))
    have key : s.literalKey symbolLengthCode = symbolLengthCode s.value + 257 := by
      simp only [Symbol.literalKey, lit, ite_false]
    rw [key] at literalSame
    simp only [symbolCost, lit, ite_false, Zlib.Trees.Proofs.curL, literalSame, distanceSame]

/-- Both source constructors, both sentinel scans, BL construction, search
and the real header-cost store retain the derived symbol-excess budget.
All data premises come from the original ledger and the actual executions. -/
theorem all_trees_symbol_excess_engine {h : Heap} {r : ZStreamRef} {ds pb ob : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (ledger : SymbolLedger buf d xs)
    (count : d.sym_next.toNat ≤ d.sym_end.toNat) :
    ∃ (mb : Int32) (result : DeflateState),
      (do Zlib.Trees.Proofs.blPrepare (some (.tab ds)); Zlib.Trees.build_bl_tree (some (.tab ds))) h =
        .ok (mb, setD h ds result) ∧
      DGood (setD h ds result) r ds z result ∧ TreesInvAt (setD h ds result) ds result pb buf ∧
      StreamBuffers (setD h ds result) r ∧ ByteSizes h (setD h ds result) ∧
      OutputStorage h (setD h ds result) r ds pb ob ∧
      2 ≤ mb.toInt ∧ mb.toInt ≤ 18 ∧ Zlib.Trees.Proofs.SourceGuards result ∧
      TreePreparationFrame d result ∧
      Zlib.Trees.Proofs.Out.outBits buf result = Zlib.Trees.Proofs.Out.outBits buf d ∧
      1000 * Zlib.Trees.Overlay.bitExcess (dynamicSymbolCosts result xs) ≤ 6257 * (xs.length + 3) := by
  obtain ⟨literal, ready, prepare, goodR, treesR, buffersR, sizesR, storageR, input,
    frameL, frameD, facts, excess⟩ := source_trees_symbol_excess_engine (ob := ob) good trees buffers ledger count
  obtain ⟨mb, scanned, built, result, B, run, goodA, treesA, buffersA, sizesA, storageA,
    scans, _frequencies, frame, finish, _index, lower, upper, guards, _codes, output⟩ :=
    build_bl_tree_engine (ob := ob) goodR treesR buffersR input
  obtain ⟨otherMb, other, otherRun, _lDesc, _dDesc, lTree, dTree, _otherTrees, _otherOutput⟩ :=
    Zlib.Trees.Proofs.build_bl_preserves_source_codes treesR input
  have same : result = other := Zlib.Trees.Proofs.same_record_of_runs run otherRun
  have costs : dynamicSymbolCosts result xs = dynamicSymbolCosts ready xs := by
    rw [same]
    exact dynamicSymbolCosts_live_congr ledger facts lTree dTree
  rw [← costs] at excess
  have complete : (do
        Zlib.Trees.Proofs.blPrepare (some (.tab ds))
        Zlib.Trees.build_bl_tree (some (.tab ds))) h = .ok (mb, setD h ds result) := by
    rw [bind_app, prepare]
    simpa only [setD_setD] using run
  have sizes := sizesR.trans sizesA
  have storage := storageR.trans storageA
  have fields := all_tree_frames frameL frameD scans frame finish
  obtain ⟨_l, _r, prepare2, _g, _t, _b, _s, _o, _i, _f1, _f2, outputR⟩ :=
    source_trees_engine (ob := ob) good trees buffers
  have sameReady : ready = _r := Zlib.Trees.Proofs.same_record_of_runs prepare prepare2
  rw [← sameReady] at outputR
  simp only [setD_setD] at goodA treesA buffersA sizes storage
  exact ⟨mb, result, complete, goodA, treesA, buffersA, sizes, storage,
    lower, upper, guards, fields, output.trans outputR, excess⟩

end Zlib.Deflate.Engine.Proofs
