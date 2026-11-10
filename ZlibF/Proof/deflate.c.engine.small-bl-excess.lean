import ZlibF.Proof.«deflate.c.engine.small-source-excess»
import ZlibF.Proof.«deflate.c.engine.bl-symbol-excess»

namespace Zlib.Deflate.Engine.Proofs.SmallMemory
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs
open Zlib.Trees.Proofs (SourceLengthFacts)
open Zlib.Trees.Proofs.Out (TreesInvAt dcodeN)
open ZlibF.Math.DeflateSymbols ZlibF.Math.DeflatePush
set_option autoImplicit false

/-- Actual paired source construction, both BL scans, BL build/search and
cost stores retain the 5315 excess bound. Sentinel agreement is proved
only where the original symbol ledger has positive frequency. -/
theorem all_trees_small_excess_engine {h : Heap} {r : ZStreamRef} {ds pb ob : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (ledger : SymbolLedger buf d xs)
    (count : d.sym_next.toNat ≤ d.sym_end.toNat) (memory : d.lit_bufsize.toNat ≤ 1024) :
    ∃ (mb : Int32) (result : DeflateState),
      (do Zlib.Trees.Proofs.blPrepare (some (.tab ds)); Zlib.Trees.build_bl_tree (some (.tab ds))) h =
        .ok (mb, setD h ds result) ∧
      DGood (setD h ds result) r ds z result ∧ TreesInvAt (setD h ds result) ds result pb buf ∧
      StreamBuffers (setD h ds result) r ∧ ByteSizes h (setD h ds result) ∧
      OutputStorage h (setD h ds result) r ds pb ob ∧
      2 ≤ mb.toInt ∧ mb.toInt ≤ 18 ∧ Zlib.Trees.Proofs.SourceGuards result ∧
      TreePreparationFrame d result ∧
      Zlib.Trees.Proofs.Out.outBits buf result = Zlib.Trees.Proofs.Out.outBits buf d ∧
      1000 * Zlib.Trees.Overlay.bitExcess (dynamicSymbolCosts result xs) ≤ 5315 * (xs.length + 3) := by
  obtain ⟨literal, ready, prepare, goodR, treesR, buffersR, sizesR, storageR, input,
    frameL, frameD, facts, excess⟩ := source_small_excess_engine (ob := ob) good trees buffers ledger count memory
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

#print axioms all_trees_small_excess_engine
end Zlib.Deflate.Engine.Proofs.SmallMemory
