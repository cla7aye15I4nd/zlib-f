import ZlibF.Proof.«deflate.c.engine.small-source-pair»
import ZlibF.Math.DeflateSmallMemoryDynamic
import ZlibF.Proof.«deflate.c.engine.symbol-excess»

namespace Zlib.Deflate.Engine.Proofs.SmallMemory
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs
open Zlib.Trees.Proofs (TK BTBuildFrame btFreq SourceLengthFacts)
open Zlib.Trees.Proofs.Out (TreesInvAt dcodeN)
open ZlibF.Math.DeflateSymbols ZlibF.Math.DeflatePush
set_option autoImplicit false

/-- Both real source builds on a small-memory symbol ledger yield the
unrepaired 5315 excess bound on their actual returned heap. No numeric
budget, source-frequency contract or repair-class assumption is supplied. -/
theorem source_small_excess_engine {h : Heap} {r : ZStreamRef} {ds pb ob : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (ledger : SymbolLedger buf d xs)
    (count : d.sym_next.toNat ≤ d.sym_end.toNat) (memory : d.lit_bufsize.toNat ≤ 1024) :
    ∃ literal result,
      Zlib.Trees.Proofs.blPrepare (some (.tab ds)) h = .ok ((), setD h ds result) ∧
      DGood (setD h ds result) r ds z result ∧ TreesInvAt (setD h ds result) ds result pb buf ∧
      StreamBuffers (setD h ds result) r ∧ ByteSizes h (setD h ds result) ∧
      OutputStorage h (setD h ds result) r ds pb ob ∧ Zlib.Trees.Proofs.BLInput result ∧
      BTBuildFrame .lit .lit d literal ∧ BTBuildFrame .dist .dist literal result ∧
      SourceLengthFacts d result ∧
      1000 * Zlib.Trees.Overlay.bitExcess (dynamicSymbolCosts result xs) ≤ 5315 * (xs.length + 3) := by
  obtain ⟨literal, result, run, goodA, treesA, buffersA, sizes, storage, input, frameL,frameD,WL,WD,weightL,weightD,fibL,fibD⟩ :=
    source_pair_small_direct_engine (ob := ob) good trees buffers ledger count memory
  obtain ⟨other, otherRun, facts⟩ := Zlib.Trees.Proofs.bl_prepare_length_facts trees
  have same : result = other := Zlib.Trees.Proofs.same_record_of_runs run otherRun
  cases same
  have literalFib : ∀ v, v < 286 → literalFrequency symbolLengthCode xs v ≠ 0 →
      literalFrequency symbolLengthCode xs v * Zlib.Trees.HuffmanAbstract.fib
        (Zlib.Trees.Proofs.curL result.dyn_ltree v + 1) ≤ WL := by
    intro v bound nonzero
    have equal : (btFreq .lit d v).toNat = literalFrequency symbolLengthCode xs v := ledger.literal v bound
    have original : btFreq .lit d v ≠ 0 := by
      intro zero; apply nonzero; rw [← equal,zero]; rfl
    simpa only [equal] using fibL v bound original
  have distanceFib : ∀ v, v < 30 → distanceFrequency dcodeN xs v ≠ 0 →
      distanceFrequency dcodeN xs v * Zlib.Trees.HuffmanAbstract.fib
        (Zlib.Trees.Proofs.curL result.dyn_dtree v + 1) ≤ WD := by
    intro v bound nonzero
    have equal : (btFreq .dist d v).toNat = distanceFrequency dcodeN xs v := ledger.distance v bound
    have original : btFreq .dist d v ≠ 0 := by
      intro zero; apply nonzero; rw [← equal,zero]; rfl
    simpa only [equal] using fibD v bound original
  change WL ≤ mass (fun v => d.dyn_ltree[v]!.fc.toNat) 286 + 2 at weightL
  change WD ≤ mass (fun v => d.dyn_dtree[v]!.fc.toNat) 30 + 2 at weightD
  have literalMass := ledger_literal_mass ledger
  have distanceMass := ledger_distance_mass ledger
  rw [literalMass] at weightL
  have data := source_extra_cost_data
  have excess := symbol_excess_without_repair xs
    (Zlib.Trees.Proofs.curL result.dyn_ltree) (Zlib.Trees.Proofs.curL result.dyn_dtree)
    sourceLiteralExtra sourceDistanceExtra symbolLengthCode dcodeN WL WD ledger.valid
    (fun s member => valid_literal_key (ledger.valid s member))
    (fun s member k selected => valid_distance_key (ledger.valid s member) selected)
    (fun c bound => data.1 ⟨c, bound⟩) (fun c bound => data.2.1 ⟨c, bound⟩)
    (fun v bound _nonzero => facts.literal v bound) (fun v bound _nonzero => facts.distance v bound)
    literalFib distanceFib data.2.2.1 data.2.2.2 (by omega) (by omega)
  exact ⟨literal, result, run, goodA, treesA, buffersA, sizes, storage, input, frameL, frameD, facts, excess⟩

#print axioms source_small_excess_engine
end Zlib.Deflate.Engine.Proofs.SmallMemory
