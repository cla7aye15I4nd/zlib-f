import ZlibF.Proof.«deflate.c.engine.tree-fib-origins»
import ZlibF.Proof.«trees.c.build.symbol-budget»
import ZlibF.Proof.«trees.c.source-length-facts»
import ZlibF.Math.DeflateSymbolExcess

/-! # Actual source-tree preparation establishes the dynamic symbol-excess budget -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs (TK BTBuildFrame btFreq SourceLengthFacts)
open Zlib.Trees.Proofs.Out (TreesInvAt dcodeN)
open ZlibF.Math.DeflateSymbols
open ZlibF.Math.DeflatePush
set_option autoImplicit false

def sourceLiteralExtra (c : Nat) : Nat := Zlib.Trees.extra_lbits_tab[c]!.toInt.toNat
def sourceDistanceExtra (c : Nat) : Nat := Zlib.Trees.extra_dbits_tab[c]!.toInt.toNat

def dynamicSymbolCosts (d : DeflateState) (xs : List Symbol) : List Nat :=
  xs.map (symbolCost (Zlib.Trees.Proofs.curL d.dyn_ltree) (Zlib.Trees.Proofs.curL d.dyn_dtree)
    sourceLiteralExtra sourceDistanceExtra symbolLengthCode dcodeN)

set_option maxRecDepth 10000 in
/-- Finite extra-bit data and integer certificate coefficients agree with
the actual translated source tables. The kernel checks all table entries. -/
theorem source_extra_cost_data :
    (∀ c : Fin 29, sourceLiteralExtra c.val < 6) ∧
    (∀ c : Fin 30, sourceDistanceExtra c.val < 14) ∧
    mass (fun v => if v < 257 then 0 else lengthCoefficient (sourceLiteralExtra (v - 257))) 286 = 1921 ∧
    mass (fun v => distanceCoefficient (sourceDistanceExtra v)) 30 = 1660 := by decide +kernel

/-- The real source-tree calls, exact original symbol ledger and proved
FibPush results establish the whole stored-symbol excess bound on their
actual returned heap. The only frequency facts are those from the original
ledger and actual dummy/merge execution. BL sentinel transport and emission
are subsequent source steps, not assumed called-function contracts. -/
theorem source_trees_symbol_excess_engine {h : Heap} {r : ZStreamRef} {ds pb ob : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (ledger : SymbolLedger buf d xs)
    (count : d.sym_next.toNat ≤ d.sym_end.toNat) :
    ∃ literal result,
      Zlib.Trees.Proofs.blPrepare (some (.tab ds)) h = .ok ((), setD h ds result) ∧
      DGood (setD h ds result) r ds z result ∧ TreesInvAt (setD h ds result) ds result pb buf ∧
      StreamBuffers (setD h ds result) r ∧ ByteSizes h (setD h ds result) ∧
      OutputStorage h (setD h ds result) r ds pb ob ∧ Zlib.Trees.Proofs.BLInput result ∧
      BTBuildFrame .lit .lit d literal ∧ BTBuildFrame .dist .dist literal result ∧
      SourceLengthFacts d result ∧
      1000 * Zlib.Trees.Overlay.bitExcess (dynamicSymbolCosts result xs) ≤ 6257 * (xs.length + 3) := by
  obtain ⟨literal, result, run, goodA, treesA, buffersA, sizes, storage, input, frameL, frameD, originsL, originsD⟩ :=
    source_trees_fib_origins_engine (ob := ob) good trees buffers ledger count
  obtain ⟨other, otherRun, facts⟩ := Zlib.Trees.Proofs.bl_prepare_length_facts trees
  have same : result = other := Zlib.Trees.Proofs.same_record_of_runs run otherRun
  cases same
  obtain ⟨WL, weightL, fibL⟩ := originsL.symbol_budget
  obtain ⟨WD, weightD, fibD⟩ := originsD.symbol_budget
  have literalFib : SymbolFibPush 286 WL (literalFrequency symbolLengthCode xs)
      (Zlib.Trees.Proofs.curL result.dyn_ltree) := by
    apply fibL.congr_frequency
    intro v bound
    exact (ledger.literal v bound).symm
  have distanceFib : SymbolFibPush 30 WD (distanceFrequency dcodeN xs)
      (Zlib.Trees.Proofs.curL result.dyn_dtree) := by
    apply fibD.congr_frequency
    intro v bound
    exact (ledger.distance v bound).symm
  change WL ≤ mass (fun v => d.dyn_ltree[v]!.fc.toNat) 286 + 2 at weightL
  change WD ≤ mass (fun v => d.dyn_dtree[v]!.fc.toNat) 30 + 2 at weightD
  have literalMass := ledger_literal_mass ledger
  have distanceMass := ledger_distance_mass ledger
  rw [literalMass] at weightL
  have data := source_extra_cost_data
  have excess := symbol_excess_from_fib xs
    (Zlib.Trees.Proofs.curL result.dyn_ltree) (Zlib.Trees.Proofs.curL result.dyn_dtree)
    sourceLiteralExtra sourceDistanceExtra symbolLengthCode dcodeN WL WD ledger.valid
    (fun s member => valid_literal_key (ledger.valid s member))
    (fun s member k selected => valid_distance_key (ledger.valid s member) selected)
    (fun c bound => data.1 ⟨c, bound⟩) (fun c bound => data.2.1 ⟨c, bound⟩)
    (fun v bound _nonzero => facts.literal v bound) (fun v bound _nonzero => facts.distance v bound)
    literalFib distanceFib data.2.2.1 data.2.2.2 (by omega) (by omega)
  exact ⟨literal, result, run, goodA, treesA, buffersA, sizes, storage, input, frameL, frameD, facts, excess⟩

end Zlib.Deflate.Engine.Proofs
