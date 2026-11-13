import ZlibF.Math.DeflateOverlayFibActual
import ZlibF.Proof.«trees.c.universal-overlay-mid»

/-!
# deflate.c: the block excess at the actual frequencies (`TinyOverlay`, B3)

For a block with `lit_bufsize ≤ 1024` (`memLevel` 1 to 3), the data trees stay unclamped (their
weight is below F(17) = 1597), so every code keeps its Fibonacci length bound for the tree weight,
which is at most `lit_bufsize + 2`. Hence the excess of the prepared block is at most
`excessFibActual (lit_bufsize + 2)` of the actual symbol frequencies. Stated from the tree
invariant on any heap, so it applies on the heap with any stream record (`DynamicOverlay`).
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs (blPrepare btFreq curL same_record_of_runs)
open Zlib.Trees.Proofs.Out (TreesInvAt dcodeN)
open ZlibF.Math.DeflateSymbols
open ZlibF.Math.DeflatePush (symbolCost)
open ZlibF.Math.DeflateOverlaySmall
set_option autoImplicit false

/-- **B3: the excess with the actual frequencies.** -/
theorem excess_fib_actual {h : Heap} {ds pb : Nat} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol}
    (trees : TreesInvAt h ds d pb buf) (ledger : SymbolLedger buf d xs) (fit : d.lit_bufsize.toNat ≤ 1024)
    {mb : Int32} {ready : DeflateState}
    (run : (do blPrepare (some (.tab ds)); Zlib.Trees.build_bl_tree (some (.tab ds))) h =
      .ok (mb, setD h ds ready)) :
    Zlib.Trees.Overlay.bitExcess (dynamicSymbolCosts ready xs) ≤
      excessFibActual (d.lit_bufsize.toNat + 2) (literalFrequency symbolLengthCode xs)
        (distanceFrequency dcodeN xs) sourceLiteralExtra sourceDistanceExtra := by
  have capacity : xs.length + 1 ≤ d.lit_bufsize.toNat := by
    have bound := trees.run.sym_next_le
    rw [ledger.count, trees.base.sym_end] at bound
    have low := trees.base.lit_lo
    omega
  have literalMass := ledger_literal_mass ledger
  have distanceMass := ledger_distance_mass ledger
  have budgetL : mass (fun v => (btFreq .lit d v).toNat) 286 + 2 < 1597 := by
    change mass (fun k => (d.dyn_ltree[k]!).fc.toNat) 286 + 2 < 1597
    omega
  have budgetD : mass (fun v => (btFreq .dist d v).toNat) 30 + 2 < 1597 := by
    change mass (fun k => (d.dyn_dtree[k]!).fc.toNat) 30 + 2 < 1597
    omega
  obtain ⟨readyP, prepare, fibL, fibD⟩ := Zlib.Trees.Proofs.bl_prepare_fib_plus trees budgetL budgetD
  obtain ⟨other, otherRun, facts⟩ := Zlib.Trees.Proofs.bl_prepare_length_facts trees
  have sameF : readyP = other := same_record_of_runs prepare otherRun
  subst other
  obtain ⟨WL, weightL, symbolL⟩ := fibL.symbol_fib_plus
  obtain ⟨WD, weightD, symbolD⟩ := fibD.symbol_fib_plus
  change WL ≤ mass (fun v => (d.dyn_ltree[v]!).fc.toNat) 286 + 2 at weightL
  change WD ≤ mass (fun v => (d.dyn_dtree[v]!).fc.toNat) 30 + 2 at weightD
  have literalFib : SymbolFibPlus 286 WL (literalFrequency symbolLengthCode xs) (curL readyP.dyn_ltree) := by
    intro v bound nonzero
    have equal : (btFreq .lit d v).toNat = literalFrequency symbolLengthCode xs v := ledger.literal v bound
    have claim := symbolL v bound (by show (btFreq .lit d v).toNat ≠ 0; rw [equal]; exact nonzero)
    dsimp only at claim
    rw [equal] at claim
    exact claim
  have distanceFib : SymbolFibPlus 30 WD (distanceFrequency dcodeN xs) (curL readyP.dyn_dtree) := by
    intro v bound nonzero
    have equal : (btFreq .dist d v).toNat = distanceFrequency dcodeN xs v := ledger.distance v bound
    have claim := symbolD v bound (by show (btFreq .dist d v).toNat ≠ 0; rw [equal]; exact nonzero)
    dsimp only at claim
    rw [equal] at claim
    exact claim
  have excess := symbol_excess_fib_actual xs (curL readyP.dyn_ltree) (curL readyP.dyn_dtree)
    sourceLiteralExtra sourceDistanceExtra symbolLengthCode dcodeN WL WD (d.lit_bufsize.toNat + 2) ledger.valid
    (fun s member => valid_literal_key (ledger.valid s member))
    (fun s member k selected => valid_distance_key (ledger.valid s member) selected)
    (fun v bound _nonzero => facts.literal v bound) (fun v bound _nonzero => facts.distance v bound)
    literalFib distanceFib (by omega) (by omega)
  -- the costs of the prepared state are those after the data trees
  obtain ⟨other, prepared, input, treesR, _bl, _bits⟩ := Zlib.Trees.Proofs.bl_prepare trees
  have sameR : readyP = other := same_record_of_runs prepare prepared
  subst other
  obtain ⟨mb', result, run', _lDesc, _dDesc, lTree, dTree, _treesA, _outputA⟩ :=
    Zlib.Trees.Proofs.build_bl_preserves_source_codes treesR input
  have costs : dynamicSymbolCosts result xs = dynamicSymbolCosts readyP xs :=
    dynamicSymbolCosts_live_congr ledger facts lTree dTree
  have complete : (do
        Zlib.Trees.Proofs.blPrepare (some (.tab ds))
        Zlib.Trees.build_bl_tree (some (.tab ds))) h = .ok (mb', setD h ds result) := by
    rw [bind_app, prepare]
    rw [Zlib.Trees.Proofs.setD_setD] at run'
    exact run'
  have eR : ready = result := same_record_of_runs run complete
  subst eR
  rw [costs]
  exact excess

#print axioms excess_fib_actual

end Zlib.Deflate.Engine.Proofs
