import ZlibF.Math.«existing-slow-small-rows-math»
import ZlibF.Proof.«deflate.c.engine.small-bl-excess»
import ZlibF.Proof.«trees.c.source-code-facts»

namespace Zlib.Deflate.Engine.Proofs.SmallMemory
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs
open Zlib.Trees.Proofs (curL SourceCodeFacts)
open Zlib.Trees.Proofs.Out (TreesInvAt dcodeN)
open ZlibF.Math.DeflateSymbols ZlibF.Math.SmallMemoryRows
set_option autoImplicit false

/-- The actual literal/distance/BL constructors produce original-frequency
LP base rows on one returned heap: symbol mass, match balance, exact EOB and
all twenty-five excess rows. These are ungrouped real-symbol rows, before the
remaining finite column/type aggregation and full LP feasibility proof.
No feasibility or lowmem_lp_bound hypothesis is introduced. -/
theorem actual_small_memory_base_rows {h : Heap} {r : ZStreamRef} {ds pb ob : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (ledger : SymbolLedger buf d xs)
    (count : d.sym_next.toNat ≤ d.sym_end.toNat) (memory : d.lit_bufsize.toNat ≤ 512) :
    ∃ (mb : Int32) (result : DeflateState),
      (do Zlib.Trees.Proofs.blPrepare (some (.tab ds)); Zlib.Trees.build_bl_tree (some (.tab ds))) h =
        .ok (mb,setD h ds result) ∧
      DGood (setD h ds result) r ds z result ∧ TreesInvAt (setD h ds result) ds result pb buf ∧
      StreamBuffers (setD h ds result) r ∧ ByteSizes h (setD h ds result) ∧
      OutputStorage h (setD h ds result) r ds pb ob ∧ SourceCodeFacts d result ∧
      mass (fun v => d.dyn_ltree[v]!.fc.toNat) 286 = xs.length+1 ∧
      mass (fun v => d.dyn_dtree[v]!.fc.toNat) 30 ≤ xs.length ∧
      mass (fun v => d.dyn_ltree[v]!.fc.toNat * (if v < 257 then 0 else 1)) 286 =
        mass (fun v => d.dyn_dtree[v]!.fc.toNat) 30 ∧ d.dyn_ltree[256]!.fc.toNat = 1 ∧
      (∀ a, a ≤ 24 → Zlib.Trees.Overlay.bitExcess (dynamicSymbolCosts result xs) ≤
        mass (fun v => d.dyn_ltree[v]!.fc.toNat *
          (if v < 257 then 0 else curL result.dyn_ltree v+sourceLiteralExtra (v-257)-a)) 286 +
        mass (fun v => d.dyn_dtree[v]!.fc.toNat *
          (curL result.dyn_dtree v+sourceDistanceExtra v-(24-a))) 30) ∧
      1000 * Zlib.Trees.Overlay.bitExcess (dynamicSymbolCosts result xs) ≤ 5315*(xs.length+3) := by
  obtain ⟨mb,result,run,goodA,treesA,buffersA,sizes,storage,_lower,_upper,_guards,_fields,_output,excess⟩ :=
    all_trees_small_excess_engine (ob := ob) good trees buffers ledger count (by omega)
  obtain ⟨otherMb,other,codeRun,codes⟩ := Zlib.Trees.Proofs.prepare_source_code_facts trees
  have same : other = result := Zlib.Trees.Proofs.same_record_of_runs codeRun run
  subst other
  have literalKeys : ∀ s ∈ xs, s.literalKey symbolLengthCode < 286 :=
    fun s member => valid_literal_key (ledger.valid s member)
  have distanceKeys : ∀ s ∈ xs, ∀ k, s.distanceKey dcodeN = some k → k < 30 :=
    fun s member _ selected => valid_distance_key (ledger.valid s member) selected
  have balance : mass (fun v => d.dyn_ltree[v]!.fc.toNat * (if v < 257 then 0 else 1)) 286 =
      mass (fun v => d.dyn_dtree[v]!.fc.toNat) 30 := by
    calc
      _ = mass (fun v => literalFrequency symbolLengthCode xs v * (if v < 257 then 0 else 1)) 286 :=
        mass_congr (fun v fit => by rw [ledger.literal v fit])
      _ = mass (distanceFrequency dcodeN xs) 30 :=
        match_frequency_balance symbolLengthCode dcodeN xs ledger.valid literalKeys distanceKeys
      _ = _ := (mass_congr ledger.distance).symm
  have marker : d.dyn_ltree[256]!.fc.toNat = 1 := by
    rw [ledger.literal 256 (by decide)]
    exact end_frequency symbolLengthCode xs ledger.valid
  have rows : ∀ a, a ≤ 24 → Zlib.Trees.Overlay.bitExcess (dynamicSymbolCosts result xs) ≤
      mass (fun v => d.dyn_ltree[v]!.fc.toNat *
        (if v < 257 then 0 else curL result.dyn_ltree v+sourceLiteralExtra (v-257)-a)) 286 +
      mass (fun v => d.dyn_dtree[v]!.fc.toNat *
        (curL result.dyn_dtree v+sourceDistanceExtra v-(24-a))) 30 := by
    intro a bound
    have literalBound : ∀ s ∈ xs, s.distance = 0 → curL result.dyn_ltree s.value ≤ 24 := by
      intro s member literal
      have key : s.literalKey symbolLengthCode = s.value := by simp only [Symbol.literalKey,literal,ite_true]
      have used := ledger.literal_used member
      rw [key] at used
      have value := (ledger.valid s member).2
      have fit := (codes.literal s.value (by omega) used).1
      change result.dyn_ltree[s.value]!.dl.toNat ≤ 15 at fit
      unfold curL
      omega
    have split := excess_split_family xs (curL result.dyn_ltree) (curL result.dyn_dtree)
      sourceLiteralExtra sourceDistanceExtra symbolLengthCode dcodeN ledger.valid literalKeys distanceKeys literalBound a bound
    have literalMass : mass (fun v => d.dyn_ltree[v]!.fc.toNat *
        (if v < 257 then 0 else curL result.dyn_ltree v+sourceLiteralExtra (v-257)-a)) 286 =
        mass (fun v => literalFrequency symbolLengthCode xs v *
          (if v < 257 then 0 else curL result.dyn_ltree v+sourceLiteralExtra (v-257)-a)) 286 :=
      mass_congr (fun v fit => by rw [ledger.literal v fit])
    have distanceMass : mass (fun v => d.dyn_dtree[v]!.fc.toNat *
        (curL result.dyn_dtree v+sourceDistanceExtra v-(24-a))) 30 =
        mass (fun v => distanceFrequency dcodeN xs v *
          (curL result.dyn_dtree v+sourceDistanceExtra v-(24-a))) 30 :=
      mass_congr (fun v fit => by rw [ledger.distance v fit])
    rw [literalMass,distanceMass]
    exact split
  exact ⟨mb,result,run,goodA,treesA,buffersA,sizes,storage,codes,ledger_literal_mass ledger,
    ledger_distance_mass ledger,balance,marker,rows,excess⟩

#print axioms actual_small_memory_base_rows
end Zlib.Deflate.Engine.Proofs.SmallMemory
