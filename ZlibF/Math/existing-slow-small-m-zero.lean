import ZlibF.Proof.«deflate.c.engine.existing-slow-small-actual-rows»

namespace ZlibF.Math.SmallMemoryRows
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- M0 has no original length-code or distance-code columns. The actual
constructor still creates its two phantom distance codes; this theorem
makes no claim that the final distance array is empty. -/
theorem literal_only_histograms (lc dc : Nat → Nat) (xs : List Symbol)
    (valid : ∀ s ∈ xs, s.Valid) (literal : ∀ s ∈ xs, s.distance = 0) :
    (∀ v, distanceFrequency dc xs v = 0) ∧
      (∀ v, 257 ≤ v → literalFrequency lc xs v = 0) := by
  have distance : ∀ v, countKey (Symbol.distanceKey dc) xs v = 0 := by
    induction xs with
    | nil => intro v; rfl
    | cons s xs ih =>
      intro v
      have first := literal s (by simp)
      have rest := ih (fun t member => valid t (by simp [member])) (fun t member => literal t (by simp [member])) v
      simp only [countKey,Symbol.distanceKey,first,ite_true,reduceCtorEq,ite_false,Nat.zero_add,rest]
  have lengths : ∀ v, 257 ≤ v → countKey (fun s => some (s.literalKey lc)) xs v = 0 := by
    clear distance
    induction xs with
    | nil => intro v _; rfl
    | cons s xs ih =>
      intro v bound
      have first := literal s (by simp)
      have value := (valid s (by simp)).2
      have rest := ih (fun t member => valid t (by simp [member])) (fun t member => literal t (by simp [member])) v bound
      have different : s.literalKey lc ≠ v := by simp only [Symbol.literalKey,first,ite_true]; omega
      simp only [countKey,Option.some.injEq,different,ite_false,Nat.zero_add,rest]
  refine ⟨distance,?_⟩
  intro v bound
  have notEnd : v ≠ 256 := by omega
  simp only [literalFrequency,notEnd,ite_false,lengths v bound,Nat.zero_add]

#print axioms literal_only_histograms
end ZlibF.Math.SmallMemoryRows

namespace Zlib.Deflate.Engine.Proofs.SmallMemory
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs
open Zlib.Trees.Proofs (curL SourceCodeFacts)
open Zlib.Trees.Proofs.Out (TreesInvAt dcodeN)
open ZlibF.Math.DeflateSymbols ZlibF.Math.DeflatePush ZlibF.Math.SmallMemoryRows
set_option autoImplicit false

/-- Actual M0 source/BL construction yields rowExc0 and excludes original
length/distance columns. The all-zero original distance histogram is this
internal case's definition, not a restriction on the public caller domain.
Phantom codes in the final constructor/RLE header remain separate data. -/
theorem actual_mzero_rows {h : Heap} {r : ZStreamRef} {ds pb ob : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (ledger : SymbolLedger buf d xs)
    (count : d.sym_next.toNat ≤ d.sym_end.toNat) (memory : d.lit_bufsize.toNat ≤ 512)
    (noDistance : ∀ v, v < 30 → d.dyn_dtree[v]!.fc = 0) :
    ∃ (mb : Int32) (result : DeflateState),
      (do Zlib.Trees.Proofs.blPrepare (some (.tab ds)); Zlib.Trees.build_bl_tree (some (.tab ds))) h =
        .ok (mb,setD h ds result) ∧
      DGood (setD h ds result) r ds z result ∧ TreesInvAt (setD h ds result) ds result pb buf ∧
      StreamBuffers (setD h ds result) r ∧ ByteSizes h (setD h ds result) ∧
      OutputStorage h (setD h ds result) r ds pb ob ∧ SourceCodeFacts d result ∧
      (∀ s ∈ xs, s.distance = 0) ∧
      (∀ v, v < 30 → d.dyn_dtree[v]!.fc.toNat = 0) ∧
      (∀ v, 257 ≤ v → v < 286 → d.dyn_ltree[v]!.fc.toNat = 0) ∧
      Zlib.Trees.Overlay.bitExcess (dynamicSymbolCosts result xs) = 0 := by
  obtain ⟨mb,result,run,goodA,treesA,buffersA,sizes,storage,codes,_literalMass,_distanceMass,
    _balance,_marker,_rows,_excess⟩ := actual_small_memory_base_rows (ob := ob) good trees buffers ledger count memory
  have literalOnly : ∀ s ∈ xs, s.distance = 0 := by
    intro s member
    by_cases zero : s.distance = 0
    · exact zero
    · have selected : s.distanceKey dcodeN = some (dcodeN (s.distance-1)) := by
        simp only [Symbol.distanceKey,zero,ite_false]
      have fit := valid_distance_key (ledger.valid s member) selected
      have positive := ledger.distance_used member zero
      rw [noDistance _ fit] at positive
      contradiction
  have hist := literal_only_histograms symbolLengthCode dcodeN xs ledger.valid literalOnly
  have noLengths : ∀ v, 257 ≤ v → v < 286 → d.dyn_ltree[v]!.fc.toNat = 0 := by
    intro v lower upper
    rw [ledger.literal v upper]
    exact hist.2 v lower
  have zeroTerms : xs.map (fun s => symbolCost (curL result.dyn_ltree) (curL result.dyn_dtree)
      sourceLiteralExtra sourceDistanceExtra symbolLengthCode dcodeN s - 24) = xs.map (fun _ => 0) := by
    apply List.map_congr_left
    intro s member
    have literal := literalOnly s member
    have key : s.literalKey symbolLengthCode = s.value := by simp only [Symbol.literalKey,literal,ite_true]
    have used := ledger.literal_used member
    rw [key] at used
    have value := (ledger.valid s member).2
    have fit := (codes.literal s.value (by omega) used).1
    change curL result.dyn_ltree s.value ≤ 15 at fit
    simp only [symbolCost,literal,ite_true]
    omega
  have excessZero : Zlib.Trees.Overlay.bitExcess (dynamicSymbolCosts result xs) = 0 := by
    unfold dynamicSymbolCosts Zlib.Trees.Overlay.bitExcess
    rw [List.map_map]
    change (xs.map (fun s => symbolCost (curL result.dyn_ltree) (curL result.dyn_dtree)
      sourceLiteralExtra sourceDistanceExtra symbolLengthCode dcodeN s - 24)).sum = 0
    rw [zeroTerms]
    have zeroSum (ys : List Symbol) : (ys.map (fun _ => (0 : Nat))).sum = 0 := by
      induction ys with
      | nil => rfl
      | cons s ys ih => simp only [List.map_cons,List.sum_cons,ih,Nat.zero_add]
    exact zeroSum xs
  exact ⟨mb,result,run,goodA,treesA,buffersA,sizes,storage,codes,literalOnly,
    (fun v fit => by rw [noDistance v fit]; rfl),noLengths,excessZero⟩

#print axioms actual_mzero_rows
end Zlib.Deflate.Engine.Proofs.SmallMemory
