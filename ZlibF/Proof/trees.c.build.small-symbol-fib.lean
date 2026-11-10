import ZlibF.Proof.«trees.c.build.small-memory-producer»
import ZlibF.Math.DeflateSymbolFibPush

namespace ZlibF.Math.DeflatePush
open Zlib.Trees.Proofs.GB
open Zlib.Trees.HuffmanAbstract
set_option autoImplicit false

/-- Retained source leaf ranks transport a direct Fibonacci inequality
back to every original used symbol, preserving its exact frequency. -/
theorem direct_symbol_fib_of_ranked_tree {H treeFrequency frequency length : Nat → Nat}
    {hm J alphabet maxc weight : Nat} (shape : PShape H hm J alphabet maxc)
    (used : ∀ v, v < alphabet → frequency v ≠ 0 → v ≤ maxc ∧ ∃ q, hm < q ∧ q < 573 ∧ H q = v)
    (frequencies : ∀ v, v < alphabet → frequency v ≠ 0 → treeFrequency v = frequency v)
    (ranked : ∀ rank, 1 ≤ rank → rank ≤ LeafRank.count H hm J maxc →
      LeafRank.value H treeFrequency hm J maxc rank *
        fib (LeafRank.value H length hm J maxc rank + 1) ≤ weight) :
    ∀ v, v < alphabet → frequency v ≠ 0 → frequency v * fib (length v + 1) ≤ weight := by
  let ranks := LeafRank.count H hm J maxc
  let rank := fun v => cntL (LeafRank.selected H hm maxc) (nodePosition H hm J v + 1)
  have boundary := shape.hm_eq
  have rankSpec (v : Nat) (bound : v < alphabet) (nonzero : frequency v ≠ 0) :
      1 ≤ rank v ∧ rank v ≤ ranks ∧ H (hm + 1 + LeafRank.index H hm J maxc (rank v)) = v := by
    obtain ⟨symbol, q, lower, upper, value⟩ := used v bound nonzero
    have found : ∃ i, i < 2 * J ∧ H (hm + 1 + i) = v :=
      ⟨q - hm - 1, by omega, by rw [show hm + 1 + (q - hm - 1) = q by omega]; exact value⟩
    have position := nodePosition_spec found
    have selected : LeafRank.selected H hm maxc (nodePosition H hm J v) = true := by
      simp only [LeafRank.selected, position.2, symbol, decide_true]
    have bounds := rank_bounds (LeafRank.selected H hm maxc) position.1 selected
    have inverse := idxR_rank (LeafRank.selected H hm maxc) position.1 selected
    refine ⟨bounds.1, bounds.2, ?_⟩
    change H (hm + 1 + idxR (LeafRank.selected H hm maxc) (2 * J) (rank v)) = v
    rw [inverse, position.2]
  intro v bound nonzero
  obtain ⟨lower, upper, node⟩ := rankSpec v bound nonzero
  have claim := ranked (rank v) lower upper
  unfold LeafRank.value at claim
  rw [node, frequencies v bound nonzero] at claim
  exact claim

end ZlibF.Math.DeflatePush

namespace Zlib.Trees.Proofs
open C Zlib.Trees Zlib.Trees.Proofs.GB
open ZlibF.Math.DeflateSymbols (mass)
set_option autoImplicit false

/-- The whole actual small-mass source constructor establishes direct
Fibonacci bounds for original symbol frequencies and final stored lengths.
It includes real heap construction, dummy repair, gen_bitlen and code
assignment. No length-repair contract or frequency contract is assumed. -/
theorem ws_build_tree_small_direct_symbol_fib {h0 : Heap} {id : Nat} {tk dk : TK} {d : DeflateState}
    {sref : StaticTreeDescRef} {dd : TreeDesc} {sd : StaticTreeDesc}
    {xb : Nat → Nat} {slOpt : Option (Nat → Nat)}
    (hdd : (dk.descRef id).get (setD h0 id d) = some dd)
    (hsd : StaticTreeDescRef.get h0 sref = some sd)
    (hstat : dd.stat_desc = some sref) (htree : dd.dyn_tree = .ref (tk.ref id) 0)
    (he3 : 3 ≤ sd.elems.toInt) (he286 : sd.elems.toInt ≤ 286)
    (hT : 2 * sd.elems.toInt.toNat - 1 ≤ (tk.arr d).size) (hTbig : (tk.arr d).size ≤ 600)
    (hD : 2 * sd.elems.toInt.toNat - 1 ≤ d.depth.size)
    (hH : d.heap.size = 573) (hB : d.bl_count.size = 16)
    (hs : BTBuildStatic h0 id sd xb slOpt) (limit : sd.max_length.toInt.toNat = 15)
    (budget : mass (fun v => (btFreq tk d v).toNat) sd.elems.toInt.toNat + 2 < 2 ^ 16)
    (smallMass : mass (fun v => (btFreq tk d v).toNat) sd.elems.toInt.toNat ≤ 1024) :
    WS h0 id (build_tree (Sp id) (some (dk.descRef id))) d
      (fun _ result => ∃ weight,
        weight ≤ mass (fun v => (btFreq tk d v).toNat) sd.elems.toInt.toNat + 2 ∧
        ∀ v, v < sd.elems.toInt.toNat → btFreq tk d v ≠ 0 →
          (btFreq tk d v).toNat * HuffmanAbstract.fib (curL (tk.arr result) v + 1) ≤ weight) := by
  refine WS.mono (ws_build_tree_small_direct_fib_origins hdd hsd hstat htree he3 he286 hT hTbig hD hH hB hs limit budget smallMass) ?_
  intro _ result ⟨prepared, built, mc, K, tree, weight, frequencies, used, fib⟩
  refine ⟨frn (tk.arr built) (Hn built (574 - 2 * K)), weight, ?_⟩
  have point := ZlibF.Math.DeflatePush.direct_symbol_fib_of_ranked_tree tree.shape
    (frequency := fun v => (btFreq tk d v).toNat)
    (treeFrequency := frn (tk.arr built)) (length := curL (tk.arr result))
    (by
      intro v bound nonzero
      have wordNonzero : btFreq tk d v ≠ 0 := by
        intro zero
        apply nonzero
        rw [zero]
        rfl
      exact used v bound wordNonzero)
    (by
      intro v bound nonzero
      have wordNonzero : btFreq tk d v ≠ 0 := by
        intro zero
        apply nonzero
        rw [zero]
        rfl
      change (btFreq tk built v).toNat = (btFreq tk d v).toNat
      rw [frequencies v bound wordNonzero]) fib
  intro v bound nonzero
  apply point v bound
  intro zero
  apply nonzero
  exact UInt16.toNat_inj.mp zero

end Zlib.Trees.Proofs

#print axioms ZlibF.Math.DeflatePush.direct_symbol_fib_of_ranked_tree
#print axioms Zlib.Trees.Proofs.ws_build_tree_small_direct_symbol_fib
