import ZlibF.Proof.«trees.c.build.small-memory-codes»
import ZlibF.Proof.«trees.c.build.fib-origins»

namespace Zlib.Trees.Proofs
open C Zlib.Trees Zlib.Trees.Proofs.GB
open ZlibF.Math.DeflateSymbols (mass)
set_option autoImplicit false

/-- The complete actual constructor retains original symbol origins and
direct Fibonacci bounds for small original leaf mass. Dummy-leaf freshness and frequency preservation are derived from
actual short-queue repair and merging. Fifteen-bit length repair is excluded
by the derived small root weight. No callee contract is assumed. -/
theorem ws_build_tree_small_direct_fib_origins {h0 : Heap} {id : Nat} {tk dk : TK} {d : DeflateState}
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
      (fun _ result => ∃ (prepared built : DeflateState) (mc : Int32) (K : Nat),
      BTBuilt tk sd.elems.toInt.toNat K mc prepared built ∧
      frn (tk.arr built) (Hn built (574 - 2 * K)) ≤
        mass (fun v => (btFreq tk d v).toNat) sd.elems.toInt.toNat + 2 ∧
      (∀ v, v < sd.elems.toInt.toNat → btFreq tk d v ≠ 0 → btFreq tk built v = btFreq tk d v) ∧
      (∀ v, v < sd.elems.toInt.toNat → btFreq tk d v ≠ 0 → v ≤ mc.toInt.toNat ∧
        ∃ q, 574 - 2 * K < q ∧ q < 573 ∧ Hn built q = v) ∧
      ∀ rank, 1 ≤ rank →
        rank ≤ LeafRank.count (Hn built) (574 - 2 * K) (K - 1) mc.toInt.toNat →
        LeafRank.value (Hn built) (frn (tk.arr built)) (574 - 2 * K) (K - 1) mc.toInt.toNat rank *
          HuffmanAbstract.fib (LeafRank.value (Hn built) (curL (tk.arr result))
            (574 - 2 * K) (K - 1) mc.toInt.toNat rank + 1) ≤
              frn (tk.arr built) (Hn built (574 - 2 * K))) := by
  obtain ⟨sl, repair⟩ := hs.repair
  rw [build_tree_eq_heap_codes]
  refine WS.bind' (merge_ws_and
    (ws_btHeap_trace hdd hsd hstat htree he3 he286 hT hD hH repair budget)
    (ws_btHeap_frequencies hdd hsd hstat htree he3 he286 hT hTbig hD hH hB repair)) ?_
  intro a built ⟨⟨ptr, weight, prepared, K, builtData, values, order, leaves⟩,
    _ptr, _prepared, otherK, otherBuilt, descriptor, counts, treeSize, frequencies, supported⟩
  rcases a with ⟨tree, mc⟩
  dsimp only at ptr builtData descriptor ⊢
  subst tree
  have sameK : otherK = K := by
    have firstMax := builtData.heap_max
    have secondMax := otherBuilt.heap_max
    have firstBound : K ≤ 286 := Nat.le_trans builtData.kN builtData.n286
    have secondBound : otherK ≤ 286 := Nat.le_trans otherBuilt.kN otherBuilt.n286
    omega
  rw [sameK] at supported
  have context := builtData.bitlen_ctx hs rfl counts treeSize
  have sums : ∀ a, a < K - 1 → frn (tk.arr built) (sd.elems.toInt.toNat + a) =
      frn (tk.arr built) (Hn built (572 - 2 * a)) + frn (tk.arr built) (Hn built (571 - 2 * a)) :=
    values.sum
  have positive := tree_weights_positive builtData.shape (frn (tk.arr built)) leaves.positive sums
  have k2 := builtData.k2
  have kN := builtData.kN
  have n286 := builtData.n286
  have ordered : ∀ q q', 574 - 2 * K + 1 ≤ q' → q' ≤ q → q < 573 →
      frn (tk.arr built) (Hn built q) ≤ frn (tk.arr built) (Hn built q') := by
    intro q q' lower between upper
    exact order.monotone (q := q') (q' := q) (by omega) between upper
  have rootBound : frn (tk.arr built) (Hn built (574 - 2 * K)) ≤
      mass (fun v => (btFreq tk d v).toNat) sd.elems.toInt.toNat + 2 := by
    have index : built.heap_max.toInt.toNat = 574 - 2 * K := by have := builtData.heap_max; omega
    rw [index] at weight
    exact weight
  have code := ws_btCodes_small_direct_fib (h0 := h0) (id := id) (tk := tk) (d := built)
    (r := dk.descRef id) (sref := sref) (dd := { dd with max_code := mc }) (sd := sd)
    (hm := 574 - 2 * K) (J := K - 1) (elems := sd.elems.toInt.toNat) (maxc := mc.toInt.toNat)
    (L := sd.max_length.toInt.toNat) (baseN := sd.extra_base.toInt.toNat) (xb := xb) (slOpt := slOpt)
    descriptor hsd hstat htree context builtData.heap_max hs.length_capacity (by omega) builtData.unused
    limit sums ordered (fun q lo hi => positive q (by omega) hi) (by omega)
  refine WS.mono code ?_
  intro _ result ⟨mid, _done, _stage, _codes, fib⟩
  refine ⟨prepared, built, mc, K, builtData, ?_, frequencies, supported, fib⟩
  have index : built.heap_max.toInt.toNat = 574 - 2 * K := by have := builtData.heap_max; omega
  rw [index] at weight
  exact weight


end Zlib.Trees.Proofs

#print axioms Zlib.Trees.Proofs.ws_build_tree_small_direct_fib_origins
