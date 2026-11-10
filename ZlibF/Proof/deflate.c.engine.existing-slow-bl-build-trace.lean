import ZlibF.Proof.«deflate.c.engine.existing-slow-bl-codes-trace»
import ZlibF.Proof.«trees.c.build.fib-origins»
namespace Zlib.Trees.Proofs
open C Zlib.Trees Zlib.Trees.Proofs.GB
open ZlibF.Math.DeflateSymbols (mass)
set_option autoImplicit false
/-- The complete actual maximum-seven source constructor retains its
pre-code natural frequencies, parent sums, removal order and exact repaired
rank lengths on the final returned heap. No quantitative overflow bound is
assumed. The original frequency/code union is kept separate from final codes. -/
theorem ws_build_tree_bl_rank_trace {h0 : Heap} {id : Nat} {tk dk : TK} {d : DeflateState}
    {sref : StaticTreeDescRef} {dd : TreeDesc} {sd : StaticTreeDesc}
    {xb : Nat → Nat} {slOpt : Option (Nat → Nat)}
    (hdd : (dk.descRef id).get (setD h0 id d) = some dd)
    (hsd : StaticTreeDescRef.get h0 sref = some sd)
    (hstat : dd.stat_desc = some sref) (htree : dd.dyn_tree = .ref (tk.ref id) 0)
    (he3 : 3 ≤ sd.elems.toInt) (he286 : sd.elems.toInt ≤ 286)
    (hT : 2 * sd.elems.toInt.toNat - 1 ≤ (tk.arr d).size) (hTbig : (tk.arr d).size ≤ 600)
    (hD : 2 * sd.elems.toInt.toNat - 1 ≤ d.depth.size)
    (hH : d.heap.size = 573) (hB : d.bl_count.size = 16)
    (hs : BTBuildStatic h0 id sd xb slOpt) (limit : sd.max_length.toInt.toNat = 7)
    (budget : mass (fun v => (btFreq tk d v).toNat) sd.elems.toInt.toNat + 2 < 2 ^ 16) :
    WS h0 id (build_tree (Sp id) (some (dk.descRef id))) d
      (fun _ result => ∃ (prepared built : DeflateState) (mc : Int32) (K : Nat),
        BTBuilt tk sd.elems.toInt.toNat K mc prepared built ∧
        frn (tk.arr built) (Hn built (574-2*K)) ≤
          mass (fun v => (btFreq tk d v).toNat) sd.elems.toInt.toNat + 2 ∧
        (∀ v, v < sd.elems.toInt.toNat → btFreq tk d v ≠ 0 → btFreq tk built v = btFreq tk d v) ∧
        BTMergeValues tk sd.elems.toInt.toNat (K-1) built ∧ BTMergeOrder tk K (K-1) built ∧
        BLRepairRanks tk built (574-2*K) (K-1) sd.elems.toInt.toNat mc.toInt.toNat result) := by
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
  have code := ws_btCodes_bl_rank_trace (h0 := h0) (id := id) (tk := tk) (d := built)
    (r := dk.descRef id) (sref := sref) (dd := { dd with max_code := mc }) (sd := sd)
    (hm := 574 - 2 * K) (J := K - 1) (elems := sd.elems.toInt.toNat) (maxc := mc.toInt.toNat)
    (L := sd.max_length.toInt.toNat) (baseN := sd.extra_base.toInt.toNat) (xb := xb) (slOpt := slOpt)
    descriptor hsd hstat htree context builtData.heap_max hs.length_capacity (by omega) builtData.unused
    limit
  refine WS.mono code ?_
  intro _ result ⟨mid, _done, _stage, _codes, ranks⟩
  refine ⟨prepared, built, mc, K, builtData, ?_, frequencies, values, order, ranks⟩
  have index : built.heap_max.toInt.toNat = 574 - 2 * K := by have := builtData.heap_max; omega
  rw [index] at weight
  exact weight


#print axioms ws_build_tree_bl_rank_trace
end Zlib.Trees.Proofs
