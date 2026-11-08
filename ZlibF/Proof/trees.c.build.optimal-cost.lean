import ZlibF.Proof.«trees.c.build.optimal-inputs»

/-! # The real complete constructor adds the original dynamic leaf cost -/

namespace Zlib.Trees.Proofs
open C Zlib.Trees
set_option autoImplicit false

/-- `local void build_tree(deflate_state *s, tree_desc *desc)`.
Actual leaf scanning, dummy repair, heap construction, bit-length generation,
overflow repair and canonical stores add exactly the original-frequency
dynamic cost. Dummy contributions cancel the actual unsigned decrements.
All code-length premises come from the same translated constructor run. -/
theorem ws_build_tree_optimal_cost {h0 : Heap} {id : Nat} {tk dk : TK} {d : DeflateState}
    {sref : StaticTreeDescRef} {dd : TreeDesc} {sd : StaticTreeDesc}
    {extra : Nat → Nat} {slOpt : Option (Nat → Nat)}
    (hdd : (dk.descRef id).get (setD h0 id d) = some dd) (hsd : StaticTreeDescRef.get h0 sref = some sd)
    (hstat : dd.stat_desc = some sref) (htree : dd.dyn_tree = .ref (tk.ref id) 0)
    (he3 : 3 ≤ sd.elems.toInt) (he286 : sd.elems.toInt ≤ 286)
    (hT : 2 * sd.elems.toInt.toNat - 1 ≤ (tk.arr d).size) (hTbig : (tk.arr d).size ≤ 600)
    (hD : 2 * sd.elems.toInt.toNat - 1 ≤ d.depth.size) (hH : d.heap.size = 573) (hB : d.bl_count.size = 16)
    (tables : BTBuildStatic h0 id sd extra slOpt) (dummy : ∀ v, v ≤ 2 → extra v = 0) :
    WS h0 id (build_tree (Sp id) (some (dk.descRef id))) d (fun _ result =>
      result.opt_len = d.opt_len + UInt64.ofNat
        (btLeafCost tk sd.elems.toInt.toNat (fun v => curL (tk.arr result) v + extra v) d)) := by
  obtain ⟨sl, repair⟩ := tables.repair
  rw [build_tree_eq_heap_codes]
  refine WS.bind' (merge_ws_and
    (ws_btHeap_optimal_cost hdd hsd hstat htree he3 he286 hT hTbig hD hH hB repair)
    (merge_ws_and
      (ws_btHeap_complete_leaves hdd hsd hstat htree he3 he286 hT hD hH repair)
      (ws_btHeap_upper_zero hdd hsd hstat htree he3 he286 hT hD hH repair))) ?_
  intro a built ⟨⟨pointer, prepared, K, tree, descriptor, counts, size, balance⟩,
    ⟨usedBound, usedSeen⟩, above⟩
  rcases a with ⟨treePointer, mc⟩
  dsimp only at pointer tree descriptor usedBound usedSeen above balance ⊢
  subst treePointer
  have context := tree.bitlen_ctx tables rfl counts size
  have codes := ws_btCodes (h0 := h0) (id := id) (tk := tk) (d := built)
    (r := dk.descRef id) (sref := sref) (dd := { dd with max_code := mc }) (sd := sd)
    (hm := 574 - 2 * K) (J := K - 1) (elems := sd.elems.toInt.toNat) (maxc := mc.toInt.toNat)
    (L := sd.max_length.toInt.toNat) (baseN := sd.extra_base.toInt.toNat) (xb := extra) (slOpt := slOpt)
    descriptor hsd hstat htree context tree.heap_max tables.length_capacity (by omega) tree.unused
  refine WS.mono codes ?_
  intro _ result ⟨mid, done, a, fields, arraySize, stores⟩
  have seen : ∀ v, v < sd.elems.toInt.toNat → ((btFreq tk built v).toNat ≠ 0 ↔
      ∃ q, 574 - 2 * K < q ∧ q < 573 ∧ Hn built q = v) := by
    simpa only [tree.heap_max, Int.toNat_natCast] using usedSeen
  obtain ⟨lengthBound, used, kraft⟩ :=
    done.optimal_cost_inputs tree.shape tree.unused above usedBound seen
  have balanced := balance (curL (tk.arr mid)) extra sd.max_length.toInt.toNat
    lengthBound used kraft dummy
  have middle : mid.opt_len = d.opt_len + UInt64.ofNat
      (btLeafCost tk sd.elems.toInt.toNat (fun v => curL (tk.arr mid) v + extra v) d) :=
    done.opt_len.trans balanced
  have counter : result.opt_len = mid.opt_len := by rw [fields]; cases tk <;> rfl
  have lengths := code_stores_lengths fields arraySize stores
  have cost : btLeafCost tk sd.elems.toInt.toNat (fun v => curL (tk.arr result) v + extra v) d =
      btLeafCost tk sd.elems.toInt.toNat (fun v => curL (tk.arr mid) v + extra v) d := by
    apply ZlibF.Math.DeflateSymbols.mass_congr
    intro v _fit
    simp only [curL, lengths v]
  rw [counter, cost]
  exact middle

end Zlib.Trees.Proofs
