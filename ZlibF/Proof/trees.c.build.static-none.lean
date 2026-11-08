import ZlibF.Proof.«trees.c.build.static-initialized»

/-! # A constructor without a static table retains the static-cost counter -/

namespace Zlib.Trees.Proofs
open C Zlib.Trees
set_option autoImplicit false

theorem BTForceTrace.static_none {tk : TK} {k : Nat} {mc0 mc : Int32} {d result : DeflateState}
    (trace : BTForceTrace tk none k mc0 d mc result) : result.static_len = d.static_len := by
  induction trace with
  | nil => rfl
  | snoc node hl before hn hnT hm hhl ih =>
    simpa only [btForceState] using ih

theorem GBDone.static_none {tk : TK} {built result : DeflateState} {hm J maxc L : Nat}
    {extra : Nat → Nat} (done : GBDone tk built hm J maxc L extra none result) :
    result.static_len = built.static_len := by
  obtain ⟨T, B, O, S, fields, _treeSize, _countsSize, _freq, _outside, _lengths,
    _kraft, _counts, _opt, cost⟩ := done
  rw [fields]
  cases tk <;> exact cost

/-- Actual scan, dummy repair and heapify do not write the static cost
when the real descriptor has a null static-tree pointer. -/
theorem ws_btSortedStart_static_none {h0 : Heap} {id : Nat} {tk dk : TK} {d : DeflateState}
    {sref : StaticTreeDescRef} {dd : TreeDesc} {sd : StaticTreeDesc}
    (hdd : (dk.descRef id).get (setD h0 id d) = some dd) (hsd : StaticTreeDescRef.get h0 sref = some sd)
    (hstat : dd.stat_desc = some sref) (htree : dd.dyn_tree = .ref (tk.ref id) 0)
    (he3 : 3 ≤ sd.elems.toInt) (he286 : sd.elems.toInt ≤ 286)
    (hT : sd.elems.toInt ≤ (tk.arr d).size) (hD : sd.elems.toInt ≤ d.depth.size) (hH : d.heap.size = 573)
    (null : sd.static_tree = .null) :
    WS h0 id (btSortedStart (Sp id) (some (dk.descRef id))) d
      (fun _ result => result.static_len = d.static_len) := by
  unfold btSortedStart
  refine WS.bind' (ws_btLeavesStart hdd hsd hstat htree he3 he286 hT hD hH (Or.inl ⟨null, rfl⟩)) ?_
  intro a mid ⟨tree, statree, elems, leaf, scanned, scanMc, k, scan, _len, _kBound, _count, trace⟩
  rcases a with ⟨pointer, staticPointer, count, maximum⟩
  dsimp only at tree statree elems leaf trace ⊢
  subst pointer
  subst staticPointer
  subst count
  have cost : mid.static_len = d.static_len := trace.static_none.trans scan.static_len
  refine WS.bind' (ws_btOrder_leaf tk dk mid sd.elems.toInt.toNat maximum leaf)
    fun _ result ⟨_leaf, H, fields, _rest⟩ => ?_
  refine WS.pure' ?_
  rw [fields]
  cases dk <;> exact cost

/-- The complete actual heap construction retains the same counter. -/
theorem ws_btHeap_static_none {h0 : Heap} {id : Nat} {tk dk : TK} {d : DeflateState}
    {sref : StaticTreeDescRef} {dd : TreeDesc} {sd : StaticTreeDesc}
    (hdd : (dk.descRef id).get (setD h0 id d) = some dd) (hsd : StaticTreeDescRef.get h0 sref = some sd)
    (hstat : dd.stat_desc = some sref) (htree : dd.dyn_tree = .ref (tk.ref id) 0)
    (he3 : 3 ≤ sd.elems.toInt) (he286 : sd.elems.toInt ≤ 286)
    (hT : 2 * sd.elems.toInt.toNat - 1 ≤ (tk.arr d).size)
    (hD : 2 * sd.elems.toInt.toNat - 1 ≤ d.depth.size) (hH : d.heap.size = 573)
    (null : sd.static_tree = .null) :
    WS h0 id (btHeap (Sp id) (some (dk.descRef id))) d
      (fun _ result => result.static_len = d.static_len) := by
  have capacity : sd.elems.toInt ≤ (tk.arr d).size := by omega
  have depth : sd.elems.toInt ≤ d.depth.size := by omega
  have static : BTStatic h0 id sd.static_tree sd.elems.toInt.toNat none := Or.inl ⟨null, rfl⟩
  unfold btHeap btMergedStart
  simp only [M_bind_assoc, M_pure_bind]
  refine WS.bind' (merge_ws_and (merge_ws_and
    (ws_btSortedStart hdd hsd hstat htree he3 he286 capacity depth hH static)
    (ws_btSortedStart_sizes hdd hsd hstat htree he3 he286 capacity depth hH static))
    (ws_btSortedStart_static_none hdd hsd hstat htree he3 he286 capacity depth hH null)) ?_
  intro a prepared ⟨⟨⟨pointer, statree, elems, leaf, two, maximum, descriptor, ordered, _minimum⟩,
    treeSize, depthSize⟩, cost⟩
  rcases a with ⟨treePointer, staticPointer, count, mc⟩
  dsimp only at pointer statree elems leaf descriptor ⊢
  subst treePointer
  subst staticPointer
  subst count
  have leafCount := leaf.count
  have countBound := Math.scanCount_le (btFreq tk prepared) sd.elems.toInt.toNat
  have forest := BTForest.of_leaf leaf two maximum (node := sd.elems) (by omega)
    (by rw [treeSize]; omega) (by rw [depthSize]; omega) ordered
  refine WS.bind' (ws_btMergeLoop_forest forest) fun next merged ⟨forestM, frameM, _lengthM⟩ => ?_
  refine WS.bind' (ws_btSaveRoot_forest forestM frameM) fun _ built tree => ?_
  exact WS.pure' (tree.frame.static_len.trans cost)

/-- No static-cost update is hidden in gen_bitlen or canonical-code
writes when construction uses the absent static table. -/
theorem ws_build_tree_static_none {h0 : Heap} {id : Nat} {tk dk : TK} {d : DeflateState}
    {sref : StaticTreeDescRef} {dd : TreeDesc} {sd : StaticTreeDesc} {extra : Nat → Nat}
    (hdd : (dk.descRef id).get (setD h0 id d) = some dd) (hsd : StaticTreeDescRef.get h0 sref = some sd)
    (hstat : dd.stat_desc = some sref) (htree : dd.dyn_tree = .ref (tk.ref id) 0)
    (he3 : 3 ≤ sd.elems.toInt) (he286 : sd.elems.toInt ≤ 286)
    (hT : 2 * sd.elems.toInt.toNat - 1 ≤ (tk.arr d).size) (hTbig : (tk.arr d).size ≤ 600)
    (hD : 2 * sd.elems.toInt.toNat - 1 ≤ d.depth.size) (hH : d.heap.size = 573) (hB : d.bl_count.size = 16)
    (tables : BTBuildStatic h0 id sd extra none) (null : sd.static_tree = .null) :
    WS h0 id (build_tree (Sp id) (some (dk.descRef id))) d
      (fun _ result => result.static_len = d.static_len) := by
  rw [build_tree_eq_heap_codes]
  refine WS.bind' (merge_ws_and
    (ws_btHeap_built hdd hsd hstat htree he3 he286 hT hTbig hD hH hB (Or.inl ⟨null, rfl⟩))
    (ws_btHeap_static_none hdd hsd hstat htree he3 he286 hT hD hH null)) ?_
  intro a built ⟨⟨pointer, prepared, K, tree, descriptor, counts, size⟩, counter⟩
  rcases a with ⟨treePointer, mc⟩
  dsimp only at pointer tree descriptor ⊢
  subst treePointer
  have context := tree.bitlen_ctx tables rfl counts size
  refine WS.mono (ws_btCodes (h0 := h0) (id := id) (tk := tk) (d := built)
    (r := dk.descRef id) (sref := sref) (dd := { dd with max_code := mc }) (sd := sd)
    (hm := 574 - 2 * K) (J := K - 1) (elems := sd.elems.toInt.toNat) (maxc := mc.toInt.toNat)
    (L := sd.max_length.toInt.toNat) (baseN := sd.extra_base.toInt.toNat) (xb := extra) (slOpt := none)
    descriptor hsd hstat htree context tree.heap_max tables.length_capacity (by omega) tree.unused) ?_
  intro _ result ⟨mid, done, a, fields, _size, _values⟩
  rw [fields]
  have cost := done.static_none.trans counter
  cases tk <;> exact cost

/-- The installed bit-length descriptor supplies the null-static case. -/
theorem ws_build_bl_initialized_static_none {h0 : Heap} {id : Nat} {d : DeflateState}
    (hwf : d.WellFormed) (hs : Out.TreesStatic h0.static) (hr : Out.TreesRun0 id d) :
    WS h0 id (build_tree (Sp id) (some (TK.bl.descRef id))) d
      (fun _ result => result.static_len = d.static_len) := by
  obtain ⟨hLT, hDT, hBT, hBC, hH, hD⟩ := hwf
  exact ws_build_tree_static_none (tk := .bl) (bt_desc_get .bl h0 id d) (trees_build_desc_get hs .bl)
    hr.blstat hr.bldyn (by decide +kernel) (by decide +kernel)
    (by change 37 ≤ d.bl_tree.size; omega) (by change d.bl_tree.size ≤ 600; omega)
    (by change 37 ≤ d.depth.size; omega) hH hBC (trees_build_static hs .bl) rfl

end Zlib.Trees.Proofs
