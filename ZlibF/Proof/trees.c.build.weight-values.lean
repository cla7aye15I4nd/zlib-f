import ZlibF.Proof.«trees.c.build.weight-heap»
import ZlibF.Proof.«trees.c.build.values»
import ZlibF.Proof.«trees.c.build.removal-order»
import ZlibF.Proof.«trees.c.build.leaf-values»

/-! # The complete actual heap prefix retains its parent-value equations -/

namespace Zlib.Trees.Proofs
open C Zlib.Trees
open ZlibF.Math.DeflateSymbols (mass)
set_option autoImplicit false

/-- Natural parent sums and modular depths survive the entire actual heap
prefix, together with its built layout and leaf-derived root budget. -/
theorem ws_btHeap_values {h0 : Heap} {id : Nat} {tk dk : TK} {d : DeflateState}
    {sref : StaticTreeDescRef} {dd : TreeDesc} {sd : StaticTreeDesc} {sl : Option (Nat → UInt16)}
    (hdd : (dk.descRef id).get (setD h0 id d) = some dd)
    (hsd : StaticTreeDescRef.get h0 sref = some sd)
    (hstat : dd.stat_desc = some sref) (htree : dd.dyn_tree = .ref (tk.ref id) 0)
    (he3 : 3 ≤ sd.elems.toInt) (he286 : sd.elems.toInt ≤ 286)
    (hT : 2 * sd.elems.toInt.toNat - 1 ≤ (tk.arr d).size)
    (hD : 2 * sd.elems.toInt.toNat - 1 ≤ d.depth.size)
    (hH : d.heap.size = 573) (hs : BTStatic h0 id sd.static_tree sd.elems.toInt.toNat sl)
    (budget : mass (fun v => (btFreq tk d v).toNat) sd.elems.toInt.toNat + 2 < 2 ^ 16) :
    WS h0 id (btHeap (Sp id) (some (dk.descRef id))) d (fun a e =>
      a.1 = .ref (tk.ref id) 0 ∧
      (btFreq tk e (Hn e e.heap_max.toInt.toNat)).toNat ≤
        mass (fun v => (btFreq tk d v).toNat) sd.elems.toInt.toNat + 2 ∧
      ∃ prepared K, BTBuilt tk sd.elems.toInt.toNat K a.2 prepared e ∧ BTMergeValues tk sd.elems.toInt.toNat (K - 1) e) := by
  have hT0 : sd.elems.toInt ≤ (tk.arr d).size := by omega
  have hD0 : sd.elems.toInt ≤ d.depth.size := by omega
  unfold btHeap btMergedStart
  simp only [M_bind_assoc, M_pure_bind]
  refine WS.bind' (merge_ws_and (merge_ws_and
    (ws_btSortedStart hdd hsd hstat htree he3 he286 hT0 hD0 hH hs)
    (ws_btSortedStart_sizes hdd hsd hstat htree he3 he286 hT0 hD0 hH hs))
    (ws_btSortedStart_weight hdd hsd hstat htree he3 he286 hT0 hD0 hH hs)) ?_
  intro a prepared ⟨⟨⟨ht, hst, he, leaf, h2, hm, _desc, ho, _minimum⟩, hTs, hDs⟩, weight⟩
  rcases a with ⟨tree, stree, elems, mc⟩
  dsimp only at ht hst he leaf ⊢
  subst tree; subst stree; subst elems
  have count := leaf.count
  have maxCount := Math.scanCount_le (btFreq tk prepared) sd.elems.toInt.toNat
  have initial := BTForest.of_leaf leaf h2 hm (node := sd.elems) (by omega)
    (by rw [hTs]; omega) (by rw [hDs]; omega) ho
  have total : btQueueWeight tk prepared prepared.heap_len.toInt.toNat < 2 ^ 16 := by omega
  refine WS.bind' (ws_btMergeLoop_values initial total) ?_
  intro next before ⟨forest, frame, len, rootWeight, values⟩
  have max := forest.queue.max
  have size := forest.queue.heap
  have k2 := forest.queue.k2
  have kN := forest.queue.kN
  have n286 := forest.queue.n286
  refine WS.bind' (merge_ws_and (merge_ws_and
    (ws_btSaveRoot_forest forest frame) (ws_btSaveRoot_values forest values))
    (ws_btSaveRoot before (by omega) (by omega) (by omega) (by omega))) ?_
  intro _ e ⟨⟨built, valuesA⟩, rootIndex, _index, fields, _size, rootStore, _heapFrame⟩
  have array : tk.arr e = tk.arr before := by rw [fields]; cases tk <;> rfl
  have index : e.heap_max = rootIndex := by rw [fields]
  have root : Hn e e.heap_max.toInt.toNat = before.heap[1]!.toInt.toNat := by
    unfold Hn
    rw [index, rootStore]
  have freq : btFreq tk e (Hn e e.heap_max.toInt.toNat) = btFreq tk before before.heap[1]!.toInt.toNat := by
    rw [root]
    unfold btFreq
    rw [array]
  refine WS.pure' ⟨rfl, ?_, prepared, prepared.heap_len.toInt.toNat, built, valuesA⟩
  rw [freq, rootWeight]
  exact weight

/-- Actual initialized descriptors and array storage discharge the
complete source-prefix profile, retaining every internal parent equation. -/
theorem ws_btHeap_initialized_values {h0 : Heap} {id : Nat} {d : DeflateState}
    (tk : TK) (wf : d.WellFormed) (static : Out.TreesStatic h0.static)
    (run : Out.TreesRun0 id d)
    (budget : mass (fun v => (btFreq tk d v).toNat) tk.buildDesc.elems.toInt.toNat + 2 < 2 ^ 16) :
    WS h0 id (btHeap (Sp id) (some (tk.descRef id))) d (fun a e =>
      a.1 = .ref (tk.ref id) 0 ∧
      (btFreq tk e (Hn e e.heap_max.toInt.toNat)).toNat ≤
        mass (fun v => (btFreq tk d v).toNat) tk.buildDesc.elems.toInt.toNat + 2 ∧
      ∃ prepared K, BTBuilt tk tk.buildDesc.elems.toInt.toNat K a.2 prepared e ∧
        BTMergeValues tk tk.buildDesc.elems.toInt.toNat (K - 1) e) := by
  obtain ⟨lt, dt, bt, _bc, heap, depth⟩ := wf
  have elems3 : 3 ≤ tk.buildDesc.elems.toInt := by cases tk <;> decide +kernel
  have elems286 : tk.buildDesc.elems.toInt ≤ 286 := by cases tk <;> decide +kernel
  have tree : 2 * tk.buildDesc.elems.toInt.toNat - 1 ≤ (tk.arr d).size := by
    cases tk
    · change 571 ≤ d.dyn_ltree.size; omega
    · change 59 ≤ d.dyn_dtree.size; omega
    · change 37 ≤ d.bl_tree.size; omega
  have depths : 2 * tk.buildDesc.elems.toInt.toNat - 1 ≤ d.depth.size := by
    cases tk
    · change 571 ≤ d.depth.size; omega
    · change 59 ≤ d.depth.size; omega
    · change 37 ≤ d.depth.size; omega
  have stat : (tk.getDesc d).stat_desc = some tk.buildStaticRef := by
    cases tk
    · exact run.lstat
    · exact run.dstat
    · exact run.blstat
  have dyn : (tk.getDesc d).dyn_tree = .ref (tk.ref id) 0 := by
    cases tk
    · exact run.ldyn
    · exact run.ddyn
    · exact run.bldyn
  obtain ⟨sl, repair⟩ := (trees_build_static (id := id) static tk).repair
  exact ws_btHeap_values (bt_desc_get tk h0 id d) (trees_build_desc_get static tk) stat dyn
    elems3 elems286 tree depths heap repair budget

/-- Complete source heap construction retains the natural weight sums,
exact depth updates and the chronological order of all removals. -/
theorem ws_btHeap_trace {h0 : Heap} {id : Nat} {tk dk : TK} {d : DeflateState}
    {sref : StaticTreeDescRef} {dd : TreeDesc} {sd : StaticTreeDesc} {sl : Option (Nat → UInt16)}
    (hdd : (dk.descRef id).get (setD h0 id d) = some dd)
    (hsd : StaticTreeDescRef.get h0 sref = some sd)
    (hstat : dd.stat_desc = some sref) (htree : dd.dyn_tree = .ref (tk.ref id) 0)
    (he3 : 3 ≤ sd.elems.toInt) (he286 : sd.elems.toInt ≤ 286)
    (hT : 2 * sd.elems.toInt.toNat - 1 ≤ (tk.arr d).size)
    (hD : 2 * sd.elems.toInt.toNat - 1 ≤ d.depth.size)
    (hH : d.heap.size = 573) (hs : BTStatic h0 id sd.static_tree sd.elems.toInt.toNat sl)
    (budget : mass (fun v => (btFreq tk d v).toNat) sd.elems.toInt.toNat + 2 < 2 ^ 16) :
    WS h0 id (btHeap (Sp id) (some (dk.descRef id))) d (fun a e =>
      a.1 = .ref (tk.ref id) 0 ∧
      (btFreq tk e (Hn e e.heap_max.toInt.toNat)).toNat ≤
        mass (fun v => (btFreq tk d v).toNat) sd.elems.toInt.toNat + 2 ∧
      ∃ prepared K, BTBuilt tk sd.elems.toInt.toNat K a.2 prepared e ∧ BTMergeValues tk sd.elems.toInt.toNat (K - 1) e ∧ BTMergeOrder tk K (K - 1) e ∧ BTLeafValues tk sd.elems.toInt.toNat (574 - 2 * K) e) := by
  have hT0 : sd.elems.toInt ≤ (tk.arr d).size := by omega
  have hD0 : sd.elems.toInt ≤ d.depth.size := by omega
  unfold btHeap btMergedStart
  simp only [M_bind_assoc, M_pure_bind]
  refine WS.bind' (merge_ws_and (merge_ws_and
    (ws_btSortedStart hdd hsd hstat htree he3 he286 hT0 hD0 hH hs)
    (ws_btSortedStart_sizes hdd hsd hstat htree he3 he286 hT0 hD0 hH hs))
    (ws_btSortedStart_weight hdd hsd hstat htree he3 he286 hT0 hD0 hH hs)) ?_
  intro a prepared ⟨⟨⟨ht, hst, he, leaf, h2, hm, _desc, ho, _minimum⟩, hTs, hDs⟩, weight⟩
  rcases a with ⟨tree, stree, elems, mc⟩
  dsimp only at ht hst he leaf ⊢
  subst tree; subst stree; subst elems
  have count := leaf.count
  have maxCount := Math.scanCount_le (btFreq tk prepared) sd.elems.toInt.toNat
  have initial := BTForest.of_leaf leaf h2 hm (node := sd.elems) (by omega)
    (by rw [hTs]; omega) (by rw [hDs]; omega) ho
  have total : btQueueWeight tk prepared prepared.heap_len.toInt.toNat < 2 ^ 16 := by omega
  refine WS.bind' (merge_ws_and (ws_btMergeLoop_values initial total)
    (ws_btMergeLoop_order initial total)) ?_
  intro next before ⟨⟨forest, frame, len, rootWeight, values⟩, _forest, _frame, _len, _weight, order⟩
  have max := forest.queue.max
  have size := forest.queue.heap
  have k2 := forest.queue.k2
  have kN := forest.queue.kN
  have n286 := forest.queue.n286
  refine WS.bind' (merge_ws_and (merge_ws_and
    (ws_btSaveRoot_forest forest frame) (ws_btSaveRoot_values forest values))
    (merge_ws_and (merge_ws_and (ws_btSaveRoot_order forest order) (ws_btSaveRoot_leaf_values forest))
      (ws_btSaveRoot before (by omega) (by omega) (by omega) (by omega)))) ?_
  intro _ e ⟨⟨built, valuesA⟩, ⟨orderA, leaves⟩, rootIndex, _index, fields, _size, rootStore, _heapFrame⟩
  have array : tk.arr e = tk.arr before := by rw [fields]; cases tk <;> rfl
  have index : e.heap_max = rootIndex := by rw [fields]
  have root : Hn e e.heap_max.toInt.toNat = before.heap[1]!.toInt.toNat := by
    unfold Hn
    rw [index, rootStore]
  have freq : btFreq tk e (Hn e e.heap_max.toInt.toNat) = btFreq tk before before.heap[1]!.toInt.toNat := by
    rw [root]
    unfold btFreq
    rw [array]
  refine WS.pure' ⟨rfl, ?_, prepared, prepared.heap_len.toInt.toNat, built, valuesA, orderA, leaves⟩
  rw [freq, rootWeight]
  exact weight

/-- The installed profile supplies the complete weight/order/depth trace. -/
theorem ws_btHeap_initialized_trace {h0 : Heap} {id : Nat} {d : DeflateState}
    (tk : TK) (wf : d.WellFormed) (static : Out.TreesStatic h0.static)
    (run : Out.TreesRun0 id d)
    (budget : mass (fun v => (btFreq tk d v).toNat) tk.buildDesc.elems.toInt.toNat + 2 < 2 ^ 16) :
    WS h0 id (btHeap (Sp id) (some (tk.descRef id))) d (fun a e =>
      a.1 = .ref (tk.ref id) 0 ∧
      (btFreq tk e (Hn e e.heap_max.toInt.toNat)).toNat ≤
        mass (fun v => (btFreq tk d v).toNat) tk.buildDesc.elems.toInt.toNat + 2 ∧
      ∃ prepared K, BTBuilt tk tk.buildDesc.elems.toInt.toNat K a.2 prepared e ∧
        BTMergeValues tk tk.buildDesc.elems.toInt.toNat (K - 1) e ∧ BTMergeOrder tk K (K - 1) e ∧ BTLeafValues tk tk.buildDesc.elems.toInt.toNat (574 - 2 * K) e) := by
  obtain ⟨lt, dt, bt, _bc, heap, depth⟩ := wf
  have elems3 : 3 ≤ tk.buildDesc.elems.toInt := by cases tk <;> decide +kernel
  have elems286 : tk.buildDesc.elems.toInt ≤ 286 := by cases tk <;> decide +kernel
  have tree : 2 * tk.buildDesc.elems.toInt.toNat - 1 ≤ (tk.arr d).size := by
    cases tk
    · change 571 ≤ d.dyn_ltree.size; omega
    · change 59 ≤ d.dyn_dtree.size; omega
    · change 37 ≤ d.bl_tree.size; omega
  have depths : 2 * tk.buildDesc.elems.toInt.toNat - 1 ≤ d.depth.size := by
    cases tk
    · change 571 ≤ d.depth.size; omega
    · change 59 ≤ d.depth.size; omega
    · change 37 ≤ d.depth.size; omega
  have stat : (tk.getDesc d).stat_desc = some tk.buildStaticRef := by
    cases tk
    · exact run.lstat
    · exact run.dstat
    · exact run.blstat
  have dyn : (tk.getDesc d).dyn_tree = .ref (tk.ref id) 0 := by
    cases tk
    · exact run.ldyn
    · exact run.ddyn
    · exact run.bldyn
  obtain ⟨sl, repair⟩ := (trees_build_static (id := id) static tk).repair
  exact ws_btHeap_trace (bt_desc_get tk h0 id d) (trees_build_desc_get static tk) stat dyn
    elems3 elems286 tree depths heap repair budget

end Zlib.Trees.Proofs
