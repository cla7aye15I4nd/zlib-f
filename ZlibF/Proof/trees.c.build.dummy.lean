import ZlibF.Proof.«trees.c.build.optimal-cost»
import ZlibF.Proof.«trees.c.build.lengths»
import ZlibF.Proof.«trees.c.source-length-facts»

/-!
# trees.c: a code with a nonzero length and no occurrence is a forced leaf (index ≤ 2)

`build_tree` gives a nonzero length only to the leaves of the Huffman heap. The leaves are the
symbols of nonzero frequency after the repair loop, which forces frequency 1 onto at most two
symbols of index at most 2 (`node = max_code < 2 ? ++max_code : 0`). So after `build_tree`, a
symbol with a nonzero length either had a nonzero frequency before, or has index at most 2.
-/

namespace Zlib.Trees.Proofs
open C Zlib.Trees
set_option autoImplicit false

/-- After the leaf scan and the repair loop, a leaf of nonzero frequency had a nonzero frequency
before, or is a forced leaf of index at most 2. -/
theorem ws_btLeavesStart_dummy {h0 : Heap} {id : Nat} {tk : TK} {d : DeflateState}
    {r : TreeDescRef} {sref : StaticTreeDescRef} {dd : TreeDesc} {sd : StaticTreeDesc}
    {sl : Option (Nat → UInt16)}
    (hdd : r.get (setD h0 id d) = some dd) (hsd : StaticTreeDescRef.get h0 sref = some sd)
    (hstat : dd.stat_desc = some sref) (htree : dd.dyn_tree = .ref (tk.ref id) 0)
    (he3 : 3 ≤ sd.elems.toInt) (he286 : sd.elems.toInt ≤ 286)
    (hT : sd.elems.toInt ≤ (tk.arr d).size) (hD : sd.elems.toInt ≤ d.depth.size)
    (hH : d.heap.size = 573) (hs : BTStatic h0 id sd.static_tree sd.elems.toInt.toNat sl) :
    WS h0 id (btLeavesStart (Sp id) (some r)) d (fun _ e =>
      ∀ v, v < sd.elems.toInt.toNat → btFreq tk e v ≠ 0 → btFreq tk d v ≠ 0 ∨ v ≤ 2) := by
  refine WS.mono (ws_btLeavesStart hdd hsd hstat htree he3 he286 hT hD hH hs) ?_
  intro a e ⟨_, _, _, _, mid, mc, k, hscan, _, _, _, trace⟩ v hv nonzero
  rcases trace.frequency_or_one_small v with same | ⟨_, small⟩
  · left
    rw [same] at nonzero
    obtain ⟨T, H, D, hl, rfl, hsT, _, _, _, _, ht, _⟩ := hscan
    have hT' : v < T.size := by
      have same : tk.arr { d with heap_len := 0, heap_max := HEAP_SIZE } = tk.arr d := by cases tk <;> rfl
      rw [hsT, same]
      omega
    have keep : btFreq tk (btScanState tk { d with heap_len := 0, heap_max := HEAP_SIZE } T H D hl) v =
        btFreq tk d v := by
      unfold btFreq
      rw [btScanState_tree, ht v hT']
      split <;> cases tk <;> rfl
    rw [keep] at nonzero
    exact nonzero
  · right
    exact small

/-- The ordering step keeps the leaf frequencies. -/
theorem ws_btSortedStart_dummy {h0 : Heap} {id : Nat} {tk dk : TK} {d : DeflateState}
    {sref : StaticTreeDescRef} {dd : TreeDesc} {sd : StaticTreeDesc} {sl : Option (Nat → UInt16)}
    (hdd : (dk.descRef id).get (setD h0 id d) = some dd) (hsd : StaticTreeDescRef.get h0 sref = some sd)
    (hstat : dd.stat_desc = some sref) (htree : dd.dyn_tree = .ref (tk.ref id) 0)
    (he3 : 3 ≤ sd.elems.toInt) (he286 : sd.elems.toInt ≤ 286)
    (hT : sd.elems.toInt ≤ (tk.arr d).size) (hD : sd.elems.toInt ≤ d.depth.size) (hH : d.heap.size = 573)
    (static : BTStatic h0 id sd.static_tree sd.elems.toInt.toNat sl) :
    WS h0 id (btSortedStart (Sp id) (some (dk.descRef id))) d (fun _ e =>
      ∀ v, v < sd.elems.toInt.toNat → btFreq tk e v ≠ 0 → btFreq tk d v ≠ 0 ∨ v ≤ 2) := by
  unfold btSortedStart
  refine WS.bind' (merge_ws_and
    (ws_btLeavesStart hdd hsd hstat htree he3 he286 hT hD hH static)
    (ws_btLeavesStart_dummy hdd hsd hstat htree he3 he286 hT hD hH static)) ?_
  intro a mid ⟨⟨tree, statree, elems, leaf, _scan⟩, dummy⟩
  rcases a with ⟨pointer, staticPointer, count, maximum⟩
  dsimp only at tree statree elems leaf ⊢
  subst pointer
  subst staticPointer
  subst count
  refine WS.bind' (ws_btOrder_leaf tk dk mid sd.elems.toInt.toNat maximum leaf)
    fun _ result ⟨_leaf, H, fields, _rest⟩ => ?_
  refine WS.pure' ?_
  intro v hv nonzero
  have arrays : tk.arr result = tk.arr mid := by rw [fields]; simp only [tk_arr_heap, tk_arr_setDesc]
  apply dummy v hv
  simpa only [btFreq, arrays] using nonzero

/-- The heap keeps the leaf frequencies: after the whole heap, a leaf of nonzero frequency had a
nonzero frequency before, or has index at most 2. -/
theorem ws_btHeap_dummy {h0 : Heap} {id : Nat} {tk dk : TK} {d : DeflateState}
    {sref : StaticTreeDescRef} {dd : TreeDesc} {sd : StaticTreeDesc} {sl : Option (Nat → UInt16)}
    (hdd : (dk.descRef id).get (setD h0 id d) = some dd) (hsd : StaticTreeDescRef.get h0 sref = some sd)
    (hstat : dd.stat_desc = some sref) (htree : dd.dyn_tree = .ref (tk.ref id) 0)
    (he3 : 3 ≤ sd.elems.toInt) (he286 : sd.elems.toInt ≤ 286)
    (hT : 2 * sd.elems.toInt.toNat - 1 ≤ (tk.arr d).size)
    (hD : 2 * sd.elems.toInt.toNat - 1 ≤ d.depth.size) (hH : d.heap.size = 573)
    (static : BTStatic h0 id sd.static_tree sd.elems.toInt.toNat sl) :
    WS h0 id (btHeap (Sp id) (some (dk.descRef id))) d (fun _ result =>
      ∀ v, v < sd.elems.toInt.toNat → btFreq tk result v ≠ 0 → btFreq tk d v ≠ 0 ∨ v ≤ 2) := by
  have capacity : sd.elems.toInt ≤ (tk.arr d).size := by omega
  have depth : sd.elems.toInt ≤ d.depth.size := by omega
  unfold btHeap btMergedStart
  simp only [M_bind_assoc, M_pure_bind]
  refine WS.bind' (merge_ws_and (merge_ws_and
    (ws_btSortedStart hdd hsd hstat htree he3 he286 capacity depth hH static)
    (ws_btSortedStart_sizes hdd hsd hstat htree he3 he286 capacity depth hH static))
    (ws_btSortedStart_dummy (tk := tk) hdd hsd hstat htree he3 he286 capacity depth hH static)) ?_
  intro a prepared ⟨⟨⟨pointer, statree, elems, leaf, two, maximum, _descriptor, ordered, _minimum⟩,
    treeSize, depthSize⟩, dummy⟩
  rcases a with ⟨treePointer, staticPointer, count, mc⟩
  dsimp only at pointer statree elems leaf ⊢
  subst treePointer
  subst staticPointer
  subst count
  have leafCount := leaf.count
  have countBound := Math.scanCount_le (btFreq tk prepared) sd.elems.toInt.toNat
  have forest := BTForest.of_leaf leaf two maximum (node := sd.elems) (by omega)
    (by rw [treeSize]; omega) (by rw [depthSize]; omega) ordered
  refine WS.bind' (ws_btMergeLoop_forest forest) fun next merged ⟨forestM, frameM, _lengthM⟩ => ?_
  refine WS.bind' (ws_btSaveRoot_forest forestM frameM) fun _ result tree => ?_
  refine WS.pure' ?_
  intro v hv nonzero
  apply dummy v hv
  have keep : btFreq tk result v = btFreq tk prepared v := by
    unfold btFreq; rw [tree.leaf_freq v hv]
  rw [← keep]
  exact nonzero

/-- **Forced leaves**: after `build_tree`, a symbol with a nonzero length had a nonzero frequency
before, or has index at most 2. -/
theorem ws_build_tree_dummy {h0 : Heap} {id : Nat} {tk dk : TK} {d : DeflateState}
    {sref : StaticTreeDescRef} {dd : TreeDesc} {sd : StaticTreeDesc}
    {xb : Nat → Nat} {slOpt : Option (Nat → Nat)}
    (hdd : (dk.descRef id).get (setD h0 id d) = some dd)
    (hsd : StaticTreeDescRef.get h0 sref = some sd)
    (hstat : dd.stat_desc = some sref) (htree : dd.dyn_tree = .ref (tk.ref id) 0)
    (he3 : 3 ≤ sd.elems.toInt) (he286 : sd.elems.toInt ≤ 286)
    (hT : 2 * sd.elems.toInt.toNat - 1 ≤ (tk.arr d).size) (hTbig : (tk.arr d).size ≤ 600)
    (hD : 2 * sd.elems.toInt.toNat - 1 ≤ d.depth.size)
    (hH : d.heap.size = 573) (hB : d.bl_count.size = 16)
    (hs : BTBuildStatic h0 id sd xb slOpt) :
    WS h0 id (build_tree (Sp id) (some (dk.descRef id))) d (fun _ e =>
      ∀ v, v < sd.elems.toInt.toNat → (tk.arr e)[v]!.dl ≠ 0 → btFreq tk d v ≠ 0 ∨ v ≤ 2) := by
  obtain ⟨sl, hsRepair⟩ := hs.repair
  rw [build_tree_eq_heap_codes]
  refine WS.bind' (merge_ws_and (merge_ws_and
    (ws_btHeap_built hdd hsd hstat htree he3 he286 hT hTbig hD hH hB hsRepair)
    (ws_btHeap_upper_zero hdd hsd hstat htree he3 he286 hT hD hH hsRepair))
    (merge_ws_and
      (ws_btHeap_complete_leaves hdd hsd hstat htree he3 he286 hT hD hH hsRepair)
      (ws_btHeap_dummy (tk := tk) hdd hsd hstat htree he3 he286 hT hD hH hsRepair)))
    fun a built ⟨⟨⟨ht, prepared, K, hbuilt, hdesc, hBs, hTs⟩, habove⟩, ⟨_usedBound, seen⟩, dummy⟩ => ?_
  rcases a with ⟨tree, mc⟩
  dsimp only at ht hbuilt hdesc habove seen dummy ⊢
  subst tree
  have hctx := hbuilt.bitlen_ctx hs rfl hBs hTs
  have hcodes := ws_btCodes (h0 := h0) (id := id) (tk := tk) (d := built)
    (r := dk.descRef id) (sref := sref) (dd := { dd with max_code := mc }) (sd := sd)
    (hm := 574 - 2 * K) (J := K - 1) (elems := sd.elems.toInt.toNat) (maxc := mc.toInt.toNat)
    (L := sd.max_length.toInt.toNat) (baseN := sd.extra_base.toInt.toNat) (xb := xb) (slOpt := slOpt)
    hdesc hsd hstat htree hctx hbuilt.heap_max hs.length_capacity (by omega) hbuilt.unused
  refine WS.mono hcodes ?_
  intro _ e ⟨mid, hdone, T, he, hT, hstores⟩ v hv nonzero
  have hlens := code_stores_lengths he hT hstores
  rw [hlens] at nonzero
  -- a symbol that is no heap node keeps the length of the built tree, which is zero
  have leafy : ∃ q, 574 - 2 * K ≤ q ∧ q < 573 ∧ Hn built q = v := by
    apply Classical.byContradiction
    intro none
    have hnone : ∀ q, 574 - 2 * K ≤ q → q < 573 → Hn built q ≠ v := by
      intro q hq1 hq2 hqv
      exact none ⟨q, hq1, hq2, hqv⟩
    obtain ⟨Tf, Bf, O, S, hemid, hTf, hBf, hfreq, hout, rest⟩ := hdone
    apply nonzero
    rw [hemid, tk_arr_mkP1, hout v hnone]
    by_cases above : mc.toInt.toNat < v
    · exact habove v hv above
    · exact hbuilt.unused v (by omega) hnone
  obtain ⟨q, hq1, hq2, hqv⟩ := leafy
  -- the root position holds an inner node, so a leaf sits strictly above heap_max
  have inner : q ≠ 574 - 2 * K := by
    intro e0
    have root := hbuilt.shape.root
    have k2 := hbuilt.k2
    rw [← e0, hqv] at root
    omega
  have used : (btFreq tk built v).toNat ≠ 0 := by
    apply (seen v hv).mpr
    refine ⟨q, ?_, hq2, hqv⟩
    rw [hbuilt.heap_max]
    simp only [Int.toNat_natCast]
    omega
  exact dummy v hv (fun z => used (by rw [z]; rfl))

/-- **Kraft equality**: after `build_tree`, the nonzero lengths fill the code space. -/
theorem ws_build_tree_kraft {h0 : Heap} {id : Nat} {tk dk : TK} {d : DeflateState}
    {sref : StaticTreeDescRef} {dd : TreeDesc} {sd : StaticTreeDesc}
    {xb : Nat → Nat} {slOpt : Option (Nat → Nat)}
    (hdd : (dk.descRef id).get (setD h0 id d) = some dd)
    (hsd : StaticTreeDescRef.get h0 sref = some sd)
    (hstat : dd.stat_desc = some sref) (htree : dd.dyn_tree = .ref (tk.ref id) 0)
    (he3 : 3 ≤ sd.elems.toInt) (he286 : sd.elems.toInt ≤ 286)
    (hT : 2 * sd.elems.toInt.toNat - 1 ≤ (tk.arr d).size) (hTbig : (tk.arr d).size ≤ 600)
    (hD : 2 * sd.elems.toInt.toNat - 1 ≤ d.depth.size)
    (hH : d.heap.size = 573) (hB : d.bl_count.size = 16)
    (hs : BTBuildStatic h0 id sd xb slOpt) :
    WS h0 id (build_tree (Sp id) (some (dk.descRef id))) d (fun _ e =>
      GB.rs (fun v => if (tk.arr e)[v]!.dl.toNat ≠ 0 then
        2 ^ (sd.max_length.toInt.toNat - (tk.arr e)[v]!.dl.toNat) else 0) sd.elems.toInt.toNat =
        2 ^ sd.max_length.toInt.toNat) := by
  obtain ⟨sl, hsRepair⟩ := hs.repair
  rw [build_tree_eq_heap_codes]
  refine WS.bind' (merge_ws_and (merge_ws_and
    (ws_btHeap_built hdd hsd hstat htree he3 he286 hT hTbig hD hH hB hsRepair)
    (ws_btHeap_upper_zero hdd hsd hstat htree he3 he286 hT hD hH hsRepair))
    (ws_btHeap_complete_leaves hdd hsd hstat htree he3 he286 hT hD hH hsRepair))
    fun a built ⟨⟨⟨ht, prepared, K, hbuilt, hdesc, hBs, hTs⟩, habove⟩, ⟨usedBound, usedSeen⟩⟩ => ?_
  rcases a with ⟨tree, mc⟩
  dsimp only at ht hbuilt hdesc habove usedBound usedSeen ⊢
  subst tree
  have hctx := hbuilt.bitlen_ctx hs rfl hBs hTs
  have hcodes := ws_btCodes (h0 := h0) (id := id) (tk := tk) (d := built)
    (r := dk.descRef id) (sref := sref) (dd := { dd with max_code := mc }) (sd := sd)
    (hm := 574 - 2 * K) (J := K - 1) (elems := sd.elems.toInt.toNat) (maxc := mc.toInt.toNat)
    (L := sd.max_length.toInt.toNat) (baseN := sd.extra_base.toInt.toNat) (xb := xb) (slOpt := slOpt)
    hdesc hsd hstat htree hctx hbuilt.heap_max hs.length_capacity (by omega) hbuilt.unused
  refine WS.mono hcodes ?_
  intro _ e ⟨mid, hdone, T, he, hT, hstores⟩
  have seen : ∀ v, v < sd.elems.toInt.toNat → ((btFreq tk built v).toNat ≠ 0 ↔
      ∃ q, 574 - 2 * K < q ∧ q < 573 ∧ Hn built q = v) := by
    simpa only [hbuilt.heap_max, Int.toNat_natCast] using usedSeen
  obtain ⟨_, _, kraft⟩ := hdone.optimal_cost_inputs hbuilt.shape hbuilt.unused habove usedBound seen
  have hlens := code_stores_lengths he hT hstores
  have same : (fun v : Nat => if ((tk.arr e)[v]! : CtData).dl.toNat ≠ 0 then
      2 ^ (sd.max_length.toInt.toNat - ((tk.arr e)[v]! : CtData).dl.toNat) else 0) =
      (fun v : Nat => if ((tk.arr mid)[v]! : CtData).dl.toNat ≠ 0 then
      2 ^ (sd.max_length.toInt.toNat - ((tk.arr mid)[v]! : CtData).dl.toNat) else 0) := by
    funext v; rw [hlens v]
  rw [same]
  exact kraft

/-- Kraft equality and forced leaves of `build_tree`, from the stream's initial tree state. -/
theorem ws_build_tree_leaf_facts_initialized {h0 : Heap} {id : Nat} {d : DeflateState}
    (tk : TK) (hwf : d.WellFormed) (hs : Out.TreesStatic h0.static) (hr : Out.TreesRun0 id d) :
    WS h0 id (build_tree (Sp id) (some (tk.descRef id))) d (fun _ e =>
      (∀ v, v < tk.buildDesc.elems.toInt.toNat → (tk.arr e)[v]!.dl ≠ 0 → btFreq tk d v ≠ 0 ∨ v ≤ 2) ∧
      GB.rs (fun v => if (tk.arr e)[v]!.dl.toNat ≠ 0 then
        2 ^ (tk.buildDesc.max_length.toInt.toNat - (tk.arr e)[v]!.dl.toNat) else 0)
        tk.buildDesc.elems.toInt.toNat = 2 ^ tk.buildDesc.max_length.toInt.toNat) := by
  obtain ⟨hLT, hDT, hBT, hBC, hH, hD⟩ := hwf
  have he3 : 3 ≤ tk.buildDesc.elems.toInt := by cases tk <;> decide +kernel
  have he286 : tk.buildDesc.elems.toInt ≤ 286 := by cases tk <;> decide +kernel
  have hT : 2 * tk.buildDesc.elems.toInt.toNat - 1 ≤ (tk.arr d).size := by
    cases tk
    · change 571 ≤ d.dyn_ltree.size; omega
    · change 59 ≤ d.dyn_dtree.size; omega
    · change 37 ≤ d.bl_tree.size; omega
  have hTbig : (tk.arr d).size ≤ 600 := by
    cases tk
    · change d.dyn_ltree.size ≤ 600; omega
    · change d.dyn_dtree.size ≤ 600; omega
    · change d.bl_tree.size ≤ 600; omega
  have hDepth : 2 * tk.buildDesc.elems.toInt.toNat - 1 ≤ d.depth.size := by
    cases tk
    · change 571 ≤ d.depth.size; omega
    · change 59 ≤ d.depth.size; omega
    · change 37 ≤ d.depth.size; omega
  have hstat : (tk.getDesc d).stat_desc = some tk.buildStaticRef := by
    cases tk
    · exact hr.lstat
    · exact hr.dstat
    · exact hr.blstat
  have htree : (tk.getDesc d).dyn_tree = .ref (tk.ref id) 0 := by
    cases tk
    · exact hr.ldyn
    · exact hr.ddyn
    · exact hr.bldyn
  exact merge_ws_and
    (ws_build_tree_dummy (bt_desc_get tk h0 id d) (trees_build_desc_get hs tk) hstat htree
      he3 he286 hT hTbig hDepth hH hBC (trees_build_static hs tk))
    (ws_build_tree_kraft (bt_desc_get tk h0 id d) (trees_build_desc_get hs tk) hstat htree
      he3 he286 hT hTbig hDepth hH hBC (trees_build_static hs tk))

/-- **The two data trees after `blPrepare`**: forced leaves only at index ≤ 2 (against the
frequencies before), and Kraft equality over the 286 and 30 symbols with 15-bit lengths. -/
theorem bl_prepare_leaf_facts {h : Heap} {id b : Nat} {d : DeflateState} {buf : Array UInt8}
    (trees : Out.TreesInvAt h id d b buf) :
    ∃ result, blPrepare (Sp id) h = .ok ((), setD h id result) ∧
      (∀ v, v < 286 → result.dyn_ltree[v]!.dl ≠ 0 → btFreq .lit d v ≠ 0 ∨ v ≤ 2) ∧
      (∀ v, v < 30 → result.dyn_dtree[v]!.dl ≠ 0 → btFreq .dist d v ≠ 0 ∨ v ≤ 2) ∧
      GB.rs (fun v => if result.dyn_ltree[v]!.dl.toNat ≠ 0 then 2 ^ (15 - result.dyn_ltree[v]!.dl.toNat) else 0)
        286 = 2 ^ 15 ∧
      GB.rs (fun v => if result.dyn_dtree[v]!.dl.toNat ≠ 0 then 2 ^ (15 - result.dyn_dtree[v]!.dl.toNat) else 0)
        30 = 2 ^ 15 ∧
      (∀ v, v < 286 → btFreq .lit d v ≠ 0 → 1 ≤ result.dyn_ltree[v]!.dl.toNat) ∧
      (∀ v, v < 30 → btFreq .dist d v ≠ 0 → 1 ≤ result.dyn_dtree[v]!.dl.toNat) := by
  obtain ⟨aL, literal, runL, frameL, factsL, usedL⟩ := merge_ws_and
    (ws_build_tree_frame_initialized (h0 := h) .lit trees.base.wf trees.base.static trees.run.to0)
    (merge_ws_and
      (ws_build_tree_leaf_facts_initialized (h0 := h) .lit trees.base.wf trees.base.static trees.run.to0)
      (ws_build_tree_usable_initialized (h0 := h) .lit trees.base.wf trees.base.static trees.run.to0))
  have unitL : aL = () := Subsingleton.elim _ _
  subst aL
  rw [setD_self trees.base.dstate] at runL
  have treesL := frameL.treesInvAt trees
  obtain ⟨aD, result, runD, frameD, factsD, usedD⟩ := merge_ws_and
    (ws_build_tree_frame_initialized (h0 := h) .dist treesL.base.wf treesL.base.static treesL.run.to0)
    (merge_ws_and
      (ws_build_tree_leaf_facts_initialized (h0 := h) .dist treesL.base.wf treesL.base.static treesL.run.to0)
      (ws_build_tree_usable_initialized (h0 := h) .dist treesL.base.wf treesL.base.static treesL.run.to0))
  have unitD : aD = () := Subsingleton.elim _ _
  subst aD
  have literalTree := frameD.other_tree .lit (by decide +kernel)
  have originalDistance := frameL.other_tree .dist (by decide +kernel)
  simp only [TK.arr] at literalTree originalDistance
  obtain ⟨dummyL, kraftL⟩ := factsL
  obtain ⟨dummyD, kraftD⟩ := factsD
  have nL : TK.lit.buildDesc.elems.toInt.toNat = 286 := by decide +kernel
  have nD : TK.dist.buildDesc.elems.toInt.toNat = 30 := by decide +kernel
  have mL : TK.lit.buildDesc.max_length.toInt.toNat = 15 := by decide +kernel
  have mD : TK.dist.buildDesc.max_length.toInt.toNat = 15 := by decide +kernel
  rw [nL] at dummyL
  rw [nL, mL] at kraftL
  rw [nD] at dummyD
  rw [nD, mD] at kraftD
  change ∀ v, v < 286 → literal.dyn_ltree[v]!.dl ≠ 0 → btFreq .lit d v ≠ 0 ∨ v ≤ 2 at dummyL
  change GB.rs (fun v => if literal.dyn_ltree[v]!.dl.toNat ≠ 0 then
    2 ^ (15 - literal.dyn_ltree[v]!.dl.toNat) else 0) 286 = 2 ^ 15 at kraftL
  change ∀ v, v < 30 → result.dyn_dtree[v]!.dl ≠ 0 → btFreq .dist literal v ≠ 0 ∨ v ≤ 2 at dummyD
  change GB.rs (fun v => if result.dyn_dtree[v]!.dl.toNat ≠ 0 then
    2 ^ (15 - result.dyn_dtree[v]!.dl.toNat) else 0) 30 = 2 ^ 15 at kraftD
  have run : blPrepare (Sp id) h = .ok ((), setD h id result) := by
    have ptrL : pLdesc (Sp id) h = .ok (some (.in_dstate_l_desc id), h) := by
      simp only [pLdesc, bind_app, Out.sid_run trees.base.dstate]
      rfl
    have ptrD : pDdesc (Sp id) (setD h id literal) = .ok (some (.in_dstate_d_desc id), setD h id literal) := by
      simp only [pDdesc, bind_app, Out.sid_run treesL.base.dstate]
      rfl
    unfold blPrepare
    simp only [bind_app, ptrL, TK.descRef] at runL runD ⊢
    rw [runL]
    simp only [bind_app, ptrD]
    simpa only [setD_setD] using runD
  rw [nL] at usedL
  rw [nD] at usedD
  refine ⟨result, run, ?_, ?_, ?_, kraftD, ?_, ?_⟩
  · intro v hv nz
    rw [literalTree] at nz
    exact dummyL v hv nz
  · intro v hv nz
    rcases dummyD v hv nz with used | small
    · left
      unfold btFreq at used ⊢
      rw [show TK.dist.arr literal = literal.dyn_dtree from rfl, originalDistance] at used
      exact used
    · exact Or.inr small
  · rw [literalTree]
    exact kraftL
  · intro v hv used
    have positive := (usedL v hv used).1
    change 1 ≤ literal.dyn_ltree[v]!.dl.toNat at positive
    rw [literalTree]
    exact positive
  · intro v hv used
    have source : btFreq .dist literal v ≠ 0 := by
      unfold btFreq at used ⊢
      rw [show TK.dist.arr literal = literal.dyn_dtree from rfl, originalDistance]
      exact used
    exact (usedD v hv source).1

end Zlib.Trees.Proofs
