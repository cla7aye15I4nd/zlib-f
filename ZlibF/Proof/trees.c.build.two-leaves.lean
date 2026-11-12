import ZlibF.Proof.«trees.c.build.dummy»

/-!
# trees.c: a tree with a forced leaf has exactly two leaves

`build_tree` forces leaves only while the heap holds fewer than two symbols, and then stops at
two. So if some symbol has a nonzero length but had no occurrence, the tree has exactly two
nonzero lengths.
-/

namespace Zlib.Trees.Proofs
open C Zlib.Trees
set_option autoImplicit false

/-- No repair step: the state is unchanged. -/
theorem BTForceTrace.zero_same {tk : TK} {sl : Option (Nat → UInt16)} {mc0 mc : Int32} {d0 d : DeflateState}
    (trace : BTForceTrace tk sl 0 mc0 d0 mc d) : d = d0 := by
  cases trace
  rfl

theorem scanCount_congr {f g : Nat → UInt16} {n : Nat} (agree : ∀ v, v < n → f v = g v) :
    Math.scanCount f n = Math.scanCount g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Math.scanCount]
    rw [ih (fun v lt => agree v (by omega)), agree n (by omega)]

/-- After the leaf scan and the repair loop: a forced leaf means exactly two leaves. -/
theorem ws_btLeavesStart_two {h0 : Heap} {id : Nat} {tk : TK} {d : DeflateState}
    {r : TreeDescRef} {sref : StaticTreeDescRef} {dd : TreeDesc} {sd : StaticTreeDesc}
    {sl : Option (Nat → UInt16)}
    (hdd : r.get (setD h0 id d) = some dd) (hsd : StaticTreeDescRef.get h0 sref = some sd)
    (hstat : dd.stat_desc = some sref) (htree : dd.dyn_tree = .ref (tk.ref id) 0)
    (he3 : 3 ≤ sd.elems.toInt) (he286 : sd.elems.toInt ≤ 286)
    (hT : sd.elems.toInt ≤ (tk.arr d).size) (hD : sd.elems.toInt ≤ d.depth.size)
    (hH : d.heap.size = 573) (hs : BTStatic h0 id sd.static_tree sd.elems.toInt.toNat sl) :
    WS h0 id (btLeavesStart (Sp id) (some r)) d (fun _ e =>
      (∃ v, v < sd.elems.toInt.toNat ∧ btFreq tk e v ≠ 0 ∧ btFreq tk d v = 0) →
        Math.scanCount (btFreq tk e) sd.elems.toInt.toNat = 2) := by
  refine WS.mono (ws_btLeavesStart hdd hsd hstat htree he3 he286 hT hD hH hs) ?_
  intro a e ⟨_, _, _, leaf, mid, mc, k, hscan, hlen, _, hkexact, trace⟩ ⟨v, hv, forced, zero⟩
  have keep : btFreq tk mid v = btFreq tk d v := by
    obtain ⟨T, H, D, hl, rfl, hsT, _, _, _, _, ht, _⟩ := hscan
    have same : tk.arr { d with heap_len := 0, heap_max := HEAP_SIZE } = tk.arr d := by cases tk <;> rfl
    have hT' : v < T.size := by rw [hsT, same]; omega
    unfold btFreq
    rw [btScanState_tree, ht v hT']
    split <;> cases tk <;> rfl
  have kpos : k ≠ 0 := by
    intro k0
    subst k0
    have same := trace.zero_same
    subst same
    rw [keep] at forced
    exact forced zero
  have count := leaf.count
  have small : mid.heap_len.toInt < 2 := by omega
  have two : e.heap_len.toInt = 2 := by rw [hlen]; omega
  rw [two] at count
  omega

/-- The ordering step keeps it. -/
theorem ws_btSortedStart_two {h0 : Heap} {id : Nat} {tk dk : TK} {d : DeflateState}
    {sref : StaticTreeDescRef} {dd : TreeDesc} {sd : StaticTreeDesc} {sl : Option (Nat → UInt16)}
    (hdd : (dk.descRef id).get (setD h0 id d) = some dd) (hsd : StaticTreeDescRef.get h0 sref = some sd)
    (hstat : dd.stat_desc = some sref) (htree : dd.dyn_tree = .ref (tk.ref id) 0)
    (he3 : 3 ≤ sd.elems.toInt) (he286 : sd.elems.toInt ≤ 286)
    (hT : sd.elems.toInt ≤ (tk.arr d).size) (hD : sd.elems.toInt ≤ d.depth.size) (hH : d.heap.size = 573)
    (static : BTStatic h0 id sd.static_tree sd.elems.toInt.toNat sl) :
    WS h0 id (btSortedStart (Sp id) (some (dk.descRef id))) d (fun _ e =>
      (∃ v, v < sd.elems.toInt.toNat ∧ btFreq tk e v ≠ 0 ∧ btFreq tk d v = 0) →
        Math.scanCount (btFreq tk e) sd.elems.toInt.toNat = 2) := by
  unfold btSortedStart
  refine WS.bind' (merge_ws_and
    (ws_btLeavesStart hdd hsd hstat htree he3 he286 hT hD hH static)
    (ws_btLeavesStart_two hdd hsd hstat htree he3 he286 hT hD hH static)) ?_
  intro a mid ⟨⟨tree, statree, elems, leaf, _scan⟩, two⟩
  rcases a with ⟨pointer, staticPointer, count, maximum⟩
  dsimp only at tree statree elems leaf ⊢
  subst pointer
  subst staticPointer
  subst count
  refine WS.bind' (ws_btOrder_leaf tk dk mid sd.elems.toInt.toNat maximum leaf)
    fun _ result ⟨_leaf, H, fields, _rest⟩ => ?_
  refine WS.pure' ?_
  have arrays : tk.arr result = tk.arr mid := by rw [fields]; simp only [tk_arr_heap, tk_arr_setDesc]
  have freq : btFreq tk result = btFreq tk mid := by funext v; simp only [btFreq, arrays]
  rw [freq]
  exact two

/-- The heap keeps the leaf frequencies, so it keeps it. -/
theorem ws_btHeap_two {h0 : Heap} {id : Nat} {tk dk : TK} {d : DeflateState}
    {sref : StaticTreeDescRef} {dd : TreeDesc} {sd : StaticTreeDesc} {sl : Option (Nat → UInt16)}
    (hdd : (dk.descRef id).get (setD h0 id d) = some dd) (hsd : StaticTreeDescRef.get h0 sref = some sd)
    (hstat : dd.stat_desc = some sref) (htree : dd.dyn_tree = .ref (tk.ref id) 0)
    (he3 : 3 ≤ sd.elems.toInt) (he286 : sd.elems.toInt ≤ 286)
    (hT : 2 * sd.elems.toInt.toNat - 1 ≤ (tk.arr d).size)
    (hD : 2 * sd.elems.toInt.toNat - 1 ≤ d.depth.size) (hH : d.heap.size = 573)
    (static : BTStatic h0 id sd.static_tree sd.elems.toInt.toNat sl) :
    WS h0 id (btHeap (Sp id) (some (dk.descRef id))) d (fun _ result =>
      (∃ v, v < sd.elems.toInt.toNat ∧ btFreq tk result v ≠ 0 ∧ btFreq tk d v = 0) →
        Math.scanCount (btFreq tk result) sd.elems.toInt.toNat = 2) := by
  have capacity : sd.elems.toInt ≤ (tk.arr d).size := by omega
  have depth : sd.elems.toInt ≤ d.depth.size := by omega
  unfold btHeap btMergedStart
  simp only [M_bind_assoc, M_pure_bind]
  refine WS.bind' (merge_ws_and (merge_ws_and
    (ws_btSortedStart hdd hsd hstat htree he3 he286 capacity depth hH static)
    (ws_btSortedStart_sizes hdd hsd hstat htree he3 he286 capacity depth hH static))
    (ws_btSortedStart_two (tk := tk) hdd hsd hstat htree he3 he286 capacity depth hH static)) ?_
  intro a prepared ⟨⟨⟨pointer, statree, elems, leaf, two, maximum, _descriptor, ordered, _minimum⟩,
    treeSize, depthSize⟩, twoLeaves⟩
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
  have keep : ∀ v, v < sd.elems.toInt.toNat → btFreq tk result v = btFreq tk prepared v := by
    intro v hv; unfold btFreq; rw [tree.leaf_freq v hv]
  intro ⟨v, hv, forced, zero⟩
  rw [scanCount_congr keep]
  exact twoLeaves ⟨v, hv, by rw [← keep v hv]; exact forced, zero⟩

theorem scanCount_mass (f : Nat → UInt16) (n : Nat) :
    Math.scanCount f n = ZlibF.Math.DeflateSymbols.mass (fun v => if f v ≠ 0 then 1 else 0) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Math.scanCount, ih]; rfl

/-- **Two leaves**: after `build_tree`, if some symbol has a nonzero length but had no occurrence,
exactly two symbols have a nonzero length. -/
theorem ws_build_tree_two {h0 : Heap} {id : Nat} {tk dk : TK} {d : DeflateState}
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
      (∃ v, v < sd.elems.toInt.toNat ∧ (tk.arr e)[v]!.dl.toNat ≠ 0 ∧ btFreq tk d v = 0) →
        ZlibF.Math.DeflateSymbols.mass (fun v => if (tk.arr e)[v]!.dl.toNat ≠ 0 then 1 else 0)
          sd.elems.toInt.toNat = 2) := by
  obtain ⟨sl, hsRepair⟩ := hs.repair
  rw [build_tree_eq_heap_codes]
  refine WS.bind' (merge_ws_and (merge_ws_and (merge_ws_and
    (ws_btHeap_built hdd hsd hstat htree he3 he286 hT hTbig hD hH hB hsRepair)
    (ws_btHeap_upper_zero hdd hsd hstat htree he3 he286 hT hD hH hsRepair))
    (ws_btHeap_complete_leaves hdd hsd hstat htree he3 he286 hT hD hH hsRepair))
    (ws_btHeap_two (tk := tk) hdd hsd hstat htree he3 he286 hT hD hH hsRepair))
    fun a built ⟨⟨⟨⟨ht, prepared, K, hbuilt, hdesc, hBs, hTs⟩, habove⟩, ⟨usedBound, usedSeen⟩⟩, two⟩ => ?_
  rcases a with ⟨tree, mc⟩
  dsimp only at ht hbuilt hdesc habove usedBound usedSeen two ⊢
  subst tree
  have hctx := hbuilt.bitlen_ctx hs rfl hBs hTs
  have hcodes := ws_btCodes (h0 := h0) (id := id) (tk := tk) (d := built)
    (r := dk.descRef id) (sref := sref) (dd := { dd with max_code := mc }) (sd := sd)
    (hm := 574 - 2 * K) (J := K - 1) (elems := sd.elems.toInt.toNat) (maxc := mc.toInt.toNat)
    (L := sd.max_length.toInt.toNat) (baseN := sd.extra_base.toInt.toNat) (xb := xb) (slOpt := slOpt)
    hdesc hsd hstat htree hctx hbuilt.heap_max hs.length_capacity (by omega) hbuilt.unused
  refine WS.mono hcodes ?_
  intro _ e ⟨mid, hdone, T, he, hT, hstores⟩ ⟨v, hv, forced, zero⟩
  have seen : ∀ v, v < sd.elems.toInt.toNat → ((btFreq tk built v).toNat ≠ 0 ↔
      ∃ q, 574 - 2 * K < q ∧ q < 573 ∧ Hn built q = v) := by
    simpa only [hbuilt.heap_max, Int.toNat_natCast] using usedSeen
  obtain ⟨_, used, _⟩ := hdone.optimal_cost_inputs hbuilt.shape hbuilt.unused habove usedBound seen
  have hlens := code_stores_lengths he hT hstores
  have iff : ∀ v, v < sd.elems.toInt.toNat → ((tk.arr e)[v]!.dl.toNat ≠ 0 ↔ btFreq tk built v ≠ 0) := by
    intro v hv
    rw [hlens v, used v hv]
    constructor
    · intro ne z; apply ne; rw [z]; rfl
    · intro ne z; apply ne; exact UInt16.toNat_inj.mp (by rw [z]; rfl)
  have count := two ⟨v, hv, (iff v hv).mp forced, zero⟩
  rw [scanCount_mass] at count
  rw [← count]
  apply ZlibF.Math.DeflateSymbols.mass_congr
  intro w hw
  by_cases z : (tk.arr e)[w]!.dl.toNat ≠ 0
  · rw [if_pos z, if_pos ((iff w hw).mp z)]
  · rw [if_neg z, if_neg (fun nz => z ((iff w hw).mpr nz))]

theorem ws_build_tree_two_initialized {h0 : Heap} {id : Nat} {d : DeflateState}
    (tk : TK) (hwf : d.WellFormed) (hs : Out.TreesStatic h0.static) (hr : Out.TreesRun0 id d) :
    WS h0 id (build_tree (Sp id) (some (tk.descRef id))) d (fun _ e =>
      (∃ v, v < tk.buildDesc.elems.toInt.toNat ∧ (tk.arr e)[v]!.dl.toNat ≠ 0 ∧ btFreq tk d v = 0) →
        ZlibF.Math.DeflateSymbols.mass (fun v => if (tk.arr e)[v]!.dl.toNat ≠ 0 then 1 else 0)
          tk.buildDesc.elems.toInt.toNat = 2) := by
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
  exact ws_build_tree_two (bt_desc_get tk h0 id d) (trees_build_desc_get hs tk) hstat htree
    he3 he286 hT hTbig hDepth hH hBC (trees_build_static hs tk)

/-- **Two leaves after `blPrepare`**: a data tree with a forced leaf has exactly two nonzero
lengths. -/
theorem bl_prepare_two_leaves {h : Heap} {id b : Nat} {d : DeflateState} {buf : Array UInt8}
    (trees : Out.TreesInvAt h id d b buf) :
    ∃ result, blPrepare (Sp id) h = .ok ((), setD h id result) ∧
      ((∃ v, v < 286 ∧ result.dyn_ltree[v]!.dl.toNat ≠ 0 ∧ btFreq .lit d v = 0) →
        ZlibF.Math.DeflateSymbols.mass (fun v => if result.dyn_ltree[v]!.dl.toNat ≠ 0 then 1 else 0) 286 = 2) ∧
      ((∃ v, v < 30 ∧ result.dyn_dtree[v]!.dl.toNat ≠ 0 ∧ btFreq .dist d v = 0) →
        ZlibF.Math.DeflateSymbols.mass (fun v => if result.dyn_dtree[v]!.dl.toNat ≠ 0 then 1 else 0) 30 = 2) := by
  obtain ⟨aL, literal, runL, frameL, twoL⟩ := merge_ws_and
    (ws_build_tree_frame_initialized (h0 := h) .lit trees.base.wf trees.base.static trees.run.to0)
    (ws_build_tree_two_initialized (h0 := h) .lit trees.base.wf trees.base.static trees.run.to0)
  have unitL : aL = () := Subsingleton.elim _ _
  subst aL
  rw [setD_self trees.base.dstate] at runL
  have treesL := frameL.treesInvAt trees
  obtain ⟨aD, result, runD, frameD, twoD⟩ := merge_ws_and
    (ws_build_tree_frame_initialized (h0 := h) .dist treesL.base.wf treesL.base.static treesL.run.to0)
    (ws_build_tree_two_initialized (h0 := h) .dist treesL.base.wf treesL.base.static treesL.run.to0)
  have unitD : aD = () := Subsingleton.elim _ _
  subst aD
  have literalTree := frameD.other_tree .lit (by decide +kernel)
  have originalDistance := frameL.other_tree .dist (by decide +kernel)
  simp only [TK.arr] at literalTree originalDistance
  have nL : TK.lit.buildDesc.elems.toInt.toNat = 286 := by decide +kernel
  have nD : TK.dist.buildDesc.elems.toInt.toNat = 30 := by decide +kernel
  rw [nL] at twoL
  rw [nD] at twoD
  change (∃ v, v < 286 ∧ literal.dyn_ltree[v]!.dl.toNat ≠ 0 ∧ btFreq .lit d v = 0) →
    ZlibF.Math.DeflateSymbols.mass (fun v => if literal.dyn_ltree[v]!.dl.toNat ≠ 0 then 1 else 0) 286 = 2 at twoL
  change (∃ v, v < 30 ∧ result.dyn_dtree[v]!.dl.toNat ≠ 0 ∧ btFreq .dist literal v = 0) →
    ZlibF.Math.DeflateSymbols.mass (fun v => if result.dyn_dtree[v]!.dl.toNat ≠ 0 then 1 else 0) 30 = 2 at twoD
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
  refine ⟨result, run, ?_, ?_⟩
  · rw [literalTree]
    exact twoL
  · intro ⟨v, hv, nz, zero⟩
    apply twoD ⟨v, hv, nz, ?_⟩
    unfold btFreq at zero ⊢
    rw [show TK.dist.arr literal = literal.dyn_dtree from rfl, originalDistance]
    exact zero

end Zlib.Trees.Proofs
