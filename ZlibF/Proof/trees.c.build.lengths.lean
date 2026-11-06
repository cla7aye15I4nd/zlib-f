import ZlibF.Proof.«trees.c.build.frame»

/-! # trees.c: lengths of the entire alphabet after actual construction -/

namespace Zlib.Trees.Proofs
open C Zlib.Trees

/-- Every leaf above the actual prepared maximum is unused and remains
zero-length throughout merging. This also covers leaves outside 0..max_code. -/
theorem BTForest.above_max_zero {tk : TK} {N K j : Nat} {mc node : Int32}
    {d0 d : DeflateState} (hi : BTForest tk N K j mc d0 node d)
    (v : Nat) (hv : v < N) (hmax : mc.toInt.toNat < v) : (tk.arr d)[v]!.dl = 0 := by
  apply hi.unused v hv
  have hm := hi.initial.maxCode
  rcases Math.scanMax_spec (btFreq tk d0) N with ⟨he, hz⟩ | ⟨u, he, hu, hf, hz⟩
  · exact hz v hv
  · exact hz v (by omega) hv

/-- Complete actual heap building retains zero lengths above its maximum.
The property comes from the actual forest and the root store's exact frame. -/
theorem ws_btHeap_upper_zero {h0 : Heap} {id : Nat} {tk dk : TK} {d : DeflateState}
    {sref : StaticTreeDescRef} {dd : TreeDesc} {sd : StaticTreeDesc} {sl : Option (Nat → UInt16)}
    (hdd : (dk.descRef id).get (setD h0 id d) = some dd)
    (hsd : StaticTreeDescRef.get h0 sref = some sd)
    (hstat : dd.stat_desc = some sref) (htree : dd.dyn_tree = .ref (tk.ref id) 0)
    (he3 : 3 ≤ sd.elems.toInt) (he286 : sd.elems.toInt ≤ 286)
    (hT : 2 * sd.elems.toInt.toNat - 1 ≤ (tk.arr d).size)
    (hD : 2 * sd.elems.toInt.toNat - 1 ≤ d.depth.size)
    (hH : d.heap.size = 573) (hs : BTStatic h0 id sd.static_tree sd.elems.toInt.toNat sl) :
    WS h0 id (btHeap (Sp id) (some (dk.descRef id))) d (fun a e =>
      ∀ v < sd.elems.toInt.toNat, a.2.toInt.toNat < v → (tk.arr e)[v]!.dl = 0) := by
  have hT0 : sd.elems.toInt ≤ (tk.arr d).size := by omega
  have hD0 : sd.elems.toInt ≤ d.depth.size := by omega
  unfold btHeap btMergedStart
  simp only [M_bind_assoc, M_pure_bind]
  refine WS.bind' (merge_ws_and
    (ws_btSortedStart hdd hsd hstat htree he3 he286 hT0 hD0 hH hs)
    (ws_btSortedStart_sizes hdd hsd hstat htree he3 he286 hT0 hD0 hH hs))
    fun a prepared ⟨⟨ht, hst, he, hleaf, h2, hm, hdesc, ho, hmin⟩, hTs, hDs⟩ => ?_
  rcases a with ⟨tree, stree, elems, mc⟩
  dsimp only at ht hst he hleaf hdesc ⊢
  subst tree; subst stree; subst elems
  have hcnt := hleaf.count
  have hKN := Math.scanCount_le (btFreq tk prepared) sd.elems.toInt.toNat
  have hI := BTForest.of_leaf hleaf h2 hm (node := sd.elems) (by omega)
    (by rw [hTs]; omega) (by rw [hDs]; omega) ho
  refine WS.bind' (ws_btMergeLoop_forest hI) fun next merged ⟨hforest, hframe, hlen⟩ => ?_
  have hK2 := hforest.queue.k2
  have hKN := hforest.queue.kN
  have hN286 := hforest.queue.n286
  have hsize := hforest.queue.heap
  have hmax := hforest.queue.max
  have hj := hforest.queue.stage
  refine WS.bind' (ws_btSaveRoot merged (by omega) (by omega) (by omega) (by omega))
    fun _ e ⟨hm, hhm, he, hsz, hroot, htail⟩ => ?_
  refine WS.pure' ?_
  intro v hv hmaxv
  have hz := hforest.above_max_zero v hv hmaxv
  rw [he]
  cases tk <;> exact hz

/-- Complete actual construction bounds every alphabet length, including
zero-frequency symbols above max_code. Those omitted symbols are exactly
zero, so subsequent header writes never read an unconstrained old length. -/
theorem ws_build_tree_all_lengths {h0 : Heap} {id : Nat} {tk dk : TK} {d : DeflateState}
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
      (∀ v < sd.elems.toInt.toNat, (tk.arr e)[v]!.dl.toNat ≤ sd.max_length.toInt.toNat) ∧
      ∀ v < sd.elems.toInt.toNat, (dk.getDesc e).max_code.toInt.toNat < v → (tk.arr e)[v]!.dl = 0) := by
  obtain ⟨sl, hsRepair⟩ := hs.repair
  rw [build_tree_eq_heap_codes]
  refine WS.bind' (merge_ws_and
    (ws_btHeap_built hdd hsd hstat htree he3 he286 hT hTbig hD hH hB hsRepair)
    (ws_btHeap_upper_zero hdd hsd hstat htree he3 he286 hT hD hH hsRepair))
    fun a built ⟨⟨ht, prepared, K, hbuilt, hdesc, hBs, hTs⟩, habove⟩ => ?_
  rcases a with ⟨tree, mc⟩
  dsimp only at ht hbuilt hdesc habove ⊢
  subst tree
  have hctx := hbuilt.bitlen_ctx hs rfl hBs hTs
  have hcodes := ws_btCodes (h0 := h0) (id := id) (tk := tk) (d := built)
    (r := dk.descRef id) (sref := sref) (dd := { dd with max_code := mc }) (sd := sd)
    (hm := 574 - 2 * K) (J := K - 1) (elems := sd.elems.toInt.toNat) (maxc := mc.toInt.toNat)
    (L := sd.max_length.toInt.toNat) (baseN := sd.extra_base.toInt.toNat) (xb := xb) (slOpt := slOpt)
    hdesc hsd hstat htree hctx hbuilt.heap_max hs.length_capacity (by omega) hbuilt.unused
  refine WS.mono hcodes ?_
  intro _ e ⟨mid, hdone, T, he, hT, hstores⟩
  have hlens := code_stores_lengths he hT hstores
  have hlow := (hdone.symbolic_lengths hbuilt.shape hbuilt.unused).1
  have hupper : ∀ v < sd.elems.toInt.toNat, mc.toInt.toNat < v → (tk.arr mid)[v]!.dl = 0 := by
    intro v hv hmv
    have hnone : ∀ q, 574 - 2 * K ≤ q → q < 573 → Hn built q ≠ v := by
      intro q hq1 hq2 hqv
      have hk := hbuilt.shape.kind q hq1 hq2
      omega
    obtain ⟨Tf, Bf, O, S, hemid, hTf, hBf, hfreq, hout, rest⟩ := hdone
    rw [hemid, tk_arr_mkP1, hout v hnone, habove v hv hmv]
  have hmaxBuilt : (dk.getDesc built).max_code = mc := by
    have hg := bt_desc_get dk h0 id built
    rw [hg] at hdesc
    exact congrArg TreeDesc.max_code (Option.some.inj hdesc)
  have hmaxE : (dk.getDesc e).max_code = mc := by
    rw [he]
    have hdescmid := hdone.descriptor dk
    cases tk <;> cases dk <;> exact (congrArg TreeDesc.max_code hdescmid).trans hmaxBuilt
  constructor
  · intro v hv
    rw [hlens]
    by_cases hvm : v ≤ mc.toInt.toNat
    · exact hlow v hvm
    · rw [hupper v hv (by omega)]
      change 0 ≤ sd.max_length.toInt.toNat
      omega
  · intro v hv hmv
    rw [hmaxE] at hmv
    rw [hlens]
    exact hupper v hv hmv

/-- Every installed alphabet's full length bound follows from the existing
initialization representation and actual constructor execution. -/
theorem ws_build_tree_all_lengths_initialized {h0 : Heap} {id : Nat} {d : DeflateState}
    (tk : TK) (hwf : d.WellFormed) (hs : Out.TreesStatic h0.static) (hr : Out.TreesRun0 id d) :
    WS h0 id (build_tree (Sp id) (some (tk.descRef id))) d (fun _ e =>
      (∀ v < tk.buildDesc.elems.toInt.toNat, (tk.arr e)[v]!.dl.toNat ≤ tk.buildDesc.max_length.toInt.toNat) ∧
      ∀ v < tk.buildDesc.elems.toInt.toNat, (tk.getDesc e).max_code.toInt.toNat < v → (tk.arr e)[v]!.dl = 0) := by
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
  exact ws_build_tree_all_lengths (bt_desc_get tk h0 id d) (trees_build_desc_get hs tk) hstat htree
    he3 he286 hT hTbig hDepth hH hBC (trees_build_static hs tk)

end Zlib.Trees.Proofs
