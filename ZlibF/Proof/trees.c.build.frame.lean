import ZlibF.Proof.«trees.c.build.format»

/-! # trees.c: caller state retained by complete tree construction -/

namespace Zlib.Trees.Proofs
open C Zlib.Trees

/-- The complete record footprint of tree construction. Only the selected
tree, selected descriptor maximum, work arrays, heap controls and costs may
change. The replacement arrays have the original sizes. -/
def BTBuildFrame (tk dk : TK) (d e : DeflateState) : Prop :=
  ∃ (T : Array CtData) (H : Array Int32) (D : Array UInt8) (B : Array UInt16)
    (hl hm mc : Int32) (O S : UInt64),
    e = { tk.setArr (dk.setDesc d { dk.getDesc d with max_code := mc }) T with
      heap := H, depth := D, bl_count := B, heap_len := hl, heap_max := hm,
      opt_len := O, static_len := S } ∧
    T.size = (tk.arr d).size ∧ H.size = d.heap.size ∧
    D.size = d.depth.size ∧ B.size = d.bl_count.size

theorem BTBuildFrame.refl (tk dk : TK) (d : DeflateState) : BTBuildFrame tk dk d d := by
  refine ⟨tk.arr d, d.heap, d.depth, d.bl_count, d.heap_len, d.heap_max,
    (dk.getDesc d).max_code, d.opt_len, d.static_len, ?_, rfl, rfl, rfl, rfl⟩
  cases tk <;> cases dk <;> simp only [TK.setArr, TK.setDesc, TK.getDesc, TK.arr] <;> rfl

theorem BTBuildFrame.trans {tk dk : TK} {a b c : DeflateState}
    (hab : BTBuildFrame tk dk a b) (hbc : BTBuildFrame tk dk b c) :
    BTBuildFrame tk dk a c := by
  obtain ⟨T, H, D, B, hl, hm, mc, O, S, rfl, hT, hH, hD, hB⟩ := hab
  obtain ⟨T', H', D', B', hl', hm', mc', O', S', rfl, hT', hH', hD', hB'⟩ := hbc
  refine ⟨T', H', D', B', hl', hm', mc', O', S', ?_, ?_, ?_, ?_, ?_⟩
  · cases tk <;> cases dk <;> simp only [TK.setArr, TK.setDesc, TK.getDesc] <;> rfl
  · have hT'' : T'.size = T.size := by
      cases tk <;> cases dk <;> exact hT'
    exact hT''.trans hT
  · exact hH'.trans hH
  · exact hD'.trans hD
  · exact hB'.trans hB

/-- The forest's checked exact write frame is contained in the complete
construction footprint. -/
theorem BTForestFrame.build_frame {tk : TK} {d e : DeflateState}
    (hi : BTForestFrame tk d e) (dk : TK) : BTBuildFrame tk dk d e := by
  obtain ⟨T, H, D, hl, hm, rfl, hT, hH, hD⟩ := hi
  refine ⟨T, H, D, d.bl_count, hl, hm, (dk.getDesc d).max_code,
    d.opt_len, d.static_len, ?_, hT, hH, hD, rfl⟩
  cases tk <;> cases dk <;> simp only [TK.setArr, TK.setDesc, TK.getDesc, btScanState] <;> rfl

/-- Repair never changes the heap's allocated length. -/
theorem BTForceTrace.heap_size {tk : TK} {sl : Option (Nat → UInt16)}
    {k : Nat} {mc0 mc : Int32} {d e : DeflateState} (hi : BTForceTrace tk sl k mc0 d mc e) :
    e.heap.size = d.heap.size := by
  induction hi with
  | nil => rfl
  | snoc node hl before hn hnT hm hhl ih =>
    simpa only [btForceState_heap, Array.size_set!] using ih

/-- The actual reset, scan, repair, maximum store and heapify retain all
caller fields outside the complete construction footprint. -/
theorem ws_btSortedStart_frame {h0 : Heap} {id : Nat} {tk dk : TK} {d : DeflateState}
    {sref : StaticTreeDescRef} {dd : TreeDesc} {sd : StaticTreeDesc} {sl : Option (Nat → UInt16)}
    (hdd : (dk.descRef id).get (setD h0 id d) = some dd)
    (hsd : StaticTreeDescRef.get h0 sref = some sd)
    (hstat : dd.stat_desc = some sref) (htree : dd.dyn_tree = .ref (tk.ref id) 0)
    (he3 : 3 ≤ sd.elems.toInt) (he286 : sd.elems.toInt ≤ 286)
    (hT : sd.elems.toInt ≤ (tk.arr d).size) (hD : sd.elems.toInt ≤ d.depth.size)
    (hH : d.heap.size = 573) (hs : BTStatic h0 id sd.static_tree sd.elems.toInt.toNat sl) :
    WS h0 id (btSortedStart (Sp id) (some (dk.descRef id))) d
      (fun _ e => BTBuildFrame tk dk d e) := by
  unfold btSortedStart
  refine WS.bind' (ws_btLeavesStart hdd hsd hstat htree he3 he286 hT hD hH hs)
    fun a mid ⟨ht, hst, he, hleaf, scan, scanMc, k, hscan, hlen, hk, hkexact, htrace⟩ => ?_
  rcases a with ⟨tree, stree, elems, mc⟩
  dsimp only at ht hst he hleaf htrace ⊢
  subst tree; subst stree; subst elems
  have hsz := htrace.merge_sizes
  have hheap := htrace.heap_size
  have hB := htrace.bl_count
  obtain ⟨Ts, Hs, Ds, hls, hscanEq, hsT, hsH, hsD, rest⟩ := hscan
  obtain ⟨T, H, D, hl, O, S, hmid⟩ := htrace.frame
  refine WS.bind' (ws_btOrder_leaf tk dk mid sd.elems.toInt.toNat mc hleaf)
    fun _ e ⟨hleaf', H', he, hsH', hf, hp, ho, hdesc', hmin⟩ => ?_
  refine WS.pure' ?_
  refine ⟨T, H', D, d.bl_count, hl, HEAP_SIZE, mc, O, S, ?_, ?_, ?_, ?_, rfl⟩
  · rw [he, hmid, hscanEq]
    cases tk <;> cases dk <;> simp only [TK.setArr, TK.setDesc, TK.getDesc, btScanState] <;> rfl
  · rw [hmid] at hsz
    have hszt : T.size = (tk.arr scan).size := by
      cases tk <;> exact hsz.1
    rw [hscanEq, btScanState_tree] at hszt
    have hsT' : Ts.size = (tk.arr d).size := by
      cases tk <;> exact hsT
    exact hszt.trans hsT'
  · rw [hsH', hheap, hscanEq]
    exact hsH
  · rw [hmid, hscanEq] at hsz
    exact hsz.2.trans hsD

/-- The actual complete heap-building prefix keeps the caller frame.
Its forest premises come from the actual sorted-leaf prefix. -/
theorem ws_btHeap_frame {h0 : Heap} {id : Nat} {tk dk : TK} {d : DeflateState}
    {sref : StaticTreeDescRef} {dd : TreeDesc} {sd : StaticTreeDesc} {sl : Option (Nat → UInt16)}
    (hdd : (dk.descRef id).get (setD h0 id d) = some dd)
    (hsd : StaticTreeDescRef.get h0 sref = some sd)
    (hstat : dd.stat_desc = some sref) (htree : dd.dyn_tree = .ref (tk.ref id) 0)
    (he3 : 3 ≤ sd.elems.toInt) (he286 : sd.elems.toInt ≤ 286)
    (hT : 2 * sd.elems.toInt.toNat - 1 ≤ (tk.arr d).size)
    (hD : 2 * sd.elems.toInt.toNat - 1 ≤ d.depth.size)
    (hH : d.heap.size = 573) (hs : BTStatic h0 id sd.static_tree sd.elems.toInt.toNat sl) :
    WS h0 id (btHeap (Sp id) (some (dk.descRef id))) d
      (fun _ e => BTBuildFrame tk dk d e) := by
  have hT0 : sd.elems.toInt ≤ (tk.arr d).size := by omega
  have hD0 : sd.elems.toInt ≤ d.depth.size := by omega
  unfold btHeap btMergedStart
  simp only [M_bind_assoc, M_pure_bind]
  refine WS.bind' (merge_ws_and (merge_ws_and
    (ws_btSortedStart hdd hsd hstat htree he3 he286 hT0 hD0 hH hs)
    (ws_btSortedStart_sizes hdd hsd hstat htree he3 he286 hT0 hD0 hH hs))
    (ws_btSortedStart_frame hdd hsd hstat htree he3 he286 hT0 hD0 hH hs))
    fun a prepared ⟨⟨⟨ht, hst, he, hleaf, h2, hm, hdesc, ho, hmin⟩, hTs, hDs⟩, hframe⟩ => ?_
  rcases a with ⟨tree, stree, elems, mc⟩
  dsimp only at ht hst he hleaf hdesc ⊢
  subst tree; subst stree; subst elems
  have hcnt := hleaf.count
  have hKN := Math.scanCount_le (btFreq tk prepared) sd.elems.toInt.toNat
  have hI := BTForest.of_leaf hleaf h2 hm (node := sd.elems) (by omega)
    (by rw [hTs]; omega) (by rw [hDs]; omega) ho
  refine WS.bind' (ws_btMergeLoop_forest hI) fun next merged ⟨hforest, hmerge, hlen⟩ => ?_
  refine WS.bind' (ws_btSaveRoot_forest hforest hmerge) fun _ e hbuilt => ?_
  exact WS.pure' (hframe.trans (hbuilt.frame.build_frame dk))

/-- Length generation has the complete caller footprint. -/
theorem GBDone.build_frame {tk : TK} {d e : DeflateState} {hm J maxc L : Nat}
    {xb : Nat → Nat} {slOpt : Option (Nat → Nat)}
    (hi : GBDone tk d hm J maxc L xb slOpt e) (hB : d.bl_count.size = 16) (dk : TK) :
    BTBuildFrame tk dk d e := by
  obtain ⟨T, B, O, S, rfl, hT, hBs, rest⟩ := hi
  refine ⟨T, d.heap, d.depth, B, d.heap_len, d.heap_max, (dk.getDesc d).max_code,
    O, S, ?_, hT, rfl, rfl, hBs.trans hB.symm⟩
  cases tk <;> cases dk <;> simp only [mkP1, TK.setArr, TK.setDesc, TK.getDesc] <;> rfl

/-- Canonical code stores keep the complete caller footprint. -/
theorem BTBuildFrame.codes (tk dk : TK) (d : DeflateState) (T : Array CtData)
    (hT : T.size = (tk.arr d).size) : BTBuildFrame tk dk d (tk.setArr d T) := by
  refine ⟨T, d.heap, d.depth, d.bl_count, d.heap_len, d.heap_max, (dk.getDesc d).max_code,
    d.opt_len, d.static_len, ?_, hT, rfl, rfl, rfl⟩
  cases tk <;> cases dk <;> simp only [TK.setArr, TK.setDesc, TK.getDesc] <;> rfl

/-- Complete actual build_tree retains all caller state outside its exact
record footprint. No postcondition of a callee is assumed. -/
theorem ws_build_tree_frame {h0 : Heap} {id : Nat} {tk dk : TK} {d : DeflateState}
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
    WS h0 id (build_tree (Sp id) (some (dk.descRef id))) d
      (fun _ e => BTBuildFrame tk dk d e) := by
  obtain ⟨sl, hsRepair⟩ := hs.repair
  rw [build_tree_eq_heap_codes]
  refine WS.bind' (merge_ws_and
    (ws_btHeap_built hdd hsd hstat htree he3 he286 hT hTbig hD hH hB hsRepair)
    (ws_btHeap_frame hdd hsd hstat htree he3 he286 hT hD hH hsRepair))
    fun a built ⟨⟨ht, prepared, K, hbuilt, hdesc, hBs, hTs⟩, hframe⟩ => ?_
  rcases a with ⟨tree, mc⟩
  dsimp only at ht hbuilt hdesc ⊢
  subst tree
  have hctx := hbuilt.bitlen_ctx hs rfl hBs hTs
  have hcodes := ws_btCodes (h0 := h0) (id := id) (tk := tk) (d := built)
    (r := dk.descRef id) (sref := sref) (dd := { dd with max_code := mc }) (sd := sd)
    (hm := 574 - 2 * K) (J := K - 1) (elems := sd.elems.toInt.toNat) (maxc := mc.toInt.toNat)
    (L := sd.max_length.toInt.toNat) (baseN := sd.extra_base.toInt.toNat) (xb := xb) (slOpt := slOpt)
    hdesc hsd hstat htree hctx hbuilt.heap_max hs.length_capacity (by omega) hbuilt.unused
  refine WS.mono hcodes ?_
  intro _ e ⟨mid, hdone, T, he, hT, hstores⟩
  subst e
  exact hframe.trans ((hdone.build_frame hBs dk).trans (BTBuildFrame.codes tk dk mid T hT))

/-- The construction footprint preserves every array size in WellFormed. -/
theorem BTBuildFrame.wellFormed {tk dk : TK} {d e : DeflateState}
    (hi : BTBuildFrame tk dk d e) (hw : d.WellFormed) : e.WellFormed := by
  obtain ⟨T, H, D, B, hl, hm, mc, O, S, rfl, hT, hH, hD, hB⟩ := hi
  obtain ⟨hLT, hDT, hBT, hBC, hHeap, hDepth⟩ := hw
  cases tk <;> cases dk <;>
    simp only [TK.setArr, TK.setDesc, DeflateState.WellFormed] <;>
    simp_all only [TK.arr, and_self]

/-- Tree construction retains the live output buffer, descriptor pointers,
symbol count and bit-buffer invariant. -/
theorem BTBuildFrame.treesInvAt {tk dk : TK} {h : Heap} {id b : Nat}
    {d e : DeflateState} {buf : Array UInt8} (hi : BTBuildFrame tk dk d e)
    (hI : Out.TreesInvAt h id d b buf) : Out.TreesInvAt (setD h id e) id e b buf := by
  have hw := hi.wellFormed hI.base.wf
  obtain ⟨T, H, D, B, hl, hm, mc, O, S, rfl, rest⟩ := hi
  cases tk <;> cases dk <;>
    exact ⟨⟨by simp [setD], hw, hI.base.static, hI.base.pbuf, hI.base.bytes, hI.base.rw,
      hI.base.size, hI.base.psize, hI.base.sym, hI.base.lit_lo, hI.base.lit_hi,
      hI.base.sym_end, hI.base.pending_le⟩,
      ⟨hI.run.ldyn, hI.run.lstat, hI.run.ddyn, hI.run.dstat, hI.run.bldyn, hI.run.blstat,
        hI.run.bi_lo, hI.run.bi_hi, hI.run.bi_buf, hI.run.sym_next_le, hI.run.sym_next_mod⟩⟩

/-- Building codes changes no pending output bits. -/
theorem BTBuildFrame.outBits {tk dk : TK} {d e : DeflateState}
    (hi : BTBuildFrame tk dk d e) (buf : Array UInt8) : Out.outBits buf e = Out.outBits buf d := by
  obtain ⟨T, H, D, B, hl, hm, mc, O, S, rfl, rest⟩ := hi
  cases tk <;> cases dk <;> rfl

/-- Building a different alphabet retains this tree exactly, including all
code words and lengths needed for subsequent emission. -/
theorem BTBuildFrame.other_tree {tk dk : TK} {d e : DeflateState}
    (hi : BTBuildFrame tk dk d e) (other : TK) (hne : other ≠ tk) :
    other.arr e = other.arr d := by
  obtain ⟨T, H, D, B, hl, hm, mc, O, S, rfl, rest⟩ := hi
  cases tk <;> cases other <;> cases dk <;> first | exact False.elim (hne rfl) | rfl

/-- The installed descriptors and existing initialization representation
supply every premise of the complete caller-frame proof. -/
theorem ws_build_tree_frame_initialized {h0 : Heap} {id : Nat} {d : DeflateState}
    (tk : TK) (hwf : d.WellFormed) (hs : Out.TreesStatic h0.static) (hr : Out.TreesRun0 id d) :
    WS h0 id (build_tree (Sp id) (some (tk.descRef id))) d
      (fun _ e => BTBuildFrame tk tk d e) := by
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
  exact ws_build_tree_frame (bt_desc_get tk h0 id d) (trees_build_desc_get hs tk) hstat htree
    he3 he286 hT hTbig hDepth hH hBC (trees_build_static hs tk)

/-- Complete tree construction preserves the actual caller's live output
invariant and pending bits, without assuming either fact after the call. -/
theorem build_tree_preserves {h : Heap} {id b : Nat} {d : DeflateState} {buf : Array UInt8}
    (hI : Out.TreesInvAt h id d b buf) (tk : TK) :
    ∃ e : DeflateState, build_tree (Sp id) (some (tk.descRef id)) h = .ok ((), setD h id e) ∧
      BTBuildFrame tk tk d e ∧ Out.TreesInvAt (setD h id e) id e b buf ∧
      Out.outBits buf e = Out.outBits buf d := by
  obtain ⟨a, e, he, hframe⟩ := ws_build_tree_frame_initialized (h0 := h) tk
    hI.base.wf hI.base.static hI.run.to0
  have ha : a = () := Subsingleton.elim _ _
  subst a
  rw [setD_self hI.base.dstate] at he
  exact ⟨e, he, hframe, hframe.treesInvAt hI, hframe.outBits buf⟩

/-- Building the actual tree and then sending one originally used symbol
runs on one caller heap. The appended output decodes to that symbol under
the independently specified decoder, with every following suffix retained.
The fifteen-bit room premise is an internal caller obligation. It still
needs to be derived from block output and overlay bounds. This is a symbol
result, not a complete block or public deflate theorem. -/
theorem build_tree_send_decodable {h : Heap} {id b : Nat} {d : DeflateState} {buf : Array UInt8}
    (hI : Out.TreesInvAt h id d b buf) (tk : TK) (v : Nat)
    (hv : v < tk.buildDesc.elems.toInt.toNat) (hfreq : btFreq tk d v ≠ 0)
    (hroom : 8 * d.pending.toNat + d.bi_valid.toInt.toNat + 15 ≤ 8 * buf.size) :
    ∃ (built e : DeflateState) (buf' : Array UInt8) (maxc : Nat),
      build_tree (Sp id) (some (tk.descRef id)) h = .ok ((), setD h id built) ∧
      (do build_tree (Sp id) (some (tk.descRef id))
          send_code (Sp id) (v : Int) (.ref (tk.ref id) 0)) h =
        .ok ((), Out.setD (Out.setB h b buf') id e) ∧
      Out.TreesInvAt (Out.setD (Out.setB h b buf') id e) id e b buf' ∧
      BTBuildFrame tk tk d built ∧ Out.BitsDiff built e ∧
      (tk.getDesc built).max_code.toInt = maxc ∧
      maxc < tk.buildDesc.elems.toInt.toNat ∧
      Out.outBits buf' e = Out.outBits buf d ++
        Out.natBits (tk.arr built)[v]!.fc.toNat (tk.arr built)[v]!.dl.toNat ∧
      ∀ suffix : List Bool,
        ZlibF.Spec.decodeSym
          (Zlib.Inftrees.Proofs.lensOf (fun n => (tk.arr built)[n]!.dl.toNat) (maxc + 1))
          (Out.natBits (tk.arr built)[v]!.fc.toNat (tk.arr built)[v]!.dl.toNat ++ suffix) =
            some (v, suffix) := by
  obtain ⟨a, built, hbuild, hframe, husable, maxc, hmax, hdesc, haccept, hdecode⟩ :=
    merge_ws_and (ws_build_tree_frame_initialized (h0 := h) tk hI.base.wf hI.base.static hI.run.to0)
      (merge_ws_and (ws_build_tree_usable_initialized (h0 := h) tk hI.base.wf hI.base.static hI.run.to0)
        (ws_build_tree_decodable_initialized (h0 := h) tk hI.base.wf hI.base.static hI.run.to0))
  have ha : a = () := Subsingleton.elim _ _
  subst a
  rw [setD_self hI.base.dstate] at hbuild
  have hIbuilt := hframe.treesInvAt hI
  have hbits := hframe.outBits buf
  have hcount := congrArg List.length hbits
  simp only [Out.outBits_length] at hcount
  have hused := husable v hv hfreq
  have hL : tk.buildDesc.max_length.toInt.toNat ≤ 15 := by cases tk <;> decide +kernel
  have hsize : tk.buildDesc.elems.toInt.toNat ≤ (tk.arr built).size := by
    obtain ⟨hLT, hDT, hBT, hBC, hH, hD⟩ := hIbuilt.base.wf
    cases tk
    · change 286 ≤ built.dyn_ltree.size; omega
    · change 30 ≤ built.dyn_dtree.size; omega
    · change 19 ≤ built.bl_tree.size; omega
  have hg := tk_get (h0 := h) (id := id) (d := built) tk
  have hdl : getDl (.ref (tk.ref id) 0) (v : Int) (setD h id built) =
      .ok ((tk.arr built)[v]!.dl, setD h id built) := by
    simpa only [getElem!_pos, show v < (tk.arr built).size by omega] using
      Out.getDl_gen hg (show v < (tk.arr built).size by omega)
  have hfc : getFc (.ref (tk.ref id) 0) (v : Int) (setD h id built) =
      .ok ((tk.arr built)[v]!.fc, setD h id built) := by
    simpa only [getElem!_pos, show v < (tk.arr built).size by omega] using
      Out.getFc_gen hg (show v < (tk.arr built).size by omega)
  obtain ⟨buf', e, hsend, hIe, hout, hsize', houtside, hlow, hupp, hdiff⟩ :=
    Out.send_code_emit hIbuilt (v : Int) (.ref (tk.ref id) 0) _ _ hdl hfc
      (by omega) hused.2.2.2 (by omega)
  have hheap : Out.setD (Out.setB (setD h id built) b buf') id e =
      Out.setD (Out.setB h b buf') id e := by
    change Out.setD (Out.setB (Out.setD h id built) b buf') id e = _
    rw [Out.setB_setD, Out.setD_setD]
  rw [hheap] at hsend hIe
  have hsend' : send_code (Sp id) (v : Int) (.ref (tk.ref id) 0) (setD h id built) =
      .ok ((), Out.setD (Out.setB h b buf') id e) := by
    exact hsend
  have hIe' : Out.TreesInvAt (Out.setD (Out.setB h b buf') id e) id e b buf' := by
    exact hIe
  refine ⟨built, e, buf', maxc, hbuild, ?_, hIe', hframe, hdiff, hdesc, hmax, ?_, hdecode v hv hfreq⟩
  · rw [bind_app, hbuild]
    exact hsend'
  · rw [hout, hbits]

end Zlib.Trees.Proofs
