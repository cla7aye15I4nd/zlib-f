import ZlibF.Proof.«trees.c.build.static»

/-! # trees.c: original nonzero frequencies obtain usable codes -/

namespace Zlib.Trees.Proofs
open C Zlib.Trees

/-- The actual first scan changes only code lengths, so every represented
frequency is retained. -/
theorem BTScanInv.frequency {tk : TK} {d e : DeflateState} {N : Nat} {mc : Int32}
    (hi : BTScanInv tk d N mc e) (v : Nat) (hv : v < (tk.arr d).size) :
    btFreq tk e v = btFreq tk d v := by
  obtain ⟨T, H, D, hl, rfl, hT, hH, hD, hlen, hmax, hcells, rest⟩ := hi
  unfold btFreq
  rw [btScanState_tree, hcells v (by omega)]
  split <;> rfl

/-- A dummy-leaf update writes frequency one. Thus it cannot erase any
original nonzero frequency, even without using freshness of the dummy. -/
theorem BTForceTrace.nonzero {tk : TK} {sl : Option (Nat → UInt16)}
    {k : Nat} {mc0 mc : Int32} {d0 d : DeflateState} (hi : BTForceTrace tk sl k mc0 d0 mc d)
    (v : Nat) (hv : btFreq tk d0 v ≠ 0) : btFreq tk d v ≠ 0 := by
  induction hi with
  | nil => exact hv
  | snoc node hl before hn hnT hm hhl ih =>
    rw [btForceState_freq tk _ node hl sl hnT]
    dsimp only
    split
    · decide +kernel
    · exact ih hv

/-- The complete actual prepared-leaf prefix retains every original
positive-frequency symbol. No assumption about the original heap or lengths
is used, and the repair's frequency writes are included. -/
theorem ws_btSortedStart_nonzero {h0 : Heap} {id : Nat} {tk dk : TK} {d : DeflateState}
    {sref : StaticTreeDescRef} {dd : TreeDesc} {sd : StaticTreeDesc} {sl : Option (Nat → UInt16)}
    (hdd : (dk.descRef id).get (setD h0 id d) = some dd)
    (hsd : StaticTreeDescRef.get h0 sref = some sd)
    (hstat : dd.stat_desc = some sref) (htree : dd.dyn_tree = .ref (tk.ref id) 0)
    (he3 : 3 ≤ sd.elems.toInt) (he286 : sd.elems.toInt ≤ 286)
    (hT : sd.elems.toInt ≤ (tk.arr d).size) (hD : sd.elems.toInt ≤ d.depth.size)
    (hH : d.heap.size = 573) (hs : BTStatic h0 id sd.static_tree sd.elems.toInt.toNat sl) :
    WS h0 id (btSortedStart (Sp id) (some (dk.descRef id))) d (fun _ e =>
      ∀ v < sd.elems.toInt.toNat, btFreq tk d v ≠ 0 → btFreq tk e v ≠ 0) := by
  unfold btSortedStart
  refine WS.bind' (ws_btLeavesStart hdd hsd hstat htree he3 he286 hT hD hH hs)
    fun a mid ⟨ht, hst, he, hleaf, scan, scanMc, k, hscan, hlen, hk, hkexact, htrace⟩ => ?_
  rcases a with ⟨tree, stree, elems, mc⟩
  dsimp only at ht hst he hleaf htrace ⊢
  subst tree; subst stree; subst elems
  have hused : ∀ v < sd.elems.toInt.toNat, btFreq tk d v ≠ 0 → btFreq tk mid v ≠ 0 := by
    intro v hv hfv
    have hreset : tk.arr { d with heap_len := 0, heap_max := HEAP_SIZE } = tk.arr d := by cases tk <;> rfl
    have hscanfr := hscan.frequency v (by rw [hreset]; omega)
    change btFreq tk scan v = btFreq tk { d with heap_len := 0, heap_max := HEAP_SIZE } v at hscanfr
    have hscanfr' : btFreq tk scan v = btFreq tk d v := by
      simpa only [btFreq, hreset] using hscanfr
    exact htrace.nonzero v (by rw [hscanfr']; exact hfv)
  refine WS.bind' (ws_btOrder_leaf tk dk mid sd.elems.toInt.toNat mc hleaf)
    fun _ e ⟨hleaf', H, he, hsH, hf, hp, ho, hdesc', hmin⟩ => ?_
  subst e
  refine WS.pure' ?_
  intro v hv hfv
  simp only [btFreq, tk_arr_heap, tk_arr_setDesc]
  exact hused v hv hfv

/-- Every used prepared leaf remains in the non-root retained interval
after the actual root store. Completeness is derived from the forest count,
and the unique root is an internal node. -/
theorem ws_btSaveRoot_support {h0 : Heap} {id : Nat} {tk : TK} {d0 d : DeflateState}
    {N K : Nat} {mc node : Int32} (hi : BTForest tk N K (K - 1) mc d0 node d) :
    WS h0 id (btSaveRoot (Sp id)) d (fun _ e =>
      ∀ v < N, btFreq tk d0 v ≠ 0 → v ≤ mc.toInt.toNat ∧
        ∃ q : Nat, 574 - 2 * K < q ∧ q < 573 ∧ Hn e q = v) := by
  have hK2 := hi.queue.k2
  have hKN := hi.queue.kN
  have hNb := hi.queue.n286
  have hsize := hi.queue.heap
  have hlen := hi.queue.len
  have hmax := hi.queue.max
  have hlast := hi.last_root (by omega)
  have hrootN : N ≤ Hn d 1 := by unfold Hn; omega
  refine WS.mono (ws_btSaveRoot d (by omega) (by omega) (by omega) (by omega)) ?_
  intro _ e ⟨hm, hhm, he, hsz, hroot, hframe⟩
  intro v hv hfv
  obtain ⟨q, hq, hqv⟩ := hi.used_position v hv hfv
  have hqtail : 573 - 2 * (K - 1) ≤ q ∧ q < 573 := by
    rcases hq with hq | hq
    · have hq1 : q = 1 := by omega
      rw [hq1] at hqv
      omega
    · exact hq
  have hvc : v ≤ mc.toInt.toNat := by
    rcases hi.kind q (Or.inr hqtail) with hqmc | hqN
    · rwa [hqv] at hqmc
    · omega
  refine ⟨hvc, q, by omega, hqtail.2, ?_⟩
  unfold Hn
  rw [hframe q (by omega)]
  exact hqv

/-- Exact final-code stores preserve every length, including cells outside
the symbol range and indices outside both arrays. -/
theorem code_stores_lengths {tk : TK} {mid e : DeflateState} {mc : Int32} {a : Array CtData}
    (he : e = tk.setArr mid a) (hs : a.size = (tk.arr mid).size)
    (ha : ∀ i < a.size, a[i]! =
      if i < (mc.toInt + 1).toNat ∧ (tk.arr mid)[i]!.dl ≠ 0 then
        { (tk.arr mid)[i]! with fc := UInt16.ofNat (Math.storedCode
          (fun b => mid.bl_count[b]!.toNat) (fun v => (tk.arr mid)[v]!.dl.toNat) i) }
      else (tk.arr mid)[i]!) :
    ∀ v : Nat, (tk.arr e)[v]!.dl = (tk.arr mid)[v]!.dl := by
  subst e
  intro v
  rw [tk_arr_setArr]
  by_cases hv : v < a.size
  · rw [ha v hv]
    split <;> rfl
  · rw [getElem!_neg a v hv, getElem!_neg (tk.arr mid) v (by omega)]

/-- The actual bit-length result assigns a positive limited length to each
represented non-root leaf. -/
theorem GBDone.supported_length {tk : TK} {built mid : DeflateState} {hm J N maxc L : Nat}
    {xb : Nat → Nat} {slOpt : Option (Nat → Nat)}
    (hshape : GB.PShape (Hn built) hm J N maxc)
    (hdone : GBDone tk built hm J maxc L xb slOpt mid)
    (q v : Nat) (hq1 : hm < q) (hq2 : q < 573) (hqv : Hn built q = v) (hv : v ≤ maxc) :
    1 ≤ (tk.arr mid)[v]!.dl.toNat ∧ (tk.arr mid)[v]!.dl.toNat ≤ L := by
  obtain ⟨T, B, O, S, rfl, hsT, hsB, hfreq, hout, hlengths, rest⟩ := hdone
  rw [tk_arr_mkP1]
  have hi : q - hm - 1 < 2 * J := by have := hshape.hm_eq; omega
  have heq : hm + 1 + (q - hm - 1) = q := by omega
  have hlen := hlengths (q - hm - 1) hi (by rw [heq, hqv]; exact hv)
  rw [heq, hqv] at hlen
  exact hlen


/-- Actual heap construction retains a represented non-root leaf for every
symbol whose frequency was nonzero at function entry. Prepared-state
frequencies are connected back to the original input here. -/
theorem ws_btHeap_supported {h0 : Heap} {id : Nat} {tk dk : TK} {d : DeflateState}
    {sref : StaticTreeDescRef} {dd : TreeDesc} {sd : StaticTreeDesc} {sl : Option (Nat → UInt16)}
    (hdd : (dk.descRef id).get (setD h0 id d) = some dd)
    (hsd : StaticTreeDescRef.get h0 sref = some sd)
    (hstat : dd.stat_desc = some sref) (htree : dd.dyn_tree = .ref (tk.ref id) 0)
    (he3 : 3 ≤ sd.elems.toInt) (he286 : sd.elems.toInt ≤ 286)
    (hT : 2 * sd.elems.toInt.toNat - 1 ≤ (tk.arr d).size) (hTbig : (tk.arr d).size ≤ 600)
    (hD : 2 * sd.elems.toInt.toNat - 1 ≤ d.depth.size)
    (hH : d.heap.size = 573) (hB : d.bl_count.size = 16)
    (hs : BTStatic h0 id sd.static_tree sd.elems.toInt.toNat sl) :
    WS h0 id (btHeap (Sp id) (some (dk.descRef id))) d (fun a e =>
      a.1 = .ref (tk.ref id) 0 ∧ ∃ (prepared : DeflateState) (K : Nat),
        BTBuilt tk sd.elems.toInt.toNat K a.2 prepared e ∧
        (dk.descRef id).get (setD h0 id e) = some { dd with max_code := a.2 } ∧
        e.bl_count.size = 16 ∧ (tk.arr e).size ≤ 600 ∧
        ∀ v < sd.elems.toInt.toNat, btFreq tk d v ≠ 0 → v ≤ a.2.toInt.toNat ∧
          ∃ q : Nat, 574 - 2 * K < q ∧ q < 573 ∧ Hn e q = v) := by
  have hT0 : sd.elems.toInt ≤ (tk.arr d).size := by omega
  have hD0 : sd.elems.toInt ≤ d.depth.size := by omega
  unfold btHeap btMergedStart
  simp only [M_bind_assoc, M_pure_bind]
  refine WS.bind' (merge_ws_and (merge_ws_and (merge_ws_and
    (ws_btSortedStart hdd hsd hstat htree he3 he286 hT0 hD0 hH hs)
    (ws_btSortedStart_sizes hdd hsd hstat htree he3 he286 hT0 hD0 hH hs))
    (ws_btSortedStart_bl_count hdd hsd hstat htree he3 he286 hT0 hD0 hH hs))
    (ws_btSortedStart_nonzero hdd hsd hstat htree he3 he286 hT0 hD0 hH hs))
    fun a prepared ⟨⟨⟨⟨ht, hst, he, hleaf, h2, hm, hdesc, ho, hmin⟩, hTs, hDs⟩, hBs⟩, hused⟩ => ?_
  rcases a with ⟨tree, stree, elems, mc⟩
  dsimp only at ht hst he hleaf hdesc ⊢
  subst tree; subst stree; subst elems
  have hcnt := hleaf.count
  have hKN := Math.scanCount_le (btFreq tk prepared) sd.elems.toInt.toNat
  have hI := BTForest.of_leaf hleaf h2 hm (node := sd.elems) (by omega)
    (by rw [hTs]; omega) (by rw [hDs]; omega) ho
  refine WS.bind' (ws_btMergeLoop_forest hI) fun next merged ⟨hforest, hframe, hlen⟩ => ?_
  refine WS.bind' (merge_ws_and (ws_btSaveRoot_forest hforest hframe) (ws_btSaveRoot_support hforest))
    fun _ e ⟨hbuilt, hsupport⟩ => ?_
  have hmeta := hbuilt.frame.metadata dk
  have hDesc : dk.getDesc prepared = { dd with max_code := mc } :=
    Option.some.inj ((bt_desc_get dk h0 id prepared).symm.trans hdesc)
  have hDesc' : (dk.descRef id).get (setD h0 id e) = some { dd with max_code := mc } := by
    rw [bt_desc_get, hmeta.1, hDesc]
  have heB : e.bl_count.size = 16 := by rw [hmeta.2, hBs]; exact hB
  have heT : (tk.arr e).size = (tk.arr prepared).size := by
    obtain ⟨T, H, D, hl, hm, he, hT, hH, hD⟩ := hbuilt.frame
    rw [he]
    cases tk <;> exact hT
  refine WS.pure' ⟨rfl, prepared, prepared.heap_len.toInt.toNat, hbuilt, hDesc', heB,
    by rw [heT, hTs]; exact hTbig, ?_⟩
  intro v hv hfv
  exact hsupport v hv (hused v hv hfv)

/-- Every originally used symbol obtains a positive limited length and its
exact stored canonical code. The canonical expression refers to the final
count and length arrays, so no unconstrained intermediate state stands in
for the original-frequency connection. -/
theorem ws_build_tree_used_codes {h0 : Heap} {id : Nat} {tk dk : TK} {d : DeflateState}
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
      ∀ v < sd.elems.toInt.toNat, btFreq tk d v ≠ 0 →
        1 ≤ (tk.arr e)[v]!.dl.toNat ∧ (tk.arr e)[v]!.dl.toNat ≤ sd.max_length.toInt.toNat ∧
        (tk.arr e)[v]!.fc = UInt16.ofNat (Math.storedCode
          (fun b => e.bl_count[b]!.toNat) (fun n => (tk.arr e)[n]!.dl.toNat) v)) := by
  obtain ⟨sl, hsRepair⟩ := hs.repair
  rw [build_tree_eq_heap_codes]
  refine WS.bind' (ws_btHeap_supported hdd hsd hstat htree he3 he286 hT hTbig hD hH hB hsRepair)
    fun a built ⟨ht, prepared, K, hbuilt, hdesc, hBs, hTs, hsupport⟩ => ?_
  rcases a with ⟨tree, mc⟩
  dsimp only at ht hbuilt hdesc hsupport ⊢
  subst tree
  have hctx := hbuilt.bitlen_ctx hs rfl hBs hTs
  have hcodes := ws_btCodes (h0 := h0) (id := id) (tk := tk) (d := built)
    (r := dk.descRef id) (sref := sref) (dd := { dd with max_code := mc }) (sd := sd)
    (hm := 574 - 2 * K) (J := K - 1) (elems := sd.elems.toInt.toNat) (maxc := mc.toInt.toNat)
    (L := sd.max_length.toInt.toNat) (baseN := sd.extra_base.toInt.toNat) (xb := xb) (slOpt := slOpt)
    hdesc hsd hstat htree hctx hbuilt.heap_max hs.length_capacity (by omega) hbuilt.unused
  refine WS.mono hcodes ?_
  intro _ e ⟨mid, hdone, a, he, hsize, hstores⟩
  have hlens := code_stores_lengths he hsize hstores
  have hcounts : e.bl_count = mid.bl_count := by rw [he]; exact tk_setArr_bl_count tk a
  intro v hv hfv
  obtain ⟨hvc, q, hq1, hq2, hqv⟩ := hsupport v hv hfv
  have hlen := hdone.supported_length hbuilt.shape q v hq1 hq2 hqv hvc
  have hpos : (tk.arr mid)[v]!.dl ≠ 0 := by intro hz; rw [hz] at hlen; have hzN : (0 : UInt16).toNat = 0 := rfl; rw [hzN] at hlen; omega
  have hMidSize : (tk.arr mid).size = (tk.arr built).size := by
    obtain ⟨T, B, O, S, rfl, hT, rest⟩ := hdone
    simpa only [tk_arr_mkP1] using hT
  have hvA : v < a.size := by have := hbuilt.capacity; have := hbuilt.k2; omega
  have hvRange : v < (mc.toInt + 1).toNat := by have := hbuilt.max_nonneg; omega
  refine ⟨by rw [hlens]; exact hlen.1, by rw [hlens]; exact hlen.2, ?_⟩
  have hfun : (fun n : Nat => (tk.arr e)[n]!.dl.toNat) = (fun n : Nat => (tk.arr mid)[n]!.dl.toNat) := by
    funext n
    rw [hlens]
  rw [hcounts, hfun, he, tk_arr_setArr, hstores v hvA, if_pos ⟨hvRange, hpos⟩]


/-- A stored canonical value of length at most fifteen is represented
exactly by the 16-bit cell and fits in the declared number of bits. -/
theorem canonical_word_value (tk : TK) (d : DeflateState) (v : Nat)
    (hl : (tk.arr d)[v]!.dl.toNat ≤ 15)
    (hc : (tk.arr d)[v]!.fc = UInt16.ofNat (Math.storedCode
      (fun b => d.bl_count[b]!.toNat) (fun n => (tk.arr d)[n]!.dl.toNat) v)) :
    (tk.arr d)[v]!.fc.toNat = Math.storedCode
      (fun b => d.bl_count[b]!.toNat) (fun n => (tk.arr d)[n]!.dl.toNat) v ∧
    (tk.arr d)[v]!.fc.toNat < 2 ^ (tk.arr d)[v]!.dl.toNat := by
  have hfit := Math.storedCode_lt (fun b => d.bl_count[b]!.toNat) (fun n => (tk.arr d)[n]!.dl.toNat) v
  have hpow : 2 ^ (tk.arr d)[v]!.dl.toNat ≤ 2 ^ 15 := Nat.pow_le_pow_right (by omega) hl
  have hword : Math.storedCode (fun b => d.bl_count[b]!.toNat) (fun n => (tk.arr d)[n]!.dl.toNat) v < 65536 := by
    have h15 : 2 ^ 15 < 65536 := by decide +kernel
    omega
  have hval : (tk.arr d)[v]!.fc.toNat = Math.storedCode
      (fun b => d.bl_count[b]!.toNat) (fun n => (tk.arr d)[n]!.dl.toNat) v := by
    rw [hc, UInt16.toNat_ofNat', Nat.mod_eq_of_lt hword]
  exact ⟨hval, by rw [hval]; exact hfit⟩

/-- Complete actual construction gives every originally used symbol a
positive limited length, an exact untruncated reversed canonical value,
and the value bound consumed by the bit emitter. -/
theorem ws_build_tree_usable_codes {h0 : Heap} {id : Nat} {tk dk : TK} {d : DeflateState}
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
      ∀ v < sd.elems.toInt.toNat, btFreq tk d v ≠ 0 →
        1 ≤ (tk.arr e)[v]!.dl.toNat ∧ (tk.arr e)[v]!.dl.toNat ≤ sd.max_length.toInt.toNat ∧
        (tk.arr e)[v]!.fc.toNat = Math.storedCode
          (fun b => e.bl_count[b]!.toNat) (fun n => (tk.arr e)[n]!.dl.toNat) v ∧
        (tk.arr e)[v]!.fc.toNat < 2 ^ (tk.arr e)[v]!.dl.toNat) := by
  refine WS.mono (ws_build_tree_used_codes hdd hsd hstat htree he3 he286 hT hTbig hD hH hB hs) ?_
  intro _ e hcodes v hv hf
  obtain ⟨hl1, hlL, hc⟩ := hcodes v hv hf
  have hL := hs.length_limit
  have hL0 := hs.length_pos
  obtain ⟨hval, hfit⟩ := canonical_word_value tk e v (by omega) hc
  exact ⟨hl1, hlL, hval, hfit⟩

/-- Actual initialization facts discharge the entire domain for all three
installed dynamic trees. Every originally used symbol receives an exact
canonical word that fits a positive limited length. -/
theorem ws_build_tree_usable_initialized {h0 : Heap} {id : Nat} {d : DeflateState}
    (tk : TK) (hwf : d.WellFormed) (hs : Out.TreesStatic h0.static) (hr : Out.TreesRun0 id d) :
    WS h0 id (build_tree (Sp id) (some (tk.descRef id))) d (fun _ e =>
      ∀ v < tk.buildDesc.elems.toInt.toNat, btFreq tk d v ≠ 0 →
        1 ≤ (tk.arr e)[v]!.dl.toNat ∧ (tk.arr e)[v]!.dl.toNat ≤ tk.buildDesc.max_length.toInt.toNat ∧
        (tk.arr e)[v]!.fc.toNat = Math.storedCode
          (fun b => e.bl_count[b]!.toNat) (fun n => (tk.arr e)[n]!.dl.toNat) v ∧
        (tk.arr e)[v]!.fc.toNat < 2 ^ (tk.arr e)[v]!.dl.toNat) := by
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
  exact ws_build_tree_usable_codes (bt_desc_get tk h0 id d) (trees_build_desc_get hs tk) hstat htree
    he3 he286 hT hTbig hDepth hH hBC (trees_build_static hs tk)

/-- The supported-code result runs on the actual initialized caller heap. -/
theorem build_tree_usable_initialized {h : Heap} {id : Nat} {d : DeflateState}
    (tk : TK) (hd : h.dstates id = some d) (hwf : d.WellFormed)
    (hs : Out.TreesStatic h.static) (hr : Out.TreesRun0 id d) :
    ∃ e : DeflateState, build_tree (Sp id) (some (tk.descRef id)) h = .ok ((), setD h id e) ∧
      ∀ v < tk.buildDesc.elems.toInt.toNat, btFreq tk d v ≠ 0 →
        1 ≤ (tk.arr e)[v]!.dl.toNat ∧ (tk.arr e)[v]!.dl.toNat ≤ tk.buildDesc.max_length.toInt.toNat ∧
        (tk.arr e)[v]!.fc.toNat = Math.storedCode
          (fun b => e.bl_count[b]!.toNat) (fun n => (tk.arr e)[n]!.dl.toNat) v ∧
        (tk.arr e)[v]!.fc.toNat < 2 ^ (tk.arr e)[v]!.dl.toNat := by
  obtain ⟨a, e, he, hresult⟩ := ws_build_tree_usable_initialized tk hwf hs hr
  have ha : a = () := Subsingleton.elim _ _
  subst a
  rw [setD_self hd] at he
  exact ⟨e, he, hresult⟩

end Zlib.Trees.Proofs
