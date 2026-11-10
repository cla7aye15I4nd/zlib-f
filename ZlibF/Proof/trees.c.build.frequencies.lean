import ZlibF.Proof.«trees.c.build.force»
import ZlibF.Proof.«trees.c.build.support»

/-! # Actual dummy-leaf repair preserves every original positive frequency -/

namespace Zlib.Trees.Proofs
open C Zlib.Trees
set_option autoImplicit false

/-- The source chooses a fresh zero-frequency leaf whenever it repairs a
queue shorter than two. Its frequency-one write preserves every previously
nonzero frequency exactly, not merely its support. -/
theorem BTLeafInv.force_frequency {tk : TK} {N : Nat} {mc node hl : Int32}
    {d : DeflateState} {sl : Option (Nat → UInt16)} (leaf : BTLeafInv tk N mc d)
    (short : d.heap_len.toInt < 2) (chosen : node.toInt = (Math.forceNode mc.toInt : Int))
    (fit : node.toInt.toNat < (tk.arr d).size) {v : Nat} (nonzero : btFreq tk d v ≠ 0) :
    btFreq tk (btForceState tk d node hl sl) v = btFreq tk d v := by
  have fresh := Math.forceNode_fresh (btFreq tk d) N leaf.n3 (by have := leaf.count; omega)
  rw [← leaf.maxCode] at fresh
  have nodeNat : node.toInt.toNat = Math.forceNode mc.toInt := by omega
  have different : v ≠ node.toInt.toNat := by
    intro same
    rw [same, nodeNat, fresh.2] at nonzero
    exact nonzero rfl
  rw [btForceState_freq tk d node hl sl fit]
  dsimp only
  rw [if_neg different]

/-- The complete actual repair loop retains the exact original frequencies
of all used symbols. Freshness is derived from each real short-queue state.
It is not an additional frequency-preservation assumption on a callee. -/
theorem ws_btForce_frequencies {h0 : Heap} {id : Nat} (tk : TK) (d : DeflateState) (mc : Int32) (N : Nat)
    (stree : CtDataPtr) (sl : Option (Nat → UInt16)) (hs : BTStatic h0 id stree N sl)
    (hi : BTLeafInv tk N mc d) :
    WS h0 id (btForce (Sp id) (.ref (tk.ref id) 0) stree mc) d (fun r e =>
      BTLeafInv tk N r e ∧ e.heap_len.toInt = max 2 d.heap_len.toInt ∧
        ∃ k : Nat, k ≤ 2 ∧ k = (2 - d.heap_len.toInt).toNat ∧ BTForceTrace tk sl k mc d r e ∧
          ∀ v, btFreq tk d v ≠ 0 → btFreq tk e v = btFreq tk d v) := by
  have hlen0 : 0 ≤ d.heap_len.toInt := by have := hi.count; omega
  let Inv : Int32 → DeflateState → Prop := fun r e =>
    BTLeafInv tk N r e ∧ e.heap_len.toInt ≤ max 2 d.heap_len.toInt ∧
      ∃ k : Nat, k ≤ 2 ∧ e.heap_len.toInt = d.heap_len.toInt + k ∧ BTForceTrace tk sl k mc d r e ∧
        ∀ v, btFreq tk d v ≠ 0 → btFreq tk e v = btFreq tk d v
  let Q : Int32 → DeflateState → Prop := fun r e =>
    BTLeafInv tk N r e ∧ e.heap_len.toInt = max 2 d.heap_len.toInt ∧
      ∃ k : Nat, k ≤ 2 ∧ k = (2 - d.heap_len.toInt).toNat ∧ BTForceTrace tk sl k mc d r e ∧
        ∀ v, btFreq tk d v ≠ 0 → btFreq tk e v = btFreq tk d v
  unfold btForce
  refine WS.cwhile2 Inv (fun _ e => (2 - e.heap_len.toInt).toNat) Q ?_
    ⟨hi, by omega, 0, by omega, by omega, BTForceTrace.nil mc d, fun _ _ => rfl⟩ (by simp only [fuel]; omega)
  intro r e ⟨hie, hupper, k, hk, hlen, htrace, frequency⟩
  refine WS.bind' ws_rd fun dz e1 ⟨hdz, he1⟩ => ?_
  subst e1; subst dz
  by_cases hsmall : e.heap_len.toInt < 2
  · refine WS.pure' (Or.inr ⟨by simp only [hsmall, decide_true], ?_⟩)
    have he0 : 0 ≤ e.heap_len.toInt := by have := hie.count; omega
    have hm := Math.scanMax_bounds (btFreq tk e) N
    rw [← hie.maxCode] at hm
    refine WS.mono (btForceBody_run tk e r N stree sl hs hie.n3 hie.n286 hm.1 hm.2
      hie.tree hie.depth he0 hsmall hie.heap) ?_
    intro r' e' ⟨node, hl, hn, hmc', hhl, he'⟩
    subst e'
    have hnT : node.toInt.toNat < (tk.arr e).size := by
      have hfresh := Math.forceNode_fresh (btFreq tk e) N hie.n3 (by have := hie.count; omega)
      rw [← hie.maxCode] at hfresh
      have := hie.tree
      omega
    have preserving (v : Nat) (nonzero : btFreq tk d v ≠ 0) :
        btFreq tk (btForceState tk e node hl sl) v = btFreq tk d v := by
      have used : btFreq tk e v ≠ 0 := by rw [frequency v nonzero]; exact nonzero
      exact (hie.force_frequency hsmall hn hnT used).trans (frequency v nonzero)
    refine ⟨⟨hie.force hsmall node hl r' sl hn hmc' hhl, ?_, k + 1, by omega, ?_,
      BTForceTrace.snoc node hl htrace hn hnT hmc' hhl, preserving⟩, ?_⟩
    · simp only [btForceState_len]; omega
    · simp only [btForceState_len]; omega
    · simp only [btForceState_len]; omega
  · refine WS.pure' (Or.inl ⟨by simp only [hsmall, decide_false], hie, ?_, k, hk, ?_, htrace, frequency⟩)
    · omega
    · omega

/-- The actual scan preserves frequencies and the actual repair preserves
each original positive frequency. No initial heap contents are restricted. -/
theorem ws_btLeavesStart_frequencies {h0 : Heap} {id : Nat} {tk : TK} {d : DeflateState}
    {r : TreeDescRef} {sref : StaticTreeDescRef} {dd : TreeDesc} {sd : StaticTreeDesc}
    {sl : Option (Nat → UInt16)}
    (hdd : r.get (setD h0 id d) = some dd) (hsd : StaticTreeDescRef.get h0 sref = some sd)
    (hstat : dd.stat_desc = some sref) (htree : dd.dyn_tree = .ref (tk.ref id) 0)
    (he3 : 3 ≤ sd.elems.toInt) (he286 : sd.elems.toInt ≤ 286)
    (hT : sd.elems.toInt ≤ (tk.arr d).size) (hD : sd.elems.toInt ≤ d.depth.size)
    (hH : d.heap.size = 573) (hs : BTStatic h0 id sd.static_tree sd.elems.toInt.toNat sl) :
    WS h0 id (btLeavesStart (Sp id) (some r)) d (fun _ e =>
      ∀ v, v < sd.elems.toInt.toNat → btFreq tk d v ≠ 0 → btFreq tk e v = btFreq tk d v) := by
  unfold btLeavesStart
  refine WS.bind' (ws_btScanStart hdd hsd hstat htree (by omega) he286 hT hD hH)
    fun a mid ⟨ht, hst, he, hscan⟩ => ?_
  rcases a with ⟨tree, stree, elems, mc⟩
  dsimp only at ht hst he hscan ⊢
  subst tree; subst stree; subst elems
  let d0 : DeflateState := { d with heap_len := 0, heap_max := HEAP_SIZE }
  have ht0 : tk.arr d0 = tk.arr d := by cases tk <;> rfl
  have hleaf := BTLeafInv.of_scan hscan (by omega) (by omega)
    (by change _ ≤ (tk.arr d0).size; rw [ht0]; omega) (by change _ ≤ d.depth.size; omega) hH
  refine WS.bind' (ws_btForce_frequencies tk mid mc sd.elems.toInt.toNat sd.static_tree sl hs hleaf)
    fun mc' e ⟨_leaf, _len, _k, _steps, _count, _trace, frequency⟩ => ?_
  refine WS.pure' ?_
  intro v bound nonzero
  have scan := hscan.frequency v (by rw [ht0]; omega)
  change btFreq tk mid v = btFreq tk d0 v at scan
  have same : btFreq tk mid v = btFreq tk d v := by simpa only [btFreq, ht0] using scan
  exact (frequency v (by rw [same]; exact nonzero)).trans same

/-- Descriptor storage and heapify preserve the same exact source
frequencies. This ties original symbol counts to the prepared leaves. -/
theorem ws_btSortedStart_frequencies {h0 : Heap} {id : Nat} {tk dk : TK} {d : DeflateState}
    {sref : StaticTreeDescRef} {dd : TreeDesc} {sd : StaticTreeDesc} {sl : Option (Nat → UInt16)}
    (hdd : (dk.descRef id).get (setD h0 id d) = some dd)
    (hsd : StaticTreeDescRef.get h0 sref = some sd)
    (hstat : dd.stat_desc = some sref) (htree : dd.dyn_tree = .ref (tk.ref id) 0)
    (he3 : 3 ≤ sd.elems.toInt) (he286 : sd.elems.toInt ≤ 286)
    (hT : sd.elems.toInt ≤ (tk.arr d).size) (hD : sd.elems.toInt ≤ d.depth.size)
    (hH : d.heap.size = 573) (hs : BTStatic h0 id sd.static_tree sd.elems.toInt.toNat sl) :
    WS h0 id (btSortedStart (Sp id) (some (dk.descRef id))) d (fun _ e =>
      ∀ v, v < sd.elems.toInt.toNat → btFreq tk d v ≠ 0 → btFreq tk e v = btFreq tk d v) := by
  unfold btSortedStart
  refine WS.bind' (merge_ws_and
    (ws_btLeavesStart hdd hsd hstat htree he3 he286 hT hD hH hs)
    (ws_btLeavesStart_frequencies hdd hsd hstat htree he3 he286 hT hD hH hs)) ?_
  intro a mid ⟨⟨ht, hst, he, leaf, _scan⟩, frequency⟩
  rcases a with ⟨tree, stree, elems, mc⟩
  dsimp only at ht hst he leaf ⊢
  subst tree; subst stree; subst elems
  refine WS.bind' (ws_btOrder_leaf tk dk mid sd.elems.toInt.toNat mc leaf) ?_
  intro _ e ⟨_leaf, H, fields, _size, _frame, _permutation, _ordered, _desc, _minimum⟩
  refine WS.pure' ?_
  intro v bound used
  rw [fields]
  simpa only [btFreq, tk_arr_heap, tk_arr_setDesc] using frequency v bound used

/-- All actual merging and the root store retain the source frequencies
of original used leaves, together with the constructor metadata. -/
theorem ws_btHeap_frequencies {h0 : Heap} {id : Nat} {tk dk : TK} {d : DeflateState}
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
        (∀ v, v < sd.elems.toInt.toNat → btFreq tk d v ≠ 0 → btFreq tk e v = btFreq tk d v) ∧
        ∀ v, v < sd.elems.toInt.toNat → btFreq tk d v ≠ 0 → v ≤ a.2.toInt.toNat ∧
          ∃ q, 574 - 2 * K < q ∧ q < 573 ∧ Hn e q = v) := by
  have hT0 : sd.elems.toInt ≤ (tk.arr d).size := by omega
  have hD0 : sd.elems.toInt ≤ d.depth.size := by omega
  unfold btHeap btMergedStart
  simp only [M_bind_assoc, M_pure_bind]
  refine WS.bind' (merge_ws_and (merge_ws_and (merge_ws_and
    (ws_btSortedStart hdd hsd hstat htree he3 he286 hT0 hD0 hH hs)
    (ws_btSortedStart_sizes hdd hsd hstat htree he3 he286 hT0 hD0 hH hs))
    (ws_btSortedStart_bl_count hdd hsd hstat htree he3 he286 hT0 hD0 hH hs))
    (ws_btSortedStart_frequencies hdd hsd hstat htree he3 he286 hT0 hD0 hH hs))
    fun a prepared ⟨⟨⟨⟨ht, hst, he, hleaf, h2, hm, hdesc, ho, hmin⟩, hTs, hDs⟩, hBs⟩, frequency⟩ => ?_
  rcases a with ⟨tree, stree, elems, mc⟩
  dsimp only at ht hst he hleaf hdesc ⊢
  subst tree; subst stree; subst elems
  have hcnt := hleaf.count
  have hKN := Math.scanCount_le (btFreq tk prepared) sd.elems.toInt.toNat
  have hI := BTForest.of_leaf hleaf h2 hm (node := sd.elems) (by omega)
    (by rw [hTs]; omega) (by rw [hDs]; omega) ho
  refine WS.bind' (ws_btMergeLoop_forest hI) fun next merged ⟨hforest, hframe, hlen⟩ => ?_
  refine WS.bind' (merge_ws_and (ws_btSaveRoot_forest hforest hframe)
    (ws_btSaveRoot_support hforest)) fun _ e ⟨hbuilt, supported⟩ => ?_
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
    by rw [heT, hTs]; exact hTbig, ?_, ?_⟩
  · intro v bound nonzero
    have preserved : btFreq tk e v = btFreq tk prepared v := hbuilt.leaf_freq v bound
    exact preserved.trans (frequency v bound nonzero)
  · intro v bound nonzero
    exact supported v bound (by rw [frequency v bound nonzero]; exact nonzero)

end Zlib.Trees.Proofs
