import ZlibF.Proof.«trees.c.build.optimal-force»

/-! # Optimal-cost balance through the actual source Huffman heap -/

namespace Zlib.Trees.Proofs
open C Zlib.Trees
set_option autoImplicit false

/-- Deterministic source runs combine a universally quantified family of
proved data postconditions on the same returned record. -/
theorem merge_ws_forall {α β : Type} {h0 : Heap} {id : Nat} {m : M α} {d : DeflateState}
    {Q : β → α → DeflateState → Prop} (witness : β)
    (all : ∀ b, WS h0 id m d (Q b)) :
    WS h0 id m d (fun a result => ∀ b, Q b a result) := by
  obtain ⟨a, result, run, _initial⟩ := all witness
  refine ⟨a, result, run, ?_⟩
  intro b
  obtain ⟨other, state, otherRun, property⟩ := all b
  have same := Except.ok.inj (run.symm.trans otherRun)
  have values : a = other := congrArg Prod.fst same
  have records : result = state := by
    have heapState := congrArg (fun p => p.2.dstates id) same
    simp only [setD_dstates_same] at heapState
    exact Option.some.inj heapState
  subst other
  subst state
  exact property

/-- Heapify and descriptor storage change neither the leaf frequencies
nor the optimal counter. The original repair balance remains available
for the lengths that actual bit-length generation will construct. -/
theorem ws_btSortedStart_optimal_balance {h0 : Heap} {id : Nat} {tk dk : TK} {d : DeflateState}
    {sref : StaticTreeDescRef} {dd : TreeDesc} {sd : StaticTreeDesc} {sl : Option (Nat → UInt16)}
    (hdd : (dk.descRef id).get (setD h0 id d) = some dd) (hsd : StaticTreeDescRef.get h0 sref = some sd)
    (hstat : dd.stat_desc = some sref) (htree : dd.dyn_tree = .ref (tk.ref id) 0)
    (he3 : 3 ≤ sd.elems.toInt) (he286 : sd.elems.toInt ≤ 286)
    (hT : sd.elems.toInt ≤ (tk.arr d).size) (hD : sd.elems.toInt ≤ d.depth.size) (hH : d.heap.size = 573)
    (static : BTStatic h0 id sd.static_tree sd.elems.toInt.toNat sl) :
    WS h0 id (btSortedStart (Sp id) (some (dk.descRef id))) d (fun _ result =>
      ∀ (length extra : Nat → Nat) (L : Nat),
        (∀ n, n < sd.elems.toInt.toNat → length n ≤ L) →
        (∀ n, n < sd.elems.toInt.toNat → (length n ≠ 0 ↔ (btFreq tk result n).toNat ≠ 0)) →
        GB.rs (fun n => if length n ≠ 0 then 2 ^ (L - length n) else 0) sd.elems.toInt.toNat = 2 ^ L →
        (∀ n, n ≤ 2 → extra n = 0) →
        result.opt_len + UInt64.ofNat (btLeafCost tk sd.elems.toInt.toNat (fun n => length n + extra n) result) =
          d.opt_len + UInt64.ofNat (btLeafCost tk sd.elems.toInt.toNat (fun n => length n + extra n) d)) := by
  unfold btSortedStart
  refine WS.bind' (merge_ws_and
    (ws_btLeavesStart hdd hsd hstat htree he3 he286 hT hD hH static)
    (ws_btLeavesStart_optimal_balance hdd hsd hstat htree he3 he286 hT hD hH static)) ?_
  intro a mid ⟨⟨tree, statree, elems, leaf, _scan⟩, balance⟩
  rcases a with ⟨pointer, staticPointer, count, maximum⟩
  dsimp only at tree statree elems leaf ⊢
  subst pointer
  subst staticPointer
  subst count
  refine WS.bind' (ws_btOrder_leaf tk dk mid sd.elems.toInt.toNat maximum leaf)
    fun _ result ⟨_leaf, H, fields, _size, _frame, _permutation, _ordered, _descriptor, _minimum⟩ => ?_
  have arrays : tk.arr result = tk.arr mid := by rw [fields]; simp only [tk_arr_heap, tk_arr_setDesc]
  have counter : result.opt_len = mid.opt_len := by rw [fields]; cases dk <;> rfl
  refine WS.pure' ?_
  intro length extra L bound used kraft extraZero
  have usedMid : ∀ n, n < sd.elems.toInt.toNat →
      (length n ≠ 0 ↔ (btFreq tk mid n).toNat ≠ 0) := by
    simpa only [btFreq, arrays] using used
  have balanced := balance length extra L bound usedMid kraft extraZero
  have cost : btLeafCost tk sd.elems.toInt.toNat (fun n => length n + extra n) result =
      btLeafCost tk sd.elems.toInt.toNat (fun n => length n + extra n) mid := by
    unfold btLeafCost btFreq
    rw [arrays]
  rw [counter, cost]
  exact balanced

theorem BTForestFrame.opt_len {tk : TK} {before after : DeflateState}
    (frame : BTForestFrame tk before after) : after.opt_len = before.opt_len := by
  obtain ⟨T, H, D, hl, hm, fields, _rest⟩ := frame
  rw [fields]
  cases tk <;> rfl

/-- The full actual Huffman heap prefix retains the original optimal
cost balance for every later complete length assignment. The sum used by
real gen_bitlen is identified on the exact saved heap, including dummy
leaves and their counter subtractions. No heap-order or parent property
is left as an assumed callee contract. -/
theorem ws_btHeap_optimal_cost {h0 : Heap} {id : Nat} {tk dk : TK} {d : DeflateState}
    {sref : StaticTreeDescRef} {dd : TreeDesc} {sd : StaticTreeDesc} {sl : Option (Nat → UInt16)}
    (hdd : (dk.descRef id).get (setD h0 id d) = some dd) (hsd : StaticTreeDescRef.get h0 sref = some sd)
    (hstat : dd.stat_desc = some sref) (htree : dd.dyn_tree = .ref (tk.ref id) 0)
    (he3 : 3 ≤ sd.elems.toInt) (he286 : sd.elems.toInt ≤ 286)
    (hT : 2 * sd.elems.toInt.toNat - 1 ≤ (tk.arr d).size) (hTbig : (tk.arr d).size ≤ 600)
    (hD : 2 * sd.elems.toInt.toNat - 1 ≤ d.depth.size) (hH : d.heap.size = 573) (hB : d.bl_count.size = 16)
    (static : BTStatic h0 id sd.static_tree sd.elems.toInt.toNat sl) :
    WS h0 id (btHeap (Sp id) (some (dk.descRef id))) d (fun a result =>
      a.1 = .ref (tk.ref id) 0 ∧ ∃ (prepared : DeflateState) (K : Nat),
        BTBuilt tk sd.elems.toInt.toNat K a.2 prepared result ∧
        (dk.descRef id).get (setD h0 id result) = some { dd with max_code := a.2 } ∧
        result.bl_count.size = 16 ∧ (tk.arr result).size ≤ 600 ∧
        ∀ (length extra : Nat → Nat) (L : Nat),
          (∀ n, n < sd.elems.toInt.toNat → length n ≤ L) →
          (∀ n, n < sd.elems.toInt.toNat → (length n ≠ 0 ↔ (btFreq tk result n).toNat ≠ 0)) →
          GB.rs (fun n => if length n ≠ 0 then 2 ^ (L - length n) else 0) sd.elems.toInt.toNat = 2 ^ L →
          (∀ n, n ≤ 2 → extra n = 0) →
          result.opt_len + UInt64.ofNat (GB.costP (Hn result) (574 - 2 * K) a.2.toInt.toNat
            (frn (tk.arr result)) length extra (2 * (K - 1))) =
            d.opt_len + UInt64.ofNat (btLeafCost tk sd.elems.toInt.toNat (fun n => length n + extra n) d)) := by
  have capacity : sd.elems.toInt ≤ (tk.arr d).size := by omega
  have depth : sd.elems.toInt ≤ d.depth.size := by omega
  unfold btHeap btMergedStart
  simp only [M_bind_assoc, M_pure_bind]
  refine WS.bind' (merge_ws_and
    (merge_ws_and
      (ws_btSortedStart hdd hsd hstat htree he3 he286 capacity depth hH static)
      (ws_btSortedStart_sizes hdd hsd hstat htree he3 he286 capacity depth hH static))
    (merge_ws_and
      (ws_btSortedStart_bl_count hdd hsd hstat htree he3 he286 capacity depth hH static)
      (ws_btSortedStart_optimal_balance hdd hsd hstat htree he3 he286 capacity depth hH static))) ?_
  intro a prepared ⟨⟨⟨pointer, statree, elems, leaf, two, maximum, descriptor, ordered, _minimum⟩, treeSize, depthSize⟩,
    countsSize, balance⟩
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
  have sumAll : WS h0 id (btSaveRoot (Sp id)) merged (fun _ built =>
      ∀ length extra : Nat → Nat,
        GB.costP (Hn built) (574 - 2 * prepared.heap_len.toInt.toNat) mc.toInt.toNat
          (frn (tk.arr built)) length extra (2 * (prepared.heap_len.toInt.toNat - 1)) =
          btLeafCost tk sd.elems.toInt.toNat (fun n => length n + extra n) prepared) := by
    refine WS.mono (merge_ws_forall ((fun _ : Nat => 0), (fun _ : Nat => 0))
      (fun pair => ws_btSaveRoot_static_cost forestM pair.1 pair.2)) ?_
    intro _ built all
    intro length extra
    exact all (length, extra)
  refine WS.bind' (merge_ws_and (ws_btSaveRoot_forest forestM frameM) sumAll) ?_
  intro _ built ⟨builtTree, sumCost⟩
  have metadata := builtTree.frame.metadata dk
  have desc : dk.getDesc prepared = { dd with max_code := mc } :=
    Option.some.inj ((bt_desc_get dk h0 id prepared).symm.trans descriptor)
  have descBuilt : (dk.descRef id).get (setD h0 id built) = some { dd with max_code := mc } := by
    rw [bt_desc_get, metadata.1, desc]
  have countsBuilt : built.bl_count.size = 16 := by rw [metadata.2, countsSize]; exact hB
  have sizeBuilt : (tk.arr built).size = (tk.arr prepared).size := by
    obtain ⟨T, H, D, hl, hm, fields, size, _rest⟩ := builtTree.frame
    rw [fields]
    cases tk <;> exact size
  refine WS.pure' ⟨rfl, prepared, prepared.heap_len.toInt.toNat, builtTree, descBuilt, countsBuilt,
    by rw [sizeBuilt, treeSize]; exact hTbig, ?_⟩
  intro length extra L bound used kraft extraZero
  have usedPrepared : ∀ n, n < sd.elems.toInt.toNat →
      (length n ≠ 0 ↔ (btFreq tk prepared n).toNat ≠ 0) := by
    intro n fit
    have same : btFreq tk built n = btFreq tk prepared n := builtTree.leaf_freq n fit
    simpa only [same] using used n fit
  rw [builtTree.frame.opt_len, sumCost length extra]
  exact balance length extra L bound usedPrepared kraft extraZero

end Zlib.Trees.Proofs
