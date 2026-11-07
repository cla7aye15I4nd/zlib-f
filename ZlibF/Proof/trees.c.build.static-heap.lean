import ZlibF.Proof.«trees.c.build.static-force»
import ZlibF.Proof.«trees.c.build.weight-start»
import ZlibF.Proof.«trees.c.build.complete»

/-! # Static-cost balance and leaf costs through the actual Huffman heap -/

namespace Zlib.Trees.Proofs
open C Zlib.Trees
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Actual maximum storage and heapify change no frequency or static cost. -/
theorem ws_btSortedStart_static_balance {h0 : Heap} {id : Nat} {tk dk : TK} {d : DeflateState}
    {sref : StaticTreeDescRef} {dd : TreeDesc} {sd : StaticTreeDesc} {length : Nat → UInt16}
    (hdd : (dk.descRef id).get (setD h0 id d) = some dd) (hsd : StaticTreeDescRef.get h0 sref = some sd)
    (hstat : dd.stat_desc = some sref) (htree : dd.dyn_tree = .ref (tk.ref id) 0)
    (he3 : 3 ≤ sd.elems.toInt) (he286 : sd.elems.toInt ≤ 286)
    (hT : sd.elems.toInt ≤ (tk.arr d).size) (hD : sd.elems.toInt ≤ d.depth.size) (hH : d.heap.size = 573)
    (static : BTStatic h0 id sd.static_tree sd.elems.toInt.toNat (some length))
    (coefficient : Nat → Nat) (dummy : ∀ v, v ≤ 2 → coefficient v = (length v).toNat) :
    WS h0 id (btSortedStart (Sp id) (some (dk.descRef id))) d (fun _ result =>
      result.static_len + UInt64.ofNat (btLeafCost tk sd.elems.toInt.toNat coefficient result) =
        d.static_len + UInt64.ofNat (btLeafCost tk sd.elems.toInt.toNat coefficient d)) := by
  unfold btSortedStart
  refine WS.bind' (merge_ws_and
    (ws_btLeavesStart hdd hsd hstat htree he3 he286 hT hD hH static)
    (ws_btLeavesStart_static_balance hdd hsd hstat htree he3 he286 hT hD hH static coefficient dummy)) ?_
  intro a mid ⟨⟨tree, statree, elems, leaf, _scan⟩, balance⟩
  rcases a with ⟨pointer, staticPointer, count, maximum⟩
  dsimp only at tree statree elems leaf ⊢
  subst pointer
  subst staticPointer
  subst count
  refine WS.bind' (ws_btOrder_leaf tk dk mid sd.elems.toInt.toNat maximum leaf)
    fun _ result ⟨_leaf, H, fields, _size, _frame, _permutation, _ordered, _descriptor, _minimum⟩ => ?_
  have arrays : tk.arr result = tk.arr mid := by rw [fields]; simp only [tk_arr_heap, tk_arr_setDesc]
  have cost : btLeafCost tk sd.elems.toInt.toNat coefficient result = btLeafCost tk sd.elems.toInt.toNat coefficient mid := by
    unfold btLeafCost btFreq
    rw [arrays]
  have scalar : result.static_len = mid.static_len := by rw [fields]; cases dk <;> rfl
  refine WS.pure' ?_
  rw [scalar, cost]
  exact balance

/-- The actual live leaf queue contains the complete natural weighted
alphabet cost. Its distinctness and coverage come from scan and repair. -/
theorem BTLeafInv.queue_cost {tk : TK} {N : Nat} {mc : Int32} {d : DeflateState}
    (leaf : BTLeafInv tk N mc d) (coefficient : Nat → Nat) :
    GB.rs (fun i => (btFreq tk d (Hn d (i + 1))).toNat * coefficient (Hn d (i + 1))) d.heap_len.toInt.toNat =
      btLeafCost tk N coefficient d := by
  let len := d.heap_len.toInt.toNat
  let P := fun i => d.heap[i + 1]!.toInt.toNat
  let F := fun v => (btFreq tk d v).toNat * coefficient v
  have nonnegative : 0 ≤ d.heap_len.toInt := by have := leaf.count; omega
  have nodes (i : Nat) (bound : i < len) : 0 ≤ d.heap[i + 1]!.toInt ∧ d.heap[i + 1]!.toInt < N := by
    have valid := leaf.valid (i + 1) (by omega) (by dsimp only [len] at bound; omega)
    exact ⟨valid.1, valid.2.1⟩
  have range : ∀ i, i < len → P i < N := by
    intro i bound
    have valid := nodes i bound
    dsimp only [P]
    omega
  have injective : ∀ i j, i < len → j < len → P i = P j → i = j := by
    intro i j ib jb equal
    have ni := nodes i ib
    have nj := nodes j jb
    have words : d.heap[i + 1]! = d.heap[j + 1]! := Int32.toInt_inj.mp (by dsimp only [P] at equal; omega)
    have positions := leaf.injective (i + 1) (j + 1) (by omega) (by dsimp only [len] at ib; omega)
      (by omega) (by dsimp only [len] at jb; omega) words
    omega
  have count (v : Nat) (bound : v < N) : GB.cnt P len v * F v = F v := by
    by_cases zero : btFreq tk d v = 0
    · simp [F, zero]
    · obtain ⟨q, lower, upper, value⟩ := leaf.complete v bound zero
      have position : q - 1 < len := by dsimp only [len]; omega
      have hit : P (q - 1) = v := by
        dsimp only [P]
        rw [Nat.sub_add_cancel lower, value]
        exact Int.toNat_natCast _
      have positive := GB.cnt_pos position hit
      have unique := GB.cnt_le_one P len v injective
      have one : GB.cnt P len v = 1 := by omega
      rw [one, Nat.one_mul]
  change GB.rs (fun i => F (P i)) len = _
  rw [GB.rs_image P F len N range, GB.rs_congr count, rs_eq_mass]
  rfl

/-- After the last merge, the retained non-root leaf costs are exactly
the initial complete alphabet's cost. Created parents and the root have
zero leaf cost. This follows from the actual forest's count observations. -/
theorem BTForest.tail_cost {tk : TK} {prepared merged : DeflateState} {N K : Nat} {mc node : Int32}
    (forest : BTForest tk N K (K - 1) mc prepared node merged) (coefficient : Nat → Nat) :
    GB.rs (fun i => if Hn merged (574 - 2 * K + 1 + i) ≤ mc.toInt.toNat then
      (btFreq tk merged (Hn merged (574 - 2 * K + 1 + i))).toNat *
        coefficient (Hn merged (574 - 2 * K + 1 + i)) else 0) (2 * (K - 1)) =
      btLeafCost tk N coefficient prepared := by
  let F := fun v => if v < N then (btFreq tk merged v).toNat * coefficient v else 0
  have k2 := forest.queue.k2
  have kN := forest.queue.kN
  have n286 := forest.queue.n286
  have maxBounds := forest.max_leaf
  have root := forest.last_root (by omega)
  have rootOutside : N ≤ Hn merged 1 := by unfold Hn; omega
  have rootCost : F (Hn merged 1) = 0 := by dsimp only [F]; rw [if_neg (by omega)]
  have firstCount : K - (K - 1) = 1 := by omega
  have tailStart : 573 - 2 * (K - 1) = 574 - 2 * K + 1 := by omega
  have reverseSum : GB.rs (fun i => F (Hn merged (572 - i))) (2 * (K - 1)) =
      GB.rs (fun i => F (Hn merged (574 - 2 * K + 1 + i))) (2 * (K - 1)) := by
    calc
      _ = GB.rs (fun i => F (Hn merged (574 - 2 * K + 1 + (2 * (K - 1) - 1 - i)))) (2 * (K - 1)) := by
        apply GB.rs_congr
        intro i bound
        congr 2
        omega
      _ = _ := GB.rs_perm (fun i => 2 * (K - 1) - 1 - i)
        (fun i => F (Hn merged (574 - 2 * K + 1 + i))) (2 * (K - 1))
        (fun i bound => by omega) (fun i j ib jb equal => by omega)
  have pool : GB.poolSum (Hn merged) (K - (K - 1)) (2 * (K - 1)) F =
      GB.rs (fun i => F (Hn merged (574 - 2 * K + 1 + i))) (2 * (K - 1)) := by
    unfold GB.poolSum
    rw [firstCount, GB.rs_succ _ 0, GB.rs_zero, Nat.zero_add]
    rw [rootCost, Nat.zero_add]
    exact reverseSum
  have initial : GB.rs (fun i => F (Hn prepared (i + 1))) K = btLeafCost tk N coefficient prepared := by
    have count : prepared.heap_len.toInt.toNat = K := by have := forest.initial_len; omega
    have queue := forest.initial.queue_cost coefficient
    rw [count] at queue
    calc
      _ = GB.rs (fun i => (btFreq tk prepared (Hn prepared (i + 1))).toNat * coefficient (Hn prepared (i + 1))) K := by
        apply GB.rs_congr
        intro i bound
        have valid := forest.initial.valid (i + 1) (by omega) (by have := forest.initial_len; omega)
        have fit : Hn prepared (i + 1) < N := by unfold Hn; omega
        dsimp only [F]
        rw [if_pos fit]
        change (tk.arr merged)[Hn prepared (i + 1)]!.fc.toNat * _ = _
        rw [forest.leaf_freq _ fit]
        rfl
      _ = _ := queue
  have parents : GB.rs (fun i => F (N + i)) (K - 1) = 0 := by
    apply GB.rs_eq_zero
    intro i _
    dsimp only [F]
    rw [if_neg (by omega)]
  have tail : GB.rs (fun i => F (Hn merged (574 - 2 * K + 1 + i))) (2 * (K - 1)) =
      GB.rs (fun i => if Hn merged (574 - 2 * K + 1 + i) ≤ mc.toInt.toNat then
        (btFreq tk merged (Hn merged (574 - 2 * K + 1 + i))).toNat *
          coefficient (Hn merged (574 - 2 * K + 1 + i)) else 0) (2 * (K - 1)) := by
    apply GB.rs_congr
    intro i bound
    have kind := forest.kind (574 - 2 * K + 1 + i) (Or.inr ⟨by omega, by omega⟩)
    dsimp only [F]
    by_cases leaf : Hn merged (574 - 2 * K + 1 + i) ≤ mc.toInt.toNat
    · rw [if_pos leaf, if_pos (by omega)]
    · rw [if_neg leaf, if_neg (by omega)]
  calc
    _ = GB.rs (fun i => F (Hn merged (574 - 2 * K + 1 + i))) (2 * (K - 1)) := tail.symm
    _ = GB.poolSum (Hn merged) (K - (K - 1)) (2 * (K - 1)) F := pool.symm
    _ = GB.rs (fun i => F (Hn prepared (i + 1))) K + GB.rs (fun i => F (N + i)) (K - 1) := forest.observations F
    _ = btLeafCost tk N coefficient prepared := by rw [initial, parents, Nat.add_zero]

/-- The actual root store exposes the exact costP sum used by gen_bitlen.
Only the root position is written, and costP visits the non-root interval. -/
theorem ws_btSaveRoot_static_cost {h0 : Heap} {id : Nat} {tk : TK}
    {prepared merged : DeflateState} {N K : Nat} {mc node : Int32}
    (forest : BTForest tk N K (K - 1) mc prepared node merged) (length extra : Nat → Nat) :
    WS h0 id (btSaveRoot (Sp id)) merged (fun _ result =>
      GB.costP (Hn result) (574 - 2 * K) mc.toInt.toNat (frn (tk.arr result)) length extra (2 * (K - 1)) =
        btLeafCost tk N (fun v => length v + extra v) prepared) := by
  have k2 := forest.queue.k2
  have kN := forest.queue.kN
  have n286 := forest.queue.n286
  have size := forest.queue.heap
  have maximum := forest.queue.max
  have cost := forest.tail_cost (fun v => length v + extra v)
  refine WS.mono (ws_btSaveRoot merged (by omega) (by omega) (by omega) (by omega)) ?_
  intro _ result ⟨hm, decreased, fields, _size, _root, frame⟩
  have rootIndex : hm.toInt.toNat = 574 - 2 * K := by omega
  have arrays : tk.arr result = tk.arr merged := by rw [fields]; cases tk <;> rfl
  have positions (i : Nat) (bound : i < 2 * (K - 1)) :
      Hn result (574 - 2 * K + 1 + i) = Hn merged (574 - 2 * K + 1 + i) := by
    unfold Hn
    rw [frame _ (by omega)]
  calc
    _ = GB.rs (fun i => if Hn merged (574 - 2 * K + 1 + i) ≤ mc.toInt.toNat then
        (btFreq tk merged (Hn merged (574 - 2 * K + 1 + i))).toNat *
          (length (Hn merged (574 - 2 * K + 1 + i)) + extra (Hn merged (574 - 2 * K + 1 + i))) else 0)
          (2 * (K - 1)) := by
      unfold GB.costP
      apply GB.rs_congr
      intro i bound
      rw [positions i bound]
      simp only [frn, arrays, btFreq]
    _ = _ := cost

theorem BTForestFrame.static_len {tk : TK} {before after : DeflateState}
    (frame : BTForestFrame tk before after) : after.static_len = before.static_len := by
  obtain ⟨T, H, D, hl, hm, fields, _rest⟩ := frame
  rw [fields]
  cases tk <;> rfl

theorem BTBuilt.leaf_cost {tk : TK} {N K : Nat} {mc : Int32} {prepared built : DeflateState}
    (tree : BTBuilt tk N K mc prepared built) (coefficient : Nat → Nat) :
    btLeafCost tk N coefficient built = btLeafCost tk N coefficient prepared := by
  apply mass_congr
  intro v bound
  unfold btFreq
  rw [tree.leaf_freq v bound]

/-- The complete actual heap prefix establishes the unsigned static-cost
balance and identifies gen_bitlen's exact static sum with the same leaf
cost. Only possible dummy indices need their extra-bit coefficient zero. -/
theorem ws_btHeap_static_cost {h0 : Heap} {id : Nat} {tk dk : TK} {d : DeflateState}
    {sref : StaticTreeDescRef} {dd : TreeDesc} {sd : StaticTreeDesc} {length : Nat → UInt16}
    (hdd : (dk.descRef id).get (setD h0 id d) = some dd) (hsd : StaticTreeDescRef.get h0 sref = some sd)
    (hstat : dd.stat_desc = some sref) (htree : dd.dyn_tree = .ref (tk.ref id) 0)
    (he3 : 3 ≤ sd.elems.toInt) (he286 : sd.elems.toInt ≤ 286)
    (hT : 2 * sd.elems.toInt.toNat - 1 ≤ (tk.arr d).size) (hTbig : (tk.arr d).size ≤ 600)
    (hD : 2 * sd.elems.toInt.toNat - 1 ≤ d.depth.size) (hH : d.heap.size = 573) (hB : d.bl_count.size = 16)
    (static : BTStatic h0 id sd.static_tree sd.elems.toInt.toNat (some length))
    (extra : Nat → Nat) (dummy : ∀ v, v ≤ 2 → extra v = 0) :
    WS h0 id (btHeap (Sp id) (some (dk.descRef id))) d (fun a result =>
      a.1 = .ref (tk.ref id) 0 ∧ ∃ (prepared : DeflateState) (K : Nat),
        BTBuilt tk sd.elems.toInt.toNat K a.2 prepared result ∧
        (dk.descRef id).get (setD h0 id result) = some { dd with max_code := a.2 } ∧
        result.bl_count.size = 16 ∧ (tk.arr result).size ≤ 600 ∧
        result.static_len + UInt64.ofNat (btLeafCost tk sd.elems.toInt.toNat (fun v => (length v).toNat + extra v) result) =
          d.static_len + UInt64.ofNat (btLeafCost tk sd.elems.toInt.toNat (fun v => (length v).toNat + extra v) d) ∧
        GB.costP (Hn result) (574 - 2 * K) a.2.toInt.toNat (frn (tk.arr result))
          (fun v => (length v).toNat) extra (2 * (K - 1)) =
          btLeafCost tk sd.elems.toInt.toNat (fun v => (length v).toNat + extra v) result) := by
  have capacity : sd.elems.toInt ≤ (tk.arr d).size := by omega
  have depth : sd.elems.toInt ≤ d.depth.size := by omega
  have dummyCost : ∀ v, v ≤ 2 → (length v).toNat + extra v = (length v).toNat := by
    intro v bound
    rw [dummy v bound, Nat.add_zero]
  unfold btHeap btMergedStart
  simp only [M_bind_assoc, M_pure_bind]
  refine WS.bind' (merge_ws_and
    (merge_ws_and
      (ws_btSortedStart hdd hsd hstat htree he3 he286 capacity depth hH static)
      (ws_btSortedStart_sizes hdd hsd hstat htree he3 he286 capacity depth hH static))
    (merge_ws_and
      (ws_btSortedStart_bl_count hdd hsd hstat htree he3 he286 capacity depth hH static)
      (ws_btSortedStart_static_balance hdd hsd hstat htree he3 he286 capacity depth hH static
        (fun v => (length v).toNat + extra v) dummyCost))) ?_
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
  refine WS.bind' (merge_ws_and (ws_btSaveRoot_forest forestM frameM)
    (ws_btSaveRoot_static_cost forestM (fun v => (length v).toNat) extra)) ?_
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
  have costBuilt := builtTree.leaf_cost (fun v => (length v).toNat + extra v)
  refine WS.pure' ⟨rfl, prepared, prepared.heap_len.toInt.toNat, builtTree, descBuilt, countsBuilt,
    by rw [sizeBuilt, treeSize]; exact hTbig, ?_, ?_⟩
  · rw [builtTree.frame.static_len, costBuilt]
    exact balance
  · rw [costBuilt]
    exact sumCost

end Zlib.Trees.Proofs
