import ZlibF.Proof.«trees.c.build.fib-step»

/-! # Values retained by every actual Huffman merge -/

namespace Zlib.Trees.Proofs
open C Zlib.Trees
set_option autoImplicit false

/-- Numeric parents use increasing alphabet offsets. Their two children
remain in the descending heap tail. Natural sums require the proved weight
budget. Depth updates retain the source's UInt8 wrap until a later depth
bound rules it out. No mathematical Huffman execution is assumed here. -/
structure BTMergeValues (tk : TK) (N j : Nat) (d : DeflateState) : Prop where
  sum : ∀ a, a < j → (btFreq tk d (N + a)).toNat =
    (btFreq tk d (Hn d (572 - 2 * a))).toNat + (btFreq tk d (Hn d (571 - 2 * a))).toNat
  depth : ∀ a, a < j → d.depth[N + a]!.toNat =
    (max d.depth[Hn d (572 - 2 * a)]!.toNat d.depth[Hn d (571 - 2 * a)]!.toNat + 1) % 256

theorem BTMergeValues.initial (tk : TK) (N : Nat) (d : DeflateState) : BTMergeValues tk N 0 d :=
  ⟨by intros; omega, by intros; omega⟩

/-- One complete actual merge adds a natural parent-sum equation and the
exact source depth recurrence. Every earlier equation survives, including
its retained child indices. The child-sum bound is derived from the queue. -/
theorem ws_btMergeBody_values {h0 : Heap} {id : Nat} {tk : TK} {d0 d : DeflateState}
    {N K j : Nat} {mc node : Int32} (hi : BTForest tk N K j mc d0 node d)
    (more : j + 1 < K) (total : btQueueWeight tk d (K - j) < 2 ^ 16)
    (history : BTMergeValues tk N j d) :
    WS h0 id (btMergeBody (Sp id) (.ref (tk.ref id) 0) node) d
      (fun _ e => BTMergeValues tk N (j + 1) e) := by
  have counter := hi.queue.counter
  have len := hi.queue.len
  have max := hi.queue.max
  have size := hi.queue.heap
  have trees := hi.queue.tree
  have depths := hi.queue.depth
  have stage := hi.queue.stage
  have kN := hi.queue.kN
  have n286 := hi.queue.n286
  have parent : NV (tk.arr d) d.depth node := ⟨by omega, by omega, by omega⟩
  refine WS.mono (ws_btMergeBody_forest tk d (K - j) node len
    (by omega) (by omega) (by omega) (by omega) (by omega) parent (by omega)
    (fun i a b => hi.queue.valid i a (by omega))
    (fun i i' a b c e => hi.queue.injective i i' a (by omega) c (by omega)) hi.queue.order) ?_
  intro next e ⟨_counter, n, m, distinct, ⟨pn, pnlo, pnhi, first⟩,
    ⟨pm, pmlo, pmhi, second⟩, _len, _boundary, keepn, keepm, tail, tree, depth, _root, _counts⟩
  have nv := hi.queue.valid pn pnlo (by omega)
  have mv := hi.queue.valid pm pmlo (by omega)
  rw [← first] at nv
  rw [← second] at mv
  have hn : NV (tk.arr d) d.depth n := ⟨nv.1, by omega, by omega⟩
  have hm : NV (tk.arr d) d.depth m := ⟨mv.1, by omega, by omega⟩
  have different : pn ≠ pm := by
    intro equal
    exact distinct (first.trans (equal ▸ second.symm))
  have pair := GB.two_le_rs
    (fun i => (btFreq tk d d.heap[i + 1]!.toInt.toNat).toNat)
    (K - j) (pn - 1) (pm - 1) (by omega) (by omega) (by omega)
  simp only [Nat.sub_add_cancel pnlo, Nat.sub_add_cancel pmlo] at pair
  rw [← first, ← second] at pair
  have nowrap : (btFreq tk d n.toInt.toNat).toNat + (btFreq tk d m.toInt.toNat).toNat < 2 ^ 16 := by
    unfold btQueueWeight at total
    omega
  have frequencies (v : Nat) : btFreq tk e v =
      if v = node.toInt.toNat then btFreq tk d n.toInt.toNat + btFreq tk d m.toInt.toNat
      else btFreq tk d v := by
    unfold btFreq
    rw [tree, btParentState_fc tk d n m node hn hm parent]
  have depthCells (v : Nat) : e.depth[v]! =
      if v = node.toInt.toNat then
        (if d.depth[n.toInt.toNat]! ≥ d.depth[m.toInt.toNat]! then
          d.depth[n.toInt.toNat]! else d.depth[m.toInt.toNat]!) + 1
      else d.depth[v]! := by
    rw [depth, btParentState_depth tk d n m node parent]
  have pnIndex : (d.heap_max.toInt - 1).toNat = 572 - 2 * j := by omega
  have pmIndex : (d.heap_max.toInt - 2).toNat = 571 - 2 * j := by omega
  rw [pnIndex] at keepn
  rw [pmIndex] at keepm
  have newn : Hn e (572 - 2 * j) = n.toInt.toNat := congrArg (fun x : Int32 => x.toInt.toNat) keepn
  have newm : Hn e (571 - 2 * j) = m.toInt.toNat := congrArg (fun x : Int32 => x.toInt.toNat) keepm
  have oldTail (q : Nat) (lower : 573 - 2 * j ≤ q) : Hn e q = Hn d q := by
    exact congrArg (fun x : Int32 => x.toInt.toNat) (tail q (by omega))
  have oldNode (q : Nat) (lower : 573 - 2 * j ≤ q) (upper : q < 573) :
      Hn d q < node.toInt.toNat := by
    have valid := hi.tail_valid q lower upper
    unfold Hn
    omega
  have newNode : node.toInt.toNat = N + j := by omega
  refine ⟨?_, ?_⟩
  · intro a bound
    by_cases last : a = j
    · subst a
      rw [newn, newm, frequencies, if_pos (by omega), frequencies,
        if_neg (by omega), frequencies, if_neg (by omega), UInt16.toNat_add, Nat.mod_eq_of_lt nowrap]
    · have before : a < j := by omega
      have qn : 573 - 2 * j ≤ 572 - 2 * a := by omega
      have qm : 573 - 2 * j ≤ 571 - 2 * a := by omega
      have qnTop : 572 - 2 * a < 573 := by omega
      have qmTop : 571 - 2 * a < 573 := by omega
      have vn := oldNode _ qn qnTop
      have vm := oldNode _ qm qmTop
      rw [oldTail _ qn, oldTail _ qm, frequencies, if_neg (by omega),
        frequencies, if_neg (by omega), frequencies, if_neg (by omega)]
      exact history.sum a before
  · intro a bound
    by_cases last : a = j
    · subst a
      rw [newn, newm]
      simp only [depthCells, show N + j = node.toInt.toNat by omega,
        show n.toInt.toNat ≠ node.toInt.toNat by omega,
        show m.toInt.toNat ≠ node.toInt.toNat by omega, ite_true, ite_false]
      by_cases order : d.depth[m.toInt.toNat]! ≤ d.depth[n.toInt.toNat]!
      · rw [if_pos order, UInt8.toNat_add, Nat.max_eq_left (UInt8.le_iff_toNat_le.mp order)]
        rfl
      · have natural : ¬ d.depth[m.toInt.toNat]!.toNat ≤ d.depth[n.toInt.toNat]!.toNat :=
          fun h => order (UInt8.le_iff_toNat_le.mpr h)
        rw [if_neg order, UInt8.toNat_add, Nat.max_eq_right (by omega)]
        rfl
    · have before : a < j := by omega
      have qn : 573 - 2 * j ≤ 572 - 2 * a := by omega
      have qm : 573 - 2 * j ≤ 571 - 2 * a := by omega
      have vn := oldNode _ qn (by omega)
      have vm := oldNode _ qm (by omega)
      rw [oldTail _ qn, oldTail _ qm, depthCells, if_neg (by omega),
        depthCells, if_neg (by omega), depthCells, if_neg (by omega)]
      exact history.depth a before

/-- All source merges retain their mathematical parent sums and exact
modular depth recurrence on one returned heap. The invariant also carries
the actual forest and conserved queue budget needed by each next merge. -/
theorem ws_btMergeLoop_values {h0 : Heap} {id : Nat} {tk : TK} {d : DeflateState}
    {N K : Nat} {mc node : Int32} (hi : BTForest tk N K 0 mc d node d)
    (total : btQueueWeight tk d K < 2 ^ 16) :
    WS h0 id (btMergeLoop (Sp id) (.ref (tk.ref id) 0) node) d (fun next e =>
      BTForest tk N K (K - 1) mc d next e ∧ BTForestFrame tk d e ∧ e.heap_len.toInt = 1 ∧
        (btFreq tk e e.heap[1]!.toInt.toNat).toNat = btQueueWeight tk d K ∧
        BTMergeValues tk N (K - 1) e) := by
  let Inv : Int32 → DeflateState → Prop := fun node e =>
    ∃ j : Nat, BTForest tk N K j mc d node e ∧ BTForestFrame tk d e ∧ j + 1 < K ∧
      btQueueWeight tk e (K - j) = btQueueWeight tk d K ∧ BTMergeValues tk N j e
  let Q : Int32 → DeflateState → Prop := fun node e =>
    BTForest tk N K (K - 1) mc d node e ∧ BTForestFrame tk d e ∧ e.heap_len.toInt = 1 ∧
      (btFreq tk e e.heap[1]!.toInt.toNat).toNat = btQueueWeight tk d K ∧ BTMergeValues tk N (K - 1) e
  unfold btMergeLoop
  refine WS.cdoWhile2 Inv (fun _ e => e.heap_len.toInt.toNat) Q ?_
    ⟨0, hi, BTForestFrame.refl tk d, by have := hi.queue.k2; omega, rfl, BTMergeValues.initial tk N d⟩
    (by have := hi.queue.len; have := hi.queue.kN; have := hi.queue.n286; dsimp only [fuel]; omega)
  intro current e ⟨j, hj, hfr, more, weight, values⟩
  have budget : btQueueWeight tk e (K - j) < 2 ^ 16 := by rw [weight]; exact total
  refine WS.mono (merge_ws_and (merge_ws_and
    (merge_ws_and (ws_btMergeBody_forest_inv hj more) (ws_btMergeBody_frame hj.queue more))
    (ws_btMergeBody_weight hj more budget)) (ws_btMergeBody_values hj more budget values)) ?_
  intro next e' ⟨⟨⟨hj', hfr'⟩, conserved⟩, values'⟩
  have finalWeight := conserved.trans weight
  have frame := hfr.trans hfr'
  refine WS.bind' ws_rd fun got e'' ⟨hgot, he''⟩ => ?_
  subst e''; subst got
  have len := hj'.queue.len
  have stage := hj'.queue.stage
  have k2 := hj'.queue.k2
  by_cases cont : e'.heap_len.toInt ≥ 2
  · have nextStage : j + 1 + 1 < K := by omega
    refine WS.pure' (Or.inr ⟨by simp only [cont, decide_true],
      ⟨j + 1, hj', frame, nextStage, finalWeight, values'⟩, ?_⟩)
    have oldLen := hj.queue.len
    omega
  · have endStage : j + 1 = K - 1 := by omega
    have singleton : K - (j + 1) = 1 := by omega
    rw [singleton] at finalWeight
    have rootWeight : (btFreq tk e' e'.heap[1]!.toInt.toNat).toNat = btQueueWeight tk d K := by
      simpa only [btQueueWeight, GB.rs_succ, GB.rs_zero, Nat.zero_add] using finalWeight
    refine WS.pure' (Or.inl ⟨by simp only [cont, decide_false], ?_⟩)
    change Q next e'
    rw [endStage] at hj' values'
    exact ⟨hj', frame, by omega, rootWeight, values'⟩

/-- The last source store adds only the root position below the old child
tail. Every parent sum and depth equation therefore survives unchanged. -/
theorem ws_btSaveRoot_values {h0 : Heap} {id : Nat} {tk : TK} {d0 d : DeflateState}
    {N K : Nat} {mc node : Int32} (hi : BTForest tk N K (K - 1) mc d0 node d)
    (values : BTMergeValues tk N (K - 1) d) :
    WS h0 id (btSaveRoot (Sp id)) d (fun _ e => BTMergeValues tk N (K - 1) e) := by
  have k2 := hi.queue.k2
  have kN := hi.queue.kN
  have n286 := hi.queue.n286
  have max := hi.queue.max
  have size := hi.queue.heap
  have len := hi.queue.len
  refine WS.mono (ws_btSaveRoot d (by omega) (by omega) (by omega) (by omega)) ?_
  intro _ e ⟨hm, index, fields, _size, _root, unchanged⟩
  have array : tk.arr e = tk.arr d := by rw [fields]; cases tk <;> rfl
  have depth : e.depth = d.depth := by rw [fields]
  have oldTail (q : Nat) (lower : 573 - 2 * (K - 1) ≤ q) : Hn e q = Hn d q := by
    exact congrArg (fun x : Int32 => x.toInt.toNat) (unchanged q (by omega))
  refine ⟨?_, ?_⟩
  · intro a bound
    rw [oldTail _ (by omega), oldTail _ (by omega)]
    simpa only [btFreq, array] using values.sum a bound
  · intro a bound
    rw [oldTail _ (by omega), oldTail _ (by omega), depth]
    exact values.depth a bound

end Zlib.Trees.Proofs
