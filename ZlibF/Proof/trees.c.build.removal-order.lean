import ZlibF.Proof.«trees.c.build.minima»

/-! # Nondecreasing removals in the actual Huffman merge loop -/

namespace Zlib.Trees.Proofs
open C Zlib.Trees
set_option autoImplicit false

/-- The descending heap tail records removals in reverse chronological
order. Every adjacent old removal is no heavier than its successor, and
the last removal is no heavier than any current live node. -/
structure BTMergeOrder (tk : TK) (K j : Nat) (d : DeflateState) : Prop where
  tail : ∀ q, 573 - 2 * j ≤ q → q + 1 < 573 →
    (btFreq tk d (Hn d (q + 1))).toNat ≤ (btFreq tk d (Hn d q)).toNat
  queue : 0 < j → ∀ q, 1 ≤ q → q ≤ K - j →
    (btFreq tk d (Hn d (573 - 2 * j))).toNat ≤ (btFreq tk d (Hn d q)).toNat

theorem BTMergeOrder.initial (tk : TK) (K : Nat) (d : DeflateState) : BTMergeOrder tk K 0 d :=
  ⟨by intros; omega, by intros; omega⟩

/-- One actual iteration extends the ordered removal tail. Its two minima
and next-queue lower bound come from actual selection and nonwrapping
parent creation. Earlier tail weights and positions remain unchanged. -/
theorem ws_btMergeBody_order {h0 : Heap} {id : Nat} {tk : TK} {d0 d : DeflateState}
    {N K j : Nat} {mc node : Int32} (hi : BTForest tk N K j mc d0 node d)
    (more : j + 1 < K) (total : btQueueWeight tk d (K - j) < 2 ^ 16)
    (history : BTMergeOrder tk K j d) :
    WS h0 id (btMergeBody (Sp id) (.ref (tk.ref id) 0) node) d
      (fun _ e => BTMergeOrder tk K (j + 1) e) := by
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
  refine WS.mono (merge_ws_and
    (ws_btMergeBody_forest tk d (K - j) node len
      (by omega) (by omega) (by omega) (by omega) (by omega) parent (by omega)
      (fun i a b => hi.queue.valid i a (by omega))
      (fun i i' a b c e => hi.queue.injective i i' a (by omega) c (by omega)) hi.queue.order)
    (ws_btMergeBody_minima tk d (K - j) node len
      (by omega) (by omega) (by omega) (by omega) (by omega) parent (by omega)
      (fun i a b => hi.queue.valid i a (by omega))
      (fun i i' a b c e => hi.queue.injective i i' a (by omega) c (by omega)) hi.queue.order total)) ?_
  intro next e ⟨⟨_counter, n, m, _distinct, ⟨pn, pnlo, pnhi, first⟩,
    ⟨pm, pmlo, pmhi, second⟩, _len, _boundary, keepn, keepm, tail, tree, _depth, _root, _counts⟩,
    n', m', keepn', keepm', nBefore, _minimum, nextQueue⟩
  have sameN : n' = n := keepn'.symm.trans keepn
  have sameM : m' = m := keepm'.symm.trans keepm
  rw [sameN, sameM] at nBefore
  rw [sameM] at nextQueue
  have nv := hi.queue.valid pn pnlo (by omega)
  have mv := hi.queue.valid pm pmlo (by omega)
  rw [← first] at nv
  rw [← second] at mv
  have hn : NV (tk.arr d) d.depth n := ⟨nv.1, by omega, by omega⟩
  have hm : NV (tk.arr d) d.depth m := ⟨mv.1, by omega, by omega⟩
  have oldFreq (v : Nat) (bound : v < node.toInt.toNat) : btFreq tk e v = btFreq tk d v := by
    unfold btFreq
    rw [tree, btParentState_fc tk d n m node hn hm parent, if_neg (by omega)]
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
  refine ⟨?_, ?_⟩
  · intro q lower upper
    by_cases last : q = 571 - 2 * j
    · have successor : q + 1 = 572 - 2 * j := by omega
      rw [successor, last, newn, newm, oldFreq _ (by omega), oldFreq _ (by omega)]
      exact nBefore
    · by_cases firstNew : q = 572 - 2 * j
      · have positive : 0 < j := by omega
        have successor : q + 1 = 573 - 2 * j := by omega
        have before := history.queue positive pn pnlo pnhi
        have firstN : Hn d pn = n.toInt.toNat := congrArg (fun x : Int32 => x.toInt.toNat) first.symm
        rw [firstN] at before
        rw [successor, firstNew, newn, oldTail _ (by omega),
          oldFreq _ (oldNode _ (by omega) (by omega)), oldFreq _ (by omega)]
        exact before
      · have oldLower : 573 - 2 * j ≤ q := by omega
        rw [oldTail _ (by omega), oldTail _ oldLower,
          oldFreq _ (oldNode _ (by omega) upper), oldFreq _ (oldNode _ oldLower (by omega))]
        exact history.tail q oldLower upper
  · intro _positive q lower upper
    have start : 573 - 2 * (j + 1) = 571 - 2 * j := by omega
    rw [start, newm, oldFreq _ (by omega)]
    exact nextQueue q lower (by omega)

/-- Adjacent chronological removal comparisons imply the full reverse
heap-tail order used by the mathematical leaf-chain argument. -/
theorem BTMergeOrder.monotone {tk : TK} {K j : Nat} {d : DeflateState}
    (history : BTMergeOrder tk K j d) {q q' : Nat}
    (lower : 573 - 2 * j ≤ q) (ordered : q ≤ q') (upper : q' < 573) :
    (btFreq tk d (Hn d q')).toNat ≤ (btFreq tk d (Hn d q)).toNat := by
  suffices all : ∀ r, q ≤ r → r < 573 →
      (btFreq tk d (Hn d r)).toNat ≤ (btFreq tk d (Hn d q)).toNat from all q' ordered upper
  intro r
  induction r with
  | zero =>
    intro bound _
    have equal : q = 0 := by omega
    subst q
    exact Nat.le_refl _
  | succ r ih =>
    intro bound upper
    by_cases equal : q = r + 1
    · rw [equal]
      exact Nat.le_refl _
    · exact Nat.le_trans (history.tail r (by omega) upper) (ih (by omega) (by omega))

/-- The complete actual loop produces nondecreasing removals, retaining
its forest, exact root weight and the budget used by every next iteration. -/
theorem ws_btMergeLoop_order {h0 : Heap} {id : Nat} {tk : TK} {d : DeflateState}
    {N K : Nat} {mc node : Int32} (hi : BTForest tk N K 0 mc d node d)
    (total : btQueueWeight tk d K < 2 ^ 16) :
    WS h0 id (btMergeLoop (Sp id) (.ref (tk.ref id) 0) node) d (fun next e =>
      BTForest tk N K (K - 1) mc d next e ∧ BTForestFrame tk d e ∧ e.heap_len.toInt = 1 ∧
        (btFreq tk e e.heap[1]!.toInt.toNat).toNat = btQueueWeight tk d K ∧
        BTMergeOrder tk K (K - 1) e) := by
  let Inv : Int32 → DeflateState → Prop := fun node e =>
    ∃ j : Nat, BTForest tk N K j mc d node e ∧ BTForestFrame tk d e ∧ j + 1 < K ∧
      btQueueWeight tk e (K - j) = btQueueWeight tk d K ∧ BTMergeOrder tk K j e
  let Q : Int32 → DeflateState → Prop := fun node e =>
    BTForest tk N K (K - 1) mc d node e ∧ BTForestFrame tk d e ∧ e.heap_len.toInt = 1 ∧
      (btFreq tk e e.heap[1]!.toInt.toNat).toNat = btQueueWeight tk d K ∧ BTMergeOrder tk K (K - 1) e
  unfold btMergeLoop
  refine WS.cdoWhile2 Inv (fun _ e => e.heap_len.toInt.toNat) Q ?_
    ⟨0, hi, BTForestFrame.refl tk d, by have := hi.queue.k2; omega, rfl, BTMergeOrder.initial tk K d⟩
    (by have := hi.queue.len; have := hi.queue.kN; have := hi.queue.n286; dsimp only [fuel]; omega)
  intro current e ⟨j, hj, hfr, more, weight, values⟩
  have budget : btQueueWeight tk e (K - j) < 2 ^ 16 := by rw [weight]; exact total
  refine WS.mono (merge_ws_and (merge_ws_and
    (merge_ws_and (ws_btMergeBody_forest_inv hj more) (ws_btMergeBody_frame hj.queue more))
    (ws_btMergeBody_weight hj more budget)) (ws_btMergeBody_order hj more budget values)) ?_
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

/-- Saving the root below the removal tail preserves its order. The
remaining singleton queue is at index one and is also unchanged. -/
theorem ws_btSaveRoot_order {h0 : Heap} {id : Nat} {tk : TK} {d0 d : DeflateState}
    {N K : Nat} {mc node : Int32} (hi : BTForest tk N K (K - 1) mc d0 node d)
    (history : BTMergeOrder tk K (K - 1) d) :
    WS h0 id (btSaveRoot (Sp id)) d (fun _ e => BTMergeOrder tk K (K - 1) e) := by
  have k2 := hi.queue.k2
  have kN := hi.queue.kN
  have n286 := hi.queue.n286
  have max := hi.queue.max
  have size := hi.queue.heap
  have len := hi.queue.len
  refine WS.mono (ws_btSaveRoot d (by omega) (by omega) (by omega) (by omega)) ?_
  intro _ e ⟨hm, index, fields, _size, _root, unchanged⟩
  have array : tk.arr e = tk.arr d := by rw [fields]; cases tk <;> rfl
  have oldTail (q : Nat) (lower : 573 - 2 * (K - 1) ≤ q) : Hn e q = Hn d q := by
    exact congrArg (fun x : Int32 => x.toInt.toNat) (unchanged q (by omega))
  have oldRoot : Hn e 1 = Hn d 1 :=
    congrArg (fun x : Int32 => x.toInt.toNat) (unchanged 1 (by omega))
  refine ⟨?_, ?_⟩
  · intro q lower upper
    rw [oldTail _ (by omega), oldTail _ lower]
    simpa only [btFreq, array] using history.tail q lower upper
  · intro positive q lower upper
    have one : q = 1 := by omega
    subst q
    rw [oldTail _ (by omega), oldRoot]
    simpa only [btFreq, array] using history.queue positive 1 lower upper

end Zlib.Trees.Proofs
