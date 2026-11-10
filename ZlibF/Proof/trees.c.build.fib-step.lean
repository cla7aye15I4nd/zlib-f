import ZlibF.Math.DeflateOverlay
import ZlibF.Proof.«trees.c.build.forest»

/-!
# trees.c: the weight facts needed by the Huffman refinement

The translated selection really removes the two least-weight nodes. Parent
creation uses their mathematical sum when its explicit 16-bit bound holds.
These are the first operational links to the pure Fibonacci argument; they
do not yet establish that argument for an entire translated build_tree run.
-/

namespace Zlib.Trees.Proofs
open C Zlib.Trees
set_option autoImplicit false

/-- The source comparison orders frequencies before its depth tie-break. -/
theorem sm_frequency_le {T : Array CtData} {D : Array UInt8} {n m : Int32}
    (order : sm T D n m = true) :
    T[n.toInt.toNat]!.fc.toNat ≤ T[m.toInt.toNat]!.fc.toNat := by
  simp only [sm, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true,
    beq_iff_eq, UInt16.lt_iff_toNat_lt] at order
  rcases order with less | ⟨eq, _⟩
  · omega
  · rw [eq]
    exact Nat.le_refl _

/-- The actual comparator agrees with the pure Huffman comparator whenever
the two represented weights and subtree heights agree. This is a local
representation relation, not an assumed execution contract. -/
theorem sm_huffman {T : Array CtData} {D : Array UInt8} {n m : Int32}
    {a b : HuffmanAbstract.HTree}
    (wa : a.weight = T[n.toInt.toNat]!.fc.toNat)
    (wb : b.weight = T[m.toInt.toNat]!.fc.toNat)
    (ha : a.height = D[n.toInt.toNat]!.toNat)
    (hb : b.height = D[m.toInt.toNat]!.toNat)
    (order : sm T D n m = true) : HuffmanAbstract.smaller a b := by
  simp only [sm, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true,
    beq_iff_eq, UInt16.lt_iff_toNat_lt, UInt8.le_iff_toNat_le] at order
  unfold HuffmanAbstract.smaller
  rw [wa, wb, ha, hb]
  rcases order with less | ⟨eq, le⟩
  · exact Or.inl less
  · exact Or.inr ⟨congrArg UInt16.toNat eq, le⟩

/-- `local void build_tree(deflate_state *s, tree_desc *desc)`.
The actual two-node selection prefix yields the two least frequencies of
the current populated queue. The second minimum excludes only the selected
first node. Tree and depth storage are unchanged by this prefix.
The internal storage premises are the existing selection theorem's domain;
this is not a public deflate or complete build_tree theorem. -/
theorem ws_btPick2_weight_minima {h0 : Heap} {id : Nat}
    (tk : TK) (d : DeflateState) (len : Nat)
    (hlen : d.heap_len.toInt = len) (h2 : 2 ≤ len) (hsz : len < d.heap.size)
    (hbig : d.heap.size ≤ 573)
    (hval : ∀ i, 1 ≤ i → i ≤ len → NV (tk.arr d) d.depth d.heap[i]!)
    (hinj : ∀ i j, 1 ≤ i → i ≤ len → 1 ≤ j → j ≤ len → d.heap[i]! = d.heap[j]! → i = j)
    (ho : HeapOK (sm (tk.arr d) d.depth) (fun i => d.heap[i]!) len 0) :
    WS h0 id (btPick2 (Sp id) (.ref (tk.ref id) 0)) d (fun pair e =>
      pair.1 ≠ pair.2 ∧ tk.arr e = tk.arr d ∧ e.depth = d.depth ∧
      (btFreq tk d pair.1.toInt.toNat).toNat ≤ (btFreq tk d pair.2.toInt.toNat).toNat ∧
      ∀ q, 1 ≤ q → q ≤ len →
        (btFreq tk d pair.1.toInt.toNat).toNat ≤ (btFreq tk d d.heap[q]!.toInt.toNat).toNat ∧
        (d.heap[q]! ≠ pair.1 →
          (btFreq tk d pair.2.toInt.toNat).toNat ≤ (btFreq tk d d.heap[q]!.toInt.toNat).toNat)) := by
  refine WS.mono (ws_btPick2 tk d len hlen h2 hsz hbig hval hinj ho) ?_
  intro pair e ⟨hl, H, first, second, hhl, heap, size, frame, perm, ordered,
    nv1, nv2, distinct, min1, min2, origin, complete, absent, injective, counts⟩
  subst e
  have first_le_second :
      (btFreq tk d pair.1.toInt.toNat).toNat ≤ (btFreq tk d pair.2.toInt.toNat).toNat := by
    obtain ⟨q, qlo, qhi, node⟩ := origin 1 (by omega) (by omega)
    have le := sm_frequency_le (min1 q (by omega) qhi)
    rw [← node, ← second] at le
    exact le
  refine ⟨distinct, ?_, rfl, first_le_second, ?_⟩
  · cases tk <;> rfl
  · intro q qlo qhi
    refine ⟨sm_frequency_le (min1 q qlo qhi), ?_⟩
    intro not_first
    have qne : q ≠ 1 := by
      intro eq
      subst q
      exact not_first first.symm
    have q2 : 2 ≤ q := by omega
    obtain ⟨j, jlo, jhi, node⟩ := complete q q2 qhi
    have le := sm_frequency_le (min2 j jlo jhi)
    rw [node] at le
    exact le

/-- The source selection derives the child-sum bound from the whole
populated queue's weight. It does not assume a bound on the selected pair.
The caller must still establish and preserve the queue-weight budget. -/
theorem ws_btPick2_weight_bound {h0 : Heap} {id : Nat}
    (tk : TK) (d : DeflateState) (len : Nat)
    (hlen : d.heap_len.toInt = len) (h2 : 2 ≤ len) (hsz : len < d.heap.size)
    (hbig : d.heap.size ≤ 573)
    (hval : ∀ i, 1 ≤ i → i ≤ len → NV (tk.arr d) d.depth d.heap[i]!)
    (hinj : ∀ i j, 1 ≤ i → i ≤ len → 1 ≤ j → j ≤ len → d.heap[i]! = d.heap[j]! → i = j)
    (ho : HeapOK (sm (tk.arr d) d.depth) (fun i => d.heap[i]!) len 0)
    (total : GB.rs (fun i => (btFreq tk d d.heap[i + 1]!.toInt.toNat).toNat) len < 2 ^ 16) :
    WS h0 id (btPick2 (Sp id) (.ref (tk.ref id) 0)) d (fun pair _ =>
      (btFreq tk d pair.1.toInt.toNat).toNat +
        (btFreq tk d pair.2.toInt.toNat).toNat < 2 ^ 16) := by
  refine WS.mono (ws_btPick2 tk d len hlen h2 hsz hbig hval hinj ho) ?_
  intro pair e ⟨hl, H, first, second, hhl, heap, size, frame, perm, ordered,
    nv1, nv2, distinct, min1, min2, origin, complete, absent, injective, counts⟩
  obtain ⟨q, qlo, qhi, node⟩ := origin 1 (by omega) (by omega)
  have second_old : pair.2 = d.heap[q]! := second.trans node
  have bound := GB.two_le_rs
    (fun i => (btFreq tk d d.heap[i + 1]!.toInt.toNat).toNat)
    len 0 (q - 1) (by omega) (by omega) (by omega)
  simp only [Nat.zero_add, Nat.sub_add_cancel (by omega : 1 ≤ q)] at bound
  rw [← first, ← second_old] at bound
  omega

/-- `local void build_tree(deflate_state *s, tree_desc *desc)`.
The actual parent-creation prefix stores the natural sum of child weights
when that sum fits UInt16. Without the bound the source correctly wraps;
the pure Huffman model must not silently replace that wrapping behavior.
Later tally/forest refinement must establish this internal numeric premise. -/
theorem ws_btMakeParent_weight {h0 : Heap} {id : Nat}
    (tk : TK) (d : DeflateState) (n m node : Int32)
    (hn : NV (tk.arr d) d.depth n) (hm : NV (tk.arr d) d.depth m)
    (hp : NV (tk.arr d) d.depth node)
    (bound : (btFreq tk d n.toInt.toNat).toNat + (btFreq tk d m.toInt.toNat).toNat < 2 ^ 16) :
    WS h0 id (btMakeParent (Sp id) (.ref (tk.ref id) 0) n m node) d (fun _ e =>
      (btFreq tk e node.toInt.toNat).toNat =
        (btFreq tk d n.toInt.toNat).toNat + (btFreq tk d m.toInt.toNat).toNat) := by
  refine WS.mono (ws_btMakeParent tk d n m node hn hm hp) ?_
  intro _ e eq
  subst e
  unfold btFreq
  rw [btParentState_fc tk d n m node hn hm hp, if_pos rfl, UInt16.toNat_add]
  exact Nat.mod_eq_of_lt bound

/-- Total mathematical frequency in the populated source queue. -/
def btQueueWeight (tk : TK) (d : DeflateState) (len : Nat) : Nat :=
  GB.rs (fun i => (btFreq tk d d.heap[i + 1]!.toInt.toNat).toNat) len

/-- A complete actual merge preserves the queue's mathematical weight.
The selected child sum fits because both children are distinct members of
the bounded queue. Consequently the source UInt16 addition does not wrap.
The forest and total-weight premises are data about this run state; no
called-function contract is assumed. -/
theorem ws_btMergeBody_weight {h0 : Heap} {id : Nat} {tk : TK} {d0 d : DeflateState}
    {N K j : Nat} {mc node : Int32} (hi : BTForest tk N K j mc d0 node d)
    (more : j + 1 < K) (total : btQueueWeight tk d (K - j) < 2 ^ 16) :
    WS h0 id (btMergeBody (Sp id) (.ref (tk.ref id) 0) node) d (fun _ e =>
      btQueueWeight tk e (K - (j + 1)) = btQueueWeight tk d (K - j)) := by
  have hcounter := hi.queue.counter
  have hlen := hi.queue.len
  have hmax := hi.queue.max
  have hsize := hi.queue.heap
  have hTsize := hi.queue.tree
  have hDsize := hi.queue.depth
  have hstage := hi.queue.stage
  have hK := hi.queue.kN
  have hN := hi.queue.n286
  have hnode : NV (tk.arr d) d.depth node := ⟨by omega, by omega, by omega⟩
  refine WS.mono (ws_btMergeBody_forest tk d (K - j) node hlen
    (by omega) (by omega) (by omega) (by omega) (by omega) hnode (by omega)
    (fun i a b => hi.queue.valid i a (by omega))
    (fun i i' a b c e => hi.queue.injective i i' a (by omega) c (by omega)) hi.queue.order) ?_
  intro next e ⟨counter, n, m, distinct, ⟨pn, pnlo, pnhi, first⟩,
    ⟨pm, pmlo, pmhi, second⟩, len, boundary, keepn, keepm, tail, tree, depth, root, counts⟩
  have nv := hi.queue.valid pn pnlo (by omega)
  have mv := hi.queue.valid pm pmlo (by omega)
  rw [← first] at nv
  rw [← second] at mv
  have hn : NV (tk.arr d) d.depth n := ⟨nv.1, by omega, by omega⟩
  have hm : NV (tk.arr d) d.depth m := ⟨mv.1, by omega, by omega⟩
  have indices : pn ≠ pm := by
    intro eq
    exact distinct (first.trans (eq ▸ second.symm))
  have child_sum := GB.two_le_rs
    (fun i => (btFreq tk d d.heap[i + 1]!.toInt.toNat).toNat)
    (K - j) (pn - 1) (pm - 1) (by omega) (by omega) (by omega)
  simp only [Nat.sub_add_cancel pnlo, Nat.sub_add_cancel pmlo] at child_sum
  rw [← first, ← second] at child_sum
  have nowrap : (btFreq tk d n.toInt.toNat).toNat + (btFreq tk d m.toInt.toNat).toNat < 2 ^ 16 := by
    unfold btQueueWeight at total
    omega
  have frequencies (v : Nat) : btFreq tk e v =
      if v = node.toInt.toNat then btFreq tk d n.toInt.toNat + btFreq tk d m.toInt.toNat
      else btFreq tk d v := by
    unfold btFreq
    rw [tree, btParentState_fc tk d n m node hn hm hnode]
  have unchanged (v : Int32) (vlo : 0 ≤ v.toInt) (vhi : v.toInt < node.toInt) :
      (btFreq tk e v.toInt.toNat).toNat = (btFreq tk d v.toInt.toNat).toNat := by
    rw [frequencies, if_neg (by omega)]
  have parent_weight : (btFreq tk e node.toInt.toNat).toNat =
      (btFreq tk d n.toInt.toNat).toNat + (btFreq tk d m.toInt.toNat).toNat := by
    rw [frequencies, if_pos rfl, UInt16.toNat_add, Nat.mod_eq_of_lt nowrap]
  have old_weight : GB.rs (fun i => (btFreq tk e d.heap[i + 1]!.toInt.toNat).toNat) (K - j) =
      btQueueWeight tk d (K - j) := by
    apply GB.rs_congr
    intro i hidx
    have valid := hi.queue.valid (i + 1) (by omega) (by omega)
    exact unchanged _ valid.1 valid.2
  have count_weight := counts (fun v => (btFreq tk e v.toInt.toNat).toNat)
  rw [old_weight, parent_weight, unchanged n nv.1 nv.2, unchanged m mv.1 mv.2] at count_weight
  have new_length : K - (j + 1) = K - j - 1 := by omega
  unfold btQueueWeight
  rw [new_length]
  rw [Nat.add_assoc] at count_weight
  exact Nat.add_right_cancel count_weight

/-- The complete actual merge loop conserves its initial mathematical
weight and returns that weight in its singleton root. Every iteration
derives its non-wrapping child sum from the same initial budget. The
initial forest is produced by the existing leaf-preparation proof. -/
theorem ws_btMergeLoop_weight {h0 : Heap} {id : Nat} {tk : TK} {d : DeflateState}
    {N K : Nat} {mc node : Int32} (hi : BTForest tk N K 0 mc d node d)
    (total : btQueueWeight tk d K < 2 ^ 16) :
    WS h0 id (btMergeLoop (Sp id) (.ref (tk.ref id) 0) node) d (fun next e =>
      BTForest tk N K (K - 1) mc d next e ∧ BTForestFrame tk d e ∧ e.heap_len.toInt = 1 ∧
        (btFreq tk e e.heap[1]!.toInt.toNat).toNat = btQueueWeight tk d K) := by
  let Inv : Int32 → DeflateState → Prop := fun node e =>
    ∃ j : Nat, BTForest tk N K j mc d node e ∧ BTForestFrame tk d e ∧ j + 1 < K ∧
      btQueueWeight tk e (K - j) = btQueueWeight tk d K
  let Q : Int32 → DeflateState → Prop := fun node e =>
    BTForest tk N K (K - 1) mc d node e ∧ BTForestFrame tk d e ∧ e.heap_len.toInt = 1 ∧
      (btFreq tk e e.heap[1]!.toInt.toNat).toNat = btQueueWeight tk d K
  unfold btMergeLoop
  refine WS.cdoWhile2 Inv (fun _ e => e.heap_len.toInt.toNat) Q ?_
    ⟨0, hi, BTForestFrame.refl tk d, by have := hi.queue.k2; omega, rfl⟩
    (by have := hi.queue.len; have := hi.queue.kN; have := hi.queue.n286; dsimp only [fuel]; omega)
  intro current e ⟨j, hj, hfr, more, weight⟩
  have budget : btQueueWeight tk e (K - j) < 2 ^ 16 := by rw [weight]; exact total
  refine WS.mono (merge_ws_and
    (merge_ws_and (ws_btMergeBody_forest_inv hj more) (ws_btMergeBody_frame hj.queue more))
    (ws_btMergeBody_weight hj more budget)) ?_
  intro next e' ⟨⟨hj', hfr'⟩, conserved⟩
  have final_weight := conserved.trans weight
  have frame := hfr.trans hfr'
  refine WS.bind' ws_rd fun got e'' ⟨hgot, he''⟩ => ?_
  subst e''; subst got
  have len := hj'.queue.len
  have stage := hj'.queue.stage
  have k2 := hj'.queue.k2
  by_cases cont : e'.heap_len.toInt ≥ 2
  · have next_stage : j + 1 + 1 < K := by omega
    refine WS.pure' (Or.inr ⟨by simp only [cont, decide_true],
      ⟨j + 1, hj', frame, next_stage, final_weight⟩, ?_⟩)
    have old_len := hj.queue.len
    omega
  · have end_stage : j + 1 = K - 1 := by omega
    have singleton : K - (j + 1) = 1 := by omega
    rw [singleton] at final_weight
    have root_weight : (btFreq tk e' e'.heap[1]!.toInt.toNat).toNat = btQueueWeight tk d K := by
      simpa only [btQueueWeight, GB.rs_succ, GB.rs_zero, Nat.zero_add] using final_weight
    refine WS.pure' (Or.inl ⟨by simp only [cont, decide_false], ?_⟩)
    change Q next e'
    rw [end_stage] at hj'
    exact ⟨hj', frame, by omega, root_weight⟩

end Zlib.Trees.Proofs
