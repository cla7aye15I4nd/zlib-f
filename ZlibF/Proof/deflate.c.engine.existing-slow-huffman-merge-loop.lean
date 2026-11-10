import ZlibF.Proof.«deflate.c.engine.existing-slow-huffman-merge-prefix»
namespace Zlib.Trees.Proofs
open C Zlib.Trees
open HuffmanAbstract
set_option autoImplicit false
set_option maxHeartbeats 5000000

/-- The whole actual merge loop produces a complete mathematical Merges
run from the exact prepared live alphabet. The at-most-256-leaf internal
scope makes every represented height update fit the source UInt8; BL's
nineteen-symbol alphabet satisfies it. Natural frequency sums follow from
the real initial queue budget. Neither Merges nor optimality is assumed. -/
theorem ws_btMergeLoop_huffman {h0 : Heap} {id : Nat} {tk : TK} {d : DeflateState}
    {N K : Nat} {mc node : Int32} (initial : BTForest tk N K 0 mc d node d)
    (small : K ≤ 256) (total : btQueueWeight tk d K < 2 ^ 16) :
    WS h0 id (btMergeLoop (Sp id) (.ref (tk.ref id) 0) node) d (fun next e =>
      BTForest tk N K (K-1) mc d next e ∧ BTForestFrame tk d e ∧ e.heap_len.toInt = 1 ∧
      ∃ (R : Int32 → HTree) (removed : List HTree),
        HuffmanQueueView tk e 1 R ∧
        Merges (initForest (huffmanLeafSymbols tk d K)) removed (R e.heap[1]!) ∧
        (R e.heap[1]!).weight = btQueueWeight tk d K ∧ (R e.heap[1]!).height ≤ K-1) := by
  let alphabet := initForest (huffmanLeafSymbols tk d K)
  let Inv : Int32 → DeflateState → Prop := fun current e =>
    ∃ (j : Nat) (R : Int32 → HTree) (forest removed : List HTree),
      BTForest tk N K j mc d current e ∧ BTForestFrame tk d e ∧ j+1 < K ∧
      btQueueWeight tk e (K-j) = btQueueWeight tk d K ∧
      HuffmanQueueView tk e (K-j) R ∧
      (∀ i, 1 ≤ i → i ≤ K-j → (R e.heap[i]!).height ≤ j) ∧
      (huffmanQueue R (fun i => e.heap[i]!) (K-j)).Perm forest ∧
      HuffmanRunPrefix alphabet forest removed
  let Q : Int32 → DeflateState → Prop := fun next e =>
      BTForest tk N K (K-1) mc d next e ∧ BTForestFrame tk d e ∧ e.heap_len.toInt = 1 ∧
      ∃ (R : Int32 → HTree) (removed : List HTree),
        HuffmanQueueView tk e 1 R ∧ Merges alphabet removed (R e.heap[1]!) ∧
        (R e.heap[1]!).weight = btQueueWeight tk d K ∧ (R e.heap[1]!).height ≤ K-1
  have leafView := huffman_leaf_queue_view initial.initial initial.initial_len
  have initialPermutation : (huffmanQueue (huffmanLeafMap tk d) (fun i => d.heap[i]!) (K-0)).Perm alphabet := by
    simpa only [Nat.sub_zero,huffman_leaf_forest] using List.Perm.refl alphabet
  unfold btMergeLoop
  refine WS.cdoWhile2 Inv (fun _ e => e.heap_len.toInt.toNat) Q ?_
    ⟨0,huffmanLeafMap tk d,alphabet,[],initial,BTForestFrame.refl tk d,
      by have := initial.queue.k2; omega,by simp [btQueueWeight],leafView.1,leafView.2,initialPermutation,HuffmanRunPrefix.refl alphabet⟩
    (by have := initial.queue.len; have := initial.queue.kN; have := initial.queue.n286; dsimp only [fuel]; omega)
  intro current e ⟨j,R,forest,removed,hi,frame,more,weight,view,heights,represented,prior⟩
  have counter := hi.queue.counter
  have len := hi.queue.len
  have boundary := hi.queue.max
  have heapSize := hi.queue.heap
  have treeSize := hi.queue.tree
  have depthSize := hi.queue.depth
  have stage := hi.queue.stage
  have kN := hi.queue.kN
  have n286 := hi.queue.n286
  have parent : NV (tk.arr e) e.depth current := ⟨by omega,by omega,by omega⟩
  have budget : btQueueWeight tk e (K-j) < 2^16 := by rw [weight]; exact total
  refine WS.mono (merge_ws_and
    (merge_ws_and (merge_ws_and (ws_btMergeBody_forest_inv hi more) (ws_btMergeBody_frame hi.queue more))
      (ws_btMergeBody_weight hi more budget))
    (ws_btMergeBody_huffman tk e (K-j) current R j len (by omega) (by omega) (by omega)
      (by omega) (by omega) parent (by omega)
      (fun i lo upper => hi.queue.valid i lo (by omega))
      (fun i i' lo upper lo' upper' => hi.queue.injective i i' lo (by omega) lo' (by omega))
      hi.queue.order budget view heights (by omega))) ?_
  intro next e' ⟨⟨⟨hi',frame'⟩,conserved⟩,increment,n,m,rest,keepn,keepm,selected,permutation,view',heights'⟩
  have nextWeight := conserved.trans weight
  have nextFrame := frame.trans frame'
  let R' := huffmanAddParent R n m current
  let forest' := HTree.node (R n) (R m) :: rest
  let removed' := removed ++ [R n,R m]
  have prior' : HuffmanRunPrefix alphabet forest' removed' := prior.advance represented selected
  have viewNext : HuffmanQueueView tk e' (K-(j+1)) R' := by simpa only [R',show K-(j+1)=K-j-1 by omega] using view'
  have heightsNext : ∀ i, 1 ≤ i → i ≤ K-(j+1) → (R' e'.heap[i]!).height ≤ j+1 := by
    simpa only [R',show K-(j+1)=K-j-1 by omega] using heights'
  have permutationNext : (huffmanQueue R' (fun i => e'.heap[i]!) (K-(j+1))).Perm forest' := by
    simpa only [R',forest',show K-(j+1)=K-j-1 by omega] using permutation
  refine WS.bind' ws_rd fun got e'' ⟨same,unchanged⟩ => ?_
  subst e'';subst got
  have nextLength := hi'.queue.len
  have nextStage := hi'.queue.stage
  by_cases cont : e'.heap_len.toInt ≥ 2
  · refine WS.pure' (Or.inr ⟨by simp only [cont,decide_true],?_,?_⟩)
    · exact ⟨j+1,R',forest',removed',hi',nextFrame,by omega,nextWeight,viewNext,heightsNext,permutationNext,prior'⟩
    · omega
  · have endStage : j+1=K-1 := by omega
    have singleton : K-(j+1)=1 := by omega
    rw [singleton] at nextWeight viewNext heightsNext permutationNext
    have actualSingle : huffmanQueue R' (fun i => e'.heap[i]!) 1 = [R' e'.heap[1]!] := rfl
    have forestSingle : forest' = [R' e'.heap[1]!] := by
      apply List.perm_singleton.mp
      rw [← actualSingle]
      exact permutationNext.symm
    rw [forestSingle] at prior'
    have complete := prior' [] (R' e'.heap[1]!) (.done _)
    have rootWeight : (R' e'.heap[1]!).weight = btQueueWeight tk d K := by
      rw [viewNext.weight 1 (by omega) (by omega)]
      simpa only [btQueueWeight,GB.rs_succ,GB.rs_zero,Nat.zero_add] using nextWeight
    refine WS.pure' (Or.inl ⟨by simp only [cont,decide_false],?_⟩)
    change Q next e'
    rw [endStage] at hi'
    refine ⟨hi',nextFrame,by omega,R',removed',viewNext,?_,rootWeight,?_⟩
    · simpa only [List.append_nil] using complete
    · rw [← endStage]
      exact heightsNext 1 (by omega) (by omega)
end Zlib.Trees.Proofs
#print axioms Zlib.Trees.Proofs.ws_btMergeLoop_huffman
