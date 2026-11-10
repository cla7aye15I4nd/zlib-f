import ZlibF.Proof.«trees.c.build.fib-step»
namespace Zlib.Trees.Proofs
open C Zlib.Trees
open HuffmanAbstract
set_option autoImplicit false
set_option maxHeartbeats 3000000

/-- The mathematical forest carried by the actual populated heap queue. -/
def huffmanQueue (R : Int32 → HTree) (H : Nat → Int32) (len : Nat) : List HTree :=
  (List.range len).map fun i => R (H (i + 1))

/-- Weight and height representation of the current actual queue. -/
structure HuffmanQueueView (tk : TK) (d : DeflateState) (len : Nat) (R : Int32 → HTree) : Prop where
  weight : ∀ i, 1 ≤ i → i ≤ len → (R d.heap[i]!).weight = (btFreq tk d d.heap[i]!.toInt.toNat).toNat
  height : ∀ i, 1 ≤ i → i ≤ len → (R d.heap[i]!).height = d.depth[d.heap[i]!.toInt.toNat]!.toNat

/-- The queue's exact natural observations also determine its tree multiset. -/
theorem huffmanQueue_count (R : Int32 → HTree) (H : Nat → Int32) (len : Nat) (t : HTree) :
    (huffmanQueue R H len).count t = GB.rs (fun i => if R (H (i + 1)) = t then 1 else 0) len := by
  induction len with
  | zero => rfl
  | succ len ih =>
      simp only [huffmanQueue, List.range_succ, List.map_append, List.map_singleton,
        List.count_append, List.count_singleton, GB.rs_succ] at ih ⊢
      rw [ih]
      by_cases equal : R (H (len + 1)) = t <;> simp [equal]

/-- The first actual queue slot is the head of its represented forest. -/
theorem huffmanQueue_head (R : Int32 → HTree) (H : Nat → Int32) (len : Nat) (positive : 0 < len) :
    huffmanQueue R H len = R (H 1) :: ((List.range (len - 1)).map fun i => R (H (i + 2))) := by
  cases len with
  | zero => omega
  | succ len => simp [huffmanQueue, List.range_succ_eq_map, List.map_map, Function.comp_def, Nat.add_assoc]

/-- The real two-node selection proves the precise abstract Huffman step
choice. The new abstract parent is not yet a claim about actual parent
stores: this theorem is the actual btPick2 cutpoint. The remaining actual
queue, including the second selected root, is retained exactly. -/
theorem ws_btPick2_huffman_step {h0 : Heap} {id : Nat}
    (tk : TK) (d : DeflateState) (len : Nat) (R : Int32 → HTree)
    (hlen : d.heap_len.toInt = len) (h2 : 2 ≤ len) (hsz : len < d.heap.size)
    (hbig : d.heap.size ≤ 573)
    (hval : ∀ i, 1 ≤ i → i ≤ len → NV (tk.arr d) d.depth d.heap[i]!)
    (hinj : ∀ i j, 1 ≤ i → i ≤ len → 1 ≤ j → j ≤ len → d.heap[i]! = d.heap[j]! → i = j)
    (ho : HeapOK (sm (tk.arr d) d.depth) (fun i => d.heap[i]!) len 0)
    (view : HuffmanQueueView tk d len R) :
    WS h0 id (btPick2 (Sp id) (.ref (tk.ref id) 0)) d (fun pair e =>
      pair.1 ≠ pair.2 ∧ tk.arr e = tk.arr d ∧ e.depth = d.depth ∧
      e.heap_len.toInt = (len : Int) - 1 ∧ ∃ rest : List HTree,
        huffmanQueue R (fun i => e.heap[i]!) (len - 1) = R pair.2 :: rest ∧
        HuffmanAbstract.Step (huffmanQueue R (fun i => d.heap[i]!) len)
          (HTree.node (R pair.1) (R pair.2) :: rest) (R pair.1) (R pair.2)) := by
  refine WS.mono (ws_btPick2 tk d len hlen h2 hsz hbig hval hinj ho) ?_
  intro pair e ⟨hl, H, first, second, hhl, heap, size, frame, perm, ordered,
    nv1, nv2, distinct, min1, min2, origin, complete, absent, injective, counts⟩
  subst e
  let rest : List HTree := (List.range (len - 2)).map fun i => R H[i + 2]!
  have remaining : huffmanQueue R (fun i => H[i]!) (len - 1) = R pair.2 :: rest := by
    rw [huffmanQueue_head R _ (len - 1) (by omega), ← second]
    rfl
  have represented (i : Nat) (lo : 1 ≤ i) (hi : i ≤ len - 1) :
      (R H[i]!).weight = (btFreq tk d H[i]!.toInt.toNat).toNat ∧
      (R H[i]!).height = d.depth[H[i]!.toInt.toNat]!.toNat := by
    obtain ⟨q, qlo, qhi, eq⟩ := origin i lo hi
    rw [eq]
    exact ⟨view.weight q (by omega) qhi, view.height q (by omega) qhi⟩
  have nWeight : (R pair.1).weight = (btFreq tk d pair.1.toInt.toNat).toNat := by
    rw [first]; exact view.weight 1 (by omega) (by omega)
  have nHeight : (R pair.1).height = d.depth[pair.1.toInt.toNat]!.toNat := by
    rw [first]; exact view.height 1 (by omega) (by omega)
  have mWeight : (R pair.2).weight = (btFreq tk d pair.2.toInt.toNat).toNat := by
    rw [second]; exact (represented 1 (by omega) (by omega)).1
  have mHeight : (R pair.2).height = d.depth[pair.2.toInt.toNat]!.toNat := by
    rw [second]; exact (represented 1 (by omega) (by omega)).2
  have permutation : (huffmanQueue R (fun i => d.heap[i]!) len).Perm
      (R pair.1 :: huffmanQueue R (fun i => H[i]!) (len - 1)) := by
    apply List.perm_iff_count.mpr
    intro t
    have count := counts (fun v => if R v = t then 1 else 0)
    rw [← huffmanQueue_count R (fun i => H[i]!) (len - 1) t,
      ← huffmanQueue_count R (fun i => d.heap[i]!) len t] at count
    by_cases equal : R pair.1 = t <;> simpa [List.count_cons, equal] using count.symm
  refine ⟨distinct, ?_, rfl, hhl, rest, remaining, rest, ?_, ?_, ?_, rfl⟩
  · cases tk <;> rfl
  · rw [← remaining]; exact permutation
  · intro t member
    rw [← remaining] at member
    obtain ⟨i, hi, eq⟩ := List.mem_map.mp member
    have index : i < len - 1 := List.mem_range.mp hi
    subst t
    obtain ⟨q, qlo, qhi, entry⟩ := origin (i + 1) (by omega) (by omega)
    exact sm_huffman nWeight (represented (i + 1) (by omega) (by omega)).1
      nHeight (represented (i + 1) (by omega) (by omega)).2 (by rw [entry]; exact min1 q (by omega) qhi)
  · intro t member
    obtain ⟨i, hi, eq⟩ := List.mem_map.mp member
    have index : i < len - 2 := List.mem_range.mp hi
    subst t
    exact sm_huffman mWeight (represented (i + 2) (by omega) (by omega)).1
      mHeight (represented (i + 2) (by omega) (by omega)).2 (min2 (i + 2) (by omega) (by omega))
end Zlib.Trees.Proofs
#print axioms Zlib.Trees.Proofs.huffmanQueue_count
#print axioms Zlib.Trees.Proofs.huffmanQueue_head
#print axioms Zlib.Trees.Proofs.ws_btPick2_huffman_step
