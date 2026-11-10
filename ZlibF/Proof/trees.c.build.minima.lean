import ZlibF.Proof.«trees.c.build.fib-step»

/-! # Actual merge selection orders both removals and the next queue -/

namespace Zlib.Trees.Proofs
open C Zlib.Trees
set_option autoImplicit false

/-- The two stored children have the least original weights in removal
order. Every new live node has weight at least the second removed child.
The fresh parent uses a natural sum because the original queue fits the
frequency type. All called fragments execute on the actual source heap. -/
theorem ws_btMergeBody_minima {h0 : Heap} {id : Nat} (tk : TK) (d : DeflateState) (len : Nat) (node : Int32)
    (hlen : d.heap_len.toInt = len) (h2 : 2 ≤ len) (hsz : len < d.heap.size)
    (hbig : d.heap.size ≤ 573) (hmH : d.heap_max.toInt ≤ d.heap.size)
    (hgap : (len : Int) < d.heap_max.toInt - 1)
    (hp : NV (tk.arr d) d.depth node) (hinc : node.toInt < 2147483647)
    (hbefore : ∀ i, 1 ≤ i → i ≤ len → 0 ≤ d.heap[i]!.toInt ∧ d.heap[i]!.toInt < node.toInt)
    (hinj : ∀ i j, 1 ≤ i → i ≤ len → 1 ≤ j → j ≤ len → d.heap[i]! = d.heap[j]! → i = j)
    (ho : HeapOK (sm (tk.arr d) d.depth) (fun i => d.heap[i]!) len 0)
    (total : btQueueWeight tk d len < 2 ^ 16) :
    WS h0 id (btMergeBody (Sp id) (.ref (tk.ref id) 0) node) d (fun _ e =>
      ∃ n m : Int32,
        e.heap[(d.heap_max.toInt - 1).toNat]! = n ∧
        e.heap[(d.heap_max.toInt - 2).toNat]! = m ∧
        (btFreq tk d n.toInt.toNat).toNat ≤ (btFreq tk d m.toInt.toNat).toNat ∧
        (∀ q, 1 ≤ q → q ≤ len →
          (btFreq tk d n.toInt.toNat).toNat ≤ (btFreq tk d d.heap[q]!.toInt.toNat).toNat) ∧
        (∀ q, 1 ≤ q → q ≤ len - 1 →
          (btFreq tk d m.toInt.toNat).toNat ≤ (btFreq tk e e.heap[q]!.toInt.toNat).toNat)) := by
  have hv : ∀ i, 1 ≤ i → i ≤ len → NV (tk.arr d) d.depth d.heap[i]! := by
    intro i hi1 hi2
    have hb := hbefore i hi1 hi2
    exact ⟨hb.1, by have := hp.2.1; omega, by have := hp.2.2; omega⟩
  unfold btMergeBody
  refine WS.bind' (merge_ws_and
    (ws_btMergeOpen tk d len hlen h2 hsz hbig hmH hgap hv hinj ho)
    (ws_btMergeOpen_tail tk d len hlen h2 hsz hbig hmH hgap hv hinj ho))
    fun pair e1 ⟨⟨hl, hm1, hm2, H, hn, hm, hnm, hhl, hh1, hh2, he1, hsH, hkeepn, hkeepm,
      hnv, hmv, horder, hminn, hminm, horigin, hcomplete, hno, hHi, hcount⟩, htail⟩ => ?_
  rcases pair with ⟨n, m⟩
  dsimp only at hn hm hnm hnv hmv hkeepn hkeepm hno hcount ⊢
  subst e1
  let d1 := { d with heap := H, heap_len := hl, heap_max := hm2 }
  have hT1 : tk.arr d1 = tk.arr d := by cases tk <;> rfl
  have hD1 : d1.depth = d.depth := rfl
  have hp1 : NV (tk.arr d1) d1.depth node := by rw [hT1, hD1]; exact hp
  have hn1 : NV (tk.arr d1) d1.depth n := by rw [hT1, hD1]; exact hnv
  have hm1v : NV (tk.arr d1) d1.depth m := by rw [hT1, hD1]; exact hmv
  have hB : ∀ i, 1 ≤ i → i ≤ len - 1 → 0 ≤ H[i]!.toInt ∧ H[i]!.toInt < node.toInt := by
    intro i hi1 hi2
    obtain ⟨j, hj1, hj2, heq⟩ := horigin i hi1 hi2
    rw [heq]
    exact hbefore j (by omega) hj2
  refine WS.bind' (ws_btMakeParent tk d1 n m node hn1 hm1v hp1) fun _ e2 he2 => ?_
  subst e2
  let d2 := btParentState tk d1 n m node
  have hp2 : NV (tk.arr d2) d2.depth node := by
    simpa only [d2, NV, btParentState_tree_size, btParentState_depth_size] using hp1
  have hv2 : ∀ i, 1 ≤ i → i ≤ len - 1 → NV (tk.arr d2) d2.depth d2.heap[i]! := by
    intro i hi1 hi2
    have hb := hB i hi1 hi2
    simp only [d2, btParentState_heap, d1, NV, btParentState_tree_size, btParentState_depth_size, hT1]
    exact ⟨hb.1, by have := hp.2.1; omega, by have := hp.2.2; omega⟩
  have ho2 : HeapOK (sm (tk.arr d2) d2.depth) (fun i => d2.heap[i]!) (len - 1) 1 := by
    intro c hc2 hcl hcp
    have hb := hB c (by omega) hcl
    have hb' := hB (c / 2) (by omega) (by omega)
    dsimp only [d2]
    rw [btParentState_heap]
    change sm (tk.arr (btParentState tk d1 n m node)) (btParentState tk d1 n m node).depth H[c / 2]! H[c]! = true
    rw [btParentState_sm tk d1 n m node _ _ hn1 hm1v hp1 hb'.1 hb'.2 hb.1 hb.2, hT1, hD1]
    exact horder c hc2 hcl (by omega)
  refine WS.mono (ws_btMergeClose tk d2 (len - 1) node
    (by simpa only [d2, btParentState_len] using hhl.trans (by omega)) (by omega)
    (by simpa only [d2, btParentState_heap] using (show len - 1 < H.size by omega))
    (by simpa only [d2, btParentState_heap] using (show H.size ≤ 573 by omega)) hp2 hinc hv2 ho2) ?_
  intro next e3 ⟨hnext, H', he3, hsH', hframe, hperm, horder', hmin', hcount'⟩
  subst e3
  have hHeap2 : d2.heap = H := by simp only [d2, btParentState_heap]; rfl
  have hroot : d2.heap[1]! = m := by rw [hHeap2]; exact hm.symm
  have hmorigin : ∃ q : Nat, 1 ≤ q ∧ q ≤ len ∧ m = d.heap[q]! := by
    obtain ⟨q, hq1, hq2, hq⟩ := horigin 1 (by omega) (by omega)
    exact ⟨q, by omega, hq2, hm.trans hq⟩

  obtain ⟨pm, pmlo, pmhi, second⟩ := hmorigin
  have pmNe : pm ≠ 1 := by
    intro eq
    apply hnm
    rw [hn, second, eq]
  have pair := GB.two_le_rs (fun i => (btFreq tk d d.heap[i + 1]!.toInt.toNat).toNat)
    len 0 (pm - 1) (by omega) (by omega) (by omega)
  simp only [Nat.zero_add, Nat.sub_add_cancel pmlo] at pair
  rw [← hn, ← second] at pair
  have nowrap : (btFreq tk d n.toInt.toNat).toNat + (btFreq tk d m.toInt.toNat).toNat < 2 ^ 16 := by
    unfold btQueueWeight at total
    omega
  have frequencies (v : Nat) : btFreq tk { d2 with heap := H' } v =
      if v = node.toInt.toNat then btFreq tk d n.toInt.toNat + btFreq tk d m.toInt.toNat
      else btFreq tk d v := by
    unfold btFreq
    rw [tk_arr_heap]
    change (tk.arr (btParentState tk d1 n m node))[v]!.fc = _
    rw [btParentState_fc tk d1 n m node hn1 hm1v hp1, hT1]
  have nBefore : (btFreq tk d n.toInt.toNat).toNat ≤ (btFreq tk d m.toInt.toNat).toNat := by
    rw [second]
    exact sm_frequency_le (hminn pm pmlo pmhi)
  refine ⟨n, m, ?_, ?_, nBefore, ?_, ?_⟩
  · change H'[(d.heap_max.toInt - 1).toNat]! = n
    rw [← hh1, hframe _ (by omega), hHeap2]
    exact hkeepn
  · change H'[(d.heap_max.toInt - 2).toNat]! = m
    rw [← hh2, hframe _ (by omega), hHeap2]
    exact hkeepm
  · intro q qlo qhi
    exact sm_frequency_le (hminn q qlo qhi)
  · intro q qlo qhi
    obtain ⟨σ, range, _injective, equal⟩ := hperm
    have position := range q qlo qhi
    have entry := equal q qlo qhi
    dsimp only at entry
    rw [hHeap2] at entry
    change _ ≤ (btFreq tk { d2 with heap := H' } H'[q]!.toInt.toNat).toNat
    rw [entry]
    split
    · rw [frequencies, if_pos rfl, UInt16.toNat_add, Nat.mod_eq_of_lt nowrap]
      omega
    · have valid := hB (σ q) position.1 position.2
      have old : H[σ q]!.toInt.toNat ≠ node.toInt.toNat := by have := hp.1; omega
      rw [frequencies, if_neg old]
      exact sm_frequency_le (hminm (σ q) position.1 position.2)

end Zlib.Trees.Proofs
