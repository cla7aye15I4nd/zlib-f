import ZlibF.Proof.«deflate.c.engine.existing-slow-queue-selection-data»
namespace Zlib.Trees.Proofs
open C Zlib.Trees
open HuffmanAbstract
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- Add exactly the fresh mathematical parent to the node interpretation. -/
def huffmanAddParent (R : Int32 → HTree) (n m node v : Int32) : HTree :=
  if v = node then .node (R n) (R m) else R v

/-- One actual merge, including both tail stores, checked parent creation
and real sift-down, refines one mathematical Huffman step. The queue has
its exact represented multiset afterwards. Frequencies and source depth
bytes match the updated trees, with both wrap bounds derived from the
actual queue's mass and represented height bound. This is an internal
one-step producer, not a public-header or full build_tree assumption. -/
theorem ws_btMergeBody_huffman {h0 : Heap} {id : Nat}
    (tk : TK) (d : DeflateState) (len : Nat) (node : Int32) (R : Int32 → HTree) (stage : Nat)
    (hlen : d.heap_len.toInt = len) (h2 : 2 ≤ len) (hsz : len < d.heap.size)
    (hbig : d.heap.size ≤ 573) (hmH : d.heap_max.toInt ≤ d.heap.size)
    (hgap : (len : Int) < d.heap_max.toInt - 1)
    (hp : NV (tk.arr d) d.depth node) (hinc : node.toInt < 2147483647)
    (hbefore : ∀ i, 1 ≤ i → i ≤ len → 0 ≤ d.heap[i]!.toInt ∧ d.heap[i]!.toInt < node.toInt)
    (hinj : ∀ i j, 1 ≤ i → i ≤ len → 1 ≤ j → j ≤ len → d.heap[i]! = d.heap[j]! → i = j)
    (ho : HeapOK (sm (tk.arr d) d.depth) (fun i => d.heap[i]!) len 0)
    (total : btQueueWeight tk d len < 2 ^ 16) (view : HuffmanQueueView tk d len R)
    (heightBound : ∀ i, 1 ≤ i → i ≤ len → (R d.heap[i]!).height ≤ stage)
    (heightRoom : stage + 1 < 256) :
    WS h0 id (btMergeBody (Sp id) (.ref (tk.ref id) 0) node) d (fun next e =>
      next.toInt = node.toInt + 1 ∧ ∃ n m : Int32, ∃ rest : List HTree,
        e.heap[(d.heap_max.toInt - 1).toNat]! = n ∧
        e.heap[(d.heap_max.toInt - 2).toNat]! = m ∧
        HuffmanAbstract.Step (huffmanQueue R (fun i => d.heap[i]!) len)
          (HTree.node (R n) (R m) :: rest) (R n) (R m) ∧
        (huffmanQueue (huffmanAddParent R n m node) (fun i => e.heap[i]!) (len - 1)).Perm
          (HTree.node (R n) (R m) :: rest) ∧
        HuffmanQueueView tk e (len - 1) (huffmanAddParent R n m node) ∧
        (∀ i, 1 ≤ i → i ≤ len - 1 → ((huffmanAddParent R n m node) e.heap[i]!).height ≤ stage + 1)) := by
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
  obtain ⟨rest, remaining, selected⟩ := huffman_step_of_selection tk d H len n m R h2 view hn hm hminn hminm horigin hcount
  have nView : (R n).weight = (btFreq tk d n.toInt.toNat).toNat ∧ (R n).height = d.depth[n.toInt.toNat]!.toNat := by
    rw [hn]
    exact ⟨view.weight 1 (by omega) (by omega), view.height 1 (by omega) (by omega)⟩
  have mView : (R m).weight = (btFreq tk d m.toInt.toNat).toNat ∧ (R m).height = d.depth[m.toInt.toNat]!.toNat := by
    rw [second]
    exact ⟨view.weight pm pmlo pmhi, view.height pm pmlo pmhi⟩
  have nHeight : (R n).height ≤ stage := by rw [hn]; exact heightBound 1 (by omega) (by omega)
  have mHeight : (R m).height ≤ stage := by rw [second]; exact heightBound pm pmlo pmhi
  have depths (v : Nat) : ({d2 with heap := H'} : DeflateState).depth[v]! =
      if v = node.toInt.toNat then
        (if d.depth[n.toInt.toNat]! ≥ d.depth[m.toInt.toNat]! then
          d.depth[n.toInt.toNat]! else d.depth[m.toInt.toNat]!) + 1
      else d.depth[v]! := by
    exact btParentState_depth tk d1 n m node hp1 v
  have parentWeight : (HTree.node (R n) (R m)).weight =
      (btFreq tk {d2 with heap := H'} node.toInt.toNat).toNat := by
    rw [frequencies, ite_eq_left rfl, UInt16.toNat_add, Nat.mod_eq_of_lt nowrap]
    change (R n).weight + (R m).weight = _
    rw [nView.1,mView.1]
  have parentHeight : (HTree.node (R n) (R m)).height =
      ({d2 with heap := H'} : DeflateState).depth[node.toInt.toNat]!.toNat := by
    rw [depths, ite_eq_left rfl]
    have room : max d.depth[n.toInt.toNat]!.toNat d.depth[m.toInt.toNat]!.toNat + 1 < 256 := by
      rw [← nView.2, ← mView.2]
      have bound := Nat.max_le.mpr ⟨nHeight,mHeight⟩
      omega
    change max (R n).height (R m).height + 1 = _
    rw [nView.2,mView.2]
    by_cases order : d.depth[m.toInt.toNat]! ≤ d.depth[n.toInt.toNat]!
    · rw [ite_eq_left order, UInt8.toNat_add, Nat.max_eq_left (UInt8.le_iff_toNat_le.mp order)]
      exact (Nat.mod_eq_of_lt (by simpa only [Nat.max_eq_left (UInt8.le_iff_toNat_le.mp order)] using room)).symm
    · have strict : d.depth[n.toInt.toNat]!.toNat ≤ d.depth[m.toInt.toNat]!.toNat := by
        have notle : ¬ d.depth[m.toInt.toNat]!.toNat ≤ d.depth[n.toInt.toNat]!.toNat := fun yes => order (UInt8.le_iff_toNat_le.mpr yes)
        omega
      rw [ite_eq_right order, UInt8.toNat_add, Nat.max_eq_right strict]
      exact (Nat.mod_eq_of_lt (by simpa only [Nat.max_eq_right strict] using room)).symm
  have oldCells (v : Int32) (lo : 0 ≤ v.toInt) (hi : v.toInt < node.toInt) :
      (btFreq tk {d2 with heap := H'} v.toInt.toNat).toNat = (btFreq tk d v.toInt.toNat).toNat ∧
      ({d2 with heap := H'} : DeflateState).depth[v.toInt.toNat]! = d.depth[v.toInt.toNat]! := by
    exact ⟨by rw [frequencies, ite_eq_right (by omega)], by rw [depths, ite_eq_right (by omega)]⟩
  have newOrigin (q : Nat) (lo : 1 ≤ q) (hi : q ≤ len - 1) :
      H'[q]! = node ∨ ∃ i : Nat, 1 ≤ i ∧ i ≤ len ∧ H'[q]! = d.heap[i]! := by
    obtain ⟨σ, range, _inj, equal⟩ := hperm
    have position := range q lo hi
    have entry := equal q lo hi
    rw [hHeap2] at entry
    change H'[q]! = (if σ q = 1 then node else H[σ q]!) at entry
    by_cases root : σ q = 1
    · exact Or.inl (by simpa only [root,ite_true] using entry)
    · rw [ite_eq_right root] at entry
      obtain ⟨i, lower, upper, old⟩ := horigin (σ q) position.1 position.2
      exact Or.inr ⟨i, by omega, upper, entry.trans old⟩
  have updatedView : HuffmanQueueView tk {d2 with heap := H'} (len - 1) (huffmanAddParent R n m node) := by
    constructor
    · intro q lo hi
      rcases newOrigin q lo hi with same | ⟨i,lower,upper,same⟩
      · change (huffmanAddParent R n m node H'[q]!).weight = _
        rw [same]
        simpa only [huffmanAddParent,ite_true] using parentWeight
      · have before := hbefore i lower upper
        have different : d.heap[i]! ≠ node := by intro equal; rw [equal] at before; omega
        change (huffmanAddParent R n m node H'[q]!).weight = _
        rw [same]
        simpa only [huffmanAddParent,ite_eq_right different] using (view.weight i lower upper).trans (oldCells _ before.1 before.2).1.symm
    · intro q lo hi
      rcases newOrigin q lo hi with same | ⟨i,lower,upper,same⟩
      · change (huffmanAddParent R n m node H'[q]!).height = _
        rw [same]
        simpa only [huffmanAddParent,ite_true] using parentHeight
      · have before := hbefore i lower upper
        have different : d.heap[i]! ≠ node := by intro equal; rw [equal] at before; omega
        change (huffmanAddParent R n m node H'[q]!).height = _
        rw [same]
        simpa only [huffmanAddParent,ite_eq_right different] using (view.height i lower upper).trans (congrArg UInt8.toNat (oldCells _ before.1 before.2).2).symm
  have updatedHeight : ∀ q, 1 ≤ q → q ≤ len - 1 →
      ((huffmanAddParent R n m node) ({d2 with heap := H'} : DeflateState).heap[q]!).height ≤ stage + 1 := by
    intro q lo hi
    rcases newOrigin q lo hi with same | ⟨i,lower,upper,same⟩
    · change (huffmanAddParent R n m node H'[q]!).height ≤ _
      rw [same]
      simp only [huffmanAddParent,ite_true,HTree.height]
      exact Nat.add_le_add_right (Nat.max_le.mpr ⟨nHeight,mHeight⟩) 1
    · have before := hbefore i lower upper
      have different : d.heap[i]! ≠ node := by intro equal; rw [equal] at before; omega
      change (huffmanAddParent R n m node H'[q]!).height ≤ _
      rw [same]
      simpa only [huffmanAddParent,ite_eq_right different] using Nat.le_trans (heightBound i lower upper) (Nat.le_succ stage)
  have queuePerm : (huffmanQueue (huffmanAddParent R n m node) (fun i => H'[i]!) (len - 1)).Perm
      (HTree.node (R n) (R m) :: rest) := by
    apply List.perm_iff_count.mpr
    intro t
    let F : Int32 → Nat := fun v => if huffmanAddParent R n m node v = t then 1 else 0
    have count := hcount' F
    rw [hroot,hHeap2] at count
    have oldSum : GB.rs (fun i => F H[i+1]!) (len-1) =
        GB.rs (fun i => if R H[i+1]! = t then 1 else 0) (len-1) := by
      apply GB.rs_congr
      intro i bound
      have before := hB (i+1) (by omega) (by omega)
      have different : H[i+1]! ≠ node := by intro equal; rw [equal] at before; omega
      simp only [F,huffmanAddParent,ite_eq_right different]
    rw [oldSum,← huffmanQueue_count R (fun i => H[i]!) (len-1) t,remaining] at count
    have mBefore := hbefore pm pmlo pmhi
    have mDifferent : m ≠ node := by intro equal; rw [← second,equal] at mBefore; omega
    have fn : F node = if HTree.node (R n) (R m) = t then 1 else 0 := by simp only [F,huffmanAddParent,ite_true]
    have fm : F m = if R m = t then 1 else 0 := by simp only [F,huffmanAddParent,ite_eq_right mDifferent]
    rw [fn,fm] at count
    change (huffmanQueue (huffmanAddParent R n m node) (fun i => H'[i]!) (len-1)).count t = _
    rw [huffmanQueue_count]
    change GB.rs (fun i => F H'[i+1]!) (len-1) = _
    by_cases mt : R m = t <;> by_cases pt : HTree.node (R n) (R m) = t <;>
      simp [List.count_cons,mt,pt] at count ⊢ <;> omega
  refine ⟨hnext,n,m,rest,?_,?_,selected,queuePerm,updatedView,updatedHeight⟩
  · change H'[(d.heap_max.toInt-1).toNat]! = n
    rw [← hh1,hframe _ (by omega),hHeap2]
    exact hkeepn
  · change H'[(d.heap_max.toInt-2).toNat]! = m
    rw [← hh2,hframe _ (by omega),hHeap2]
    exact hkeepm
end Zlib.Trees.Proofs
#print axioms Zlib.Trees.Proofs.ws_btMergeBody_huffman
