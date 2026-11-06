import ZlibF.Math.DeflateHeap
import ZlibF.Proof.«trees.c.heap.pqrun»
import ZlibF.Proof.«trees.c.build.force»

/-! # trees.c: actual heap construction and preservation of its leaves -/

namespace Zlib.Trees.Proofs
open C Zlib.Trees

/-- The actual descending `pqdownheap` loop, including the initial state
read, signed division by two and separate checked decrement. -/
def btHeapify (s : DeflateStatePtr) (tree : CtDataPtr) : M Int32 := do
  cfor (σ := Int32) (fun n => pure (decide (n.toInt ≥ 1))) (fun n => isub n 1)
    (fun n => do pqdownheap s tree n; pure n) ((← rd s).heap_len / 2)

/-- Every leaf representation fact survives a permutation of the populated
heap interval. Completeness uses surjectivity, not just forward validity. -/
theorem BTLeafInv.heap_perm {tk : TK} {N : Nat} {mc : Int32} {d : DeflateState}
    (hi : BTLeafInv tk N mc d) (H : Array Int32) (hsz : H.size = d.heap.size)
    (hp : PermOn (fun q => H[q]!) (fun q => d.heap[q]!) d.heap_len.toInt.toNat) :
    BTLeafInv tk N mc { d with heap := H } := by
  have hlen0 : 0 ≤ d.heap_len.toInt := by have := hi.count; omega
  have hfreq : btFreq tk { d with heap := H } = btFreq tk d := by
    funext v; unfold btFreq; rw [tk_arr_heap]
  obtain ⟨σ, hr, hinj, he⟩ := hp
  dsimp only at hr hinj he
  refine ⟨hi.n3, hi.n286, ?_, hi.depth, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [tk_arr_heap]; exact hi.tree
  · change H.size = 573; rw [hsz, hi.heap]
  · rw [hfreq]; exact hi.count
  · rw [hfreq]; exact hi.maxCode
  · intro q hq1 hq2
    change (q : Int) ≤ d.heap_len.toInt at hq2
    have hq : q ≤ d.heap_len.toInt.toNat := by omega
    have hσ := hr q hq1 hq
    have hv := hi.valid (σ q) hσ.1 (by omega)
    change 0 ≤ H[q]!.toInt ∧ H[q]!.toInt < N ∧ _
    rw [he q hq1 hq, hfreq]
    exact hv
  · intro q q' hq1 hq2 hq'1 hq'2 heq
    have hq : q ≤ d.heap_len.toInt.toNat := by change (q : Int) ≤ d.heap_len.toInt at hq2; omega
    have hq' : q' ≤ d.heap_len.toInt.toNat := by change (q' : Int) ≤ d.heap_len.toInt at hq'2; omega
    have hσ := hr q hq1 hq
    have hσ' := hr q' hq'1 hq'
    change H[q]! = H[q']! at heq
    rw [he q hq1 hq, he q' hq'1 hq'] at heq
    exact hinj q q' hq1 hq hq'1 hq' (hi.injective _ _ hσ.1 (by omega) hσ'.1 (by omega) heq)
  · intro v hv hfv
    rw [hfreq] at hfv
    obtain ⟨q, hq1, hq2, hqv⟩ := hi.complete v hv hfv
    obtain ⟨q', hq'1, hq'2, hqeq⟩ := PermOn.preimage ⟨σ, hr, hinj, he⟩ q hq1 (by omega)
    refine ⟨q', hq'1, by dsimp; omega, ?_⟩
    change H[q']!.toInt = v
    rw [hqeq]; exact hqv
  · intro v hv hfv
    rw [hfreq] at hfv
    exact hi.usedDepth v hv hfv
  · intro v hv hfv
    rw [hfreq] at hfv
    rw [tk_arr_heap]
    exact hi.unusedLength v hv hfv

/-- The complete actual heapify loop terminates with all parent/child edges
ordered by zlib's frequency/depth comparison. Only the populated heap cells
change, and their contents are a permutation of the original cells. No
`pqdownheap` contract is assumed; its translated execution theorem is used. -/
theorem ws_btHeapify {h0 : Heap} {id : Nat} (tk : TK) (d : DeflateState) (len : Nat)
    (hlen : d.heap_len.toInt = len) (hsz : len < d.heap.size) (hbig : d.heap.size ≤ 573)
    (hval : ∀ i, 1 ≤ i → i ≤ len → NV (tk.arr d) d.depth d.heap[i]!) :
    WS h0 id (btHeapify (Sp id) (.ref (tk.ref id) 0)) d (fun r e =>
      r.toInt = 0 ∧ ∃ H : Array Int32, e = { d with heap := H } ∧ H.size = d.heap.size ∧
        (∀ i, ¬ (1 ≤ i ∧ i ≤ len) → H[i]! = d.heap[i]!) ∧
        PermOn (fun i => H[i]!) (fun i => d.heap[i]!) len ∧
        HeapOK (sm (tk.arr d) d.depth) (fun i => H[i]!) len 0) := by
  have hi1 : (1 : Int32).toInt = 1 := rfl
  have hi2 : (2 : Int32).toInt = 2 := rfl
  have hstart : (d.heap_len / 2).toInt = (len / 2 : Nat) := by
    rw [Int32.toInt_div_of_ne_right _ _ (by decide +kernel), hi2, hlen]
    exact (Int.ofNat_tdiv len 2).symm
  let Inv : Int32 → DeflateState → Prop := fun n e =>
    0 ≤ n.toInt ∧ n.toInt ≤ (len / 2 : Nat) ∧ ∃ H : Array Int32,
      e = { d with heap := H } ∧ H.size = d.heap.size ∧
      (∀ i, ¬ (1 ≤ i ∧ i ≤ len) → H[i]! = d.heap[i]!) ∧
      PermOn (fun i => H[i]!) (fun i => d.heap[i]!) len ∧
      HeapOK (sm (tk.arr d) d.depth) (fun i => H[i]!) len n.toInt.toNat
  unfold btHeapify
  refine WS.bind' ws_rd fun dz e1 ⟨hdz, he1⟩ => ?_
  subst e1; subst dz
  refine WS.cfor2 Inv (fun n _ => n.toInt.toNat) _ ?_
    ⟨by omega, by omega, d.heap, rfl, rfl, fun _ _ => rfl, PermOn.refl _ _, ?_⟩
    (by simp only [fuel]; omega)
  · intro n e ⟨hn0, hn1, H, he, hsH, hf, hp, hok⟩
    subst e
    refine WS.pure' ?_
    by_cases hpos : 1 ≤ n.toInt
    · refine Or.inr ⟨by simp only [decide_eq_true_eq]; exact hpos, ?_⟩
      have hn : n.toInt = (n.toInt.toNat : Nat) := by omega
      have hvals : ∀ i, 1 ≤ i → i ≤ len → NV (tk.arr { d with heap := H }) d.depth H[i]! := by
        obtain ⟨σ, hr, hinj, heq⟩ := hp
        dsimp only at hr hinj heq
        intro i hi1 hi2
        rw [tk_arr_heap, heq i hi1 hi2]
        exact hval _ (hr i hi1 hi2).1 (hr i hi1 hi2).2
      have horder : HeapOK (sm (tk.arr { d with heap := H }) d.depth) (fun i => H[i]!) len n.toInt.toNat := by
        rw [tk_arr_heap]; exact hok
      simp only [M_bind_assoc, M_pure_bind]
      refine WS.bind' (ws_pqdownheap tk { d with heap := H } n n.toInt.toNat len hn (by omega)
        (by omega) hlen (by dsimp; omega) (by dsimp; omega) hvals horder)
        fun _ e1 ⟨H', he1, hsH', hf', hp', hok'⟩ => ?_
      subst e1
      refine WS.mono (ws_isub n 1 (by omega) (by omega)) ?_
      intro n' e1 ⟨hn', he1⟩
      subst e1
      have hcut : n'.toInt.toNat = n.toInt.toNat - 1 := by omega
      refine ⟨⟨by omega, by omega, H', rfl,
        by dsimp at hsH'; omega, ?_, hp'.trans' hp, ?_⟩, by omega⟩
      · intro i hi; exact (hf' i hi).trans (hf i hi)
      · rw [tk_arr_heap] at hok'
        simpa only [hcut] using hok'
    · refine Or.inl ⟨by simp only [decide_eq_false_iff_not]; omega,
        by omega, H, rfl, hsH, hf, hp, ?_⟩
      have hn : n.toInt.toNat = 0 := by omega
      simpa only [hn] using hok
  · intro c hc1 hc2 hcp
    omega

/-- The actual heapify loop obtains its node bounds from the leaf invariant,
preserves that invariant, and establishes both heap order and root minimality.
The latter is the comparison used by the subsequent two-node merge. -/
theorem ws_btHeapify_leaf {h0 : Heap} {id : Nat} (tk : TK) (d : DeflateState) (N : Nat) (mc : Int32)
    (hi : BTLeafInv tk N mc d) :
    WS h0 id (btHeapify (Sp id) (.ref (tk.ref id) 0)) d (fun r e =>
      r.toInt = 0 ∧ BTLeafInv tk N mc e ∧ ∃ H : Array Int32,
        e = { d with heap := H } ∧ H.size = d.heap.size ∧
        (∀ i, ¬ (1 ≤ i ∧ i ≤ d.heap_len.toInt.toNat) → H[i]! = d.heap[i]!) ∧
        PermOn (fun i => H[i]!) (fun i => d.heap[i]!) d.heap_len.toInt.toNat ∧
        HeapOK (sm (tk.arr d) d.depth) (fun i => H[i]!) d.heap_len.toInt.toNat 0 ∧
        ∀ q, 1 ≤ q → q ≤ d.heap_len.toInt.toNat → sm (tk.arr d) d.depth H[1]! H[q]! = true) := by
  let len := d.heap_len.toInt.toNat
  have hlen : d.heap_len.toInt = len := by have := hi.count; dsimp only [len]; omega
  have hcount := Math.scanCount_le (btFreq tk d) N
  have hlenN : len ≤ N := by have := hi.count; omega
  have hval : ∀ i, 1 ≤ i → i ≤ len → NV (tk.arr d) d.depth d.heap[i]! := by
    intro i hi1 hi2
    obtain ⟨h0, hN, hf⟩ := hi.valid i hi1 (by omega)
    exact ⟨h0, by have := hi.tree; omega, by have := hi.depth; omega⟩
  refine WS.mono (ws_btHeapify tk d len hlen (by rw [hi.heap]; have := hi.n286; omega)
    (by rw [hi.heap]; omega) hval) ?_
  intro r e ⟨hr, H, he, hsz, hf, hp, ho⟩
  subst e
  refine ⟨hr, hi.heap_perm H hsz hp, H, rfl, hsz, hf, hp, ho, ?_⟩
  exact ho.root_min (sm_ok (tk.arr d) d.depth)

/-- The descriptor field selected by a dynamic-tree kind. -/
def TK.descRef : TK → Nat → TreeDescRef
  | .lit, id => .in_dstate_l_desc id
  | .dist, id => .in_dstate_d_desc id
  | .bl, id => .in_dstate_bl_desc id

def TK.getDesc : TK → DeflateState → TreeDesc
  | .lit, d => d.l_desc
  | .dist, d => d.d_desc
  | .bl, d => d.bl_desc

def TK.setDesc : TK → DeflateState → TreeDesc → DeflateState
  | .lit, d, v => { d with l_desc := v }
  | .dist, d, v => { d with d_desc := v }
  | .bl, d, v => { d with bl_desc := v }

@[simp] theorem tk_arr_setDesc (tk dk : TK) (d : DeflateState) (v : TreeDesc) :
    tk.arr (dk.setDesc d v) = tk.arr d := by cases tk <;> cases dk <;> rfl

@[simp] theorem tk_setDesc_heap (dk : TK) (d : DeflateState) (v : TreeDesc) :
    (dk.setDesc d v).heap = d.heap := by cases dk <;> rfl

@[simp] theorem tk_setDesc_len (dk : TK) (d : DeflateState) (v : TreeDesc) :
    (dk.setDesc d v).heap_len = d.heap_len := by cases dk <;> rfl

@[simp] theorem tk_setDesc_depth (dk : TK) (d : DeflateState) (v : TreeDesc) :
    (dk.setDesc d v).depth = d.depth := by cases dk <;> rfl

/-- Storing a descriptor does not change any of the leaf data. -/
theorem BTLeafInv.setDesc {tk : TK} {N : Nat} {mc : Int32} {d : DeflateState}
    (hi : BTLeafInv tk N mc d) (dk : TK) (v : TreeDesc) : BTLeafInv tk N mc (dk.setDesc d v) := by
  cases tk <;> cases dk <;>
    exact ⟨hi.n3, hi.n286, hi.tree, hi.depth, hi.heap, hi.count, hi.maxCode,
      hi.valid, hi.injective, hi.complete, hi.usedDepth, hi.unusedLength⟩

/-- The actual descriptor read/store and heapify statements, in source order. -/
def btOrder (s : DeflateStatePtr) (desc : TreeDescPtr) (tree : CtDataPtr) (mc : Int32) : M Unit := do
  stTreeDesc desc { (← ldTreeDesc desc) with max_code := mc }
  let _ ← btHeapify s tree

/-- The maximum-symbol write is an actual typed descriptor access. -/
theorem ws_btSaveMax {h0 : Heap} {id : Nat} (dk : TK) (d : DeflateState) (mc : Int32) :
    WS h0 id (do
      stTreeDesc (some (dk.descRef id)) { (← ldTreeDesc (some (dk.descRef id))) with max_code := mc }) d
      (fun _ e => e = dk.setDesc d { dk.getDesc d with max_code := mc }) := by
  refine WS.of_eq (a := ()) (d' := dk.setDesc d { dk.getDesc d with max_code := mc }) ?_ rfl
  cases dk <;> simp [TK.descRef, TK.setDesc, TK.getDesc, ldTreeDesc, stTreeDesc,
    TreeDescRef.get, TreeDescRef.put, TreeDescRef.isRo, bind_app, setD, upd_upd]

/-- The actual descriptor write followed by the complete heapify loop.
The selected descriptor gets the exact maximum; the same used leaves remain
in a heap ordered by the source comparison, with a minimal root. -/
theorem ws_btOrder_leaf {h0 : Heap} {id : Nat} (tk dk : TK) (d : DeflateState) (N : Nat) (mc : Int32)
    (hi : BTLeafInv tk N mc d) :
    WS h0 id (btOrder (Sp id) (some (dk.descRef id)) (.ref (tk.ref id) 0) mc) d (fun _ e =>
      BTLeafInv tk N mc e ∧ ∃ H : Array Int32,
        e = { dk.setDesc d { dk.getDesc d with max_code := mc } with heap := H } ∧
        H.size = d.heap.size ∧
        (∀ i, ¬ (1 ≤ i ∧ i ≤ d.heap_len.toInt.toNat) → H[i]! = d.heap[i]!) ∧
        PermOn (fun i => H[i]!) (fun i => d.heap[i]!) d.heap_len.toInt.toNat ∧
        HeapOK (sm (tk.arr d) d.depth) (fun i => H[i]!) d.heap_len.toInt.toNat 0 ∧
        (dk.descRef id).get (setD h0 id e) = some { dk.getDesc d with max_code := mc } ∧
        ∀ q, 1 ≤ q → q ≤ d.heap_len.toInt.toNat → sm (tk.arr d) d.depth H[1]! H[q]! = true) := by
  unfold btOrder
  rw [← M_bind_assoc]
  refine WS.bind' (ws_btSaveMax dk d mc) fun _ e1 he1 => ?_
  subst e1
  refine WS.bind' (ws_btHeapify_leaf tk _ N mc (hi.setDesc dk _))
    fun n e ⟨hn, hleaf, H, he, hsH, hf, hp, ho, hmin⟩ => ?_
  subst e
  simp only [tk_arr_setDesc, tk_setDesc_depth, tk_setDesc_len, tk_setDesc_heap] at hsH hf hp ho hmin
  refine WS.pure' ⟨hleaf, H, rfl, hsH, hf, hp, ho, ?_, hmin⟩
  cases dk <;> simp [TK.descRef, TK.getDesc, TK.setDesc, TreeDescRef.get, setD]

/-- The scan preserves descriptors and the merge-tail boundary. -/
theorem BTScanInv.desc_heap_max {tk : TK} {d e : DeflateState} {N : Nat} {mc : Int32}
    (hi : BTScanInv tk d N mc e) (dk : TK) :
    dk.getDesc e = dk.getDesc d ∧ e.heap_max = d.heap_max := by
  obtain ⟨T, H, D, hl, rfl, rest⟩ := hi
  cases tk <;> cases dk <;> exact ⟨rfl, rfl⟩

/-- The exact repair trace preserves descriptors and the merge-tail boundary. -/
theorem BTForceTrace.desc_heap_max {tk : TK} {sl : Option (Nat → UInt16)}
    {k : Nat} {mc0 mc : Int32} {d0 d : DeflateState}
    (h : BTForceTrace tk sl k mc0 d0 mc d) (dk : TK) :
    dk.getDesc d = dk.getDesc d0 ∧ d.heap_max = d0.heap_max := by
  obtain ⟨T, H, D, hl, O, S, rfl⟩ := h.frame
  cases tk <;> cases dk <;> exact ⟨rfl, rfl⟩

end Zlib.Trees.Proofs
