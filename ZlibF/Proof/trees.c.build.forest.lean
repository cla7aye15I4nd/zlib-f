import ZlibF.Proof.«trees.c.build.merge»
import ZlibF.Proof.«trees.c.heap.gbre»
import ZlibF.Math.DeflateForest

/-! # trees.c: retaining the forest represented by the heap queue and tail -/

namespace Zlib.Trees.Proofs
open C Zlib.Trees

/-- The actual two-node selection and child stores preserve every previously
stored tail cell. The queue/tail gap is numeric data, not a callee contract. -/
theorem ws_btMergeOpen_tail {h0 : Heap} {id : Nat} (tk : TK) (d : DeflateState) (len : Nat)
    (hlen : d.heap_len.toInt = len) (h2 : 2 ≤ len) (hsz : len < d.heap.size)
    (hbig : d.heap.size ≤ 573) (hmH : d.heap_max.toInt ≤ d.heap.size)
    (hgap : (len : Int) < d.heap_max.toInt - 1)
    (hval : ∀ i, 1 ≤ i → i ≤ len → NV (tk.arr d) d.depth d.heap[i]!)
    (hinj : ∀ i j, 1 ≤ i → i ≤ len → 1 ≤ j → j ≤ len → d.heap[i]! = d.heap[j]! → i = j)
    (ho : HeapOK (sm (tk.arr d) d.depth) (fun i => d.heap[i]!) len 0) :
    WS h0 id (btMergeOpen (Sp id) (.ref (tk.ref id) 0)) d (fun _ e =>
      ∀ q : Nat, d.heap_max.toInt ≤ (q : Int) → e.heap[q]! = d.heap[q]!) := by
  unfold btMergeOpen
  refine WS.bind' (ws_btPick2 tk d len hlen h2 hsz hbig hval hinj ho)
    fun pair e1 ⟨hl, H, hn, hm, hhl, he1, hsH, hframe, hp, horder, hnv, hmv, hnm,
      hminn, hminm, horigin, hcomplete, hno, hHinj, hcount⟩ => ?_
  subst e1
  rcases pair with ⟨n, m⟩
  refine WS.bind' (ws_btKeepChildren { d with heap := H, heap_len := hl } n m
    (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega))
    fun _ e2 ⟨hm1, hm2, hh1, hh2, he2, hsH', hnKeep, hmKeep, hKeepFrame⟩ => ?_
  subst e2
  refine WS.pure' ?_
  intro q hq
  have hqH := hKeepFrame q (by dsimp only at hh1; omega) (by dsimp only at hh2; omega)
  change ((H.set! hm1.toInt.toNat n).set! hm2.toInt.toNat m)[q]! = d.heap[q]!
  rw [hqH]
  exact hframe q (by omega)

/-- Parent creation sees the same tree and depth through heap-control-only
updates. This is a record identity, not an assumed functional contract. -/
theorem btParentState_heap_view (tk : TK) (d : DeflateState) (H : Array Int32) (hl hm n m node : Int32) :
    tk.arr (btParentState tk { d with heap := H, heap_len := hl, heap_max := hm } n m node) =
      tk.arr (btParentState tk d n m node) ∧
    (btParentState tk { d with heap := H, heap_len := hl, heap_max := hm } n m node).depth =
      (btParentState tk d n m node).depth := by
  cases tk <;> exact ⟨rfl, rfl⟩

/-- A singleton permutation of a root-replaced queue contains that root. -/
theorem PermOn.singleton_root {A H : Nat → Int32} {node : Int32}
    (hp : PermOn A (fun i => if i = 1 then node else H i) 1) : A 1 = node := by
  obtain ⟨q, hq1, hq2, hq⟩ := hp.preimage 1 (by omega) (by omega)
  have hq' : q = 1 := by omega
  simpa only [hq', ite_true] using hq

/-- A whole actual merge retains the old tail, gives exact parent-array
effects, and retains exact queue counts. Both selected nodes came from the
old queue. When this is the last merge, its new singleton root is the fresh
parent. All called-function behavior is supplied by checked execution
proofs. -/
theorem ws_btMergeBody_forest {h0 : Heap} {id : Nat} (tk : TK) (d : DeflateState) (len : Nat) (node : Int32)
    (hlen : d.heap_len.toInt = len) (h2 : 2 ≤ len) (hsz : len < d.heap.size)
    (hbig : d.heap.size ≤ 573) (hmH : d.heap_max.toInt ≤ d.heap.size)
    (hgap : (len : Int) < d.heap_max.toInt - 1)
    (hp : NV (tk.arr d) d.depth node) (hinc : node.toInt < 2147483647)
    (hbefore : ∀ i, 1 ≤ i → i ≤ len → 0 ≤ d.heap[i]!.toInt ∧ d.heap[i]!.toInt < node.toInt)
    (hinj : ∀ i j, 1 ≤ i → i ≤ len → 1 ≤ j → j ≤ len → d.heap[i]! = d.heap[j]! → i = j)
    (ho : HeapOK (sm (tk.arr d) d.depth) (fun i => d.heap[i]!) len 0) :
    WS h0 id (btMergeBody (Sp id) (.ref (tk.ref id) 0) node) d (fun next e =>
      next.toInt = node.toInt + 1 ∧ ∃ n m : Int32, n ≠ m ∧
        (∃ q : Nat, 1 ≤ q ∧ q ≤ len ∧ n = d.heap[q]!) ∧
        (∃ q : Nat, 1 ≤ q ∧ q ≤ len ∧ m = d.heap[q]!) ∧
        e.heap_len.toInt = (len : Int) - 1 ∧ e.heap_max.toInt = d.heap_max.toInt - 2 ∧
        e.heap[(d.heap_max.toInt - 1).toNat]! = n ∧ e.heap[(d.heap_max.toInt - 2).toNat]! = m ∧
        (∀ q : Nat, d.heap_max.toInt ≤ (q : Int) → e.heap[q]! = d.heap[q]!) ∧
        tk.arr e = tk.arr (btParentState tk d n m node) ∧ e.depth = (btParentState tk d n m node).depth ∧
        (len = 2 → e.heap[1]! = node) ∧
        ∀ F : Int32 → Nat, GB.rs (fun i => F e.heap[i + 1]!) (len - 1) + F n + F m =
          GB.rs (fun i => F d.heap[i + 1]!) len + F node) := by
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
  have hview := btParentState_heap_view tk d H hl hm2 n m node
  refine ⟨hnext, n, m, hnm, ⟨1, by omega, by omega, hn⟩, hmorigin,
    by simpa only [d2, btParentState_len] using hhl, by simpa only [d2, btParentState_max] using hh2,
    ?_, ?_, ?_, ?_, hview.2, ?_, ?_⟩
  · change H'[(d.heap_max.toInt - 1).toNat]! = n
    rw [← hh1, hframe _ (by omega), hHeap2]
    exact hkeepn
  · change H'[(d.heap_max.toInt - 2).toNat]! = m
    rw [← hh2, hframe _ (by omega), hHeap2]
    exact hkeepm
  · intro q hq
    change H'[q]! = d.heap[q]!
    rw [hframe q (by omega), hHeap2]
    exact htail q hq
  · rw [tk_arr_heap]
    exact hview.1
  · intro hlen2
    have hp' : PermOn (fun i => H'[i]!) (fun i => if i = 1 then node else d2.heap[i]!) 1 := by
      simpa only [hlen2] using hperm
    exact hp'.singleton_root
  · intro F
    have hc := hcount F
    have hc' := hcount' F
    rw [hroot, hHeap2] at hc'
    change GB.rs (fun i => F H'[i + 1]!) (len - 1) + F n + F m = _
    omega


/-- A forest consists of the active queue and the descending retained tail.
Its observations are exactly the original leaves plus every parent created
so far. Parent links and placement describe the actual source layout. -/
structure BTForest (tk : TK) (N K j : Nat) (mc : Int32) (d0 : DeflateState)
    (node : Int32) (d : DeflateState) : Prop where
  initial : BTLeafInv tk N mc d0
  initial_len : d0.heap_len.toInt = K
  queue : BTMergeQueue tk N K j node d
  observations : ∀ F : Nat → Nat,
    GB.poolSum (Hn d) (K - j) (2 * j) F =
      GB.rs (fun i => F (Hn d0 (i + 1))) K + GB.rs (fun i => F (N + i)) j
  tail_valid : ∀ q : Nat, 573 - 2 * j ≤ q → q < 573 →
    0 ≤ d.heap[q]!.toInt ∧ d.heap[q]!.toInt < node.toInt
  parent : ∀ q : Nat, 573 - 2 * j ≤ q → q < 573 →
    (tk.arr d)[Hn d q]!.dl = UInt16.ofNat (GB.dadP N q)
  placement : ∀ q : Nat, 573 - 2 * j ≤ q → q < 573 → N ≤ Hn d q →
    q < 571 - 2 * (Hn d q - N)
  leaf_freq : ∀ v < N, (tk.arr d)[v]!.fc = (tk.arr d0)[v]!.fc
  unused : ∀ v < N, btFreq tk d0 v = 0 → (tk.arr d)[v]!.dl = 0
  leaf_depth : ∀ v < N, btFreq tk d0 v ≠ 0 → d.depth[v]! = 0
  last_root : j + 1 = K → d.heap[1]!.toInt = (N + j - 1 : Nat)

/-- The actual prepared leaves establish the complete initial forest.
The tail is empty at this stage, so its link and placement facts are derived
without assumptions about old heap contents. -/
theorem BTForest.of_leaf {tk : TK} {d : DeflateState} {N : Nat} {mc node : Int32}
    (hi : BTLeafInv tk N mc d) (h2 : 2 ≤ d.heap_len.toInt) (hm : d.heap_max = HEAP_SIZE)
    (hn : node.toInt = N)
    (hT : N + d.heap_len.toInt.toNat - 1 ≤ (tk.arr d).size)
    (hD : N + d.heap_len.toInt.toNat - 1 ≤ d.depth.size)
    (ho : HeapOK (sm (tk.arr d) d.depth) (fun i => d.heap[i]!) d.heap_len.toInt.toNat 0) :
    BTForest tk N d.heap_len.toInt.toNat 0 mc d node d := by
  refine ⟨hi, by omega, BTMergeQueue.of_leaf hi h2 hm hn hT hD ho, ?_, ?_, ?_, ?_,
    by intros; rfl, hi.unusedLength, hi.usedDepth, ?_⟩
  · intro F
    simp only [Nat.sub_zero, Nat.mul_zero, GB.poolSum, GB.rs_zero, Nat.add_zero]
  · intro q hq hq'; omega
  · intro q hq hq'; omega
  · intro q hq hq'; omega
  · intro heq; omega

/-- Initial queue indices are distinct natural-valued leaf nodes below N. -/
theorem BTForest.initial_nodes {tk : TK} {d0 d : DeflateState} {N K j : Nat} {mc node : Int32}
    (hi : BTForest tk N K j mc d0 node d) :
    (∀ i < K, Hn d0 (i + 1) < N) ∧
    (∀ i i', i < K → i' < K → Hn d0 (i + 1) = Hn d0 (i' + 1) → i = i') := by
  have hlen := hi.initial_len
  constructor
  · intro i hiK
    have hv := hi.initial.valid (i + 1) (by omega) (by omega)
    unfold Hn
    omega
  · intro i i' hiK hiK' heq
    have hv := hi.initial.valid (i + 1) (by omega) (by omega)
    have hv' := hi.initial.valid (i' + 1) (by omega) (by omega)
    have he : d0.heap[i + 1]! = d0.heap[i' + 1]! := Int32.toInt_inj.mp (by unfold Hn at heq; omega)
    have := hi.initial.injective (i + 1) (i' + 1) (by omega) (by omega) (by omega) (by omega) he
    omega

/-- Exact observations establish uniqueness across the queue and tail,
including between those two regions. -/
theorem BTForest.injective {tk : TK} {d0 d : DeflateState} {N K j : Nat} {mc node : Int32}
    (hi : BTForest tk N K j mc d0 node d) :
    ∀ q q', ((1 ≤ q ∧ q ≤ K - j) ∨ (573 - 2 * j ≤ q ∧ q < 573)) →
      ((1 ≤ q' ∧ q' ≤ K - j) ∨ (573 - 2 * j ≤ q' ∧ q' < 573)) → Hn d q = Hn d q' → q = q' := by
  have hinit := hi.initial_nodes
  have hseq := GB.pool_unique (Hn d) (Hn d0) (K - j) (2 * j) K N j hinit.1 hinit.2 hi.observations
  have hbound : K - j + 2 * j = K + j := by have := hi.queue.stage; omega
  rw [hbound] at hseq
  exact GB.pool_heap_injective (Hn d) K j (by have := hi.queue.kN; have := hi.queue.n286; omega)
    hi.queue.stage hseq

/-- Every active leaf came from the prepared nonzero-frequency leaf set. -/
theorem BTForest.leaf_used {tk : TK} {d0 d : DeflateState} {N K j : Nat} {mc node : Int32}
    (hi : BTForest tk N K j mc d0 node d) (q : Nat)
    (hq : (1 ≤ q ∧ q ≤ K - j) ∨ (573 - 2 * j ≤ q ∧ q < 573)) (hN : Hn d q < N) :
    btFreq tk d0 (Hn d q) ≠ 0 := by
  have hK : K ≤ 286 := by have := hi.queue.kN; have := hi.queue.n286; omega
  obtain ⟨i, hiB, hei⟩ := GB.poolAt_preimage (Hn d) K j q hK hi.queue.stage hq
  have hiB' : i < K - j + 2 * j := by have := hi.queue.stage; omega
  rcases GB.pool_origin (Hn d) (Hn d0) (K - j) (2 * j) K N j hi.observations i hiB' with
    ⟨a, ha, he⟩ | he
  · have hv := hi.initial.valid (a + 1) (by omega) (by have := hi.initial_len; omega)
    rw [hei] at he
    change (d0.heap[a + 1]!).toInt.toNat = Hn d q at he
    rw [he] at hv
    exact hv.2.2
  · rw [hei] at he
    omega

/-- All retained old tail nodes are distinct from a selected old queue node. -/
theorem BTForest.queue_not_tail {tk : TK} {d0 d : DeflateState} {N K j : Nat} {mc node : Int32}
    (hi : BTForest tk N K j mc d0 node d) (p q : Nat)
    (hp1 : 1 ≤ p) (hp2 : p ≤ K - j) (hq1 : 573 - 2 * j ≤ q) (hq2 : q < 573) :
    Hn d q ≠ Hn d p := by
  intro heq
  have he := hi.injective q p (Or.inr ⟨hq1, hq2⟩) (Or.inl ⟨hp1, hp2⟩) heq
  have := hi.queue.stage
  have := hi.queue.kN
  have := hi.queue.n286
  omega


/-- The actual merge preserves the full queue/tail forest. Old parent links
and heap-tail entries are framed; the two new children point to the numeric
fresh parent. Leaf frequencies, unused lengths and initialized leaf depths
are preserved. The initial leaf representation is carried from the actual
prefix, not supplied as a called-function contract. -/
theorem ws_btMergeBody_forest_inv {h0 : Heap} {id : Nat} {tk : TK} {d0 d : DeflateState}
    {N K j : Nat} {mc node : Int32} (hi : BTForest tk N K j mc d0 node d) (hmore : j + 1 < K) :
    WS h0 id (btMergeBody (Sp id) (.ref (tk.ref id) 0) node) d
      (fun next e => BTForest tk N K (j + 1) mc d0 next e) := by
  have hK : K ≤ 286 := by have := hi.queue.kN; have := hi.queue.n286; omega
  have hj := hi.queue.stage
  have hcounter := hi.queue.counter
  have hlen := hi.queue.len
  have hmax := hi.queue.max
  have hsize := hi.queue.heap
  have hTsize := hi.queue.tree
  have hDsize := hi.queue.depth
  have hN3 := hi.queue.n3
  have hNb := hi.queue.n286
  have hKN := hi.queue.kN
  have hnode : NV (tk.arr d) d.depth node := ⟨by omega, by omega, by omega⟩
  refine WS.mono (merge_ws_and (ws_btMergeBody_queue hi.queue hmore)
    (ws_btMergeBody_forest tk d (K - j) node hlen (by omega) (by omega) (by omega)
      (by omega) (by omega) hnode (by omega)
      (fun i hi1 hi2 => hi.queue.valid i hi1 (by omega))
      (fun i i' hi1 hi2 hi'1 hi'2 => hi.queue.injective i i' hi1 (by omega) hi'1 (by omega)) hi.queue.order)) ?_
  intro next e ⟨hq, hnext, n, m, hnm, ⟨pn, hpn1, hpn2, hpn⟩, ⟨pm, hpm1, hpm2, hpm⟩,
    hlen', hmax', hkeepn, hkeepm, htail, htree, hdepth, hroot, hcount⟩
  have hnv := hi.queue.valid pn hpn1 (by omega)
  have hmv := hi.queue.valid pm hpm1 (by omega)
  rw [← hpn] at hnv
  rw [← hpm] at hmv
  have hnV : NV (tk.arr d) d.depth n := ⟨hnv.1, by omega, by omega⟩
  have hmV : NV (tk.arr d) d.depth m := ⟨hmv.1, by omega, by omega⟩
  have hnodeN : node.toInt.toNat = N + j := by omega
  have hpnN : Hn d pn = n.toInt.toNat := congrArg (fun x : Int32 => x.toInt.toNat) hpn.symm
  have hpmN : Hn d pm = m.toInt.toNat := congrArg (fun x : Int32 => x.toInt.toNat) hpm.symm
  have hboundary : d.heap_max.toInt = (573 - 2 * j : Nat) := by omega
  have hnidx : (d.heap_max.toInt - 1).toNat = 572 - 2 * j := by omega
  have hmidx : (d.heap_max.toInt - 2).toNat = 571 - 2 * j := by omega
  rw [hnidx] at hkeepn
  rw [hmidx] at hkeepm
  have hkeepnN : Hn e (572 - 2 * j) = n.toInt.toNat := congrArg (fun x : Int32 => x.toInt.toNat) hkeepn
  have hkeepmN : Hn e (571 - 2 * j) = m.toInt.toNat := congrArg (fun x : Int32 => x.toInt.toNat) hkeepm
  have htailN : ∀ q : Nat, 573 - 2 * j ≤ q → Hn e q = Hn d q := by
    intro q hq
    exact congrArg (fun x : Int32 => x.toInt.toNat) (htail q (by omega))
  have hnotn : ∀ q : Nat, 573 - 2 * j ≤ q → q < 573 → Hn d q ≠ n.toInt.toNat := by
    intro q hq1 hq2
    rw [← hpnN]
    exact hi.queue_not_tail pn q hpn1 hpn2 hq1 hq2
  have hnotm : ∀ q : Nat, 573 - 2 * j ≤ q → q < 573 → Hn d q ≠ m.toInt.toNat := by
    intro q hq1 hq2
    rw [← hpmN]
    exact hi.queue_not_tail pm q hpm1 hpm2 hq1 hq2
  have hcast : i2us node = UInt16.ofNat (N + j) := by
    rw [i2us_eq node (by omega) (by omega), hnodeN]
  have hsplit : ∀ q : Nat, 573 - 2 * (j + 1) ≤ q → q < 573 →
      q = 572 - 2 * j ∨ q = 571 - 2 * j ∨ 573 - 2 * j ≤ q := by intros; omega
  refine ⟨hi.initial, hi.initial_len, hq, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro F
    have hs := GB.poolSum_step (Hn d) (Hn e) K j n.toInt.toNat m.toInt.toNat (N + j) hK hmore
      hkeepnN hkeepmN (fun i hi => htailN (572 - i) (by omega)) (fun G => ?_) F
    · rw [hs, hi.observations, GB.rs_succ]
      omega
    · have hc := hcount (fun x => G x.toInt.toNat)
      simpa only [Hn, hnodeN] using hc
  · intro q hq1 hq2
    rcases hsplit q hq1 hq2 with he | he | hqold
    · subst q; rw [hkeepn]; exact ⟨hnv.1, by omega⟩
    · subst q; rw [hkeepm]; exact ⟨hmv.1, by omega⟩
    · rw [htail q (by omega)]
      have hv := hi.tail_valid q hqold hq2
      exact ⟨hv.1, by omega⟩
  · intro q hq1 hq2
    rw [htree, btParentState_dad tk d n m node hnV hmV hnode]
    rcases hsplit q hq1 hq2 with he | he | hqold
    · subst q; rw [hkeepnN, ite_eq_left (Or.inl rfl), hcast]
      congr 1
      unfold GB.dadP
      omega
    · subst q; rw [hkeepmN, ite_eq_left (Or.inr rfl), hcast]
      congr 1
      unfold GB.dadP
      omega
    · rw [htailN q hqold, ite_eq_right (by intro he; rcases he with he | he; exact hnotn q hqold hq2 he; exact hnotm q hqold hq2 he)]
      exact hi.parent q hqold hq2
  · intro q hq1 hq2 hqN
    rcases hsplit q hq1 hq2 with he | he | hqold
    · subst q; rw [hkeepnN] at hqN ⊢; omega
    · subst q; rw [hkeepmN] at hqN ⊢; omega
    · rw [htailN q hqold] at hqN ⊢
      exact hi.placement q hqold hq2 hqN
  · intro v hv
    rw [htree, btParentState_fc tk d n m node hnV hmV hnode, ite_eq_right (by omega)]
    exact hi.leaf_freq v hv
  · intro v hv hz
    have hvn : v ≠ n.toInt.toNat := by
      intro he
      have hu := hi.leaf_used pn (Or.inl ⟨hpn1, hpn2⟩) (by rw [hpnN, ← he]; exact hv)
      rw [hpnN, ← he] at hu
      exact hu hz
    have hvm : v ≠ m.toInt.toNat := by
      intro he
      have hu := hi.leaf_used pm (Or.inl ⟨hpm1, hpm2⟩) (by rw [hpmN, ← he]; exact hv)
      rw [hpmN, ← he] at hu
      exact hu hz
    rw [htree, btParentState_dad tk d n m node hnV hmV hnode,
      ite_eq_right (by intro he; rcases he with he | he; exact hvn he; exact hvm he)]
    exact hi.unused v hv hz
  · intro v hv hz
    rw [hdepth, btParentState_depth tk d n m node hnode, ite_eq_right (by omega)]
    exact hi.leaf_depth v hv hz
  · intro hlast
    have hlen2 : K - j = 2 := by omega
    have hr := hroot hlen2
    have hrI := congrArg Int32.toInt hr
    omega


/-- Exact footprint of merging: only the selected tree, heap, depth and
the two heap controls can change. Every array retains its size. -/
def BTForestFrame (tk : TK) (d0 d : DeflateState) : Prop :=
  ∃ (T : Array CtData) (H : Array Int32) (D : Array UInt8) (hl hm : Int32),
    d = { btScanState tk d0 T H D hl with heap_max := hm } ∧
    T.size = (tk.arr d0).size ∧ H.size = d0.heap.size ∧ D.size = d0.depth.size

theorem BTForestFrame.refl (tk : TK) (d : DeflateState) : BTForestFrame tk d d := by
  refine ⟨tk.arr d, d.heap, d.depth, d.heap_len, d.heap_max, ?_, rfl, rfl, rfl⟩
  cases tk <;> rfl

theorem BTForestFrame.trans {tk : TK} {a b c : DeflateState}
    (hab : BTForestFrame tk a b) (hbc : BTForestFrame tk b c) : BTForestFrame tk a c := by
  obtain ⟨T, H, D, hl, hm, rfl, hT, hH, hD⟩ := hab
  obtain ⟨T', H', D', hl', hm', rfl, hT', hH', hD'⟩ := hbc
  refine ⟨T', H', D', hl', hm', ?_, ?_, hH'.trans hH, hD'.trans hD⟩
  · cases tk <;> rfl
  · cases tk <;> exact hT'.trans hT

/-- Descriptor and bit-count metadata survive the exact merge footprint. -/
theorem BTForestFrame.metadata {tk : TK} {a b : DeflateState} (hi : BTForestFrame tk a b) (dk : TK) :
    dk.getDesc b = dk.getDesc a ∧ b.bl_count = a.bl_count := by
  obtain ⟨T, H, D, hl, hm, rfl, rest⟩ := hi
  cases tk <;> cases dk <;> exact ⟨rfl, rfl⟩

/-- The actual full iteration has precisely the merging footprint. -/
theorem ws_btMergeBody_frame {h0 : Heap} {id : Nat} {tk : TK} {d : DeflateState}
    {N K j : Nat} {node : Int32} (hi : BTMergeQueue tk N K j node d) (hmore : j + 1 < K) :
    WS h0 id (btMergeBody (Sp id) (.ref (tk.ref id) 0) node) d
      (fun _ e => BTForestFrame tk d e) := by
  have hN3 := hi.n3
  have hNb := hi.n286
  have hK2 := hi.k2
  have hKN := hi.kN
  have hj := hi.stage
  have hn := hi.counter
  have hl := hi.len
  have hm := hi.max
  have hH := hi.heap
  have hT := hi.tree
  have hD := hi.depth
  have hp : NV (tk.arr d) d.depth node := ⟨by omega, by omega, by omega⟩
  refine WS.mono (ws_btMergeBody tk d (K - j) node hl (by omega) (by omega)
    (by omega) (by omega) (by omega) hp (by omega)
    (fun i hi1 hi2 => hi.valid i hi1 (by omega))
    (fun i i' hi1 hi2 hi'1 hi'2 => hi.injective i i' hi1 (by omega) hi'1 (by omega)) hi.order) ?_
  intro next e ⟨hnext, n, m, hlen, hm1, hm2, H, H', hn', hm', hnm, hlen', hm1', hm2', he,
    hsize, htailn, htailm, horder, hvalid, hinj, hcount⟩
  subst e
  let mid := btParentState tk { d with heap := H, heap_len := hlen, heap_max := hm2 } n m node
  refine ⟨tk.arr mid, H', mid.depth, hlen, hm2, ?_, ?_, hsize, ?_⟩
  · cases tk <;> rfl
  · dsimp only [mid]
    rw [btParentState_tree_size]
    cases tk <;> rfl
  · dsimp only [mid]
    rw [btParentState_depth_size]

/-- The full actual merge loop preserves the forest layout and exact frame.
The singleton last root and every earlier child link follow from the
iteration proof; none is supplied as a callee contract premise. -/
theorem ws_btMergeLoop_forest {h0 : Heap} {id : Nat} {tk : TK} {d : DeflateState}
    {N K : Nat} {mc node : Int32} (hi : BTForest tk N K 0 mc d node d) :
    WS h0 id (btMergeLoop (Sp id) (.ref (tk.ref id) 0) node) d (fun next e =>
      BTForest tk N K (K - 1) mc d next e ∧ BTForestFrame tk d e ∧ e.heap_len.toInt = 1) := by
  let Inv : Int32 → DeflateState → Prop := fun node e =>
    ∃ j : Nat, BTForest tk N K j mc d node e ∧ BTForestFrame tk d e ∧ j + 1 < K
  let Q : Int32 → DeflateState → Prop := fun node e =>
    BTForest tk N K (K - 1) mc d node e ∧ BTForestFrame tk d e ∧ e.heap_len.toInt = 1
  unfold btMergeLoop
  refine WS.cdoWhile2 Inv (fun _ e => e.heap_len.toInt.toNat) Q ?_
    ⟨0, hi, BTForestFrame.refl tk d, by have := hi.queue.k2; omega⟩
    (by have := hi.queue.len; have := hi.queue.kN; have := hi.queue.n286; dsimp only [fuel]; omega)
  intro current e ⟨j, hj, hfr, hmore⟩
  refine WS.mono (merge_ws_and (ws_btMergeBody_forest_inv hj hmore) (ws_btMergeBody_frame hj.queue hmore)) ?_
  intro next e' ⟨hj', hfr'⟩
  have hframe := hfr.trans hfr'
  refine WS.bind' ws_rd fun got e'' ⟨hgot, he''⟩ => ?_
  subst e''; subst got
  have hlen := hj'.queue.len
  have hstage := hj'.queue.stage
  have hK := hj'.queue.k2
  by_cases hcontinue : e'.heap_len.toInt ≥ 2
  · have hjnext : j + 1 + 1 < K := by omega
    refine WS.pure' (Or.inr ⟨by simp only [hcontinue, decide_true], ⟨j + 1, hj', hframe, hjnext⟩, ?_⟩)
    have hlen0 := hj.queue.len
    omega
  · have hjend : j + 1 = K - 1 := by omega
    refine WS.pure' (Or.inl ⟨by simp only [hcontinue, decide_false], ?_⟩)
    change Q next e'
    rw [hjend] at hj'
    exact ⟨hj', hframe, by omega⟩


/-- The exact prepared maximum bounds every original leaf, and is a valid
nonnegative symbol. Nonemptiness comes from the actual two-leaf repair. -/
theorem BTForest.max_leaf {tk : TK} {d0 d : DeflateState} {N K j : Nat} {mc node : Int32}
    (hi : BTForest tk N K j mc d0 node d) :
    0 ≤ mc.toInt ∧ mc.toInt < N ∧ ∀ q : Nat, 1 ≤ q → q ≤ K → Hn d0 q ≤ mc.toInt.toNat := by
  have hlen := hi.initial_len
  have hK2 := hi.queue.k2
  have hmc := hi.initial.maxCode
  have hv := hi.initial.valid 1 (by omega) (by omega)
  have hvN : (d0.heap[1]!).toInt.toNat < N := by omega
  rcases Math.scanMax_spec (btFreq tk d0) N with ⟨hmax, hz⟩ | ⟨v, hmax, hvN', hfreq, hz⟩
  · exact False.elim (hv.2.2 (hz _ hvN))
  · have hmc' : mc.toInt = v := hmc.trans hmax
    refine ⟨by omega, by omega, ?_⟩
    intro q hq1 hq2
    have hvq := hi.initial.valid q hq1 (by omega)
    have hvqN : Hn d0 q < N := by unfold Hn; omega
    have hvbound : Hn d0 q ≤ v := by
      by_cases he : Hn d0 q ≤ v
      · exact he
      · have hzq := hz (Hn d0 q) (by omega) hvqN
        exact False.elim (hvq.2.2 hzq)
    omega

/-- Pool membership has the leaf/internal-node split required by the tree
layout specification. It is derived from exact observations. -/
theorem BTForest.kind {tk : TK} {d0 d : DeflateState} {N K j : Nat} {mc node : Int32}
    (hi : BTForest tk N K j mc d0 node d) (q : Nat)
    (hq : (1 ≤ q ∧ q ≤ K - j) ∨ (573 - 2 * j ≤ q ∧ q < 573)) :
    Hn d q ≤ mc.toInt.toNat ∨ (N ≤ Hn d q ∧ Hn d q < N + j) := by
  have hK : K ≤ 286 := by have := hi.queue.kN; have := hi.queue.n286; omega
  obtain ⟨i, hiB, hei⟩ := GB.poolAt_preimage (Hn d) K j q hK hi.queue.stage hq
  have hiB' : i < K - j + 2 * j := by have := hi.queue.stage; omega
  rcases GB.pool_origin (Hn d) (Hn d0) (K - j) (2 * j) K N j hi.observations i hiB' with
    ⟨a, ha, he⟩ | he
  · have hv := hi.max_leaf.2.2 (a + 1) (by omega) (by omega)
    rw [hei] at he
    exact Or.inl (he ▸ hv)
  · rw [hei] at he
    exact Or.inr he

/-- Every created internal node has a represented position below its own
children. Queue positions satisfy this bound by the queue/tail geometry;
retained positions satisfy the preserved placement property. -/
theorem BTForest.internal_position {tk : TK} {d0 d : DeflateState} {N K j : Nat} {mc node : Int32}
    (hi : BTForest tk N K j mc d0 node d) (a : Nat) (ha : a < j) :
    ∃ q : Nat, ((1 ≤ q ∧ q ≤ K - j) ∨ (573 - 2 * j ≤ q ∧ q < 573)) ∧
      q < 571 - 2 * a ∧ Hn d q = N + a := by
  have hK : K ≤ 286 := by have := hi.queue.kN; have := hi.queue.n286; omega
  have hj := hi.queue.stage
  obtain ⟨i, hiB, hei⟩ := GB.pool_internal (Hn d) (Hn d0) (K - j) (2 * j) K N j hi.observations a ha
  have hiB' : i < K + j := by omega
  obtain ⟨q, hq, hval⟩ := GB.poolAt_position (Hn d) K j i hK hj hiB'
  have hqval : Hn d q = N + a := hval.symm.trans hei
  refine ⟨q, hq, ?_, hqval⟩
  rcases hq with hq | hq
  · omega
  · have hp := hi.placement q hq.1 hq.2 (by omega)
    rw [hqval] at hp
    simpa only [Nat.add_sub_cancel_left] using hp

/-- Every initially used leaf has a represented queue or retained-tail
position after merging. -/
theorem BTForest.used_position {tk : TK} {d0 d : DeflateState} {N K j : Nat} {mc node : Int32}
    (hi : BTForest tk N K j mc d0 node d) (v : Nat) (hv : v < N) (hf : btFreq tk d0 v ≠ 0) :
    ∃ q : Nat, ((1 ≤ q ∧ q ≤ K - j) ∨ (573 - 2 * j ≤ q ∧ q < 573)) ∧ Hn d q = v := by
  have hK : K ≤ 286 := by have := hi.queue.kN; have := hi.queue.n286; omega
  have hj := hi.queue.stage
  obtain ⟨q0, hq01, hq02, hval0⟩ := hi.initial.complete v hv hf
  have hq0K : q0 ≤ K := by have := hi.initial_len; omega
  have hval0N : Hn d0 q0 = v := by unfold Hn; omega
  obtain ⟨i, hiB, hei⟩ := GB.pool_leaf (Hn d) (Hn d0) (K - j) (2 * j) K N j hi.observations (q0 - 1) (by omega)
  rw [show q0 - 1 + 1 = q0 by omega, hval0N] at hei
  have hiB' : i < K + j := by omega
  obtain ⟨q, hq, hval⟩ := GB.poolAt_position (Hn d) K j i hK hj hiB'
  exact ⟨q, hq, hval.symm.trans hei⟩


/-- The tree layout established by the actual completed heap prefix. The
root and all children occur exactly once in the retained interval. These
are data results used to build the bit-length generator's context. -/
structure BTBuilt (tk : TK) (N K : Nat) (mc : Int32) (d0 d : DeflateState) : Prop where
  k2 : 2 ≤ K
  kN : K ≤ N
  n286 : N ≤ 286
  max_nonneg : 0 ≤ mc.toInt
  heap : d.heap.size = 573
  heap_max : d.heap_max.toInt = (574 - 2 * K : Nat)
  heap_len : d.heap_len.toInt = 1
  shape : GB.PShape (Hn d) (574 - 2 * K) (K - 1) N mc.toInt.toNat
  nonneg : ∀ q : Nat, 574 - 2 * K ≤ q → q < 573 → 0 ≤ d.heap[q]!.toInt
  capacity : N + K - 1 ≤ (tk.arr d).size
  parent : ∀ q : Nat, 574 - 2 * K < q → q < 573 →
    (tk.arr d)[Hn d q]!.dl = UInt16.ofNat (GB.dadP N q)
  unused : ∀ v ≤ mc.toInt.toNat, (∀ q, 574 - 2 * K ≤ q → q < 573 → Hn d q ≠ v) → (tk.arr d)[v]!.dl = 0
  leaf_freq : ∀ v < N, (tk.arr d)[v]!.fc = (tk.arr d0)[v]!.fc
  frame : BTForestFrame tk d0 d

/-- The actual root store converts the complete forest into the precise
retained tree layout. Its shape, parent links and inactive-symbol lengths
are derived from merging, not assumed as a bit-length callee contract. -/
theorem ws_btSaveRoot_forest {h0 : Heap} {id : Nat} {tk : TK} {d0 d : DeflateState}
    {N K : Nat} {mc node : Int32} (hi : BTForest tk N K (K - 1) mc d0 node d)
    (hfr : BTForestFrame tk d0 d) :
    WS h0 id (btSaveRoot (Sp id)) d (fun _ e => BTBuilt tk N K mc d0 e) := by
  have hK2 := hi.queue.k2
  have hKN := hi.queue.kN
  have hNb := hi.queue.n286
  have hN3 := hi.queue.n3
  have hj := hi.queue.stage
  have hsize := hi.queue.heap
  have hlen := hi.queue.len
  have hmax := hi.queue.max
  have hmBounds := hi.queue.tail_bounds
  have hmc := hi.max_leaf
  let b := 574 - 2 * K
  have hb2 : 2 ≤ b := by dsimp only [b]; omega
  have hb573 : b < 573 := by dsimp only [b]; omega
  have hbmax : d.heap_max.toInt = (b + 1 : Nat) := by dsimp only [b]; omega
  have hbtail : 573 - 2 * (K - 1) = b + 1 := by dsimp only [b]; omega
  have hlast := hi.last_root (by omega)
  refine WS.mono (ws_btSaveRoot d (by omega) (by omega) (by omega) (by omega)) ?_
  intro _ e ⟨hm, hhm, he, hsz, hroot, hframe⟩
  have hhmB : hm.toInt = b := by omega
  have hhmBN : hm.toInt.toNat = b := by omega
  have hHeap : ∀ q : Nat, e.heap[q]! = if q = b then d.heap[1]! else d.heap[q]! := by
    intro q
    rw [he]
    change (d.heap.set! hm.toInt.toNat d.heap[1]!)[q]! = _
    rw [hhmBN, getD_set _ _ _ _ (by omega)]
  have hHN : ∀ q : Nat, Hn e q = if q = b then Hn d 1 else Hn d q := by
    intro q
    unfold Hn
    rw [hHeap q]
    split <;> rfl
  have hTree : tk.arr e = tk.arr d := by rw [he]; cases tk <;> rfl
  have hLen : e.heap_len.toInt = 1 := by rw [he]; dsimp only; omega
  have hMax : e.heap_max.toInt = b := by rw [he]; exact hhmB
  have hFrame : BTForestFrame tk d e := by
    refine ⟨tk.arr d, e.heap, d.depth, d.heap_len, hm, ?_, rfl, hsz, rfl⟩
    rw [he]
    cases tk <;> rfl
  let P : Nat → Nat := fun q => if q = b then 1 else q
  have hP : ∀ q : Nat, b ≤ q → q < 573 →
      (1 ≤ P q ∧ P q ≤ K - (K - 1)) ∨ (573 - 2 * (K - 1) ≤ P q ∧ P q < 573) := by
    intro q hq1 hq2
    dsimp only [P]
    split
    · exact Or.inl ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, hq2⟩
  have hVal : ∀ q : Nat, Hn e q = Hn d (P q) := by
    intro q
    rw [hHN]
    dsimp only [P]
    split <;> rfl
  have hPi : ∀ q q' : Nat, b ≤ q → q < 573 → b ≤ q' → q' < 573 → P q = P q' → q = q' := by
    intro q q' hq1 hq2 hq'1 hq'2 heq
    dsimp only [P] at heq
    split at heq <;> split at heq <;> omega
  have hLift : ∀ q : Nat,
      ((1 ≤ q ∧ q ≤ K - (K - 1)) ∨ (573 - 2 * (K - 1) ≤ q ∧ q < 573)) →
      ∃ q' : Nat, b ≤ q' ∧ q' < 573 ∧ Hn e q' = Hn d q ∧ (q ≠ 1 → q' = q) := by
    intro q hq
    by_cases hq1 : q = 1
    · refine ⟨b, by omega, hb573, ?_, ?_⟩
      · rw [hHN, ite_eq_left rfl, hq1]
      · intro hh; exact False.elim (hh hq1)
    · have hqtail : b + 1 ≤ q ∧ q < 573 := by rcases hq with hq | hq <;> omega
      refine ⟨q, by omega, hqtail.2, ?_, fun _ => rfl⟩
      rw [hHN, ite_eq_right (by omega)]
  have hshape : GB.PShape (Hn e) b (K - 1) N mc.toInt.toNat := by
    refine ⟨by dsimp only [b]; omega, by omega, by omega, ?_, ?_, ?_, ?_⟩
    · intro q q' hq1 hq2 hq'1 hq'2 heq
      rw [hVal, hVal] at heq
      exact hPi q q' hq1 hq2 hq'1 hq'2 (hi.injective _ _ (hP q hq1 hq2) (hP q' hq'1 hq'2) heq)
    · intro q hq1 hq2
      rw [hVal]
      exact hi.kind _ (hP q hq1 hq2)
    · rw [hHN, ite_eq_left rfl]
      unfold Hn
      omega
    · intro a ha
      obtain ⟨q, hq, hpos, hqval⟩ := hi.internal_position a ha
      obtain ⟨q', hq'1, hq'2, hval, hsame⟩ := hLift q hq
      refine ⟨q', hq'1, ?_, hval.trans hqval⟩
      by_cases hq1 : q = 1
      · have heq : q' = b := by
          rcases hq with hq | hq
          · have hpe := hP q' hq'1 hq'2
            have hinj := hi.injective (P q') 1 hpe (Or.inl ⟨by omega, by omega⟩)
              (by rw [← hVal, hval, hq1])
            dsimp only [P] at hinj
            split at hinj <;> omega
          · omega
        rw [heq]
        dsimp only [b]
        omega
      · rw [hsame hq1]
        exact hpos
  refine ⟨hK2, hKN, hNb, hmc.1, hsz.trans hsize, hMax, hLen, hshape, ?_, ?_, ?_, ?_, ?_, hfr.trans hFrame⟩
  · intro q hq1 hq2
    rw [hHeap]
    split
    · exact (hi.queue.valid 1 (by omega) (by omega)).1
    · exact (hi.tail_valid q (by omega) hq2).1
  · rw [hTree]
    exact hi.queue.tree
  · intro q hq1 hq2
    rw [hTree, hHN, ite_eq_right (by omega)]
    exact hi.parent q (by omega) hq2
  · intro v hv hnone
    have hvN : v < N := by omega
    have hz : btFreq tk d0 v = 0 := by
      by_cases hz : btFreq tk d0 v = 0
      · exact hz
      · obtain ⟨q, hq, hqval⟩ := hi.used_position v hvN hz
        obtain ⟨q', hq'1, hq'2, hval, hsame⟩ := hLift q hq
        exact False.elim (hnone q' hq'1 hq'2 (hval.trans hqval))
    rw [hTree]
    exact hi.unused v hvN hz
  · intro v hv
    rw [hTree]
    exact hi.leaf_freq v hv

end Zlib.Trees.Proofs
