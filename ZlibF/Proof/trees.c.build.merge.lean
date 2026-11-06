import ZlibF.Math.DeflateHeapRemove
import ZlibF.Proof.«trees.c.build.heapify»

/-! # trees.c: the actual node-merging loop and its two selected nodes -/

namespace Zlib.Trees.Proofs
open C Zlib.Trees

/-- Naming a conditional source fragment distributes its following
continuation over the unchanged decision. -/
theorem merge_ite_bind {α β : Type} (p : Prop) [Decidable p] (a b : M α) (f : α → M β) :
    ((if p then a else b) >>= f) = (if p then a >>= f else b >>= f) := by
  split <;> rfl

/-- The actual root removal and next-root read, in source order. -/
def btPick2 (s : DeflateStatePtr) (tree : CtDataPtr) : M (Int32 × Int32) := do
  let n ← pqremove s tree
  let m ← heapAt s 1
  pure (n, m)

/-- The two descending heap-tail stores, each with its own checked decrement
and state write, exactly as in the two C statements. -/
def btKeepChildren (s : DeflateStatePtr) (n m : Int32) : M Unit := do
  let hm ← isub (← rd s).heap_max 1
  md s fun d => { d with heap_max := hm }
  heapSet s hm n
  let hm ← isub (← rd s).heap_max 1
  md s fun d => { d with heap_max := hm }
  heapSet s hm m

/-- The actual selection and two tail stores before creating the parent. -/
def btMergeOpen (s : DeflateStatePtr) (tree : CtDataPtr) : M (Int32 × Int32) := do
  let (n, m) ← btPick2 s tree
  btKeepChildren s n m
  pure (n, m)

/-- The actual child comparison, selected-child reload and parent-depth store. -/
def btSetDepth (s : DeflateStatePtr) (n m node : Int32) : M Unit := do
  let dp ← pDepth s
  let dn ← Ptr.index dp n.toInt
  let dm ← Ptr.index dp m.toInt
  let mx ← if dn ≥ dm then Ptr.index dp n.toInt else Ptr.index dp m.toInt
  setAt dp node.toInt (mx + 1)

/-- The actual child-frequency reads and parent-frequency store. -/
def btSetFreq (tree : CtDataPtr) (n m node : Int32) : M Unit := do
  let fn ← getFc tree n.toInt
  let fm ← getFc tree m.toInt
  setFc tree node.toInt (fn + fm)

/-- The right-to-left stores of the chained parent assignment. -/
def btSetParents (tree : CtDataPtr) (n m node : Int32) : M Unit := do
  setDl tree m.toInt (i2us node)
  setDl tree n.toInt (i2us node)

/-- The actual parent frequency, depth, and two right-to-left `Dad` stores. -/
def btMakeParent (s : DeflateStatePtr) (tree : CtDataPtr) (n m node : Int32) : M Unit := do
  btSetFreq tree n m node
  btSetDepth s n m node
  btSetParents tree n m node

/-- The actual root replacement, checked local increment and sift-down. -/
def btMergeClose (s : DeflateStatePtr) (tree : CtDataPtr) (node : Int32) : M Int32 := do
  heapSet s 1 node
  let node' ← iadd node 1
  pqdownheap s tree 1
  pure node'

/-- One actual merge iteration, with only its two-node selection named. -/
def btMergeBody (s : DeflateStatePtr) (tree : CtDataPtr) (node : Int32) : M Int32 := do
  -- pqremove(s, tree, n);  m = s->heap[SMALLEST];
  let (n, m) ← btMergeOpen s tree
  -- tree[node].Freq = tree[n].Freq + tree[m].Freq;
  btMakeParent s tree n m node
  -- s->heap[SMALLEST] = node++;
  btMergeClose s tree node

/-- The actual do-while guard is checked after each completed merge. -/
def btMergeLoop (s : DeflateStatePtr) (tree : CtDataPtr) (node : Int32) : M Int32 :=
  cdoWhile (btMergeBody s tree)
    (fun node => do pure (decide ((← rd s).heap_len.toInt ≥ 2), node)) node

/-- The actual final root read and predecremented tail store. -/
def btSaveRoot (s : DeflateStatePtr) : M Unit := do
  let top ← heapAt s 1
  let hm ← isub (← rd s).heap_max 1
  md s fun d => { d with heap_max := hm }
  heapSet s hm top

/-- The actual removal followed by the second-root read selects two distinct
nodes. The first is minimal in the original queue; the second is minimal in
the remaining queue. Deletion preserves all other entries and their exact
counts, without a callee contract premise. -/
theorem ws_btPick2 {h0 : Heap} {id : Nat} (tk : TK) (d : DeflateState) (len : Nat)
    (hlen : d.heap_len.toInt = len) (h2 : 2 ≤ len) (hsz : len < d.heap.size)
    (hbig : d.heap.size ≤ 573)
    (hval : ∀ i, 1 ≤ i → i ≤ len → NV (tk.arr d) d.depth d.heap[i]!)
    (hinj : ∀ i j, 1 ≤ i → i ≤ len → 1 ≤ j → j ≤ len → d.heap[i]! = d.heap[j]! → i = j)
    (ho : HeapOK (sm (tk.arr d) d.depth) (fun i => d.heap[i]!) len 0) :
    WS h0 id (btPick2 (Sp id) (.ref (tk.ref id) 0)) d (fun r e =>
      ∃ (hl : Int32) (H : Array Int32), r.1 = d.heap[1]! ∧ r.2 = H[1]! ∧
        hl.toInt = (len : Int) - 1 ∧ e = { d with heap := H, heap_len := hl } ∧
        H.size = d.heap.size ∧
        (∀ i, ¬ (1 ≤ i ∧ i ≤ len - 1) → H[i]! = d.heap[i]!) ∧
        PermOn (fun i => H[i]!) (Hm (fun i => d.heap[i]!) len) (len - 1) ∧
        HeapOK (sm (tk.arr d) d.depth) (fun i => H[i]!) (len - 1) 0 ∧
        NV (tk.arr d) d.depth r.1 ∧ NV (tk.arr d) d.depth r.2 ∧ r.1 ≠ r.2 ∧
        (∀ q, 1 ≤ q → q ≤ len → sm (tk.arr d) d.depth r.1 d.heap[q]! = true) ∧
        (∀ q, 1 ≤ q → q ≤ len - 1 → sm (tk.arr d) d.depth r.2 H[q]! = true) ∧
        (∀ q, 1 ≤ q → q ≤ len - 1 →
          ∃ i : Nat, 2 ≤ i ∧ i ≤ len ∧ H[q]! = d.heap[i]!) ∧
        (∀ i, 2 ≤ i → i ≤ len → ∃ q : Nat, 1 ≤ q ∧ q ≤ len - 1 ∧ H[q]! = d.heap[i]!) ∧
        (∀ q, 1 ≤ q → q ≤ len - 1 → H[q]! ≠ r.1) ∧
        (∀ q q', 1 ≤ q → q ≤ len - 1 → 1 ≤ q' → q' ≤ len - 1 → H[q]! = H[q']! → q = q') ∧
        ∀ F : Int32 → Nat, GB.rs (fun q => F H[q + 1]!) (len - 1) + F r.1 =
          GB.rs (fun q => F d.heap[q + 1]!) len) := by
  unfold btPick2
  refine WS.bind' (ws_pqremove tk d len hlen h2 hsz (by omega) hval ho)
    fun n e1 ⟨hn, hl, H, hhl, he1, hsH, hframe, hp, horder⟩ => ?_
  subst e1
  refine WS.bind' (ws_heapAt 1 (by decide +kernel)
    (by change (1 : Int) < H.size; omega)) fun m e1 ⟨hm, he1⟩ => ?_
  subst e1
  have hindex : (1 : Int32).toInt.toNat = 1 := rfl
  change m = H[(1 : Int32).toInt.toNat]! at hm
  rw [hindex] at hm
  subst n; subst m
  have hp' : PermOn (fun i => H[i]!) (Hm (fun i => d.heap[i]!) len) (len - 1) := hp
  obtain ⟨hroot, hHinj⟩ := hp'.removed_injective h2 hinj
  have hvH : ∀ q, 1 ≤ q → q ≤ len - 1 → NV (tk.arr d) d.depth H[q]! := by
    intro q hq1 hq2
    obtain ⟨i, hi1, hi2, hqi⟩ := hp'.removed_origin h2 q hq1 hq2
    change H[q]! = d.heap[i]! at hqi
    rw [hqi]
    exact hval i (by omega) hi2
  refine WS.pure' ⟨hl, H, rfl, rfl, hhl, rfl, hsH, hframe, hp', horder,
    hval 1 (by omega) (by omega), ?_, ?_, ?_, ?_, ?_, ?_, hroot, hHinj, ?_⟩
  · have hv := hvH 1 (by omega) (by omega)
    exact hv
  · have hr := hroot 1 (by omega) (by omega)
    exact hr.symm
  · exact ho.root_min (sm_ok (tk.arr d) d.depth)
  · have hmin := horder.root_min (sm_ok (tk.arr d) d.depth)
    exact hmin
  · intro q hq1 hq2
    exact hp'.removed_origin h2 q hq1 hq2
  · intro i hi1 hi2
    exact hp'.removed_preimage h2 i hi1 hi2
  · intro F
    exact hp'.removed_sum h2 F

/-- The actual descending stores preserve both children in the correct
order and leave every other heap cell untouched. Heap length and all fields
outside the heap array and tail boundary are unchanged. -/
theorem ws_btKeepChildren {h0 : Heap} {id : Nat} (d : DeflateState) (n m : Int32)
    (hm2 : 2 ≤ d.heap_max.toInt) (hmH : d.heap_max.toInt ≤ d.heap.size) (hbig : d.heap.size ≤ 573) :
    WS h0 id (btKeepChildren (Sp id) n m) d (fun _ e =>
      ∃ hm1 hm2 : Int32, hm1.toInt = d.heap_max.toInt - 1 ∧ hm2.toInt = d.heap_max.toInt - 2 ∧
        e = { d with heap_max := hm2, heap := (d.heap.set! hm1.toInt.toNat n).set! hm2.toInt.toNat m } ∧
        e.heap.size = d.heap.size ∧ e.heap[hm1.toInt.toNat]! = n ∧ e.heap[hm2.toInt.toNat]! = m ∧
        ∀ i, i ≠ hm1.toInt.toNat → i ≠ hm2.toInt.toNat → e.heap[i]! = d.heap[i]!) := by
  have hi1 : (1 : Int32).toInt = 1 := rfl
  unfold btKeepChildren
  refine WS.bind' ws_rd fun dz e1 ⟨hdz, he1⟩ => ?_
  subst e1; subst dz
  refine WS.bind' (ws_isub d.heap_max 1 (by omega) (by omega)) fun hm1 e1 ⟨hh1, he1⟩ => ?_
  subst e1
  refine WS.bind' (ws_md _) fun _ e1 he1 => ?_
  subst e1
  unfold heapSet
  simp only [M_bind_assoc]
  refine WS.bind' ws_pHeap fun p e1 ⟨hp, he1⟩ => ?_
  subst e1; subst p
  refine WS.bind' (ws_setAt_heap hm1.toInt n (by omega) (by dsimp; omega)) fun _ e1 he1 => ?_
  subst e1
  refine WS.bind' ws_rd fun dz e1 ⟨hdz, he1⟩ => ?_
  subst e1; subst dz
  refine WS.bind' (ws_isub _ 1 (by dsimp; omega) (by dsimp; omega)) fun hm2 e1 ⟨hh2, he1⟩ => ?_
  subst e1
  refine WS.bind' (ws_md _) fun _ e1 he1 => ?_
  subst e1
  refine WS.bind' ws_pHeap fun p e1 ⟨hp, he1⟩ => ?_
  subst e1; subst p
  refine WS.mono (ws_setAt_heap hm2.toInt m (by dsimp at hh2; omega)
    (by change hm2.toInt < ((d.heap.set! hm1.toInt.toNat n).size : Int); rw [size_set!]; dsimp at hh2; omega)) ?_
  intro _ e1 he1
  subst e1
  have hh2 : hm2.toInt = d.heap_max.toInt - 2 := by dsimp at hh2; omega
  have h1 : hm1.toInt.toNat < d.heap.size := by omega
  have h2 : hm2.toInt.toNat < d.heap.size := by omega
  have hne : hm1.toInt.toNat ≠ hm2.toInt.toNat := by omega
  refine ⟨hm1, hm2, by omega, hh2, rfl, by simp only [size_set!], ?_, ?_, ?_⟩
  · dsimp only
    rw [getD_set _ hm2.toInt.toNat hm1.toInt.toNat m (by simpa only [size_set!] using h2), if_neg hne,
      getD_set _ hm1.toInt.toNat hm1.toInt.toNat n h1, if_pos rfl]
  · dsimp only
    rw [getD_set _ hm2.toInt.toNat hm2.toInt.toNat m (by simpa only [size_set!] using h2), if_pos rfl]
  · intro i hi1 hi2
    dsimp only
    rw [getD_set _ hm2.toInt.toNat i m (by simpa only [size_set!] using h2), if_neg hi2,
      getD_set _ hm1.toInt.toNat i n h1, if_neg hi1]

/-- The complete opening of an actual merge keeps both selected nodes in
the descending tail and preserves the remaining queue, its order, membership
and counts. The queue/tail gap prevents overwriting any live queue entry. -/
theorem ws_btMergeOpen {h0 : Heap} {id : Nat} (tk : TK) (d : DeflateState) (len : Nat)
    (hlen : d.heap_len.toInt = len) (h2 : 2 ≤ len) (hsz : len < d.heap.size)
    (hbig : d.heap.size ≤ 573) (hmH : d.heap_max.toInt ≤ d.heap.size)
    (hgap : (len : Int) < d.heap_max.toInt - 1)
    (hval : ∀ i, 1 ≤ i → i ≤ len → NV (tk.arr d) d.depth d.heap[i]!)
    (hinj : ∀ i j, 1 ≤ i → i ≤ len → 1 ≤ j → j ≤ len → d.heap[i]! = d.heap[j]! → i = j)
    (ho : HeapOK (sm (tk.arr d) d.depth) (fun i => d.heap[i]!) len 0) :
    WS h0 id (btMergeOpen (Sp id) (.ref (tk.ref id) 0)) d (fun r e =>
      ∃ (hl hm1 hm2 : Int32) (H : Array Int32),
        r.1 = d.heap[1]! ∧ r.2 = H[1]! ∧ r.1 ≠ r.2 ∧
        hl.toInt = (len : Int) - 1 ∧ hm1.toInt = d.heap_max.toInt - 1 ∧ hm2.toInt = d.heap_max.toInt - 2 ∧
        e = { d with heap := H, heap_len := hl, heap_max := hm2 } ∧ H.size = d.heap.size ∧
        H[hm1.toInt.toNat]! = r.1 ∧ H[hm2.toInt.toNat]! = r.2 ∧
        NV (tk.arr d) d.depth r.1 ∧ NV (tk.arr d) d.depth r.2 ∧
        HeapOK (sm (tk.arr d) d.depth) (fun i => H[i]!) (len - 1) 0 ∧
        (∀ q, 1 ≤ q → q ≤ len → sm (tk.arr d) d.depth r.1 d.heap[q]! = true) ∧
        (∀ q, 1 ≤ q → q ≤ len - 1 → sm (tk.arr d) d.depth r.2 H[q]! = true) ∧
        (∀ q, 1 ≤ q → q ≤ len - 1 → ∃ i : Nat, 2 ≤ i ∧ i ≤ len ∧ H[q]! = d.heap[i]!) ∧
        (∀ i, 2 ≤ i → i ≤ len → ∃ q : Nat, 1 ≤ q ∧ q ≤ len - 1 ∧ H[q]! = d.heap[i]!) ∧
        (∀ q, 1 ≤ q → q ≤ len - 1 → H[q]! ≠ r.1) ∧
        (∀ q q', 1 ≤ q → q ≤ len - 1 → 1 ≤ q' → q' ≤ len - 1 → H[q]! = H[q']! → q = q') ∧
        ∀ F : Int32 → Nat, GB.rs (fun q => F H[q + 1]!) (len - 1) + F r.1 =
          GB.rs (fun q => F d.heap[q + 1]!) len) := by
  unfold btMergeOpen
  refine WS.bind' (ws_btPick2 tk d len hlen h2 hsz hbig hval hinj ho)
    fun r e1 ⟨hl, H, hn, hm, hhl, he1, hsH, hframe, hp, horder, hnv, hmv, hnm,
      hminn, hminm, horigin, hcomplete, hno, hHinj, hcount⟩ => ?_
  subst e1
  rcases r with ⟨n, m⟩
  dsimp only at hn hm hnv hmv hnm hminn hminm hno hcount ⊢
  refine WS.bind' (ws_btKeepChildren { d with heap := H, heap_len := hl } n m
    (by change 2 ≤ d.heap_max.toInt; omega) (by change d.heap_max.toInt ≤ (H.size : Int); omega)
    (by change H.size ≤ 573; omega))
    fun _ e2 ⟨hm1, hm2, hh1, hh2, he2, hsH', hnKeep, hmKeep, hKeepFrame⟩ => ?_
  subst e2
  let H' := (H.set! hm1.toInt.toNat n).set! hm2.toInt.toNat m
  have hh1 : hm1.toInt = d.heap_max.toInt - 1 := hh1
  have hh2 : hm2.toInt = d.heap_max.toInt - 2 := hh2
  have hqueue : ∀ q, 1 ≤ q → q ≤ len - 1 → H'[q]! = H[q]! := by
    intro q hq1 hq2
    exact hKeepFrame q (by omega) (by omega)
  have hroot : H'[1]! = m := (hqueue 1 (by omega) (by omega)).trans hm.symm
  refine WS.pure' ⟨hl, hm1, hm2, H', hn, hroot.symm, hnm, hhl, hh1, hh2, rfl,
    by dsimp only [H']; simp only [size_set!]; exact hsH,
    hnKeep, hmKeep, hnv, hmv, ?_, hminn, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hc2 hcl hcp
    dsimp only
    rw [hqueue c (by omega) hcl, hqueue (c / 2) (by omega) (by omega)]
    exact horder c hc2 hcl hcp
  · intro q hq1 hq2
    rw [hqueue q hq1 hq2]
    exact hminm q hq1 hq2
  · intro q hq1 hq2
    obtain ⟨i, hi1, hi2, hqi⟩ := horigin q hq1 hq2
    exact ⟨i, hi1, hi2, (hqueue q hq1 hq2).trans hqi⟩
  · intro i hi1 hi2
    obtain ⟨q, hq1, hq2, hqi⟩ := hcomplete i hi1 hi2
    exact ⟨q, hq1, hq2, (hqueue q hq1 hq2).trans hqi⟩
  · intro q hq1 hq2
    rw [hqueue q hq1 hq2]
    exact hno q hq1 hq2
  · intro q q' hq1 hq2 hq'1 hq'2 heq
    rw [hqueue q hq1 hq2, hqueue q' hq'1 hq'2] at heq
    exact hHinj q q' hq1 hq2 hq'1 hq'2 heq
  · intro F
    rw [show GB.rs (fun q => F H'[q + 1]!) (len - 1) = GB.rs (fun q => F H[q + 1]!) (len - 1) by
      apply GB.rs_congr
      intro q hq
      rw [hqueue (q + 1) (by omega) (by omega)]]
    exact hcount F

/-- The corrected source expression, including its third read, stores the
selected child depth plus one modulo 256. Every other depth and state field
is unchanged. No non-wrapping-depth assumption is required. -/
theorem ws_btSetDepth {h0 : Heap} {id : Nat} (d : DeflateState) (n m node : Int32)
    (hn0 : 0 ≤ n.toInt) (hnD : n.toInt < d.depth.size)
    (hm0 : 0 ≤ m.toInt) (hmD : m.toInt < d.depth.size)
    (hp0 : 0 ≤ node.toInt) (hpD : node.toInt < d.depth.size) :
    WS h0 id (btSetDepth (Sp id) n m node) d (fun _ e =>
      e = { d with
        depth := d.depth.set! node.toInt.toNat
          ((if d.depth[n.toInt.toNat]! ≥ d.depth[m.toInt.toNat]! then
            d.depth[n.toInt.toNat]! else d.depth[m.toInt.toNat]!) + 1) }) := by
  unfold btSetDepth
  refine WS.bind' ws_pDepth fun p e1 ⟨hp, he1⟩ => ?_
  subst e1; subst p
  refine WS.bind' (ws_index_depth n.toInt hn0 hnD) fun dn e1 ⟨hdn, he1⟩ => ?_
  subst e1; subst dn
  refine WS.bind' (ws_index_depth m.toInt hm0 hmD) fun dm e1 ⟨hdm, he1⟩ => ?_
  subst e1; subst dm
  by_cases hc : d.depth[n.toInt.toNat]! ≥ d.depth[m.toInt.toNat]!
  · simp only [hc, ite_true]
    refine WS.bind' (ws_index_depth n.toInt hn0 hnD) fun mx e1 ⟨hmx, he1⟩ => ?_
    subst e1; subst mx
    exact ws_setAt_depth node.toInt _ hp0 hpD
  · simp only [hc, ite_false]
    refine WS.bind' (ws_index_depth m.toInt hm0 hmD) fun mx e1 ⟨hmx, he1⟩ => ?_
    subst e1; subst mx
    exact ws_setAt_depth node.toInt _ hp0 hpD

/-- Exact parent-creation record, retaining source order even if the three
indices alias. Parent-index casts and both byte/word arithmetic operations
keep their unsigned wrapping behavior. -/
def btParentState (tk : TK) (d : DeflateState) (n m node : Int32) : DeflateState :=
  let T := tk.arr d
  let T1 := T.set! node.toInt.toNat { T[node.toInt.toNat]! with fc := T[n.toInt.toNat]!.fc + T[m.toInt.toNat]!.fc }
  let T2 := T1.set! m.toInt.toNat { T1[m.toInt.toNat]! with dl := i2us node }
  let T3 := T2.set! n.toInt.toNat { T2[n.toInt.toNat]! with dl := i2us node }
  { tk.setArr d T3 with
    depth := d.depth.set! node.toInt.toNat
      ((if d.depth[n.toInt.toNat]! ≥ d.depth[m.toInt.toNat]! then
        d.depth[n.toInt.toNat]! else d.depth[m.toInt.toNat]!) + 1) }

/-- Exact frequency store, including unsigned 16-bit addition wrap. -/
theorem ws_btSetFreq {h0 : Heap} {id : Nat} (tk : TK) (d : DeflateState) (n m node : Int32)
    (hn0 : 0 ≤ n.toInt) (hnT : n.toInt < (tk.arr d).size)
    (hm0 : 0 ≤ m.toInt) (hmT : m.toInt < (tk.arr d).size)
    (hp0 : 0 ≤ node.toInt) (hpT : node.toInt < (tk.arr d).size) :
    WS h0 id (btSetFreq (.ref (tk.ref id) 0) n m node) d (fun _ e =>
      e = tk.setArr d ((tk.arr d).set! node.toInt.toNat
        { (tk.arr d)[node.toInt.toNat]! with fc := ((tk.arr d)[n.toInt.toNat]!).fc + ((tk.arr d)[m.toInt.toNat]!).fc })) := by
  unfold btSetFreq
  refine WS.bind' (ws_getFc tk n.toInt hn0 hnT) fun fn e1 ⟨hfn, he1⟩ => ?_
  subst e1; subst fn
  refine WS.bind' (ws_getFc tk m.toInt hm0 hmT) fun fm e1 ⟨hfm, he1⟩ => ?_
  subst e1; subst fm
  exact ws_setFc tk node.toInt _ hp0 hpT

/-- Exact parent stores, including aliases between the two child indices. -/
theorem ws_btSetParents {h0 : Heap} {id : Nat} (tk : TK) (d : DeflateState) (n m node : Int32)
    (hn0 : 0 ≤ n.toInt) (hnT : n.toInt < (tk.arr d).size)
    (hm0 : 0 ≤ m.toInt) (hmT : m.toInt < (tk.arr d).size) :
    WS h0 id (btSetParents (.ref (tk.ref id) 0) n m node) d (fun _ e =>
      let T1 := (tk.arr d).set! m.toInt.toNat { (tk.arr d)[m.toInt.toNat]! with dl := i2us node }
      e = tk.setArr d (T1.set! n.toInt.toNat { T1[n.toInt.toNat]! with dl := i2us node })) := by
  unfold btSetParents
  refine WS.bind' (ws_setDl tk m.toInt (i2us node) hm0 hmT) fun _ e1 he1 => ?_
  subst e1
  refine WS.mono (ws_setDl tk n.toInt (i2us node) hn0
    (by rw [tk_arr_setArr, size_set!]; exact hnT)) ?_
  intro _ e1 he1
  subst e1
  simp only [tk_arr_setArr]
  cases tk <;> rfl

set_option maxRecDepth 4096 in
/-- The entire actual parent-creation fragment has these exact record effects.
No acyclicity, freshness, distinctness, non-wrapping weight, or callee contract
is assumed. Those structural facts are obligations of the merge invariant. -/
theorem ws_btMakeParent {h0 : Heap} {id : Nat} (tk : TK) (d : DeflateState) (n m node : Int32)
    (hn : NV (tk.arr d) d.depth n) (hm : NV (tk.arr d) d.depth m)
    (hp : NV (tk.arr d) d.depth node) :
    WS h0 id (btMakeParent (Sp id) (.ref (tk.ref id) 0) n m node) d
      (fun _ e => e = btParentState tk d n m node) := by
  let T1 := (tk.arr d).set! node.toInt.toNat
    { (tk.arr d)[node.toInt.toNat]! with fc := ((tk.arr d)[n.toInt.toNat]!).fc + ((tk.arr d)[m.toInt.toNat]!).fc }
  have hsT1 : T1.size = (tk.arr d).size := by dsimp only [T1]; rw [size_set!]
  let D := d.depth.set! node.toInt.toNat
    ((if d.depth[n.toInt.toNat]! ≥ d.depth[m.toInt.toNat]! then
      d.depth[n.toInt.toNat]! else d.depth[m.toInt.toNat]!) + 1)
  let d1 := tk.setArr d T1
  let d2 := { d1 with depth := D }
  unfold btMakeParent
  refine WS.bind' (ws_btSetFreq tk d n m node hn.1 hn.2.1 hm.1 hm.2.1 hp.1 hp.2.1)
    fun _ e1 he1 => ?_
  change e1 = d1 at he1
  subst e1
  have hd1 : d1.depth = d.depth := by exact tk_setArr_depth tk T1
  refine WS.bind' (ws_btSetDepth d1 n m node hn.1
    (by rw [hd1]; exact hn.2.2) hm.1 (by rw [hd1]; exact hm.2.2) hp.1
    (by rw [hd1]; exact hp.2.2)) fun _ e1 he1 => ?_
  rw [hd1] at he1
  change e1 = d2 at he1
  subst e1
  have hT1 : tk.arr d2 = T1 := by cases tk <;> rfl
  refine WS.mono (ws_btSetParents tk d2 n m node hn.1
    (by rw [hT1, hsT1]; exact hn.2.1) hm.1 (by rw [hT1, hsT1]; exact hm.2.1)) ?_
  intro _ e1 he1
  subst e1
  unfold btParentState
  dsimp only [d2, d1, T1, D]
  cases tk <;> rfl

/-- The actual closing statements re-establish a fully ordered queue.
The source's signed counter increment is checked. The exact count equation
accounts for removing the old root and inserting the new parent. -/
theorem ws_btMergeClose {h0 : Heap} {id : Nat} (tk : TK) (d : DeflateState) (len : Nat) (node : Int32)
    (hlen : d.heap_len.toInt = len) (h1 : 1 ≤ len) (hsz : len < d.heap.size)
    (hbig : d.heap.size ≤ 573) (hnode : NV (tk.arr d) d.depth node) (hinc : node.toInt < 2147483647)
    (hval : ∀ i, 1 ≤ i → i ≤ len → NV (tk.arr d) d.depth d.heap[i]!)
    (ho : HeapOK (sm (tk.arr d) d.depth) (fun i => d.heap[i]!) len 1) :
    WS h0 id (btMergeClose (Sp id) (.ref (tk.ref id) 0) node) d (fun r e =>
      r.toInt = node.toInt + 1 ∧ ∃ H : Array Int32, e = { d with heap := H } ∧ H.size = d.heap.size ∧
        (∀ i, ¬ (1 ≤ i ∧ i ≤ len) → H[i]! = d.heap[i]!) ∧
        PermOn (fun i => H[i]!) (fun i => if i = 1 then node else d.heap[i]!) len ∧
        HeapOK (sm (tk.arr d) d.depth) (fun i => H[i]!) len 0 ∧
        (∀ q, 1 ≤ q → q ≤ len → sm (tk.arr d) d.depth H[1]! H[q]! = true) ∧
        ∀ F : Int32 → Nat, GB.rs (fun i => F H[i + 1]!) len + F d.heap[1]! =
          GB.rs (fun i => F d.heap[i + 1]!) len + F node) := by
  have hi1 : (1 : Int32).toInt = 1 := rfl
  have hi1N : (1 : Int32).toInt.toNat = 1 := rfl
  have hs1 : 1 < d.heap.size := by omega
  unfold btMergeClose
  refine WS.bind' (ws_heapSet 1 node (by decide +kernel) (by change (1 : Int) < d.heap.size; omega))
    fun _ e1 he1 => ?_
  simp only [hi1N] at he1
  subst e1
  refine WS.bind' (ws_iadd node 1 (by have := hnode.1; omega) (by omega)) fun next e1 ⟨hnxt, he1⟩ => ?_
  subst e1
  have hvals : ∀ i, 1 ≤ i → i ≤ len →
      NV (tk.arr { d with heap := d.heap.set! 1 node }) d.depth (d.heap.set! 1 node)[i]! := by
    intro i hi1 hi2
    rw [tk_arr_heap, getD_set d.heap 1 i node hs1]
    split
    · exact hnode
    · exact hval i hi1 hi2
  have horder : HeapOK (sm (tk.arr { d with heap := d.heap.set! 1 node }) d.depth)
      (fun i => (d.heap.set! 1 node)[i]!) len 1 := by
    rw [tk_arr_heap]
    intro c hc2 hcl hcp
    dsimp only
    rw [getD_set d.heap 1 (c / 2) node hs1, if_neg (by omega),
      getD_set d.heap 1 c node hs1, if_neg (by omega)]
    exact ho c hc2 hcl hcp
  refine WS.bind' (ws_pqdownheap tk { d with heap := d.heap.set! 1 node } 1 1 len hi1
    (by omega) h1 hlen (by dsimp only; rw [size_set!]; omega)
    (by dsimp only; rw [size_set!]; omega) hvals horder)
    fun _ e1 ⟨H, he1, hsH, hf, hp, hHeap⟩ => ?_
  subst e1
  simp only [tk_arr_heap] at hHeap
  have hp' : PermOn (fun i => H[i]!) (fun i => if i = 1 then node else d.heap[i]!) len := by
    have heq : (fun i => (d.heap.set! 1 node)[i]!) = (fun i => if i = 1 then node else d.heap[i]!) := by
      funext i
      exact getD_set d.heap 1 i node hs1
    rwa [heq] at hp
  refine WS.pure' ⟨by omega, H, rfl, by simpa only [size_set!] using hsH, ?_, hp', hHeap, ?_, ?_⟩
  · intro i hi
    have hfi := hf i hi
    dsimp only at hfi
    rw [hfi, getD_set d.heap 1 i node hs1, if_neg (by omega)]
  · exact hHeap.root_min (sm_ok (tk.arr d) d.depth)
  · intro F
    rw [hp'.sum F]
    exact replace_root_sum (fun i => d.heap[i]!) node len h1 F


/-- Updating the parent link does not change a frequency, including at the
updated cell. -/
theorem merge_setDad_fc (T : Array CtData) (k i : Nat) (dad : UInt16) (hk : k < T.size) :
    ((T.set! k { T[k]! with dl := dad })[i]!).fc = T[i]!.fc := by
  rw [getD_set T k i _ hk]
  split <;> simp_all

@[simp] theorem btParentState_heap (tk : TK) (d : DeflateState) (n m node : Int32) :
    (btParentState tk d n m node).heap = d.heap := by cases tk <;> rfl

@[simp] theorem btParentState_len (tk : TK) (d : DeflateState) (n m node : Int32) :
    (btParentState tk d n m node).heap_len = d.heap_len := by cases tk <;> rfl

@[simp] theorem btParentState_max (tk : TK) (d : DeflateState) (n m node : Int32) :
    (btParentState tk d n m node).heap_max = d.heap_max := by cases tk <;> rfl

@[simp] theorem btParentState_tree_size (tk : TK) (d : DeflateState) (n m node : Int32) :
    (tk.arr (btParentState tk d n m node)).size = (tk.arr d).size := by
  cases tk <;> simp only [btParentState, TK.arr, TK.setArr, size_set!]

@[simp] theorem btParentState_depth_size (tk : TK) (d : DeflateState) (n m node : Int32) :
    (btParentState tk d n m node).depth.size = d.depth.size := by
  cases tk <;> simp only [btParentState, TK.arr, TK.setArr, size_set!]

/-- All parent-link stores preserve frequencies. Only the fresh parent's
frequency is replaced, with the source's wrapping sum. -/
theorem btParentState_fc (tk : TK) (d : DeflateState) (n m node : Int32)
    (hn : NV (tk.arr d) d.depth n) (hm : NV (tk.arr d) d.depth m)
    (hp : NV (tk.arr d) d.depth node) (i : Nat) :
    (tk.arr (btParentState tk d n m node))[i]!.fc =
      if i = node.toInt.toNat then (tk.arr d)[n.toInt.toNat]!.fc + (tk.arr d)[m.toInt.toNat]!.fc
      else (tk.arr d)[i]!.fc := by
  have hnT : n.toInt.toNat < (tk.arr d).size := by have := hn.1; have := hn.2.1; omega
  have hmT : m.toInt.toNat < (tk.arr d).size := by have := hm.1; have := hm.2.1; omega
  have hpT : node.toInt.toNat < (tk.arr d).size := by have := hp.1; have := hp.2.1; omega
  have harr : tk.arr (btParentState tk d n m node) =
      let T := tk.arr d
      let T1 := T.set! node.toInt.toNat { T[node.toInt.toNat]! with fc := T[n.toInt.toNat]!.fc + T[m.toInt.toNat]!.fc }
      let T2 := T1.set! m.toInt.toNat { T1[m.toInt.toNat]! with dl := i2us node }
      T2.set! n.toInt.toNat { T2[n.toInt.toNat]! with dl := i2us node } := by cases tk <;> rfl
  rw [harr]
  dsimp only
  rw [merge_setDad_fc _ _ _ _ (by simp only [size_set!]; exact hnT),
    merge_setDad_fc _ _ _ _ (by simp only [size_set!]; exact hmT), getD_set _ _ _ _ hpT]
  split <;> rfl

/-- Every old depth cell is unchanged when the fresh parent depth is written. -/
theorem btParentState_depth (tk : TK) (d : DeflateState) (n m node : Int32)
    (hp : NV (tk.arr d) d.depth node) (i : Nat) :
    (btParentState tk d n m node).depth[i]! =
      if i = node.toInt.toNat then
        (if d.depth[n.toInt.toNat]! ≥ d.depth[m.toInt.toNat]! then
          d.depth[n.toInt.toNat]! else d.depth[m.toInt.toNat]!) + 1
      else d.depth[i]! := by
  have hpD : node.toInt.toNat < d.depth.size := by have := hp.1; have := hp.2.2; omega
  exact getD_set _ _ _ _ hpD

/-- The ordering key of any two previously allocated nodes is preserved.
Freshness is a numeric data condition, not a callee specification. -/
theorem btParentState_sm (tk : TK) (d : DeflateState) (n m node a b : Int32)
    (hn : NV (tk.arr d) d.depth n) (hm : NV (tk.arr d) d.depth m)
    (hp : NV (tk.arr d) d.depth node)
    (ha : 0 ≤ a.toInt) (hap : a.toInt < node.toInt)
    (hb : 0 ≤ b.toInt) (hbp : b.toInt < node.toInt) :
    sm (tk.arr (btParentState tk d n m node)) (btParentState tk d n m node).depth a b =
      sm (tk.arr d) d.depth a b := by
  have han : a.toInt.toNat ≠ node.toInt.toNat := by omega
  have hbn : b.toInt.toNat ≠ node.toInt.toNat := by omega
  simp only [sm, btParentState_fc tk d n m node hn hm hp, btParentState_depth tk d n m node hp,
    han, hbn, ite_false]


/-- One complete actual merge iteration terminates, creates its parent,
retains both children in the tail and restores a distinct ordered queue.
The explicit numeric freshness and queue/tail separation conditions are
internal representation obligations; no called function's contract is a
premise. The count equation holds for every node-counting function. -/
theorem ws_btMergeBody {h0 : Heap} {id : Nat} (tk : TK) (d : DeflateState) (len : Nat) (node : Int32)
    (hlen : d.heap_len.toInt = len) (h2 : 2 ≤ len) (hsz : len < d.heap.size)
    (hbig : d.heap.size ≤ 573) (hmH : d.heap_max.toInt ≤ d.heap.size)
    (hgap : (len : Int) < d.heap_max.toInt - 1)
    (hp : NV (tk.arr d) d.depth node) (hinc : node.toInt < 2147483647)
    (hbefore : ∀ i, 1 ≤ i → i ≤ len → 0 ≤ d.heap[i]!.toInt ∧ d.heap[i]!.toInt < node.toInt)
    (hinj : ∀ i j, 1 ≤ i → i ≤ len → 1 ≤ j → j ≤ len → d.heap[i]! = d.heap[j]! → i = j)
    (ho : HeapOK (sm (tk.arr d) d.depth) (fun i => d.heap[i]!) len 0) :
    WS h0 id (btMergeBody (Sp id) (.ref (tk.ref id) 0) node) d (fun r e =>
      r.toInt = node.toInt + 1 ∧ ∃ (n m hl hm1 hm2 : Int32) (H H' : Array Int32),
        n = d.heap[1]! ∧ m = H[1]! ∧ n ≠ m ∧
        hl.toInt = (len : Int) - 1 ∧ hm1.toInt = d.heap_max.toInt - 1 ∧ hm2.toInt = d.heap_max.toInt - 2 ∧
        e = { btParentState tk { d with heap := H, heap_len := hl, heap_max := hm2 } n m node with heap := H' } ∧
        H'.size = d.heap.size ∧ H'[hm1.toInt.toNat]! = n ∧ H'[hm2.toInt.toNat]! = m ∧
        HeapOK (sm (tk.arr e) e.depth) (fun i => H'[i]!) (len - 1) 0 ∧
        (∀ i, 1 ≤ i → i ≤ len - 1 → 0 ≤ H'[i]!.toInt ∧ H'[i]!.toInt ≤ node.toInt) ∧
        (∀ i j, 1 ≤ i → i ≤ len - 1 → 1 ≤ j → j ≤ len - 1 → H'[i]! = H'[j]! → i = j) ∧
        ∀ F : Int32 → Nat, GB.rs (fun i => F H'[i + 1]!) (len - 1) + F n + F m =
          GB.rs (fun i => F d.heap[i + 1]!) len + F node) := by
  have hv : ∀ i, 1 ≤ i → i ≤ len → NV (tk.arr d) d.depth d.heap[i]! := by
    intro i hi1 hi2
    have hb := hbefore i hi1 hi2
    exact ⟨hb.1, by have := hp.2.1; omega, by have := hp.2.2; omega⟩
  unfold btMergeBody
  refine WS.bind' (ws_btMergeOpen tk d len hlen h2 hsz hbig hmH hgap hv hinj ho)
    fun pair e1 ⟨hl, hm1, hm2, H, hn, hm, hnm, hhl, hh1, hh2, he1, hsH, hkeepn, hkeepm,
      hnv, hmv, horder, hminn, hminm, horigin, hcomplete, hno, hHi, hcount⟩ => ?_
  rcases pair with ⟨n, m⟩
  dsimp only at hn hm hnm hnv hmv hminn hminm hkeepn hkeepm hno hcount ⊢
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
  have hlen1 : 1 ≤ len - 1 := by omega
  have hroot : d2.heap[1]! = m := by rw [hHeap2]; exact hm.symm
  have hRep : ∀ i, 1 ≤ i → i ≤ len - 1 →
      0 ≤ (if i = 1 then node else H[i]!).toInt ∧ (if i = 1 then node else H[i]!).toInt ≤ node.toInt := by
    intro i hi1 hi2
    split
    · exact ⟨hp.1, by omega⟩
    · have hb := hB i hi1 hi2; exact ⟨hb.1, by omega⟩
  have hRepInj : ∀ i j, 1 ≤ i → i ≤ len - 1 → 1 ≤ j → j ≤ len - 1 →
      (if i = 1 then node else H[i]!) = (if j = 1 then node else H[j]!) → i = j := by
    intro i j hi1 hi2 hj1 hj2 heq
    by_cases hi : i = 1 <;> by_cases hj : j = 1
    · omega
    · simp only [hi, hj, ite_true, ite_false] at heq
      have hb := hB j hj1 hj2
      rw [← heq] at hb
      omega
    · simp only [hi, hj, ite_true, ite_false] at heq
      have hb := hB i hi1 hi2
      rw [heq] at hb
      omega
    · simp only [hi, hj, ite_false] at heq
      exact hHi i j hi1 hi2 hj1 hj2 heq
  have hp' : PermOn (fun i => H'[i]!) (fun i => if i = 1 then node else H[i]!) (len - 1) := by
    simpa only [hHeap2] using hperm
  refine ⟨hnext, n, m, hl, hm1, hm2, H, H', hn, hm, hnm, hhl, hh1, hh2, rfl,
    hsH'.trans (by rw [hHeap2]; exact hsH), ?_, ?_, ?_, ?_, hp'.injective hRepInj, ?_⟩
  · rw [hframe _ (by omega), hHeap2]
    exact hkeepn
  · rw [hframe _ (by omega), hHeap2]
    exact hkeepm
  · simpa only [tk_arr_heap] using horder'
  · intro i hi1 hi2
    obtain ⟨σ, hr, hi, he⟩ := hp'
    have hei := he i hi1 hi2
    dsimp only at hei
    rw [hei]
    exact hRep (σ i) (hr i hi1 hi2).1 (hr i hi1 hi2).2
  · intro F
    have hc := hcount F
    have hc' := hcount' F
    rw [hroot, hHeap2] at hc'
    omega


/-- Queue representation during actual node merging. The stage counts
completed merges. This records numeric geometry and actual data; it contains
no assumed execution contract. Tail shape and parent links are separate
obligations of the tree-layout proof. -/
structure BTMergeQueue (tk : TK) (N K j : Nat) (node : Int32) (d : DeflateState) : Prop where
  n3 : 3 ≤ N
  n286 : N ≤ 286
  k2 : 2 ≤ K
  kN : K ≤ N
  stage : j < K
  counter : node.toInt = (N + j : Nat)
  len : d.heap_len.toInt = (K - j : Nat)
  max : d.heap_max.toInt + 2 * (j : Int) = 573
  tree : N + K - 1 ≤ (tk.arr d).size
  depth : N + K - 1 ≤ d.depth.size
  heap : d.heap.size = 573
  valid : ∀ i : Nat, 1 ≤ i → (i : Int) ≤ d.heap_len.toInt →
    0 ≤ d.heap[i]!.toInt ∧ d.heap[i]!.toInt < node.toInt
  injective : ∀ i i' : Nat, 1 ≤ i → (i : Int) ≤ d.heap_len.toInt →
    1 ≤ i' → (i' : Int) ≤ d.heap_len.toInt → d.heap[i]! = d.heap[i']! → i = i'
  order : HeapOK (sm (tk.arr d) d.depth) (fun i => d.heap[i]!) (K - j) 0

/-- Actual sorted leaves establish the initial queue representation.
Internal-node array capacity is explicit; the old leaf-prefix theorem does
not claim to supply that additional capacity. -/
theorem BTMergeQueue.of_leaf {tk : TK} {d : DeflateState} {N : Nat} {mc node : Int32}
    (hi : BTLeafInv tk N mc d) (h2 : 2 ≤ d.heap_len.toInt) (hm : d.heap_max = HEAP_SIZE)
    (hn : node.toInt = N)
    (hT : N + d.heap_len.toInt.toNat - 1 ≤ (tk.arr d).size)
    (hD : N + d.heap_len.toInt.toNat - 1 ≤ d.depth.size)
    (ho : HeapOK (sm (tk.arr d) d.depth) (fun i => d.heap[i]!) d.heap_len.toInt.toNat 0) :
    BTMergeQueue tk N d.heap_len.toInt.toNat 0 node d := by
  have hc := hi.count
  have hKN := Math.scanCount_le (btFreq tk d) N
  refine ⟨hi.n3, hi.n286, by omega, by omega, by omega, by omega, by omega,
    by rw [hm]; rfl, hT, hD, hi.heap, ?_, hi.injective, ?_⟩
  · intro i hi1 hi2
    have hv := hi.valid i hi1 hi2
    exact ⟨hv.1, by omega⟩
  · simpa only [Nat.sub_zero] using ho

/-- The checked whole iteration preserves the queue representation and
advances its stage by one. Every bound for the called fragments is derived
from this representation. -/
theorem ws_btMergeBody_queue {h0 : Heap} {id : Nat} {tk : TK} {d : DeflateState}
    {N K j : Nat} {node : Int32} (hi : BTMergeQueue tk N K j node d) (hmore : j + 1 < K) :
    WS h0 id (btMergeBody (Sp id) (.ref (tk.ref id) 0) node) d
      (fun next e => BTMergeQueue tk N K (j + 1) next e) := by
  have hNs := hi.n3
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
  have hT' : (tk.arr { btParentState tk { d with heap := H, heap_len := hlen, heap_max := hm2 } n m node with heap := H' }).size = (tk.arr d).size := by
    rw [tk_arr_heap, btParentState_tree_size]
    cases tk <;> rfl
  refine ⟨hNs, hNb, hK2, hKN, hmore, by omega, ?_, ?_, by rw [hT']; exact hT,
    by simpa only [btParentState_depth_size] using hD, by exact hsize.trans hH, ?_, ?_, ?_⟩
  · simp only [btParentState_len]
    omega
  · simp only [btParentState_max]
    omega
  · intro i hi1 hi2
    simp only [btParentState_len] at hi2
    have hv := hvalid i hi1 (by omega)
    change 0 ≤ H'[i]!.toInt ∧ H'[i]!.toInt < next.toInt
    exact ⟨hv.1, by omega⟩
  · intro i i' hi1 hi2 hi'1 hi'2 heq
    simp only [btParentState_len] at hi2 hi'2
    exact hinj i i' hi1 (by omega) hi'1 (by omega) heq
  · have heq : K - (j + 1) = K - j - 1 := by omega
    rwa [heq]

/-- The complete actual merge loop terminates after exactly K-1 iterations.
Its queue has one valid root and its counter and tail boundary have their
exact source values. This is queue safety and order, not yet tree-layout or
code-emission correctness. -/
theorem ws_btMergeLoop {h0 : Heap} {id : Nat} {tk : TK} {d : DeflateState}
    {N K : Nat} {node : Int32} (hi : BTMergeQueue tk N K 0 node d) :
    WS h0 id (btMergeLoop (Sp id) (.ref (tk.ref id) 0) node) d
      (fun next e => BTMergeQueue tk N K (K - 1) next e ∧ e.heap_len.toInt = 1) := by
  let Inv : Int32 → DeflateState → Prop := fun node e =>
    ∃ j : Nat, BTMergeQueue tk N K j node e ∧ j + 1 < K
  let Q : Int32 → DeflateState → Prop := fun node e =>
    BTMergeQueue tk N K (K - 1) node e ∧ e.heap_len.toInt = 1
  unfold btMergeLoop
  refine WS.cdoWhile2 Inv (fun _ e => e.heap_len.toInt.toNat) Q ?_
    ⟨0, hi, by have := hi.k2; omega⟩ (by have := hi.len; have := hi.kN; have := hi.n286; dsimp only [fuel]; omega)
  intro current e ⟨j, hj, hmore⟩
  refine WS.mono (ws_btMergeBody_queue hj hmore) ?_
  intro next e' hj'
  refine WS.bind' ws_rd fun got e'' ⟨hgot, he''⟩ => ?_
  subst e''; subst got
  have hlen := hj'.len
  have hstage := hj'.stage
  have hK := hj'.k2
  by_cases hcontinue : e'.heap_len.toInt ≥ 2
  · have hjnext : j + 1 + 1 < K := by omega
    refine WS.pure' (Or.inr ⟨by simp only [hcontinue, decide_true], ⟨j + 1, hj', hjnext⟩, ?_⟩)
    have hlen0 := hj.len
    omega
  · have hjend : j + 1 = K - 1 := by omega
    refine WS.pure' (Or.inl ⟨by simp only [hcontinue, decide_false], ?_⟩)
    change Q next e'
    rw [hjend] at hj'
    exact ⟨hj', by omega⟩


/-- Deterministic executions of the same fragment have the same result and
state. Thus separately proved data properties can be combined. -/
theorem merge_ws_and {α : Type} {h0 : Heap} {id : Nat} {m : M α} {d : DeflateState}
    {Q R : α → DeflateState → Prop} (hq : WS h0 id m d Q) (hr : WS h0 id m d R) :
    WS h0 id m d (fun a e => Q a e ∧ R a e) := by
  obtain ⟨a, e, he, hQ⟩ := hq
  obtain ⟨b, f, hf, hR⟩ := hr
  have hp := Except.ok.inj (he.symm.trans hf)
  have hab : a = b := congrArg Prod.fst hp
  have hef : e = f := by
    have hh := congrArg (fun p => p.2.dstates id) hp
    simp only [setD_dstates_same] at hh
    exact Option.some.inj hh
  subst b; subst f
  exact ⟨a, e, he, hQ, hR⟩

/-- The final root store executes its checked decrement and keeps every
other heap cell. Its exact record effect also frames the tree and depth. -/
theorem ws_btSaveRoot {h0 : Heap} {id : Nat} (d : DeflateState)
    (hroot : 1 < d.heap.size) (hm1 : 1 ≤ d.heap_max.toInt)
    (hmH : d.heap_max.toInt ≤ d.heap.size) (hbig : d.heap.size ≤ 573) :
    WS h0 id (btSaveRoot (Sp id)) d (fun _ e => ∃ hm : Int32,
      hm.toInt = d.heap_max.toInt - 1 ∧
      e = { d with heap := d.heap.set! hm.toInt.toNat d.heap[1]!, heap_max := hm } ∧
      e.heap.size = d.heap.size ∧ e.heap[hm.toInt.toNat]! = d.heap[1]! ∧
      ∀ i : Nat, i ≠ hm.toInt.toNat → e.heap[i]! = d.heap[i]!) := by
  unfold btSaveRoot
  refine WS.bind' (ws_heapAt 1 (by decide +kernel) (by change (1 : Int) < d.heap.size; omega))
    fun top e1 ⟨htop, he1⟩ => ?_
  subst e1
  have hi1 : (1 : Int32).toInt.toNat = 1 := rfl
  change top = d.heap[(1 : Int32).toInt.toNat]! at htop
  rw [hi1] at htop
  subst top
  refine WS.bind' ws_rd fun got e1 ⟨hgot, he1⟩ => ?_
  subst e1; subst got
  refine WS.bind' (ws_isub d.heap_max 1 (by omega) (by omega)) fun hm e1 ⟨hhm, he1⟩ => ?_
  subst e1
  refine WS.bind' (ws_md (fun e => { e with heap_max := hm })) fun _ e1 he1 => ?_
  subst e1
  refine WS.mono (ws_heapSet hm d.heap[1]! (by omega) (by dsimp only; omega)) ?_
  intro _ e he
  subst e
  have hi : hm.toInt.toNat < d.heap.size := by omega
  refine ⟨hm, by omega, rfl, size_set! _ _ _, ?_, ?_⟩
  · rw [getD_set d.heap hm.toInt.toNat _ _ hi, if_pos rfl]
  · intro i hne
    rw [getD_set d.heap hm.toInt.toNat i _ hi, if_neg hne]


/-- The exact selected-tree array after parent creation. -/
theorem btParentState_arr (tk : TK) (d : DeflateState) (n m node : Int32) :
    tk.arr (btParentState tk d n m node) =
      let T := tk.arr d
      let T1 := T.set! node.toInt.toNat { T[node.toInt.toNat]! with fc := T[n.toInt.toNat]!.fc + T[m.toInt.toNat]!.fc }
      let T2 := T1.set! m.toInt.toNat { T1[m.toInt.toNat]! with dl := i2us node }
      T2.set! n.toInt.toNat { T2[n.toInt.toNat]! with dl := i2us node } := by cases tk <;> rfl

/-- A frequency store preserves every parent-link cell. -/
theorem merge_setFreq_dad (T : Array CtData) (k i : Nat) (freq : UInt16) (hk : k < T.size) :
    ((T.set! k { T[k]! with fc := freq })[i]!).dl = T[i]!.dl := by
  rw [getD_set T k i _ hk]
  split <;> simp_all

/-- A parent-link store replaces precisely one parent-link value. -/
theorem merge_setDad_dad (T : Array CtData) (k i : Nat) (dad : UInt16) (hk : k < T.size) :
    ((T.set! k { T[k]! with dl := dad })[i]!).dl = if i = k then dad else T[i]!.dl := by
  rw [getD_set T k i _ hk]
  split <;> rfl

/-- Both selected children receive the new parent index. Every other link
is unchanged, even if it is the parent node's old link. This states the
source's 16-bit cast; lossless numeric parent indices follow from bounds. -/
theorem btParentState_dad (tk : TK) (d : DeflateState) (n m node : Int32)
    (hn : NV (tk.arr d) d.depth n) (hm : NV (tk.arr d) d.depth m)
    (hp : NV (tk.arr d) d.depth node) (i : Nat) :
    (tk.arr (btParentState tk d n m node))[i]!.dl =
      if i = n.toInt.toNat ∨ i = m.toInt.toNat then i2us node else (tk.arr d)[i]!.dl := by
  have hnT : n.toInt.toNat < (tk.arr d).size := by have := hn.1; have := hn.2.1; omega
  have hmT : m.toInt.toNat < (tk.arr d).size := by have := hm.1; have := hm.2.1; omega
  have hpT : node.toInt.toNat < (tk.arr d).size := by have := hp.1; have := hp.2.1; omega
  rw [btParentState_arr]
  dsimp only
  rw [merge_setDad_dad _ _ _ _ (by simp only [size_set!]; exact hnT),
    merge_setDad_dad _ _ _ _ (by simp only [size_set!]; exact hmT), merge_setFreq_dad _ _ _ _ hpT]
  by_cases hin : i = n.toInt.toNat <;> by_cases him : i = m.toInt.toNat <;> simp only [hin, him, ite_true, ite_false, or_self, true_or, false_or, or_true, ite_self]

/-- The queue representation leaves room for the final checked root store.
This includes the largest admitted alphabet and leaf count. -/
theorem BTMergeQueue.tail_bounds {tk : TK} {d : DeflateState} {N K j : Nat} {node : Int32}
    (hi : BTMergeQueue tk N K j node d) : 3 ≤ d.heap_max.toInt ∧ d.heap_max.toInt ≤ 573 := by
  have := hi.n286
  have := hi.kN
  have := hi.stage
  have := hi.max
  omega

end Zlib.Trees.Proofs
