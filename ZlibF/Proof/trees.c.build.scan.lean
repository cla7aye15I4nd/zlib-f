import ZlibF.Math.DeflateTreeScan
import ZlibF.Proof.«trees.c.monad»
import ZlibF.Proof.«trees.c.heap.gbdef»

/-! # trees.c: the first `build_tree` scan -/

namespace Zlib.Trees.Proofs
open C Zlib.Trees

/-- The first scan's body, in the actual source order. -/
def btScanBody (s : DeflateStatePtr) (tree : CtDataPtr) : Int32 × Int32 → M (Int32 × Int32) :=
  fun (n, mc) => do
    if (← getFc tree n.toInt) != 0 then
      let hl ← iadd (← rd s).heap_len 1
      md s fun d => { d with heap_len := hl }
      heapSet s hl n
      setAt (← pDepth s) n.toInt 0
      pure (n, n)
    else
      setDl tree n.toInt 0
      pure (n, mc)

/-- The first scan, including the separate increment. -/
def btScan (s : DeflateStatePtr) (tree : CtDataPtr) (elems : Int32) : M (Int32 × Int32) :=
  cfor (σ := Int32 × Int32)
    (fun (n, _) => pure (decide (n.toInt < elems.toInt)))
    (fun (n, mc) => do pure (← iadd n 1, mc))
    (btScanBody s tree) (0, -1)

/-- Exact state frame of the scan. -/
def btScanState (tk : TK) (d : DeflateState) (T : Array CtData) (H : Array Int32)
    (D : Array UInt8) (hl : Int32) : DeflateState :=
  { tk.setArr d T with heap := H, depth := D, heap_len := hl }

@[simp] theorem btScanState_tree (tk : TK) (d T H D hl) :
    tk.arr (btScanState tk d T H D hl) = T := by cases tk <;> rfl

@[simp] theorem btScanState_heap (tk : TK) (d T H D hl) :
    (btScanState tk d T H D hl).heap = H := rfl

@[simp] theorem btScanState_depth (tk : TK) (d T H D hl) :
    (btScanState tk d T H D hl).depth = D := rfl

@[simp] theorem btScanState_len (tk : TK) (d T H D hl) :
    (btScanState tk d T H D hl).heap_len = hl := rfl

/-- One actual positive-frequency iteration writes the next heap slot and
zeroes the leaf depth. It keeps the code-tree entry unchanged. -/
theorem btScanBody_used {h0 : Heap} {id : Nat} (tk : TK) (d : DeflateState) (n mc : Int32)
    (hn0 : 0 ≤ n.toInt) (hnT : n.toInt < (tk.arr d).size)
    (hnD : n.toInt < d.depth.size) (hl0 : 0 ≤ d.heap_len.toInt)
    (hlH : d.heap_len.toInt + 1 < d.heap.size) (hbig : d.heap.size ≤ 573)
    (hf : ((tk.arr d)[n.toInt.toNat]!).fc ≠ 0) :
    WS h0 id (btScanBody (Sp id) (.ref (tk.ref id) 0) (n, mc)) d
      (fun r e => ∃ hl : Int32, hl.toInt = d.heap_len.toInt + 1 ∧ r = (n, n) ∧
        e = { d with
          heap_len := hl, heap := d.heap.set! hl.toInt.toNat n, depth := d.depth.set! n.toInt.toNat 0 }) := by
  unfold btScanBody
  refine WS.bind' (ws_getFc tk n.toInt hn0 hnT) fun v e1 ⟨hv, he1⟩ => ?_
  subst e1; subst v
  have hb : (((tk.arr d)[n.toInt.toNat]!).fc != 0) = true := by simpa using hf
  simp only [hb, Bool.true_eq, ite_true]
  refine WS.bind' ws_rd fun dz e1 ⟨hdz, he1⟩ => ?_
  subst e1; subst dz
  have hi1 : (1 : Int32).toInt = 1 := rfl
  refine WS.bind' (ws_iadd d.heap_len 1 (by omega) (by omega)) fun hl e1 ⟨hhl, he1⟩ => ?_
  subst e1
  refine WS.bind' (ws_md (fun e => { e with heap_len := hl })) fun _ e1 he1 => ?_
  subst e1
  unfold heapSet
  simp only [M_bind_assoc]
  refine WS.bind' ws_pHeap fun p e1 ⟨hp, he1⟩ => ?_
  subst e1; subst p
  refine WS.bind' (ws_setAt_heap hl.toInt n (by omega) (by dsimp; omega)) fun _ e1 he1 => ?_
  subst e1
  refine WS.bind' ws_pDepth fun p e1 ⟨hp, he1⟩ => ?_
  subst e1; subst p
  refine WS.bind' (ws_setAt_depth n.toInt 0 hn0 (by dsimp; exact hnD)) fun _ e1 he1 => ?_
  subst e1
  exact WS.pure' ⟨hl, by omega, rfl, rfl⟩

/-- One actual zero-frequency iteration only clears that leaf's length. -/
theorem btScanBody_unused {h0 : Heap} {id : Nat} (tk : TK) (d : DeflateState) (n mc : Int32)
    (hn0 : 0 ≤ n.toInt) (hnT : n.toInt < (tk.arr d).size)
    (hf : ((tk.arr d)[n.toInt.toNat]!).fc = 0) :
    WS h0 id (btScanBody (Sp id) (.ref (tk.ref id) 0) (n, mc)) d
      (fun r e => r = (n, mc) ∧
        e = tk.setArr d ((tk.arr d).set! n.toInt.toNat { (tk.arr d)[n.toInt.toNat]! with dl := 0 })) := by
  unfold btScanBody
  refine WS.bind' (ws_getFc tk n.toInt hn0 hnT) fun v e1 ⟨hv, he1⟩ => ?_
  subst e1; subst v
  simp only [hf, bne_self_eq_false, Bool.false_eq_true, ite_false]
  refine WS.bind' (ws_setDl tk n.toInt 0 hn0 hnT) fun _ e1 he1 => ?_
  subst e1
  exact WS.pure' ⟨rfl, by simp only [hf]⟩

/-- Frequencies before the scan; the scan preserves these code cells. -/
def btFreq (tk : TK) (d : DeflateState) (v : Nat) : UInt16 := ((tk.arr d)[v]!).fc

/-- The first scan's derived state: exact writes, one occurrence of every
used symbol, no other heap entries, and the exact largest used symbol. -/
def BTScanInv (tk : TK) (d : DeflateState) (k : Nat) (mc : Int32) (e : DeflateState) : Prop :=
  let fr := btFreq tk d
  ∃ (T : Array CtData) (H : Array Int32) (D : Array UInt8) (hl : Int32),
    e = btScanState tk d T H D hl ∧ T.size = (tk.arr d).size ∧ H.size = d.heap.size ∧
    D.size = d.depth.size ∧ hl.toInt = Math.scanCount fr k ∧ mc.toInt = Math.scanMax fr k ∧
    (∀ j < T.size, T[j]! = if j < k ∧ fr j = 0 then { (tk.arr d)[j]! with dl := 0 } else (tk.arr d)[j]!) ∧
    (∀ j < D.size, D[j]! = if j < k ∧ fr j ≠ 0 then 0 else d.depth[j]!) ∧
    (∀ q, ¬ (1 ≤ q ∧ q ≤ Math.scanCount fr k) → H[q]! = d.heap[q]!) ∧
    (∀ q, 1 ≤ q → q ≤ Math.scanCount fr k →
      0 ≤ H[q]!.toInt ∧ H[q]!.toInt < k ∧ fr H[q]!.toInt.toNat ≠ 0) ∧
    (∀ q q', 1 ≤ q → q ≤ Math.scanCount fr k → 1 ≤ q' → q' ≤ Math.scanCount fr k →
      H[q]! = H[q']! → q = q') ∧
    ∀ v < k, fr v ≠ 0 → ∃ q, 1 ≤ q ∧ q ≤ Math.scanCount fr k ∧ H[q]!.toInt = v

/-- The scan invariant is established by an empty heap, independently of
the old lengths and depths. -/
theorem btScan_init (tk : TK) (d : DeflateState) (hl : d.heap_len.toInt = 0) :
    BTScanInv tk d 0 (-1) d := by
  refine ⟨tk.arr d, d.heap, d.depth, d.heap_len, ?_, rfl, rfl, rfl, hl, rfl,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases tk <;> rfl
  · intro j hj; simp
  · intro j hj; simp
  · intro q hq; rfl
  · intro q hq1 hq2; simp only [Math.scanCount] at hq2; omega
  · intro q q' hq1 hq2; simp only [Math.scanCount] at hq2; omega
  · intro v hv; omega

/-- One complete scan iteration, including the separate checked increment. -/
theorem btScan_step {h0 : Heap} {id : Nat} (tk : TK) (d e : DeflateState) (k N : Nat)
    (n mc : Int32) (hn : n.toInt = k) (hk : k < N) (hN : N ≤ 286)
    (hT : N ≤ (tk.arr d).size) (hD : N ≤ d.depth.size)
    (hH : N < d.heap.size) (hbig : d.heap.size ≤ 573)
    (hi : BTScanInv tk d k mc e) :
    WS h0 id (do
      let (n, mc) ← btScanBody (Sp id) (.ref (tk.ref id) 0) (n, mc)
      pure (← iadd n 1, mc)) e (fun r e' => r.1.toInt = k + 1 ∧ BTScanInv tk d (k + 1) r.2 e') := by
  obtain ⟨T, H, D, hl, he, hsT, hsH, hsD, hhl, hmc, ht, hd, hh, hv, hj, hc⟩ := hi
  subst e
  have hcount := Math.scanCount_le (btFreq tk d) k
  have hnN : n.toInt.toNat = k := by omega
  have hkT : k < T.size := by omega
  have hkD : k < D.size := by omega
  have hcur : (T[k]!).fc = (btFreq tk d) k := by rw [ht k hkT]; split <;> rfl
  have hfcur : ((tk.arr (btScanState tk d T H D hl))[n.toInt.toNat]!).fc = (btFreq tk d) k := by
    simpa only [btScanState_tree, hnN] using hcur
  have hi1 : (1 : Int32).toInt = 1 := rfl
  by_cases hf : (btFreq tk d) k ≠ 0
  · refine WS.bind' (btScanBody_used tk (btScanState tk d T H D hl) n mc
      (by omega) (by simp only [btScanState_tree]; omega)
      (by simp only [btScanState_depth]; omega) (by simp only [btScanState_len]; omega)
      (by simp only [btScanState_len, btScanState_heap]; omega)
      (by simp only [btScanState_heap]; omega) (by rw [hfcur]; exact hf))
      fun r e1 ⟨hl', hhl', hr, he1⟩ => ?_
    subst r; subst e1
    dsimp only
    refine WS.bind' (ws_iadd n 1 (by omega) (by omega)) fun n' e1 ⟨hn', he1⟩ => ?_
    subst e1
    have hhl' : hl'.toInt = Math.scanCount (btFreq tk d) k + 1 := by simpa only [btScanState_len, hhl] using hhl'
    have hhlN : hl'.toInt.toNat = Math.scanCount (btFreq tk d) k + 1 := by omega
    have hnewH : Math.scanCount (btFreq tk d) k + 1 < H.size := by omega
    have hnext : Math.scanCount (btFreq tk d) (k + 1) = Math.scanCount (btFreq tk d) k + 1 := by simp only [Math.scanCount, if_pos hf]
    have hnextmc : Math.scanMax (btFreq tk d) (k + 1) = k := by simp only [Math.scanMax, if_pos hf]
    refine WS.pure' ⟨by dsimp; omega,
      T, H.set! (Math.scanCount (btFreq tk d) k + 1) n, D.set! k 0, hl', ?_, hsT,
      by simpa only [size_set!] using hsH, by simpa only [size_set!] using hsD,
      by rw [hnext]; omega, by dsimp; rw [hnextmc]; exact hn, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [btScanState_heap, btScanState_depth, hnN, hhlN]
      rfl
    · intro j hjT
      rw [ht j hjT]
      by_cases hjk : j = k
      · subst j; simp [hf]
      · have hcut : (j < k) ↔ (j < k + 1) := by omega
        simp only [hcut]
    · intro j hjD
      have hjD' : j < D.size := by simpa only [size_set!] using hjD
      rw [getD_set D k j 0 hkD]
      by_cases hjk : j = k
      · subst j; simp [hf]
      · rw [if_neg hjk, hd j hjD']
        have hcut : (j < k) ↔ (j < k + 1) := by omega
        simp only [hcut]
    · intro q hq
      rw [hnext] at hq
      rw [getD_set H (Math.scanCount (btFreq tk d) k + 1) q n hnewH, if_neg (by omega)]
      exact hh q (by omega)
    · intro q hq1 hq2
      rw [hnext] at hq2
      rw [getD_set H (Math.scanCount (btFreq tk d) k + 1) q n hnewH]
      by_cases hq : q = Math.scanCount (btFreq tk d) k + 1
      · rw [if_pos hq]
        exact ⟨by omega, by omega, by simpa only [hnN] using hf⟩
      · rw [if_neg hq]
        obtain ⟨h0, hlt, hfq⟩ := hv q hq1 (by omega)
        exact ⟨h0, by omega, hfq⟩
    · intro q q' hq1 hq2 hq'1 hq'2 heq
      rw [hnext] at hq2 hq'2
      rw [getD_set H (Math.scanCount (btFreq tk d) k + 1) q n hnewH,
        getD_set H (Math.scanCount (btFreq tk d) k + 1) q' n hnewH] at heq
      by_cases hq : q = Math.scanCount (btFreq tk d) k + 1
      · rw [if_pos hq] at heq
        by_cases hq' : q' = Math.scanCount (btFreq tk d) k + 1
        · omega
        · rw [if_neg hq'] at heq
          have hlt := (hv q' hq'1 (by omega)).2.1
          rw [← heq] at hlt
          omega
      · rw [if_neg hq] at heq
        by_cases hq' : q' = Math.scanCount (btFreq tk d) k + 1
        · rw [if_pos hq'] at heq
          have hlt := (hv q hq1 (by omega)).2.1
          rw [heq] at hlt
          omega
        · rw [if_neg hq'] at heq
          exact hj q q' hq1 (by omega) hq'1 (by omega) heq
    · intro v hvk hfv
      rw [hnext]
      by_cases hvk' : v = k
      · subst v
        refine ⟨Math.scanCount (btFreq tk d) k + 1, by omega, by omega, ?_⟩
        rw [getD_set H (Math.scanCount (btFreq tk d) k + 1) _ n hnewH, if_pos rfl]
        exact hn
      · obtain ⟨q, hq1, hq2, hqv⟩ := hc v (by omega) hfv
        refine ⟨q, hq1, by omega, ?_⟩
        rw [getD_set H (Math.scanCount (btFreq tk d) k + 1) q n hnewH, if_neg (by omega)]
        exact hqv
  · have hf0 : (btFreq tk d) k = 0 := by simpa using hf
    refine WS.bind' (btScanBody_unused tk (btScanState tk d T H D hl) n mc
      (by omega) (by simp only [btScanState_tree]; omega) (by rw [hfcur]; exact hf0))
      fun r e1 ⟨hr, he1⟩ => ?_
    subst r; subst e1
    dsimp only
    refine WS.bind' (ws_iadd n 1 (by omega) (by omega)) fun n' e1 ⟨hn', he1⟩ => ?_
    subst e1
    have hnext : Math.scanCount (btFreq tk d) (k + 1) = Math.scanCount (btFreq tk d) k := by simp only [Math.scanCount, hf0, ne_eq, not_true_eq_false, ite_false, Nat.add_zero]
    have hnextmc : Math.scanMax (btFreq tk d) (k + 1) = Math.scanMax (btFreq tk d) k := by simp only [Math.scanMax, hf0, ne_eq, not_true_eq_false, ite_false]
    refine WS.pure' ⟨by dsimp; omega,
      T.set! k { T[k]! with dl := 0 }, H, D, hl, ?_,
      by simpa only [size_set!] using hsT, hsH, hsD,
      by simpa only [hnext] using hhl, by simpa only [hnextmc] using hmc, ?_, ?_,
      by simpa only [hnext] using hh, ?_, by simpa only [hnext] using hj, ?_⟩
    · simp only [btScanState_tree, hnN]
      cases tk <;> rfl
    · intro j hjT
      have hjT' : j < T.size := by simpa only [size_set!] using hjT
      rw [getD_set T k j _ hkT]
      by_cases hjk : j = k
      · subst j
        rw [if_pos rfl, ht k hkT]
        simp [hf0]
      · rw [if_neg hjk, ht j hjT']
        have hcut : (j < k) ↔ (j < k + 1) := by omega
        simp only [hcut]
    · intro j hjD
      rw [hd j hjD]
      by_cases hjk : j = k
      · subst j; simp [hf0]
      · have hcut : (j < k) ↔ (j < k + 1) := by omega
        simp only [hcut]
    · intro q hq1 hq2
      rw [hnext] at hq2
      obtain ⟨h0, hlt, hfq⟩ := hv q hq1 hq2
      exact ⟨h0, by omega, hfq⟩
    · intro v hvk hfv
      rw [hnext]
      have hvk' : v < k := by
        by_cases heq : v = k
        · subst v; exact False.elim (hfv hf0)
        · omega
      exact hc v hvk' hfv

/-- The complete first scan terminates, keeps each used symbol exactly once
in the heap, computes the exact largest used symbol, clears unused lengths,
and preserves all cells outside its explicit write set. The caller must supply
the empty heap written immediately before the loop. -/
theorem ws_btScan {h0 : Heap} {id : Nat} (tk : TK) (d : DeflateState) (elems : Int32)
    (he0 : 0 ≤ elems.toInt) (he286 : elems.toInt ≤ 286)
    (hT : elems.toInt ≤ (tk.arr d).size) (hD : elems.toInt ≤ d.depth.size)
    (hH : elems.toInt < d.heap.size) (hbig : d.heap.size ≤ 573)
    (hlen : d.heap_len.toInt = 0) :
    WS h0 id (btScan (Sp id) (.ref (tk.ref id) 0) elems) d
      (fun r e => r.1.toInt = elems.toInt ∧ BTScanInv tk d elems.toInt.toNat r.2 e) := by
  let N := elems.toInt.toNat
  have heN : elems.toInt = N := by dsimp [N]; omega
  let Inv : Int32 × Int32 → DeflateState → Prop := fun r e =>
    ∃ k : Nat, k ≤ N ∧ r.1.toInt = k ∧ BTScanInv tk d k r.2 e
  unfold btScan
  refine WS.cfor2 Inv (fun r _ => N - r.1.toInt.toNat) _ ?_
    ⟨0, by omega, rfl, btScan_init tk d hlen⟩ (by simp only [fuel]; omega)
  rintro ⟨n, mc⟩ e ⟨k, hk, hn, hi⟩
  change n.toInt = (k : Int) at hn
  refine WS.pure' ?_
  by_cases hlt : k < N
  · refine Or.inr ⟨by simp only [decide_eq_true_eq]; omega, ?_⟩
    dsimp only
    refine WS.mono (btScan_step tk d e k N n mc hn hlt (by omega) (by omega)
      (by omega) (by omega) hbig hi) ?_
    intro r e' ⟨hr, hi'⟩
    exact ⟨⟨k + 1, by omega, hr, hi'⟩, by omega⟩
  · refine Or.inl ⟨by simp only [decide_eq_false_iff_not]; omega, ?_⟩
    have hkN : k = N := by omega
    exact ⟨by dsimp; omega, by simpa only [hkN] using hi⟩

/-- Any scanned symbol absent from the resulting heap has length zero.
This derives the inactive-symbol condition needed after tree construction. -/
theorem BTScanInv.absent_zero {tk : TK} {d e : DeflateState} {k : Nat} {mc : Int32}
    (hi : BTScanInv tk d k mc e) (hT : k ≤ (tk.arr d).size) (v : Nat) (hv : v < k)
    (habsent : ∀ q : Nat, 1 ≤ q → (q : Int) ≤ e.heap_len.toInt → (e.heap[q]!).toInt ≠ v) :
    ((tk.arr e)[v]!).dl = 0 := by
  obtain ⟨T, H, D, hl, rfl, hsT, hsH, hsD, hhl, hmc, ht, hd, hh, hvalid, hinj, hcomplete⟩ := hi
  have hfreq : btFreq tk d v = 0 := by
    apply Classical.byContradiction
    intro hf
    obtain ⟨q, hq1, hq2, hqv⟩ := hcomplete v hv hf
    exact habsent q hq1 (by simp only [btScanState_len]; omega) hqv
  simp only [btScanState_tree]
  rw [ht v (by omega), if_pos ⟨hv, hfreq⟩]

end Zlib.Trees.Proofs
