import ZlibF.Math.DeflateTreeForce
import ZlibF.Proof.«trees.c.build.scan»

/-!
# trees.c: repairing an alphabet with fewer than two used symbols

The fresh-leaf argument follows the reference `BuildTreeB` proof. The
executions use the actual record and pointer accessors of this translation.
-/

namespace Zlib.Trees.Proofs
open C Zlib.Trees

/-- The body of the two-leaf repair, verbatim. -/
def btForceBody (s : DeflateStatePtr) (tree stree : CtDataPtr) : Int32 → M Int32 :=
  fun mc => do
    let mut mc := mc
    let mut val : Int32 := 0
    if mc.toInt < 2 then
      mc ← iadd mc 1
      val := mc
    let hl ← iadd (← rd s).heap_len 1
    md s fun d => { d with heap_len := hl }
    heapSet s hl val
    let node := val
    setFc tree node.toInt 1
    setAt (← pDepth s) node.toInt 0
    md s fun d => { d with opt_len := d.opt_len - 1 }
    if stree != .null then
      let l ← getDl stree node.toInt
      md s fun d => { d with static_len := d.static_len - l.toUInt64 }
    pure mc

/-- The actual `while (s->heap_len < 2)` loop. -/
def btForce (s : DeflateStatePtr) (tree stree : CtDataPtr) (mc : Int32) : M Int32 :=
  cwhile (σ := Int32)
    (fun mc => do pure (decide ((← rd s).heap_len.toInt < 2), mc))
    (btForceBody s tree stree) mc

/-- A static tree is absent, or it is a readable array unchanged by every
write to this dynamic state. This is a heap representation fact. -/
def BTStatic (h0 : Heap) (id : Nat) (stree : CtDataPtr) (N : Nat) (sl : Option (Nat → UInt16)) : Prop :=
  (stree = .null ∧ sl = none) ∨ ∃ (r : CtDataRef) (T : Array CtData) (f : Nat → UInt16),
    stree = .ref r 0 ∧ sl = some f ∧
      (∀ e : DeflateState, Space.get (setD h0 id e) r = some T) ∧
      ∀ v < N, v < T.size ∧ f v = (T[v]!).dl

/-- The record produced by one repair iteration, including both cost
adjustments. Unsigned costs may wrap, exactly as in C. -/
def btForceState (tk : TK) (d : DeflateState) (node hl : Int32) (sl : Option (Nat → UInt16)) : DeflateState :=
  { tk.setArr d ((tk.arr d).set! node.toInt.toNat { (tk.arr d)[node.toInt.toNat]! with fc := 1 }) with
    heap_len := hl, heap := d.heap.set! hl.toInt.toNat node, depth := d.depth.set! node.toInt.toNat 0,
    opt_len := d.opt_len - 1,
    static_len := match sl with | none => d.static_len | some f => d.static_len - (f node.toInt.toNat).toUInt64 }

/-- The tail after selecting the dummy symbol. It runs in source order. -/
private theorem btForce_writes {h0 : Heap} {id : Nat} (tk : TK) (d : DeflateState)
    (node mc : Int32) (N : Nat) (stree : CtDataPtr) (sl : Option (Nat → UInt16))
    (hs : BTStatic h0 id stree N sl) (hn0 : 0 ≤ node.toInt) (hnN : node.toInt < N)
    (hT : N ≤ (tk.arr d).size) (hD : N ≤ d.depth.size)
    (hl0 : 0 ≤ d.heap_len.toInt) (hl2 : d.heap_len.toInt < 2) (hH : d.heap.size = 573) :
    WS h0 id (do
      let hl ← iadd (← rd (Sp id)).heap_len 1
      md (Sp id) fun d => { d with heap_len := hl }
      heapSet (Sp id) hl node
      setFc (.ref (tk.ref id) 0) node.toInt 1
      setAt (← pDepth (Sp id)) node.toInt 0
      md (Sp id) fun d => { d with opt_len := d.opt_len - 1 }
      if stree != .null then
        let l ← getDl stree node.toInt
        md (Sp id) fun d => { d with static_len := d.static_len - l.toUInt64 }
      pure mc) d (fun r e => ∃ hl : Int32,
        hl.toInt = d.heap_len.toInt + 1 ∧ r = mc ∧ e = btForceState tk d node hl sl) := by
  have hi1 : (1 : Int32).toInt = 1 := rfl
  refine WS.bind' ws_rd fun dz e1 ⟨hdz, he1⟩ => ?_
  subst e1; subst dz
  refine WS.bind' (ws_iadd d.heap_len 1 (by omega) (by omega)) fun hl e1 ⟨hhl, he1⟩ => ?_
  subst e1
  refine WS.bind' (ws_md (fun e => { e with heap_len := hl })) fun _ e1 he1 => ?_
  subst e1
  unfold heapSet
  simp only [M_bind_assoc]
  refine WS.bind' ws_pHeap fun p e1 ⟨hp, he1⟩ => ?_
  subst e1; subst p
  refine WS.bind' (ws_setAt_heap hl.toInt node (by omega) (by dsimp; omega)) fun _ e1 he1 => ?_
  subst e1
  have ht : tk.arr { d with heap_len := hl, heap := d.heap.set! hl.toInt.toNat node } = tk.arr d := by cases tk <;> rfl
  refine WS.bind' (ws_setFc tk node.toInt 1 hn0 (by rw [ht]; omega)) fun _ e1 he1 => ?_
  subst e1
  refine WS.bind' ws_pDepth fun p e1 ⟨hp, he1⟩ => ?_
  subst e1; subst p
  refine WS.bind' (ws_setAt_depth node.toInt 0 hn0 (by simp only [tk_setArr_depth]; omega)) fun _ e1 he1 => ?_
  subst e1
  refine WS.bind' (ws_md _) fun _ e1 he1 => ?_
  subst e1
  rcases hs with ⟨rfl, rfl⟩ | ⟨r, T, f, rfl, rfl, hr, hf⟩
  · simp only [bne_self_eq_false, Bool.false_eq_true, ite_false, M_pure_bind]
    refine WS.pure' ⟨hl, by omega, rfl, ?_⟩
    unfold btForceState
    rw [ht]
    cases tk <;> rfl
  · have hne : (Ptr.ref r 0 != (Ptr.null : CtDataPtr)) = true := by simp
    simp only [hne, ite_true]
    have hnN' : node.toInt.toNat < N := by omega
    have hread : ∀ e : DeflateState,
        WS h0 id (getDl (.ref r 0) node.toInt) e
          (fun v e' => v = f node.toInt.toNat ∧ e' = e) := by
      intro e
      unfold getDl
      have hget := index0_ok (hr e) (i := node.toInt) hn0 (by have := (hf _ hnN').1; omega)
      refine WS.of_eq (by simp only [bind_app, hget]; rfl) ⟨(hf _ hnN').2.symm, rfl⟩
    refine WS.bind' (hread _) fun v e1 ⟨hv, he1⟩ => ?_
    subst e1; subst v
    refine WS.bind' (ws_md _) fun _ e1 he1 => ?_
    subst e1
    refine WS.pure' ⟨hl, by omega, rfl, ?_⟩
    unfold btForceState
    rw [ht]
    cases tk <;> rfl

/-- One actual repair step chooses the C symbol and has the exact write
and unsigned-cost effects. Freshness is derived separately from the leaf
invariant, rather than assumed by this execution theorem. -/
theorem btForceBody_run {h0 : Heap} {id : Nat} (tk : TK) (d : DeflateState)
    (mc : Int32) (N : Nat) (stree : CtDataPtr) (sl : Option (Nat → UInt16))
    (hs : BTStatic h0 id stree N sl) (hN : 3 ≤ N) (hN286 : N ≤ 286)
    (hm0 : -1 ≤ mc.toInt) (hmN : mc.toInt < N)
    (hT : N ≤ (tk.arr d).size) (hD : N ≤ d.depth.size)
    (hl0 : 0 ≤ d.heap_len.toInt) (hl2 : d.heap_len.toInt < 2) (hH : d.heap.size = 573) :
    WS h0 id (btForceBody (Sp id) (.ref (tk.ref id) 0) stree mc) d (fun r e =>
      ∃ node hl : Int32, node.toInt = (Math.forceNode mc.toInt : Int) ∧
        r.toInt = Math.forceMax mc.toInt ∧ hl.toInt = d.heap_len.toInt + 1 ∧
        e = btForceState tk d node hl sl) := by
  have hi1 : (1 : Int32).toInt = 1 := rfl
  unfold btForceBody
  by_cases hsmall : mc.toInt < 2
  · simp only [hsmall, ite_true, M_bind_assoc, M_pure_bind]
    refine WS.bind' (ws_iadd mc 1 (by omega) (by omega)) fun mc' e1 ⟨hmc', he1⟩ => ?_
    subst e1
    refine WS.mono (btForce_writes tk d mc' mc' N stree sl hs (by omega) (by omega)
      hT hD hl0 hl2 hH) ?_
    intro r e ⟨hl, hhl, hr, he⟩
    subst r
    refine ⟨mc', hl, ?_, ?_, hhl, he⟩
    · simp only [Math.forceNode, if_pos hsmall]; omega
    · simp only [Math.forceMax, if_pos hsmall]; omega
  · simp only [hsmall, ite_false, M_bind_assoc, M_pure_bind]
    refine WS.mono (btForce_writes tk d 0 mc N stree sl hs (by decide +kernel) (by change (0 : Int) < N; omega)
      hT hD hl0 hl2 hH) ?_
    intro r e ⟨hl, hhl, hr, he⟩
    subst r
    exact ⟨0, hl, by simp only [Math.forceNode, if_neg hsmall]; rfl,
      by simp only [Math.forceMax, if_neg hsmall], hhl, he⟩

@[simp] theorem btForceState_tree (tk : TK) (d node hl sl) :
    tk.arr (btForceState tk d node hl sl) =
      (tk.arr d).set! node.toInt.toNat { (tk.arr d)[node.toInt.toNat]! with fc := 1 } := by cases tk <;> rfl

@[simp] theorem btForceState_heap (tk : TK) (d node hl sl) :
    (btForceState tk d node hl sl).heap = d.heap.set! hl.toInt.toNat node := rfl

@[simp] theorem btForceState_depth (tk : TK) (d node hl sl) :
    (btForceState tk d node hl sl).depth = d.depth.set! node.toInt.toNat 0 := rfl

@[simp] theorem btForceState_len (tk : TK) (d node hl sl) :
    (btForceState tk d node hl sl).heap_len = hl := rfl

/-- Facts needed by heap construction. They are established by the scan and
preserved by the two-leaf repair, including the all-zero alphabet. -/
structure BTLeafInv (tk : TK) (N : Nat) (mc : Int32) (d : DeflateState) : Prop where
  n3 : 3 ≤ N
  n286 : N ≤ 286
  tree : N ≤ (tk.arr d).size
  depth : N ≤ d.depth.size
  heap : d.heap.size = 573
  count : d.heap_len.toInt = Math.scanCount (btFreq tk d) N
  maxCode : mc.toInt = Math.scanMax (btFreq tk d) N
  valid : ∀ q : Nat, 1 ≤ q → (q : Int) ≤ d.heap_len.toInt →
    0 ≤ (d.heap[q]!).toInt ∧ (d.heap[q]!).toInt < N ∧ btFreq tk d (d.heap[q]!).toInt.toNat ≠ 0
  injective : ∀ q q' : Nat, 1 ≤ q → (q : Int) ≤ d.heap_len.toInt →
    1 ≤ q' → (q' : Int) ≤ d.heap_len.toInt → d.heap[q]! = d.heap[q']! → q = q'
  complete : ∀ v < N, btFreq tk d v ≠ 0 →
    ∃ q : Nat, 1 ≤ q ∧ (q : Int) ≤ d.heap_len.toInt ∧ (d.heap[q]!).toInt = v
  usedDepth : ∀ v < N, btFreq tk d v ≠ 0 → d.depth[v]! = 0
  unusedLength : ∀ v < N, btFreq tk d v = 0 → ((tk.arr d)[v]!).dl = 0

/-- The initial scan supplies the leaf invariant for the repair loop. -/
theorem BTLeafInv.of_scan {tk : TK} {d e : DeflateState} {N : Nat} {mc : Int32}
    (hscan : BTScanInv tk d N mc e) (hN3 : 3 ≤ N) (hN286 : N ≤ 286)
    (hT : N ≤ (tk.arr d).size) (hD : N ≤ d.depth.size) (hH : d.heap.size = 573) :
    BTLeafInv tk N mc e := by
  obtain ⟨T, H, D, hl, rfl, hsT, hsH, hsD, hhl, hmc, ht, hd, hh, hv, hj, hc⟩ := hscan
  have hfreq : ∀ v < N, btFreq tk (btScanState tk d T H D hl) v = btFreq tk d v := by
    intro v hv
    unfold btFreq
    rw [btScanState_tree, ht v (by omega)]
    split <;> rfl
  refine ⟨hN3, hN286, by simp only [btScanState_tree]; omega,
    by simp only [btScanState_depth]; omega, by simp only [btScanState_heap]; omega,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [btScanState_len, Math.scanCount_congr _ _ N hfreq] using hhl
  · simpa only [Math.scanMax_congr _ _ N hfreq] using hmc
  · intro q hq1 hq2
    obtain ⟨hq0, hqN, hfq⟩ := hv q hq1 (by simp only [btScanState_len] at hq2; omega)
    refine ⟨hq0, hqN, ?_⟩
    rw [btScanState_heap, hfreq _ (by omega)]
    exact hfq
  · intro q q' hq1 hq2 hq'1 hq'2 heq
    exact hj q q' hq1 (by simp only [btScanState_len] at hq2; omega)
      hq'1 (by simp only [btScanState_len] at hq'2; omega) heq
  · intro v hv hfv
    rw [hfreq v hv] at hfv
    obtain ⟨q, hq1, hq2, hqv⟩ := hc v hv hfv
    exact ⟨q, hq1, by simp only [btScanState_len]; omega, hqv⟩
  · intro v hv hfv
    rw [hfreq v hv] at hfv
    simp only [btScanState_depth]
    rw [hd v (by omega), if_pos ⟨hv, hfv⟩]
  · intro v hv hfv
    rw [hfreq v hv] at hfv
    simp only [btScanState_tree]
    rw [ht v (by omega), if_pos ⟨hv, hfv⟩]

/-- The code-cell write is the exact frequency-function update. -/
theorem btForceState_freq (tk : TK) (d : DeflateState) (node hl : Int32)
    (sl : Option (Nat → UInt16)) (hn : node.toInt.toNat < (tk.arr d).size) :
    btFreq tk (btForceState tk d node hl sl) =
      fun v => if v = node.toInt.toNat then 1 else btFreq tk d v := by
  funext v
  unfold btFreq
  rw [btForceState_tree, getD_set _ node.toInt.toNat v _ hn]
  split <;> rfl

/-- Every length survives the repair's frequency write. -/
theorem btForceState_lengths (tk : TK) (d : DeflateState) (node hl : Int32)
    (sl : Option (Nat → UInt16)) (hn : node.toInt.toNat < (tk.arr d).size) (v : Nat) :
    ((tk.arr (btForceState tk d node hl sl))[v]!).dl = ((tk.arr d)[v]!).dl := by
  rw [btForceState_tree, getD_set _ node.toInt.toNat v _ hn]
  split
  · rename_i heq; subst v; rfl
  · rfl

/-- One repair iteration preserves the full leaf representation. In
particular the new leaf is fresh, so the appended heap entry cannot duplicate
an existing one. The new maximum and frequency count are derived from the
actual selected symbol, including `max_code = -1`, `0`, `1` and `≥ 2`. -/
theorem BTLeafInv.force {tk : TK} {N : Nat} {mc : Int32} {d : DeflateState}
    (hi : BTLeafInv tk N mc d) (hsmall : d.heap_len.toInt < 2)
    (node hl mc' : Int32) (sl : Option (Nat → UInt16))
    (hnode : node.toInt = (Math.forceNode mc.toInt : Int))
    (hmc : mc'.toInt = Math.forceMax mc.toInt)
    (hhl : hl.toInt = d.heap_len.toInt + 1) :
    BTLeafInv tk N mc' (btForceState tk d node hl sl) := by
  have hcount : Math.scanCount (btFreq tk d) N ≤ 1 := by have := hi.count; omega
  have hfresh := Math.forceNode_fresh (btFreq tk d) N hi.n3 hcount
  rw [← hi.maxCode] at hfresh
  have hn0 : 0 ≤ node.toInt := by omega
  have hnN : node.toInt.toNat < N := by omega
  have hnodeN : node.toInt.toNat = Math.forceNode mc.toInt := by omega
  have hnT : node.toInt.toNat < (tk.arr d).size := by have := hi.tree; omega
  have hnD : node.toInt.toNat < d.depth.size := by have := hi.depth; omega
  have hhl0 : 0 ≤ d.heap_len.toInt := by have := hi.count; omega
  have hhlN : hl.toInt.toNat = d.heap_len.toInt.toNat + 1 := by omega
  have hhH : hl.toInt.toNat < d.heap.size := by rw [hi.heap]; omega
  have hfreq : btFreq tk (btForceState tk d node hl sl) = Math.forceFreq (btFreq tk d) mc.toInt := by
    rw [btForceState_freq tk d node hl sl hnT, hnodeN]
    rfl
  have hfreqcount : Math.scanCount (btFreq tk (btForceState tk d node hl sl)) N =
      Math.scanCount (btFreq tk d) N + 1 := by
    rw [hfreq, hi.maxCode]
    exact Math.scanCount_force (btFreq tk d) N hi.n3 hcount
  have hfreqmax : Math.scanMax (btFreq tk (btForceState tk d node hl sl)) N =
      Math.forceMax mc.toInt := by
    rw [hfreq, hi.maxCode]
    exact Math.scanMax_force (btFreq tk d) N hi.n3 hcount
  have hvalueNe : ∀ q : Nat, 1 ≤ q → (q : Int) ≤ d.heap_len.toInt → d.heap[q]! ≠ node := by
    intro q hq1 hq2 heq
    have hused := (hi.valid q hq1 hq2).2.2
    rw [heq, hnodeN, hfresh.2] at hused
    exact hused rfl
  refine ⟨hi.n3, hi.n286, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [btForceState_tree, size_set!]; exact hi.tree
  · simp only [btForceState_depth, size_set!]; exact hi.depth
  · simp only [btForceState_heap, size_set!]; exact hi.heap
  · simp only [btForceState_len, hfreqcount]
    have := hi.count
    omega
  · rw [hmc, hfreqmax]
  · intro q hq1 hq2
    simp only [btForceState_len] at hq2
    rw [btForceState_heap, getD_set _ hl.toInt.toNat q node hhH]
    by_cases hq : q = hl.toInt.toNat
    · rw [if_pos hq]
      refine ⟨hn0, by omega, ?_⟩
      rw [hfreq]
      simp [Math.forceFreq, hnodeN]
    · rw [if_neg hq]
      obtain ⟨h0, hN, hused⟩ := hi.valid q hq1 (by omega)
      refine ⟨h0, hN, ?_⟩
      rw [hfreq]
      unfold Math.forceFreq
      split
      · decide +kernel
      · exact hused
  · intro q q' hq1 hq2 hq'1 hq'2 heq
    simp only [btForceState_len] at hq2 hq'2
    rw [btForceState_heap, getD_set _ hl.toInt.toNat q node hhH,
      getD_set _ hl.toInt.toNat q' node hhH] at heq
    by_cases hq : q = hl.toInt.toNat
    · rw [if_pos hq] at heq
      by_cases hq' : q' = hl.toInt.toNat
      · omega
      · rw [if_neg hq'] at heq
        exact False.elim (hvalueNe q' hq'1 (by omega) heq.symm)
    · rw [if_neg hq] at heq
      by_cases hq' : q' = hl.toInt.toNat
      · rw [if_pos hq'] at heq
        exact False.elim (hvalueNe q hq1 (by omega) heq)
      · rw [if_neg hq'] at heq
        exact hi.injective q q' hq1 (by omega) hq'1 (by omega) heq
  · intro v hv hfv
    rw [hfreq] at hfv
    by_cases heq : v = node.toInt.toNat
    · refine ⟨hl.toInt.toNat, by omega, by simp only [btForceState_len]; omega, ?_⟩
      rw [btForceState_heap, getD_set _ hl.toInt.toNat _ node hhH, if_pos rfl]
      omega
    · have hfold : btFreq tk d v ≠ 0 := by
        simpa only [Math.forceFreq, if_neg (show v ≠ Math.forceNode mc.toInt by omega)] using hfv
      obtain ⟨q, hq1, hq2, hqv⟩ := hi.complete v hv hfold
      refine ⟨q, hq1, by simp only [btForceState_len]; omega, ?_⟩
      rw [btForceState_heap, getD_set _ hl.toInt.toNat q node hhH, if_neg (by omega)]
      exact hqv
  · intro v hv hfv
    rw [hfreq] at hfv
    rw [btForceState_depth, getD_set _ node.toInt.toNat v 0 hnD]
    by_cases heq : v = node.toInt.toNat
    · rw [if_pos heq]
    · rw [if_neg heq]
      apply hi.usedDepth v hv
      simpa only [Math.forceFreq, if_neg (show v ≠ Math.forceNode mc.toInt by omega)] using hfv
  · intro v hv hfv
    rw [hfreq] at hfv
    have heq : v ≠ node.toInt.toNat := by
      intro heq
      rw [heq, hnodeN] at hfv
      simp [Math.forceFreq] at hfv
    rw [btForceState_lengths tk d node hl sl hnT]
    apply hi.unusedLength v hv
    simpa only [Math.forceFreq, if_neg (show v ≠ Math.forceNode mc.toInt by omega)] using hfv

/-- Exact record effects of successive repair iterations. This records data
updates and symbol choices; it assumes no execution or callee contract. The
loop theorem below establishes this trace from the actual translated loop. -/
inductive BTForceTrace (tk : TK) (sl : Option (Nat → UInt16)) :
    Nat → Int32 → DeflateState → Int32 → DeflateState → Prop where
  | nil (mc : Int32) (d : DeflateState) : BTForceTrace tk sl 0 mc d mc d
  | snoc {k : Nat} {mc0 mc mc' : Int32} {d0 d : DeflateState} (node hl : Int32)
      (before : BTForceTrace tk sl k mc0 d0 mc d)
      (hnode : node.toInt = (Math.forceNode mc.toInt : Int))
      (hnodeT : node.toInt.toNat < (tk.arr d).size)
      (hmc : mc'.toInt = Math.forceMax mc.toInt)
      (hhl : hl.toInt = d.heap_len.toInt + 1) :
      BTForceTrace tk sl (k + 1) mc0 d0 mc' (btForceState tk d node hl sl)

/-- The complete actual repair loop terminates after at most two iterations,
produces exactly `max(2, old heap_len)` distinct live leaves, keeps the leaf
invariant, and records every source-order memory and cost update. -/
theorem ws_btForce {h0 : Heap} {id : Nat} (tk : TK) (d : DeflateState) (mc : Int32) (N : Nat)
    (stree : CtDataPtr) (sl : Option (Nat → UInt16)) (hs : BTStatic h0 id stree N sl)
    (hi : BTLeafInv tk N mc d) :
    WS h0 id (btForce (Sp id) (.ref (tk.ref id) 0) stree mc) d (fun r e =>
      BTLeafInv tk N r e ∧ e.heap_len.toInt = max 2 d.heap_len.toInt ∧
        ∃ k : Nat, k ≤ 2 ∧ k = (2 - d.heap_len.toInt).toNat ∧ BTForceTrace tk sl k mc d r e) := by
  have hlen0 : 0 ≤ d.heap_len.toInt := by have := hi.count; omega
  let Inv : Int32 → DeflateState → Prop := fun r e =>
    BTLeafInv tk N r e ∧ e.heap_len.toInt ≤ max 2 d.heap_len.toInt ∧
      ∃ k : Nat, k ≤ 2 ∧ e.heap_len.toInt = d.heap_len.toInt + k ∧ BTForceTrace tk sl k mc d r e
  let Q : Int32 → DeflateState → Prop := fun r e =>
    BTLeafInv tk N r e ∧ e.heap_len.toInt = max 2 d.heap_len.toInt ∧
      ∃ k : Nat, k ≤ 2 ∧ k = (2 - d.heap_len.toInt).toNat ∧ BTForceTrace tk sl k mc d r e
  unfold btForce
  refine WS.cwhile2 Inv (fun _ e => (2 - e.heap_len.toInt).toNat) Q ?_
    ⟨hi, by omega, 0, by omega, by omega, BTForceTrace.nil mc d⟩ (by simp only [fuel]; omega)
  intro r e ⟨hie, hupper, k, hk, hlen, htrace⟩
  refine WS.bind' ws_rd fun dz e1 ⟨hdz, he1⟩ => ?_
  subst e1; subst dz
  by_cases hsmall : e.heap_len.toInt < 2
  · refine WS.pure' (Or.inr ⟨by simp only [hsmall, decide_true], ?_⟩)
    have he0 : 0 ≤ e.heap_len.toInt := by have := hie.count; omega
    have hm := Math.scanMax_bounds (btFreq tk e) N
    rw [← hie.maxCode] at hm
    refine WS.mono (btForceBody_run tk e r N stree sl hs hie.n3 hie.n286 hm.1 hm.2
      hie.tree hie.depth he0 hsmall hie.heap) ?_
    intro r' e' ⟨node, hl, hn, hmc', hhl, he'⟩
    subst e'
    have hnT : node.toInt.toNat < (tk.arr e).size := by
      have hfresh := Math.forceNode_fresh (btFreq tk e) N hie.n3 (by have := hie.count; omega)
      rw [← hie.maxCode] at hfresh
      have := hie.tree
      omega
    refine ⟨⟨hie.force hsmall node hl r' sl hn hmc' hhl, ?_, k + 1, by omega, ?_,
      BTForceTrace.snoc node hl htrace hn hnT hmc' hhl⟩, ?_⟩
    · simp only [btForceState_len]; omega
    · simp only [btForceState_len]; omega
    · simp only [btForceState_len]; omega
  · refine WS.pure' (Or.inl ⟨by simp only [hsmall, decide_false], hie, ?_, k, hk, ?_, htrace⟩)
    · omega
    · omega

/-- The repair cannot change any tree length. This follows from the exact
trace of actual iterations, not a frame premise supplied by a caller. -/
theorem BTForceTrace.lengths {tk : TK} {sl : Option (Nat → UInt16)}
    {k : Nat} {mc0 mc : Int32} {d0 d : DeflateState} (h : BTForceTrace tk sl k mc0 d0 mc d)
    (v : Nat) : ((tk.arr d)[v]!).dl = ((tk.arr d0)[v]!).dl := by
  induction h with
  | nil => rfl
  | snoc node hl before hn hnT hm hhl ih =>
    rw [btForceState_lengths tk _ node hl sl hnT v, ih]

/-- Every field outside the selected tree, heap, depth, heap length and two
cost counters is unchanged. All other heap records are already framed by
the actual loop execution theorem's `WS` result. -/
theorem BTForceTrace.frame {tk : TK} {sl : Option (Nat → UInt16)}
    {k : Nat} {mc0 mc : Int32} {d0 d : DeflateState} (h : BTForceTrace tk sl k mc0 d0 mc d) :
    ∃ (T : Array CtData) (H : Array Int32) (D : Array UInt8) (hl : Int32) (O S : UInt64),
      d = { btScanState tk d0 T H D hl with opt_len := O, static_len := S } := by
  induction h with
  | nil mc d =>
    refine ⟨tk.arr d, d.heap, d.depth, d.heap_len, d.opt_len, d.static_len, ?_⟩
    cases tk <;> rfl
  | snoc node hl before hn hnT hm hhl ih =>
    obtain ⟨T, H, D, hl0, O, S, he⟩ := ih
    subst he
    refine ⟨T.set! node.toInt.toNat { T[node.toInt.toNat]! with fc := 1 },
      H.set! hl.toInt.toNat node, D.set! node.toInt.toNat 0, hl, O - 1,
      (match sl with | none => S | some f => S - (f node.toInt.toNat).toUInt64), ?_⟩
    cases sl <;> cases tk <;> rfl

/-- The repair subtracts exactly one from the unsigned optimal-bit counter
per iteration. No non-underflow assumption is needed. -/
theorem BTForceTrace.opt_len {tk : TK} {sl : Option (Nat → UInt16)}
    {k : Nat} {mc0 mc : Int32} {d0 d : DeflateState} (h : BTForceTrace tk sl k mc0 d0 mc d)
    (hk : k ≤ 2) : d.opt_len = d0.opt_len - UInt64.ofNat k := by
  induction h with
  | nil => simp
  | @snoc k' mc0 mc mc' d0' d' node hl before hn hnT hm hhl ih =>
    change _ - 1 = _
    rw [ih (by omega)]
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_sub, UInt64.toNat_ofNat', show (1 : UInt64).toNat = 1 from rfl]
    have hlt := d0'.opt_len.toNat_lt
    omega

end Zlib.Trees.Proofs
