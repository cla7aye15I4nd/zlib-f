import ZlibF.Proof.«trees.c.heap.base»

/-!
# trees.c: `pqdownheap` and `pqremove`

The priority queue is `s->heap[1 .. heap_len]`, ordered by `smaller` (frequency, then depth). `pqd` is the pure
model of `pqdownheap`; `ws_pqdownheap` says the translation computes it, with every index inside the arrays.
-/

namespace Zlib.Trees.Proofs
open C Zlib.Trees

/-! ### Checked `int` arithmetic -/

theorem ofInt_toInt' (x : Int) (h1 : -2147483648 ≤ x) (h2 : x ≤ 2147483647) : (Int32.ofInt x).toInt = x := by
  rw [Int32.toInt_ofInt]
  have : Int32.size = 4294967296 := rfl
  rw [this, Int.bmod_eq_of_le] <;> omega

section arith
variable {h0 : Heap} {id : Nat} {d : DeflateState}

theorem ws_ck (x : Int) (h1 : -2147483648 ≤ x) (h2 : x ≤ 2147483647) :
    WS h0 id (ck x) d (fun v d' => v.toInt = x ∧ d' = d) :=
  WS.of_eq (by simp [ck, h1, h2]) ⟨ofInt_toInt' x h1 h2, rfl⟩

theorem ws_iadd (a b : Int32) (h1 : -2147483648 ≤ a.toInt + b.toInt) (h2 : a.toInt + b.toInt ≤ 2147483647) :
    WS h0 id (iadd a b) d (fun v d' => v.toInt = a.toInt + b.toInt ∧ d' = d) := ws_ck _ h1 h2

theorem ws_isub (a b : Int32) (h1 : -2147483648 ≤ a.toInt - b.toInt) (h2 : a.toInt - b.toInt ≤ 2147483647) :
    WS h0 id (isub a b) d (fun v d' => v.toInt = a.toInt - b.toInt ∧ d' = d) := ws_ck _ h1 h2

theorem ws_shl1 (x : Int32) (h1 : 0 ≤ x.toInt) (h2 : x.toInt * 2 ≤ 2147483647) :
    WS h0 id (shl1 x) d (fun v d' => v.toInt = x.toInt * 2 ∧ d' = d) := by
  have : ¬ x.toInt < 0 := by omega
  unfold shl1
  simp only [this, ite_false]
  exact ws_ck _ (by omega) h2

theorem ws_heapAt (i : Int32) (h1 : 0 ≤ i.toInt) (h2 : i.toInt < d.heap.size) :
    WS h0 id (heapAt (Sp id) i) d (fun v d' => v = d.heap[i.toInt.toNat]! ∧ d' = d) := by
  unfold heapAt
  refine WS.bind' ws_pHeap fun p d1 ⟨hp, hd⟩ => ?_
  subst hp; subst hd
  exact ws_index_heap _ h1 h2

theorem ws_heapSet (i : Int32) (v : Int32) (h1 : 0 ≤ i.toInt) (h2 : i.toInt < d.heap.size) :
    WS h0 id (heapSet (Sp id) i v) d (fun _ d' => d' = { d with heap := d.heap.set! i.toInt.toNat v }) := by
  unfold heapSet
  refine WS.bind' ws_pHeap fun p d1 ⟨hp, hd⟩ => ?_
  subst hp; subst hd
  exact ws_setAt_heap _ _ h1 h2

end arith

/-! ### The order `smaller` -/

/-- `smaller(tree, n, m, depth)` on the arrays. -/
def sm (T : Array CtData) (D : Array UInt8) (n m : Int32) : Bool :=
  decide ((T[n.toInt.toNat]!).fc < (T[m.toInt.toNat]!).fc) ||
  ((T[n.toInt.toNat]!).fc == (T[m.toInt.toNat]!).fc && decide (D[n.toInt.toNat]! ≤ D[m.toInt.toNat]!))

/-- `x` is a node of the tree `T` with a depth entry. -/
def NV (T : Array CtData) (D : Array UInt8) (x : Int32) : Prop :=
  0 ≤ x.toInt ∧ x.toInt < T.size ∧ x.toInt < D.size

theorem ws_smaller {h0 : Heap} {id : Nat} {d : DeflateState} (k : TK) (n m : Int32)
    (hn : NV (k.arr d) d.depth n) (hm : NV (k.arr d) d.depth m) :
    WS h0 id (smaller (Ptr.ref (k.ref id) 0) n m (Ptr.ref (BRef.dstate_depth id) 0)) d
      (fun v d' => v = sm (k.arr d) d.depth n m ∧ d' = d) := by
  obtain ⟨hn0, hn1, hn2⟩ := hn
  obtain ⟨hm0, hm1, hm2⟩ := hm
  unfold smaller
  refine WS.bind' (ws_getFc k _ hn0 hn1) fun fn d1 ⟨hfn, hd1⟩ => ?_
  subst hd1
  refine WS.bind' (ws_getFc k _ hm0 hm1) fun fm d1 ⟨hfm, hd1⟩ => ?_
  subst hd1
  subst hfn; subst hfm
  refine WS.ite' (fun hlt => ?_) (fun hnlt => ?_)
  · refine WS.pure' ⟨?_, rfl⟩
    simp only [sm, hlt, decide_true, Bool.true_or]
  · refine WS.ite' (fun heq => ?_) (fun hne => ?_)
    · refine WS.bind' (ws_index_depth _ hn0 hn2) fun dn d1 ⟨hdn, hd1⟩ => ?_
      subst hd1
      refine WS.bind' (ws_index_depth _ hm0 hm2) fun dm d1 ⟨hdm, hd1⟩ => ?_
      subst hd1
      subst hdn; subst hdm
      refine WS.pure' ⟨?_, rfl⟩
      simp only [sm, hnlt, heq, decide_false, Bool.false_or, Bool.true_and]
    · refine WS.pure' ⟨?_, rfl⟩
      have hne' : ((k.arr d1)[n.toInt.toNat]!.fc == (k.arr d1)[m.toInt.toNat]!.fc) = false := by simpa using hne
      simp only [sm, hnlt, hne', decide_false, Bool.false_or, Bool.false_and]


@[simp] theorem tk_arr_heap (tk : TK) (d : DeflateState) (a : Array Int32) : tk.arr { d with heap := a } = tk.arr d := by
  cases tk <;> rfl

/-- The common tail of one pass of the loop of `pqdownheap`, for the child `jj` that was chosen. -/
theorem ws_pq_cont {h0 : Heap} {id : Nat} (tk : TK) (kk jj v : Int32) (e : DeflateState)
    (hk1 : 1 ≤ kk.toInt) (hk2 : kk.toInt < e.heap.size) (hj1 : 1 ≤ jj.toInt) (hj2 : jj.toInt < e.heap.size)
    (hj3 : jj.toInt ≤ 1000000000)
    (hnj : NV (tk.arr e) e.depth (e.heap[jj.toInt.toNat]!)) (hnv : NV (tk.arr e) e.depth v) :
    WS h0 id (do
        let hj ← heapAt (Sp id) jj
        let dp ← pDepth (Sp id)
        let b ← smaller (Ptr.ref (tk.ref id) 0) v hj dp
        if b = true then pure (kk, jj, true) else do
          heapSet (Sp id) kk hj
          let j2 ← shl1 jj
          pure (jj, j2, false)) e
      (fun st e' =>
        (sm (tk.arr e) e.depth v e.heap[jj.toInt.toNat]! = true ∧ st = (kk, jj, true) ∧ e' = e) ∨
        (sm (tk.arr e) e.depth v e.heap[jj.toInt.toNat]! = false ∧ st.1 = jj ∧ st.2.1.toInt = 2 * jj.toInt ∧
          st.2.2 = false ∧ e' = { e with heap := e.heap.set! kk.toInt.toNat e.heap[jj.toInt.toNat]! })) := by
  refine WS.bind' (ws_heapAt jj (by omega) hj2) fun hj e1 ⟨hhj, he1⟩ => ?_
  subst e1; subst hhj
  refine WS.bind' ws_pDepth fun dp e1 ⟨hdp, he1⟩ => ?_
  subst e1; subst hdp
  refine WS.bind' (ws_smaller tk v _ hnv hnj) fun b e1 ⟨hb, he1⟩ => ?_
  subst e1; subst hb
  cases hsm : sm (tk.arr e) e.depth v e.heap[jj.toInt.toNat]!
  · simp only [Bool.false_eq_true, ite_false]
    refine WS.bind' (ws_heapSet kk _ (by omega) hk2) fun _ e1 he1 => ?_
    subst e1
    refine WS.bind' (ws_shl1 jj (by omega) (by omega)) fun j2 e1 ⟨hj2', he1⟩ => ?_
    subst e1
    refine WS.pure' (Or.inr ⟨trivial, rfl, ?_, rfl, rfl⟩)
    show j2.toInt = 2 * jj.toInt
    omega
  · simp only [ite_true]
    exact WS.pure' (Or.inl ⟨trivial, rfl, rfl⟩)

end Zlib.Trees.Proofs
