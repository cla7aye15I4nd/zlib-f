import ZlibF.Proof.«trees.c.heap.pq»
import ZlibF.Proof.«trees.c.heap.ord»

/-!
# trees.c: `pqdownheap` keeps the heap order

The loop invariant and the hole lemmas (`HoleInv`, `hole_step`, ...) are those of the earlier attempt
(`Proofs/trees/PqDownHeapOrd.lean`), restated for the record `d` of the new heap model.
-/

namespace Zlib.Trees.Proofs
open C Zlib.Trees

theorem sm_eq (T : Array CtData) (D : Array UInt8) :
    sm T D = smallerB (fun n => (T[n]!).fc) (fun n => D[n]!) := rfl

theorem sm_ok (T : Array CtData) (D : Array UInt8) : KeyOK (sm T D) := by
  rw [sm_eq]; exact smallerB_ok _ _

/-- The heap array with the pending value `v` in the hole `K`. -/
def wh (hp : Array Int32) (K : Nat) (v : Int32) : Nat → Int32 := fun i => if i = K then v else hp[i]!

theorem ws_pqdownheap {h0 : Heap} {id : Nat} (tk : TK) (d : DeflateState) (kk : Int32) (k0 len : Nat)
    (hk : kk.toInt = k0) (hk1 : 1 ≤ k0) (hk2 : k0 ≤ len) (hlen : d.heap_len.toInt = len)
    (hsz : len < d.heap.size) (hbig : d.heap.size ≤ 1000000)
    (hval : ∀ i, 1 ≤ i → i ≤ len → NV (tk.arr d) d.depth d.heap[i]!)
    (hheap : HeapOK (sm (tk.arr d) d.depth) (fun i => d.heap[i]!) len k0) :
    WS h0 id (pqdownheap (Sp id) (Ptr.ref (tk.ref id) 0) kk) d (fun _ d' =>
      ∃ hp', d' = { d with heap := hp' } ∧ hp'.size = d.heap.size ∧
        (∀ i, ¬ (1 ≤ i ∧ i ≤ len) → hp'[i]! = d.heap[i]!) ∧
        PermOn (fun i => hp'[i]!) (fun i => d.heap[i]!) len ∧
        HeapOK (sm (tk.arr d) d.depth) (fun i => hp'[i]!) len (k0 - 1)) := by
  have kOK := sm_ok (tk.arr d) d.depth
  unfold pqdownheap
  simp only []
  refine WS.bind' (ws_heapAt kk (by omega) (by omega)) fun v d1 ⟨hv, hd1⟩ => ?_
  subst d1
  refine WS.bind' (ws_shl1 kk (by omega) (by omega)) fun j d1 ⟨hj, hd1⟩ => ?_
  subst d1
  have hv' : v = d.heap[k0]! := by rw [hv]; congr 1; omega
  have hnv : NV (tk.arr d) d.depth v := by rw [hv']; exact hval k0 hk1 hk2
  let H : Nat → Int32 := fun i => d.heap[i]!
  let Inv : Int32 × Int32 × Bool → DeflateState → Prop := fun st e => ∃ (K : Nat) (hpc : Array Int32),
    e = { d with heap := hpc } ∧ hpc.size = d.heap.size ∧ (∀ i, ¬ (1 ≤ i ∧ i ≤ len) → hpc[i]! = d.heap[i]!) ∧
    st.1.toInt = K ∧ k0 ≤ K ∧ K ≤ len ∧ (st.2.2 = false → st.2.1.toInt = 2 * K) ∧
    PermOn (wh hpc K v) H len ∧ HoleInv (sm (tk.arr d) d.depth) (wh hpc K v) len k0 K ∧
    (st.2.2 = true → ∃ j', MinChild (sm (tk.arr d) d.depth) (wh hpc K v) len K j' ∧
      sm (tk.arr d) d.depth (wh hpc K v K) (wh hpc K v j') = true)
  let Q : Int32 × Int32 × Bool → DeflateState → Prop := fun st e => ∃ (K : Nat) (hpc : Array Int32),
    e = { d with heap := hpc } ∧ hpc.size = d.heap.size ∧ (∀ i, ¬ (1 ≤ i ∧ i ≤ len) → hpc[i]! = d.heap[i]!) ∧
    st.1.toInt = K ∧ k0 ≤ K ∧ K ≤ len ∧ PermOn (wh hpc K v) H len ∧
    HeapOK (sm (tk.arr d) d.depth) (wh hpc K v) len (k0 - 1)
  let μ : Int32 × Int32 × Bool → DeflateState → Nat := fun st _ => if st.2.2 then 0 else 4000000 - st.2.1.toInt.toNat
  have hf : ∀ st e, μ st e < fuel := fun st e => by
    unfold μ; split <;> simp only [fuel] <;> omega
  have hwh0 : wh d.heap k0 v = H := by
    funext i; simp only [wh, H]; split <;> simp_all
  have hI0 : Inv (kk, j, false) d :=
    ⟨k0, d.heap, rfl, rfl, fun _ _ => rfl, hk, Nat.le_refl _, hk2, fun _ => by simp only; omega,
      by rw [hwh0]; exact PermOn.refl _ _, by rw [hwh0]; exact hole_init hheap, fun e => by simp at e⟩
  refine WS.bind' (Q := Q) (WS.cwhile2 (id := id) Inv μ Q ?_ hI0 (hf _ d)) ?_
  · -- one step
    rintro ⟨kk', jj, bb⟩ e ⟨K, hpc, he, hsz', hfr, hK, hK1, hK2, hj', hp, hhole, hbrk⟩
    subst he
    simp only at hK hj' hbrk
    have hvalA : ∀ i, 1 ≤ i → i ≤ len → NV (tk.arr d) d.depth (wh hpc K v i) := by
      obtain ⟨σ, hr, -, hee⟩ := hp
      intro i h1 h2
      have := hee i h1 h2
      have h3 : wh hpc K v i = d.heap[σ i]! := this
      rw [h3]; exact hval _ (hr i h1 h2).1 (hr i h1 h2).2
    cases bb with
    | true =>
      refine WS.pure' (Or.inl ⟨rfl, ?_⟩)
      obtain ⟨j', hm, hkey⟩ := hbrk rfl
      exact ⟨K, hpc, rfl, hsz', hfr, hK, hK1, hK2, hp, hole_break kOK ⟨hk1, hK1⟩ hhole hm hkey⟩
    | false =>
      have hj'' : jj.toInt = 2 * K := hj' rfl
      refine WS.bind' ws_rd fun l e1 ⟨hl, he1⟩ => ?_
      subst e1; subst hl
      by_cases hleaf : 2 * K ≤ len
      · -- the body runs
        refine WS.pure' (Or.inr ⟨?_, ?_⟩)
        · simp only [decide_eq_true_eq]
          show jj.toInt ≤ d.heap_len.toInt
          omega
        refine WS.bind' ws_rd fun l e1 ⟨hl, he1⟩ => ?_
        subst e1; subst hl
        dsimp only
        have hK573 : K < hpc.size := by omega
        have hvK : NV (tk.arr d) d.depth v := hnv
        -- the common tail, for the chosen child `j1 = J`
        have tail : ∀ (j1 : Int32) (J : Nat), j1.toInt = J → MinChild (sm (tk.arr d) d.depth) (wh hpc K v) len K J →
            WS h0 id (do
              let hj ← heapAt (Sp id) j1
              let dp ← pDepth (Sp id)
              let b ← smaller (Ptr.ref (tk.ref id) 0) v hj dp
              if b = true then pure (kk', j1, true) else do
                heapSet (Sp id) kk' hj
                let j2 ← shl1 j1
                pure (j1, j2, false)) { d with heap := hpc }
              (fun st e2 => Inv st e2 ∧ μ st e2 < μ (kk', jj, false) { d with heap := hpc }) := by
          intro j1 J hJ hm
          have hJK : J ≠ K := by have := hm.1; omega
          have hJ1 : 1 ≤ J ∧ J ≤ len := ⟨by have := hm.2.1; omega, hm.2.2.1⟩
          have hK1' : 1 ≤ K := by omega
          have hJsz : J < hpc.size := by omega
          have hJv : (wh hpc K v J) = hpc[J]! := by simp [wh, hJK]
          have hnJ : NV (tk.arr d) d.depth hpc[J]! := by rw [← hJv]; exact hvalA J hJ1.1 hJ1.2
          have hjtn : j1.toInt.toNat = J := by omega
          have hnJ' : NV (tk.arr { d with heap := hpc }) ({ d with heap := hpc }).depth
              (({ d with heap := hpc }).heap[j1.toInt.toNat]!) := by
            rw [tk_arr_heap]; show NV (tk.arr d) d.depth hpc[j1.toInt.toNat]!; rw [hjtn]; exact hnJ
          have hnv' : NV (tk.arr { d with heap := hpc }) ({ d with heap := hpc }).depth v := by
            rw [tk_arr_heap]; exact hnv
          refine WS.mono (ws_pq_cont (h0 := h0) (id := id) tk kk' j1 v { d with heap := hpc }
            (by show 1 ≤ kk'.toInt; omega) (by show kk'.toInt < hpc.size; omega)
            (by show 1 ≤ j1.toInt; omega) (by show j1.toInt < hpc.size; omega) (by omega) hnJ' hnv') ?_
          intro st e2 hq
          rcases hq with ⟨hsm, hst, he2⟩ | ⟨hsm, hst1, hst2, hst3, he2⟩
          · subst hst; subst he2
            simp only [hjtn] at hsm
            refine ⟨⟨K, hpc, rfl, hsz', hfr, hK, hK1, hK2, fun e => by simp at e, hp, hhole,
              fun _ => ⟨J, hm, ?_⟩⟩, ?_⟩
            · simpa [wh, hJK] using hsm
            · simp only [μ, ite_true, Bool.false_eq_true, ite_false, Int32.toNatClampNeg]; omega
          · have hkK : kk'.toInt.toNat = K := by omega
            simp only [hjtn, hkK] at he2
            subst he2
            simp only [hjtn] at hsm
            have hsw : wh (hpc.set! K hpc[J]!) J v = swapAt (wh hpc K v) K J := by
              funext i
              simp only [wh, swapAt, getD_set hpc K i _ hK573]
              by_cases e1 : i = J
              · subst e1; simp [hJK]
              · by_cases e2 : i = K
                · subst e2; simp [e1]; intro h; omega
                · simp [e1, e2]
            have hkey : sm (tk.arr d) d.depth (wh hpc K v K) (wh hpc K v J) = false := by
              simpa [wh, hJK] using hsm
            refine ⟨⟨J, hpc.set! K hpc[J]!, rfl, by rw [size_set!]; exact hsz', ?_, by rw [hst1]; exact hJ, by have := hm.1; omega, hJ1.2,
              fun _ => by omega, ?_, ?_, fun e => by rw [hst3] at e; simp at e⟩, ?_⟩
            · intro i hi
              rw [getD_set hpc K i _ hK573, if_neg (by omega)]; exact hfr i hi
            · rw [hsw]; exact hp.swap ⟨hK1', hK2⟩ hJ1
            · rw [hsw]
              exact hole_step kOK ⟨hk1, hK1⟩ hhole hm hkey
            · simp only [μ, hst3, ite_true, Bool.false_eq_true, ite_false, Int32.toNatClampNeg]
              have := hm.1
              have h1 : st.2.1.toInt = 2 * (J : Int) := by omega
              omega
        have hNVe : ∀ x, NV (tk.arr d) d.depth x →
            NV (tk.arr { d with heap := hpc }) ({ d with heap := hpc }).depth x :=
          fun x hx => by rw [tk_arr_heap]; exact hx
        have hAe : ∀ i, i ≠ K → wh hpc K v i = hpc[i]! := fun i hi => by simp [wh, hi]
        have h1i : (1 : Int32).toInt = 1 := rfl
        have refl : ∀ x, sm (tk.arr d) d.depth x x = true := fun x => (kOK.total x x).elim (fun h => h) (fun h => h)
        by_cases h2 : 2 * K < len
        · have hlt : jj.toInt < d.heap_len.toInt := by omega
          refine WS.ite' (fun _ => ?_) (fun hn => absurd hlt hn)
          refine WS.bind' (ws_iadd jj 1 (by rw [h1i]; omega) (by rw [h1i]; omega)) fun j1 e1 ⟨hj1, he1⟩ => ?_
          subst e1
          have hi1 : j1.toInt.toNat = 2 * K + 1 := by rw [h1i] at hj1; omega
          have hi0 : jj.toInt.toNat = 2 * K := by omega
          refine WS.bind' (ws_heapAt j1 (by rw [h1i] at hj1; omega) (by show j1.toInt < (hpc.size : Int); rw [h1i] at hj1; omega))
            fun a e1 ⟨ha, he1⟩ => ?_
          subst e1
          refine WS.bind' (ws_heapAt jj (by omega) (by show jj.toInt < (hpc.size : Int); omega)) fun b e1 ⟨hb, he1⟩ => ?_
          subst e1
          refine WS.bind' ws_pDepth fun dp e1 ⟨hdp, he1⟩ => ?_
          subst e1; subst hdp
          have hv1 : NV (tk.arr d) d.depth hpc[2 * K + 1]! := by
            rw [← hAe _ (by omega)]; exact hvalA _ (by omega) (by omega)
          have hv0 : NV (tk.arr d) d.depth hpc[2 * K]! := by
            rw [← hAe _ (by omega)]; exact hvalA _ (by omega) (by omega)
          have ha' : a = hpc[2 * K + 1]! := by rw [ha]; show hpc[j1.toInt.toNat]! = _; rw [hi1]
          have hb' : b = hpc[2 * K]! := by rw [hb]; show hpc[jj.toInt.toNat]! = _; rw [hi0]
          subst ha'; subst hb'
          refine WS.bind' (ws_smaller tk _ _ (hNVe _ hv1) (hNVe _ hv0)) fun s1 e1 ⟨hs1, he1⟩ => ?_
          subst e1
          by_cases hs : sm (tk.arr d) d.depth hpc[2 * K + 1]! hpc[2 * K]! = true
          · have hs1' : s1 = true := by rw [hs1]; simpa using hs
            subst hs1'
            simp only [ite_true]
            refine WS.bind' (ws_iadd jj 1 (by rw [h1i]; omega) (by rw [h1i]; omega)) fun j1' e1 ⟨hj1', he1⟩ => ?_
            subst e1
            refine tail j1' (2 * K + 1) (by rw [h1i] at hj1'; omega) ⟨by omega, by omega, by omega, ?_⟩
            intro c hc h2c hlc
            have : c = 2 * K ∨ c = 2 * K + 1 := by omega
            rcases this with rfl | rfl
            · rw [hAe _ (by omega), hAe _ (by omega)]; exact hs
            · exact refl _
          · have hs1' : s1 = false := by rw [hs1]; simpa using hs
            subst hs1'
            simp only [Bool.false_eq_true, ite_false]
            refine tail jj (2 * K) (by omega) ⟨by omega, by omega, by omega, ?_⟩
            intro c hc h2c hlc
            have : c = 2 * K ∨ c = 2 * K + 1 := by omega
            rcases this with rfl | rfl
            · exact refl _
            · rcases kOK.total (wh hpc K v (2 * K)) (wh hpc K v (2 * K + 1)) with e | e
              · exact e
              · rw [hAe _ (by omega), hAe _ (by omega)] at e; exact absurd e hs
        · have hnlt : ¬ jj.toInt < d.heap_len.toInt := by omega
          refine WS.ite' (fun hn => absurd hn hnlt) (fun _ => ?_)
          refine tail jj (2 * K) (by omega) ⟨by omega, by omega, by omega, ?_⟩
          intro c hc h2c hlc
          have : c = 2 * K := by omega
          subst this
          exact refl _
      · refine WS.pure' (Or.inl ⟨?_, ?_⟩)
        · simp only [decide_eq_false_iff_not]
          show ¬ (jj.toInt ≤ d.heap_len.toInt)
          omega
        · exact ⟨K, hpc, rfl, hsz', hfr, hK, hK1, hK2, hp, hole_leaf ⟨hk1, hK1⟩ hhole (by omega)⟩
  · rintro ⟨kk', jj, bb⟩ e ⟨K, hpc, he, hsz', hfr, hK, hK1, hK2, hp, hok⟩
    subst he
    simp only at hK
    have hKs : K < hpc.size := by omega
    refine WS.mono (ws_heapSet kk' v (by omega) (by show kk'.toInt < (hpc.size : Int); omega)) ?_
    intro _ e2 he2
    have hkn : kk'.toInt.toNat = K := by omega
    simp only [hkn] at he2
    subst he2
    have hw : (fun i => (hpc.set! K v)[i]!) = wh hpc K v := by
      funext i; simp only [wh, getD_set hpc K i v hKs]
    refine ⟨hpc.set! K v, rfl, by rw [size_set!]; exact hsz', ?_, by rw [hw]; exact hp, by rw [hw]; exact hok⟩
    intro i hi
    rw [getD_set hpc K i v hKs, if_neg (by omega)]; exact hfr i hi

@[simp] theorem tk_arr_heap_len (tk : TK) (d : DeflateState) (a : Int32) : tk.arr { d with heap_len := a } = tk.arr d := by
  cases tk <;> rfl

/-- `pqremove`: the smallest node is returned and the heap, one shorter, has its order again. `Hm H len` is the heap
with its last entry moved to the top, which `pqdownheap` then repairs. -/
def Hm (H : Nat → Int32) (len : Nat) : Nat → Int32 := fun i => if i = 1 then H len else H i

theorem ws_pqremove {h0 : Heap} {id : Nat} (tk : TK) (d : DeflateState) (len : Nat)
    (hlen : d.heap_len.toInt = len) (h2 : 2 ≤ len) (hsz : len < d.heap.size) (hbig : d.heap.size ≤ 1000000)
    (hval : ∀ i, 1 ≤ i → i ≤ len → NV (tk.arr d) d.depth d.heap[i]!)
    (hheap : HeapOK (sm (tk.arr d) d.depth) (fun i => d.heap[i]!) len 0) :
    WS h0 id (pqremove (Sp id) (Ptr.ref (tk.ref id) 0)) d (fun top d' =>
      top = d.heap[1]! ∧ ∃ (hl' : Int32) (hp' : Array Int32), hl'.toInt = (len : Int) - 1 ∧
        d' = { d with heap := hp', heap_len := hl' } ∧ hp'.size = d.heap.size ∧
        (∀ i, ¬ (1 ≤ i ∧ i ≤ len - 1) → hp'[i]! = d.heap[i]!) ∧
        PermOn (fun i => hp'[i]!) (Hm (fun i => d.heap[i]!) len) (len - 1) ∧
        HeapOK (sm (tk.arr d) d.depth) (fun i => hp'[i]!) (len - 1) 0) := by
  have kOK := sm_ok (tk.arr d) d.depth
  unfold pqremove
  refine WS.bind' (ws_heapAt 1 (by decide) (by show (1 : Int) < d.heap.size; omega)) fun top d1 ⟨htop, hd1⟩ => ?_
  subst d1
  refine WS.bind' ws_rd fun l d1 ⟨hl, hd1⟩ => ?_
  subst d1; subst l
  refine WS.bind' (ws_heapAt d.heap_len (by omega) (by omega)) fun v d1 ⟨hv, hd1⟩ => ?_
  subst d1
  refine WS.bind' (ws_isub d.heap_len 1 (by have : (1 : Int32).toInt = 1 := rfl; omega)
    (by have : (1 : Int32).toInt = 1 := rfl; omega)) fun hl' d1 ⟨hhl', hd1⟩ => ?_
  subst d1
  have h1i : (1 : Int32).toInt = 1 := rfl
  refine WS.bind' (ws_md (fun e => { e with heap_len := hl' })) fun _ d1 hd1 => ?_
  subst hd1
  refine WS.bind' (ws_heapSet 1 v (by decide) (by show (1 : Int) < d.heap.size; omega)) fun _ d1 hd1 => ?_
  subst hd1
  have hvi : v = d.heap[len]! := by rw [hv]; congr 1; omega
  have hhl' : hl'.toInt = (len : Int) - 1 := by omega
  have hnode : ∀ i, 1 ≤ i → i ≤ len - 1 → NV (tk.arr d) d.depth
      ({ ({ d with heap_len := hl' } : DeflateState) with heap := d.heap.set! (1 : Int32).toInt.toNat v }).heap[i]! := by
    intro i h1 h3
    show NV (tk.arr d) d.depth (d.heap.set! (1 : Int32).toInt.toNat v)[i]!
    rw [getD_set _ _ _ _ (by rw [h1i]; show 1 < d.heap.size; omega)]
    split
    · rw [hvi]; exact hval len (by omega) (Nat.le_refl _)
    · exact hval i h1 (by omega)
  have e1n : (1 : Int32).toInt.toNat = 1 := rfl
  have hheap2 : HeapOK (sm (tk.arr d) d.depth) (fun i => (d.heap.set! 1 v)[i]!) (len - 1) 1 := by
    intro c h2c hlc hc
    have hs1 : 1 < d.heap.size := by omega
    simp only [getD_set d.heap 1 _ v hs1]
    rw [if_neg (by omega), if_neg (by omega)]
    exact hheap c h2c (by omega) (by omega)
  have key := ws_pqdownheap (h0 := h0) (id := id) tk
    { ({ d with heap_len := hl' } : DeflateState) with heap := d.heap.set! (1 : Int32).toInt.toNat v } 1 1 (len - 1)
    (by rw [h1i]; rfl) (Nat.le_refl _) (by omega) (by show hl'.toInt = _; omega)
    (by show len - 1 < (d.heap.set! _ v).size; rw [size_set!]; omega)
    (by show (d.heap.set! _ v).size ≤ _; rw [size_set!]; omega)
    (fun i h1 h3 => by rw [tk_arr_heap, tk_arr_heap_len]; exact hnode i h1 h3)
    (by rw [tk_arr_heap, tk_arr_heap_len, e1n]; exact hheap2)
  refine WS.bind' key fun _ d1 ⟨hp', hd1, hsz', hfr, hperm, hok⟩ => ?_
  subst hd1
  refine WS.pure' ⟨?_, hl', hp', ?_, rfl, ?_, ?_, ?_, ?_⟩
  · rw [htop, e1n]
  · omega
  · simpa using hsz'
  · intro i hi
    have := hfr i hi
    simp only [e1n, getD_set d.heap 1 i v (by omega : 1 < d.heap.size)] at this
    rw [this, if_neg (by omega)]
  · have hw : (fun i => (d.heap.set! 1 v)[i]!) = Hm (fun i => d.heap[i]!) len := by
      funext i; simp only [Hm]; rw [getD_set d.heap 1 i v (by omega : 1 < d.heap.size), hvi]
    have hperm' : PermOn (fun i => hp'[i]!) (fun i => (d.heap.set! 1 v)[i]!) (len - 1) := hperm
    rw [hw] at hperm'; exact hperm'
  · rw [tk_arr_heap, tk_arr_heap_len] at hok; exact hok

/-! ### Heap-level statements -/

/-- **`pqdownheap`, correct and safe.** Called on the heap `heap[1 .. len]`, `len = heap_len`, with the hole at
`k0 ∈ [1, len]`. Precondition: `len` is the current `heap_len`, the heap array has more than `len` entries (the C
array has `HEAP_SIZE = 573`), the nodes `heap[1..len]` index `tree` and `depth` (in `build_tree` they are below
`2 * elems + 1 ≤ 573`), and the heap order holds for every parent `> k0` (`build_tree` calls it for `k0 = heap_len/2`
down to 1, and for `k0 = 1` after replacing the root). Result: no fault; only `heap[1..len]` changes; the new
heap is a permutation of the old one and the order holds for every parent `> k0 - 1`. `tk` says which tree array
`tree` points to (`dyn_ltree`, `dyn_dtree` or `bl_tree` of the same state). -/
theorem pqdownheap_correct {h : Heap} {id : Nat} {d : DeflateState} (hd : h.dstates id = some d) (tk : TK)
    (kk : Int32) (k0 len : Nat) (hk : kk.toInt = k0) (hk1 : 1 ≤ k0) (hk2 : k0 ≤ len) (hlen : d.heap_len.toInt = len)
    (hsz : len < d.heap.size) (hbig : d.heap.size ≤ 1000000)
    (hval : ∀ i, 1 ≤ i → i ≤ len → NV (tk.arr d) d.depth d.heap[i]!)
    (hheap : HeapOK (sm (tk.arr d) d.depth) (fun i => d.heap[i]!) len k0) :
    ∃ hp', pqdownheap (Sp id) (Ptr.ref (tk.ref id) 0) kk h = .ok ((), setD h id { d with heap := hp' }) ∧
      hp'.size = d.heap.size ∧ (∀ i, ¬ (1 ≤ i ∧ i ≤ len) → hp'[i]! = d.heap[i]!) ∧
      PermOn (fun i => hp'[i]!) (fun i => d.heap[i]!) len ∧
      HeapOK (sm (tk.arr d) d.depth) (fun i => hp'[i]!) len (k0 - 1) := by
  have := ws_pqdownheap (h0 := h) (id := id) tk d kk k0 len hk hk1 hk2 hlen hsz hbig hval hheap
  obtain ⟨_, d', e, hp', rfl, hr⟩ := this
  rw [setD_self hd] at e
  exact ⟨hp', e, hr⟩

/-- **`pqdownheap` does not fault**: the preconditions of `pqdownheap_correct` (hole `k0 ∈ [1, heap_len]`, nodes of
`heap[1..heap_len]` inside `tree` and `depth`, heap order for parents `> k0`) give a run to the end; every index is
inside the arrays. -/
theorem pqdownheap_safe {h : Heap} {id : Nat} {d : DeflateState} (hd : h.dstates id = some d) (tk : TK)
    (kk : Int32) (k0 len : Nat) (hk : kk.toInt = k0) (hk1 : 1 ≤ k0) (hk2 : k0 ≤ len) (hlen : d.heap_len.toInt = len)
    (hsz : len < d.heap.size) (hbig : d.heap.size ≤ 1000000)
    (hval : ∀ i, 1 ≤ i → i ≤ len → NV (tk.arr d) d.depth d.heap[i]!)
    (hheap : HeapOK (sm (tk.arr d) d.depth) (fun i => d.heap[i]!) len k0) :
    ∃ h', pqdownheap (Sp id) (Ptr.ref (tk.ref id) 0) kk h = .ok ((), h') := by
  obtain ⟨hp', e, -⟩ := pqdownheap_correct hd tk kk k0 len hk hk1 hk2 hlen hsz hbig hval hheap
  exact ⟨_, e⟩

/-- **`pqremove`, correct and safe.** Called with `heap_len = len ≥ 2` (the loop of `build_tree` runs while
`heap_len ≥ 2`), the heap order holding everywhere. It returns `heap[1]`, the smallest node, sets `heap_len` to
`len - 1`, and leaves `heap[1 .. len-1]` a heap, a permutation of the old `heap[2..len]`. -/
theorem pqremove_correct {h : Heap} {id : Nat} {d : DeflateState} (hd : h.dstates id = some d) (tk : TK) (len : Nat)
    (hlen : d.heap_len.toInt = len) (h2 : 2 ≤ len) (hsz : len < d.heap.size) (hbig : d.heap.size ≤ 1000000)
    (hval : ∀ i, 1 ≤ i → i ≤ len → NV (tk.arr d) d.depth d.heap[i]!)
    (hheap : HeapOK (sm (tk.arr d) d.depth) (fun i => d.heap[i]!) len 0) :
    ∃ (hl' : Int32) (hp' : Array Int32), hl'.toInt = (len : Int) - 1 ∧
      pqremove (Sp id) (Ptr.ref (tk.ref id) 0) h = .ok (d.heap[1]!, setD h id { d with heap := hp', heap_len := hl' }) ∧
      hp'.size = d.heap.size ∧ (∀ i, ¬ (1 ≤ i ∧ i ≤ len - 1) → hp'[i]! = d.heap[i]!) ∧
      PermOn (fun i => hp'[i]!) (Hm (fun i => d.heap[i]!) len) (len - 1) ∧
      HeapOK (sm (tk.arr d) d.depth) (fun i => hp'[i]!) (len - 1) 0 := by
  have := ws_pqremove (h0 := h) (id := id) tk d len hlen h2 hsz hbig hval hheap
  obtain ⟨top, d', e, htop, hl', hp', hh, rfl, hr⟩ := this
  rw [setD_self hd] at e
  subst htop
  exact ⟨hl', hp', hh, e, hr⟩

/-- **`pqremove` does not fault**: `heap_len ≥ 2`, the nodes of `heap[1..heap_len]` inside `tree` and `depth`, the
heap order everywhere (see `pqremove_correct`). -/
theorem pqremove_safe {h : Heap} {id : Nat} {d : DeflateState} (hd : h.dstates id = some d) (tk : TK) (len : Nat)
    (hlen : d.heap_len.toInt = len) (h2 : 2 ≤ len) (hsz : len < d.heap.size) (hbig : d.heap.size ≤ 1000000)
    (hval : ∀ i, 1 ≤ i → i ≤ len → NV (tk.arr d) d.depth d.heap[i]!)
    (hheap : HeapOK (sm (tk.arr d) d.depth) (fun i => d.heap[i]!) len 0) :
    ∃ (top : Int32) (h' : Heap), pqremove (Sp id) (Ptr.ref (tk.ref id) 0) h = .ok (top, h') := by
  obtain ⟨_, _, _, e, -⟩ := pqremove_correct hd tk len hlen h2 hsz hbig hval hheap
  exact ⟨_, _, e⟩

end Zlib.Trees.Proofs
