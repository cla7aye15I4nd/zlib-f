import ZlibF.Proof.«trees.c.heap.gbre-inner-order»

/-! # Both actual reassignment loops retain sorted leaf lengths -/

namespace Zlib.Trees.Proofs
open C Zlib.Trees Zlib.Trees.Proofs.GB
set_option autoImplicit false

/-- The actual inner scan extends the sorted region until every required
leaf of the current length has been assigned. -/
theorem ws_gbInnerLoop_order {h0 : Heap} {id : Nat} {tk : TK} {e0 : DeflateState} {hm J elems maxc L : Nat}
    {xb : Nat → Nat} {c : Nat → Nat} {opt0 : UInt64} (ctx : RCtx tk e0 hm J elems maxc L c)
    (mc bitsv : Int32) (hmc : mc.toInt = maxc) (b : Nat) (hb1 : 1 ≤ b) (hbL : b ≤ L) (hbv : bitsv.toInt = b)
    (n hc : Nat) (nI hI : Int32) (hnI : nI.toInt = n) (hhI : hI.toInt = hc) (e : DeflateState)
    (hR : ReSt tk e0 hm J maxc L xb c opt0 hc b n e)
    (ordered : ReOrdered (Hn e0) (curL (tk.arr e)) maxc hc) :
    WS h0 id (cwhile (σ := Int32 × Int32) (fun (n, h) => pure (n != 0, (n, h)))
      (gbInner (Sp id) (Ptr.ref (tk.ref id) 0) mc bitsv) (nI, hI)) e (fun r e' =>
      ∃ hc' : Nat, r.2.toInt = (hc' : Int) ∧ r.1.toInt = 0 ∧ ReSt tk e0 hm J maxc L xb c opt0 hc' b 0 e' ∧ ReOrdered (Hn e0) (curL (tk.arr e')) maxc hc') := by
  refine WS.cwhile2 (id := id)
    (fun (st : Int32 × Int32) e' => ∃ n hc : Nat, st.1.toInt = (n : Int) ∧ st.2.toInt = (hc : Int) ∧ ReSt tk e0 hm J maxc L xb c opt0 hc b n e' ∧ ReOrdered (Hn e0) (curL (tk.arr e')) maxc hc)
    (fun (st : Int32 × Int32) _ => st.2.toInt.toNat)
    (fun (st : Int32 × Int32) e' => ∃ hc' : Nat, st.2.toInt = (hc' : Int) ∧ st.1.toInt = 0 ∧ ReSt tk e0 hm J maxc L xb c opt0 hc' b 0 e' ∧ ReOrdered (Hn e0) (curL (tk.arr e')) maxc hc')
    ?_ ⟨n, hc, hnI, hhI, hR, ordered⟩ (by
      have := ctx.hsz; simp only [fuel]
      have := hI.toInt_le
      have e : Int32.maxValue.toInt = 2147483647 := by decide
      omega)
  rintro ⟨n1, h1⟩ e' ⟨n2, hc2, hn2, hh2, hR2, ordered2⟩
  simp only at hn2 hh2
  refine WS.pure' ?_
  by_cases hz : n2 = 0
  · refine Or.inl ⟨?_, hc2, hh2, by show n1.toInt = 0; omega, by subst hz; exact hR2, ordered2⟩
    have : ¬ n1.toInt ≠ 0 := by omega
    have h' := mt (bne_zero_iff n1).mp this
    simpa using h'
  · refine Or.inr ⟨?_, ?_⟩
    · exact (bne_zero_iff n1).mpr (by omega)
    · refine WS.mono (ws_gbInner_order ctx mc bitsv hmc b hb1 hbL hbv n2 hc2 n1 h1 hn2 hh2 (by omega) e' hR2 ordered2) ?_
      rintro r e'' ⟨hc', n', hr1, hr2, hlt, hR', ordered'⟩
      exact ⟨⟨n', hc', hr1, hr2, hR', ordered'⟩, by show r.2.toInt.toNat < h1.toInt.toNat; omega⟩


/-- The outer loop decreases the assigned length and preserves the same
sorted region. It starts from the actual empty scanned tail. -/
theorem ws_gbOuter_order {h0 : Heap} {id : Nat} {tk : TK} {e0 : DeflateState} {hm J elems maxc L : Nat}
    {xb : Nat → Nat} {c : Nat → Nat} {opt0 : UInt64} (ctx : RCtx tk e0 hm J elems maxc L c) (hB : BcIs e0 c)
    (mc ml : Int32) (hmc : mc.toInt = maxc) (hml : ml.toInt = L) (hI : Int32) (hhI : hI.toInt = 573) (e : DeflateState)
    (hR : ReSt tk e0 hm J maxc L xb c opt0 573 L (c L) e) :
    WS h0 id (cfor (σ := Int32 × Int32) (fun (bits, _) => pure (bits != 0))
      (fun (bits, h) => do pure (← isub bits 1, h)) (gbOuter (Sp id) (Ptr.ref (tk.ref id) 0) mc) (ml, hI)) e
      (fun r e' => ∃ hc, ReSt tk e0 hm J maxc L xb c opt0 hc 0 0 e' ∧ ReOrdered (Hn e0) (curL (tk.arr e')) maxc hc) := by
  have hL15 := ctx.L15
  have hL1 := ctx.L1
  have hcL : ∀ x, x ≤ L → c x ≤ 600 := by
    intro x hx
    have h1 := le_rs (F := c) (n := L + 1) (i := x) (by omega)
    have h2 := nLeaves_le ctx.shape
    have h3 := ctx.shape.maxc_lt
    have h4 := ctx.nc; have h5 := ctx.tsz
    rw [ctx.ctot] at h1; omega
  have h1i : (1 : Int32).toInt = 1 := rfl
  have hfuel : ml.toInt.toNat < fuel := by
    have := ml.toInt_le
    have e : Int32.maxValue.toInt = 2147483647 := by decide
    simp only [fuel]; omega
  refine WS.cfor2 (id := id)
    (fun (st : Int32 × Int32) e' => ∃ b hc : Nat, st.1.toInt = (b : Int) ∧ st.2.toInt = (hc : Int) ∧ b ≤ L ∧
      ReSt tk e0 hm J maxc L xb c opt0 hc b (c b) e' ∧ ReOrdered (Hn e0) (curL (tk.arr e')) maxc hc)
    (fun (st : Int32 × Int32) _ => st.1.toInt.toNat)
    (fun (st : Int32 × Int32) e' => ∃ hc, ReSt tk e0 hm J maxc L xb c opt0 hc 0 0 e' ∧ ReOrdered (Hn e0) (curL (tk.arr e')) maxc hc) ?_
    ⟨L, 573, hml, hhI, Nat.le_refl _, hR, ReOrdered.initial _ _ _⟩ hfuel
  rintro ⟨bits, h⟩ e' ⟨b, hc, hb, hh, hbL, hR2, ordered2⟩
  simp only at hb hh
  refine WS.pure' ?_
  by_cases hz : b = 0
  · subst hz
    refine Or.inl ⟨?_, hc, ?_, ordered2⟩
    · have : ¬ bits.toInt ≠ 0 := by omega
      simpa using mt (bne_zero_iff bits).mp this
    · rw [ctx.c0] at hR2; exact hR2
  · refine Or.inr ⟨?_, ?_⟩
    · exact (bne_zero_iff bits).mpr (by omega)
    · -- the body, then the step
      have hbody : WS h0 id (gbOuter (Sp id) (Ptr.ref (tk.ref id) 0) mc (bits, h)) e'
          (fun r e'' => r.1 = bits ∧ ∃ hc' : Nat, r.2.toInt = (hc' : Int) ∧
            ReSt tk e0 hm J maxc L xb c opt0 hc' b 0 e'' ∧ ReOrdered (Hn e0) (curL (tk.arr e'')) maxc hc') := by
        unfold gbOuter
        simp only []
        refine WS.bind' ws_pBlCount fun bc e1 ⟨hbc, he1⟩ => ?_
        subst e1; subst hbc
        obtain ⟨Tc, O, he, hTs, hc1, hc2, hnc, hO, hfc, hout, hsc, hst⟩ := hR2
        subst he
        have hcb := hcL b hbL
        refine WS.bind' (ws_index_blc bits.toInt (by omega) (by rw [mkP2_bl_count, hB.1]; omega)) fun v e1 ⟨hv, he1⟩ => ?_
        subst e1
        have hv' : v = UInt16.ofNat (c b) := by
          rw [hv, mkP2_bl_count, show bits.toInt.toNat = b by omega]; exact hB.2 b (by omega)
        have hu : (u16i v).toInt = (c b : Int) := by
          rw [u16i_toInt, hv', UInt16.toNat_ofNat']; omega
        refine WS.bind' (ws_gbInnerLoop_order ctx mc bits hmc b (by omega) hbL hb (c b) hc (u16i v) h hu hh _
          ⟨Tc, O, rfl, hTs, hc1, hc2, hnc, hO, hfc, hout, hsc, hst⟩ ordered2) fun r e1 ⟨hc', hr2, hr1, hR3, ordered3⟩ => ?_
        obtain ⟨n3, h3⟩ := r
        exact WS.pure' ⟨rfl, hc', hr2, hR3, ordered3⟩
      refine WS.bind' hbody fun r e1 ⟨hr1, hc', hr2, hR3, ordered3⟩ => ?_
      have hr1' : r.1.toInt = bits.toInt := by rw [hr1]
      refine WS.bind' (ws_isub r.1 1 (by omega) (by omega)) fun b2 e2 ⟨hb2, he2⟩ => ?_
      subst e2
      refine WS.pure' ⟨⟨b - 1, hc', by show b2.toInt = ((b - 1 : Nat) : Int); omega, hr2, by omega, ReSt_down (by omega) hbL hR3, ordered3⟩, ?_⟩
      show b2.toInt.toNat < bits.toInt.toNat
      omega

end Zlib.Trees.Proofs
