import ZlibF.Proof.«inffast.c.loop»

namespace Zlib.Inffast.Proofs
open C Zlib.Inffast Zlib.Inffast.Spec
variable {e : Env} {c : Ctx}

/-- The actual fast loop never retracts output. Unless it reaches TYPE or
BAD, its first body emits output and every later body preserves that strict
progress. This is stronger than merely reporting exhausted margins. -/
theorem fast_loop_wp_progress (hc : CtxOK e c) (l : L) (i o : Nat) (A : Array UInt8)
    (hl : LS e l i o) (hA : A.size = e.A0.size) (hb : l.broke = false)
    (hi : i + 6 ≤ e.i0 + e.sm0.avail_in.toNat)
    (ho : o + 258 ≤ e.o0 + e.sm0.avail_out.toNat)
    (hf : ∀ j, (j < e.o0 ∨ o ≤ j) → A[j]? = e.A0[j]?) :
    Wp (cdoWhile (inflate_fast_body c)
      (fun l => do
        if l.broke then pure (false, l)
        else if ← Ptr.lt l.in_ c.last then pure (← Ptr.lt l.out c.end_, l)
        else pure (false, l)) l) (e.heap A e.sm0.msg e.s0.mode)
      (fun l' h' => ∃ i' o' A' msg' m',
        LS e l' i' o' ∧ o' ≤ e.o0 + e.sm0.avail_out.toNat ∧ A'.size = e.A0.size ∧
        h' = e.heap A' msg' m' ∧
        (∀ j, (j < e.o0 ∨ o' ≤ j) → A'[j]? = e.A0[j]?) ∧
        ((m' = e.s0.mode ∧ msg' = e.sm0.msg) ∨ (m' = TYPE ∧ msg' = e.sm0.msg) ∨ m' = BAD) ∧
        (m' ≠ TYPE → m' ≠ BAD → i' + 6 > e.i0 + e.sm0.avail_in.toNat ∨
          o' + 258 > e.o0 + e.sm0.avail_out.toNat) ∧ o ≤ o' ∧
        (m' ≠ TYPE → m' ≠ BAD → o < o')) := by
  let firstOut := o
  let Inv : L → Heap → Prop := fun l h => ∃ i o A,
    LS e l i o ∧ A.size = e.A0.size ∧ h = e.heap A e.sm0.msg e.s0.mode ∧ l.broke = false ∧
    i + 6 ≤ e.i0 + e.sm0.avail_in.toNat ∧ o + 258 ≤ e.o0 + e.sm0.avail_out.toNat ∧
    (∀ j, (j < e.o0 ∨ o ≤ j) → A[j]? = e.A0[j]?) ∧ firstOut ≤ o
  let μ : L → Nat := fun l => match l.out with
    | .null => 0
    | .ref _ k => e.o0 + e.sm0.avail_out.toNat - k
  have hμ : ∀ l i o, LS e l i o → μ l = e.o0 + e.sm0.avail_out.toNat - o := by
    intro l i o hl
    simp only [μ, hl.hout]
  refine Wp.cdoWhile Inv μ _ ?_ ⟨i, o, A, hl, hA, rfl, hb, hi, ho, hf, Nat.le_refl _⟩ ?_
  · intro l h hI
    obtain ⟨i, o, A, hl, hA, rfl, hb, hi, ho, hf, lower⟩ := hI
    have hp : StepPre e c A l i o :=
      ⟨hc, hl, hA, hi, ho, hb, e.inputFrame_of_frame hA hf (by omega) hl.hi0⟩
    obtain ⟨l1, h1, hr, hpost⟩ := inflate_fast_body_step_safe e c A e.sm0.msg e.s0.mode l i o hp
    obtain ⟨B, p, q, hmsgheap, _, htype⟩ := Wp.at_run
      (inflate_fast_body_type_message e c A e.sm0.msg e.s0.mode l i o hp) hr
    obtain ⟨i', o', A', msg', m', hl', hii, hi6, hoo, ho258, hsz, hh, _, hframe, hcont, hbreak⟩ := hpost
    have hAsz : A'.size = e.A0.size := hsz.trans hA
    have hoend : o' ≤ e.o0 + e.sm0.avail_out.toNat := by omega
    have hft : ∀ j, (j < e.o0 ∨ o' ≤ j) → A'[j]? = e.A0[j]? := by
      intro j hj
      rw [hframe j (by have := hl.ho0; omega)]
      exact hf j (by omega)
    have hmq := e.heap_msg_mode_eq (hh.symm.trans hmsgheap)
    have htype' : m' = TYPE → msg' = e.sm0.msg := by
      intro hm
      exact hmq.1.trans (htype (hmq.2.symm.trans hm))
    refine ⟨l1, h1, hr, ?_⟩
    cases hstop : l1.broke with
    | true =>
      refine Or.inl ⟨l1, h1, ?_, i', o', A', msg', m', hl', hoend, hAsz, hh, hft, ?_, ?_, ?_, ?_⟩
      · simp [hstop]
      · rcases hbreak hstop with hm | hm
        · exact Or.inr (Or.inl ⟨hm, htype' hm⟩)
        · exact Or.inr (Or.inr hm)
      · intro hnt hnb
        rcases hbreak hstop with hm | hm
        · exact False.elim (hnt hm)
        · exact False.elim (hnb hm)
      · exact Nat.le_trans lower hoo
      · intro hnt hnb
        rcases hbreak hstop with hm | hm
        · exact False.elim (hnt hm)
        · exact False.elim (hnb hm)
    | false =>
      obtain ⟨hout, hmsg, hmode⟩ := hcont hstop
      have hcnd := fast_cond_live hc A' msg' m' l1 i' o' hl' hAsz hoend hstop
      by_cases hroom : i' + 6 ≤ e.i0 + e.sm0.avail_in.toNat ∧
          o' + 258 ≤ e.o0 + e.sm0.avail_out.toNat
      · refine Or.inr ⟨l1, h1, ?_, ?_, ?_⟩
        · rw [hh]; simpa [hstop, hroom.1, hroom.2] using hcnd
        · exact ⟨i', o', A', hl', hAsz, by rw [hh, hmsg, hmode], hstop, hroom.1, hroom.2, hft, Nat.le_trans lower hoo⟩
        · rw [hμ _ _ _ hl', hμ _ _ _ hl]
          omega
      · refine Or.inl ⟨l1, h1, ?_, i', o', A', msg', m', hl', hoend, hAsz, hh, hft,
          Or.inl ⟨hmode, hmsg⟩, ?_, Nat.le_trans lower hoo, ?_⟩
        · have hcfalse : (decide (i' + 6 ≤ e.i0 + e.sm0.avail_in.toNat) &&
              decide (o' + 258 ≤ e.o0 + e.sm0.avail_out.toNat)) = false := by
            simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
            omega
          rw [hh]
          simpa [hstop, hcfalse] using hcnd
        · intro _ _; omega
        · intro _ _
          exact Nat.lt_of_le_of_lt lower hout
  · rw [hμ _ _ _ hl]
    apply lt_fuel_of
    have := UInt32.toNat_lt e.sm0.avail_out
    have := hl.ho0
    omega

end Zlib.Inffast.Proofs
