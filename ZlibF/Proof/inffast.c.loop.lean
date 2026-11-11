import ZlibF.Proof.«inffast.c.message»

/-!
# inffast.c: the complete fast loop

The loop uses the checked actual body theorem. Its measure is remaining
output room, following the earlier output-room proof method. The invariant
is local to the proof and introduces no additional caller contract.
-/

namespace Zlib.Inffast.Proofs
open C Zlib.Inffast Zlib.Inffast.Spec
variable {e : Env} {c : Ctx}

theorem zstream_put_self {h : Heap} {r : ZStreamRef} {z : ZStream}
    (hz : r.get h = some z) : r.put h z = h := by
  cases r with
  | tab i =>
    simp only [ZStreamRef.get] at hz
    simp [ZStreamRef.put, hz, upd_self _ _ _ hz]
  | in_gzstate_strm i =>
    simp only [ZStreamRef.get] at hz
    obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.mp hz
    simp [ZStreamRef.put, hg, upd_self _ _ _ hg]

theorem Env.heap_initial (e : Env) : e.heap e.A0 e.sm0.msg e.s0.mode = e.h0 := by
  unfold Env.heap
  rw [upd_self _ _ _ e.hA0, upd_self _ _ _ e.hs0]
  exact zstream_put_self e.hsm

theorem Env.heap_msg_mode_eq (e : Env) {A B : Array UInt8} {p q : BPtr} {m n : UInt32}
    (hh : e.heap A p m = e.heap B q n) : p = q ∧ m = n := by
  have hz := congrArg (fun h => e.r.get h) hh
  simp only [e.heap_rget, Option.some.injEq] at hz
  have hs := congrArg (fun h => h.istates e.stid) hh
  simp only [e.heap_istates, upd_same, Option.some.injEq] at hs
  exact ⟨congrArg ZStream.msg hz, congrArg InflateState.mode hs⟩

/-- On a running state, the actual loop condition is exactly the two margins. -/
theorem fast_cond_live (hc : CtxOK e c) (A : Array UInt8) (msg : BPtr) (m : UInt32)
    (l : L) (i o : Nat) (hl : LS e l i o) (hA : A.size = e.A0.size)
    (ho : o ≤ e.o0 + e.sm0.avail_out.toNat) (hb : l.broke = false) :
    (do
      if l.broke then pure (false, l)
      else if ← Ptr.lt l.in_ c.last then pure (← Ptr.lt l.out c.end_, l)
      else pure (false, l)) (e.heap A msg m) =
    .ok ((decide (i + 6 ≤ e.i0 + e.sm0.avail_in.toNat) &&
      decide (o + 258 ≤ e.o0 + e.sm0.avail_out.toNat), l), e.heap A msg m) := by
  have hi : OkOn (e.heap A msg m) (Ptr.lt l.in_ c.last)
      (decide (i < e.i0 + e.sm0.avail_in.toNat - 5)) := by
    rw [hl.hin, hc.last]
    exact Ptr.lt_ok (e.heap_bytes_in A msg m)
      (by have := hl.hi1; have := e.hINsz; have := e.inArr_size_of hA; omega)
      (by have := e.hINsz; have := e.inArr_size_of hA; omega)
  have hout : OkOn (e.heap A msg m) (Ptr.lt l.out c.end_)
      (decide (o < e.o0 + e.sm0.avail_out.toNat - 257)) := by
    rw [hl.hout, hc.end_]
    exact Ptr.lt_ok (e.heap_bytes_ob A msg m) (by rw [hA]; have := e.hAsz; omega)
      (by rw [hA]; have := e.hAsz; omega)
  have hei : decide (i < e.i0 + e.sm0.avail_in.toNat - 5) =
      decide (i + 6 ≤ e.i0 + e.sm0.avail_in.toNat) := by
    simp only [decide_eq_decide]; have := e.hai; omega
  have heo : decide (o < e.o0 + e.sm0.avail_out.toNat - 257) =
      decide (o + 258 ≤ e.o0 + e.sm0.avail_out.toNat) := by
    simp only [decide_eq_decide]; have := e.hao; omega
  simp only [hb, Bool.false_eq_true, ite_false]
  rw [bind_ok hi]
  by_cases hi' : i < e.i0 + e.sm0.avail_in.toNat - 5
  · simp only [hi', decide_true, ite_true]
    rw [bind_ok hout, ← hei, ← heo]
    simp [hi']
  · simp only [hi', decide_false, Bool.false_eq_true, ite_false]
    rw [← hei]
    simp [hi']

/-- Every actual loop execution terminates, frames the output, and records
whether a margin or an error/end-of-block stopped it. -/
theorem fast_loop_wp (hc : CtxOK e c) (l : L) (i o : Nat) (A : Array UInt8)
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
          o' + 258 > e.o0 + e.sm0.avail_out.toNat)) := by
  let Inv : L → Heap → Prop := fun l h => ∃ i o A,
    LS e l i o ∧ A.size = e.A0.size ∧ h = e.heap A e.sm0.msg e.s0.mode ∧ l.broke = false ∧
    i + 6 ≤ e.i0 + e.sm0.avail_in.toNat ∧ o + 258 ≤ e.o0 + e.sm0.avail_out.toNat ∧
    (∀ j, (j < e.o0 ∨ o ≤ j) → A[j]? = e.A0[j]?)
  let μ : L → Nat := fun l => match l.out with
    | .null => 0
    | .ref _ k => e.o0 + e.sm0.avail_out.toNat - k
  have hμ : ∀ l i o, LS e l i o → μ l = e.o0 + e.sm0.avail_out.toNat - o := by
    intro l i o hl
    simp only [μ, hl.hout]
  refine Wp.cdoWhile Inv μ _ ?_ ⟨i, o, A, hl, hA, rfl, hb, hi, ho, hf⟩ ?_
  · intro l h hI
    obtain ⟨i, o, A, hl, hA, rfl, hb, hi, ho, hf⟩ := hI
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
      refine Or.inl ⟨l1, h1, ?_, i', o', A', msg', m', hl', hoend, hAsz, hh, hft, ?_, ?_⟩
      · simp [hstop]
      · rcases hbreak hstop with hm | hm
        · exact Or.inr (Or.inl ⟨hm, htype' hm⟩)
        · exact Or.inr (Or.inr hm)
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
        · exact ⟨i', o', A', hl', hAsz, by rw [hh, hmsg, hmode], hstop, hroom.1, hroom.2, hft⟩
        · rw [hμ _ _ _ hl', hμ _ _ _ hl]
          omega
      · refine Or.inl ⟨l1, h1, ?_, i', o', A', msg', m', hl', hoend, hAsz, hh, hft,
          Or.inl ⟨hmode, hmsg⟩, ?_⟩
        · have hcfalse : (decide (i' + 6 ≤ e.i0 + e.sm0.avail_in.toNat) &&
              decide (o' + 258 ≤ e.o0 + e.sm0.avail_out.toNat)) = false := by
            simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
            omega
          rw [hh]
          simpa [hstop, hcfalse] using hcnd
        · intro _ _; omega
  · rw [hμ _ _ _ hl]
    apply lt_fuel_of
    have := UInt32.toNat_lt e.sm0.avail_out
    have := hl.ho0
    omega

end Zlib.Inffast.Proofs
