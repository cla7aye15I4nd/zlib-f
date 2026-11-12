import ZlibF.Proof.«public-uncompress-call»

/-!
# uncompr.c: the decompression loop

From a loop state the `do ... while (err == Z_OK)` loop of `uncompress2_z` returns,
and its last iteration ended the run. Each continuing iteration leaves less
unread source or unfilled room, and the work is below the loop fuel.
-/

namespace ZlibF.Spec.Public.Proofs.Uncompress
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Gzguts Zlib.Inflate.Proofs Zlib.Uncompr
open Zlib.Inflate (inflate)
set_option autoImplicit false

/-- The loop's end: the last call and the state after it. -/
def Ended (e : Env) (i : Nat) (l : UncLoop) (H : Heap) : Prop :=
  ∃ Hp logp input output u zp z sp s, Final e l l.err Hp H logp input output u i zp z sp s

theorem refilled_full_in (z : ZStream) (l : UncLoop) :
    (refilled z l).avail_in = 0 → (refilledLoop z l).len = 0 := by
  intro h
  simp only [refilled, refilledLoop] at h ⊢
  by_cases zi : z.avail_in = 0
  · simp only [zi, ite_true] at h ⊢
    have e0 := (refill_le l.len).2.1 h
    rw [e0]; rfl
  · simp only [zi, ite_false] at h

theorem refilled_full_out (z : ZStream) (l : UncLoop) :
    (refilled z l).avail_out = 0 → (refilledLoop z l).left = 0 := by
  intro h
  simp only [refilled, refilledLoop] at h ⊢
  by_cases zo : z.avail_out = 0
  · simp only [zo, ite_true] at h ⊢
    have e0 := (refill_le l.left).2.1 h
    rw [e0]; rfl
  · simp only [zo, ite_false] at h

theorem measure_refill {e : Env} {l : UncLoop} {H : Heap} {log : DataLog} {i : Nat} {z : ZStream}
    {s : InflateState} (st : SafeState e l H log i z s) :
    measure e (refilledLoop z l) (e.r.put H (refilled z l)) = measure e l H := by
  have hz : e.r.get H = some z := st.good.live.hz
  simp only [measure, ZStreamRef.get_put_same hz, hz]
  have := refilled_avail_in z l
  have := refilled_avail_out z l
  omega

theorem measure_bound {e : Env} {l : UncLoop} {H : Heap} {log : DataLog} {i : Nat} {z : ZStream}
    {s : InflateState} (ok : EnvOK e) (st : SafeState e l H log i z s) : measure e l H < fuel := by
  have hz : e.r.get H = some z := st.good.live.hz
  simp only [measure, hz]
  have := st.inCount
  have := st.outCount
  have := ok.nBound
  have := ok.capBound
  simp only [fuel]
  omega

/-- The loop returns, and its last iteration ended the run. -/
theorem loop_run (facts : DecoderFacts) {e : Env} {l : UncLoop} {H : Heap} {log : DataLog} {i : Nat}
    {z : ZStream} {s : InflateState} (ok : EnvOK e) (st : State e l H log i z s) :
    ∃ l' H', cdoWhile (loopBody (some e.r)) loopCond l H = .ok (l', H') ∧ Ended e i l' H' := by
  refine cdoWhile_decreasing (fun l H => ∃ log z s, State e l H log i z s) (Ended e i) (measure e)
    ?_ ⟨log, z, s, st⟩ (measure_bound ok st.toSafeState)
  rintro l H ⟨log, z, s, st⟩
  have hz : e.r.get H = some z := st.good.live.hz
  have st1 := st.refill ok
  obtain ⟨rc, H', run, more, done⟩ :=
    call_phase facts ok st1 (refilled_full_in z l) (refilled_full_out z l)
  have body : loopBody (some e.r) l H = .ok ({ refilledLoop z l with err := rc }, H') := by
    rw [loopBody_run l hz rfl]
    simp only [bind_app, pure_app]
    rw [show inflate (some e.r) Z_NO_FLUSH (e.r.put H (refilled z l)) = .ok (rc, H') from run]
  refine ⟨_, H', rc == Z_OK, { refilledLoop z l with err := rc }, H', body, rfl, ?_, ?_⟩
  · intro c
    have rcOk : rc = Z_OK := by simpa using c
    obtain ⟨log', z', s', st', lt⟩ := more rcOk
    refine ⟨⟨log', z', s', st'⟩, ?_⟩
    rw [measure_refill st.toSafeState] at lt
    exact lt
  · intro c
    have rcNe : rc ≠ Z_OK := by simpa using c
    obtain ⟨input, output, u, z', s', fin⟩ := done rcNe
    exact ⟨_, _, input, output, u, _, z', _, s', fin⟩

/-- The loop's end without format facts. -/
def SafeEnded (e : Env) (i : Nat) (l : UncLoop) (H : Heap) : Prop :=
  ∃ Hp logp input output u zp z sp s, SafeFinal e l l.err Hp H logp input output u i zp z sp s

/-- The loop returns, and its last iteration ended the run, from the public
`inflate` goal alone. The measure is the unread source plus the unfilled room;
every `Z_OK` call decreases it by the progress clause of `Goal.inflate`. -/
theorem loop_run_safe (call : Goal.inflate) {e : Env} {l : UncLoop} {H : Heap} {log : DataLog} {i : Nat}
    {z : ZStream} {s : InflateState} (ok : EnvOK e) (st : SafeState e l H log i z s) :
    ∃ l' H', cdoWhile (loopBody (some e.r)) loopCond l H = .ok (l', H') ∧ SafeEnded e i l' H' := by
  refine cdoWhile_decreasing (fun l H => ∃ log z s, SafeState e l H log i z s) (SafeEnded e i) (measure e)
    ?_ ⟨log, z, s, st⟩ (measure_bound ok st)
  rintro l H ⟨log, z, s, st⟩
  have hz : e.r.get H = some z := st.good.live.hz
  have st1 := st.refill ok
  obtain ⟨rc, H', run, more, done⟩ :=
    call_phase_safe call ok st1 (refilled_full_in z l) (refilled_full_out z l)
  have body : loopBody (some e.r) l H = .ok ({ refilledLoop z l with err := rc }, H') := by
    rw [loopBody_run l hz rfl]
    simp only [bind_app, pure_app]
    rw [show inflate (some e.r) Z_NO_FLUSH (e.r.put H (refilled z l)) = .ok (rc, H') from run]
  refine ⟨_, H', rc == Z_OK, { refilledLoop z l with err := rc }, H', body, rfl, ?_, ?_⟩
  · intro c
    have rcOk : rc = Z_OK := by simpa using c
    obtain ⟨_, _, _, z', s', -, -, -, st', lt⟩ := more rcOk
    refine ⟨⟨_, z', s', st'⟩, ?_⟩
    rw [measure_refill st] at lt
    exact lt
  · intro c
    have rcNe : rc ≠ Z_OK := by simpa using c
    obtain ⟨input, output, u, z', s', fin⟩ := done rcNe
    exact ⟨_, _, input, output, u, _, z', _, s', fin⟩

end ZlibF.Spec.Public.Proofs.Uncompress
