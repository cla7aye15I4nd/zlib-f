import ZlibF.Proof.Api.DeflateBounds

namespace ZlibF.Spec.Api.Proofs
open ZlibF.Spec

private def FlushInvariant (s : DeflState) : Prop :=
  s.done = true → s.started = true ∧ s.finishing = true ∧
    (s.precise = true → s.params.wrap = .raw → s.dict = none → ∀ pl il,
      s.fullAt = some (pl, il) → Deflate.Decodes [] (s.produced.drop pl) (s.input.drop il))

private theorem flush_run {st st' : DeflState} {c : DeflCall} {o : DeflOut}
    (hr : DeflRun st c o st') (hroom : c.availOut ≠ 0)
    (hfinish : st.done = true → c.flush = .finish) (hp : FlushInvariant st) : FlushInvariant st' := by
  rcases hr with ⟨hf, hparams, hprec, hstart, hrcs, _, _, _, hokfinish, hend, _, _, _, hfullold, hdone, _, hbuf,
    hstable, _, _, _, _, hstarted, _⟩
  rcases hf with ⟨_, _, hi, ho, _, _, hd, _⟩
  intro hdone'
  by_cases hd0 : st.done = true
  · have hs := hstable hd0
    have hfinish' := hfinish hd0
    have hrnot : o.rc ≠ Z.ok := by
      intro he
      have := hokfinish he hfinish'
      rw [hs.2] at this
      simp only [List.length_nil] at this
      exact hroom this.symm
    have hfin : st'.finishing = true := by
      rcases hrcs with he | he | he
      · exact (hrnot he).elim
      · exact (hend he).2.2.2.1
      · exact (hbuf he).2.trans (hp hd0).2.1
    refine ⟨hstarted (hp hd0).1, hfin, fun hpr hw hdict pl il hfull => ?_⟩
    have hold : st'.fullAt = st.fullAt := by
      apply hfullold
      intro hcontra
      have he : Flush.finish = Flush.fullFlush := hfinish'.symm.trans hcontra.2.2
      cases he
    have hprior := (hp hd0).2.2 (hprec.symm.trans hpr) (by simpa [hparams] using hw)
      (by simpa [hd] using hdict) pl il (by simpa [hold] using hfull)
    simpa only [hi, ho, hs.1, hs.2, List.take_zero, List.append_nil] using hprior
  · have hrc := (hdone.mp hdone').resolve_left hd0
    refine ⟨(hstart (Or.inr hrc)).1, (hend hrc).2.2.2.1, fun hpr hw hdict pl il hfull => ?_⟩
    have hold : st'.fullAt = st.fullAt := by
      apply hfullold
      intro hc
      have he : Z.ok = Z.streamEnd := hc.1.symm.trans hrc
      cases he
    have hprior := (hend hrc).2.2.2.2.2.2.2.1 (hprec.symm.trans hpr)
      (by simpa [hparams] using hw) (by simpa [hd] using hdict) pl il (by simpa [hold] using hfull)
    simpa only [hi, ho] using hprior

private theorem flush_step {st st' : DeflState} {c : DeflCall} {o : DeflOut}
    (hr : DeflStep st c o st') (hp : FlushInvariant st) : FlushInvariant st' := by
  by_cases ht : c.flush = .trees
  · have he := (hr.1 ht).2.2.2
    subst st'; exact hp
  by_cases hb : c.badBuf = true ∨ (st.finishing = true ∧ c.flush ≠ .finish)
  · have he := (hr.2.1 ht hb).2.2.2
    subst st'; exact hp
  have hbuf : c.badBuf = false := by cases h : c.badBuf <;> simp_all
  have hnfin : ¬ (st.finishing = true ∧ c.flush ≠ .finish) := fun h => hb (Or.inr h)
  by_cases hz : c.availOut = 0
  · have he := (hr.2.2.1 ht hbuf hnfin hz).2.2.2
    subst st'; exact hp
  have hfinish : st.done = true → c.flush = .finish := by
    intro hd
    by_cases he : c.flush = .finish
    · exact he
    · exact (hnfin ⟨(hp hd).2.1, he⟩).elim
  exact flush_run (hr.2.2.2 ht hbuf hnfin hz) hz hfinish hp

private theorem flush_dict {st st' : DeflState} {d : List UInt8} {rc : Int}
    (hr : DeflSetDict st d rc st') (hp : FlushInvariant st) : FlushInvariant st' := by
  cases hw : st.params.wrap with
  | gzip => simp only [DeflSetDict, hw] at hr; rcases hr with ⟨_, rfl⟩; exact hp
  | zlib =>
    simp only [DeflSetDict, hw] at hr
    split at hr
    · rcases hr with ⟨_, rfl⟩; exact hp
    · rename_i hn
      rcases hr with ⟨_, rfl⟩
      intro hd
      exact (hn (hp hd).1).elim
  | raw =>
    simp only [DeflSetDict, hw] at hr
    split at hr
    · rcases hr with ⟨_, rfl⟩
      intro hd
      refine ⟨(hp hd).1, (hp hd).2.1, ?_⟩
      intro _ _ hdict
      cases hdict
    · rcases hr with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact hp
      · intro hd
        refine ⟨(hp hd).1, (hp hd).2.1, ?_⟩
        intro hprec
        cases hprec

private theorem flush_header {st st' : DeflState} {h : GzHead} {rc : Int}
    (hr : DeflSetHeader st h rc st') (hp : FlushInvariant st) : FlushInvariant st' := by
  unfold DeflSetHeader at hr
  split at hr
  · rcases hr with ⟨_, rfl⟩; exact hp
  · rcases hr with ⟨_, hbad, hgood⟩
    by_cases hb : st.started = true ∨ ¬ h.Valid
    · obtain rfl := hbad hb
      intro hd
      refine ⟨(hp hd).1, (hp hd).2.1, ?_⟩
      intro hprec
      cases hprec
    · obtain rfl := hgood hb
      intro hd
      exact (hb (Or.inl (hp hd).1)).elim

private theorem trace_flush {X : List UInt8} {st st' : DeflState} (ht : DeflTrace X st st')
    (hp : FlushInvariant st) : FlushInvariant st' := by
  induction ht with
  | nil => exact hp
  | step _ hm _ ih => exact ih (flush_step hm.1 hp)
  | dict hm _ ih => exact ih (flush_dict hm hp)
  | header hm _ ih => exact ih (flush_header hm hp)

private theorem params_step {st st' : DeflState} {c : DeflCall} {o : DeflOut}
    (hr : DeflStep st c o st') : st'.params = st.params := by
  by_cases ht : c.flush = .trees
  · rw [(hr.1 ht).2.2.2]
  by_cases hb : c.badBuf = true ∨ (st.finishing = true ∧ c.flush ≠ .finish)
  · rw [(hr.2.1 ht hb).2.2.2]
  have hbuf : c.badBuf = false := by cases h : c.badBuf <;> simp_all
  have hnfin : ¬ (st.finishing = true ∧ c.flush ≠ .finish) := fun h => hb (Or.inr h)
  by_cases hz : c.availOut = 0
  · rw [(hr.2.2.1 ht hbuf hnfin hz).2.2.2]
  exact (hr.2.2.2 ht hbuf hnfin hz).2.1

private theorem params_dict {st st' : DeflState} {d : List UInt8} {rc : Int}
    (hr : DeflSetDict st d rc st') : st'.params = st.params := by
  cases hw : st.params.wrap with
  | gzip => simp only [DeflSetDict, hw] at hr; rcases hr with ⟨_, rfl⟩; rfl
  | zlib =>
    simp only [DeflSetDict, hw] at hr
    split at hr <;> rcases hr with ⟨_, rfl⟩ <;> rfl
  | raw =>
    simp only [DeflSetDict, hw] at hr
    split at hr
    · rcases hr with ⟨_, rfl⟩; rfl
    · rcases hr with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl

private theorem params_header {st st' : DeflState} {h : GzHead} {rc : Int}
    (hr : DeflSetHeader st h rc st') : st'.params = st.params := by
  unfold DeflSetHeader at hr
  split at hr
  · rcases hr with ⟨_, rfl⟩; rfl
  · rcases hr with ⟨_, hbad, hgood⟩
    by_cases hb : st.started = true ∨ ¬ h.Valid
    · rw [hbad hb]
    · rw [hgood hb]

/-- Deflate calls, dictionary updates, and header updates preserve stream parameters. -/
theorem deflate_trace_params {X : List UInt8} {st st' : DeflState} (ht : DeflTrace X st st') :
    st'.params = st.params := by
  induction ht with
  | nil => rfl
  | step _ hm _ ih => exact ih.trans (params_step hm.1)
  | dict hm _ ih => exact ih.trans (params_dict hm)
  | header hm _ ih => exact ih.trans (params_header hm)

/-- The abstract completed raw-stream trace retains the independent full-flush suffix.
Refinement of the translated compressor is a separate obligation. -/
theorem deflate_full_flush_resync : Goal.deflate_full_flush_resync := by
  intro p x s pl il _ hw ht hd hp hdict hfull
  have hparams : s.params = p := by simpa [DeflState.fresh] using deflate_trace_params ht
  exact (trace_flush ht (by simp [FlushInvariant, DeflState.fresh]) hd).2.2 hp
    (by simpa [hparams] using hw) hdict pl il hfull

#print axioms deflate_full_flush_resync
end ZlibF.Spec.Api.Proofs
