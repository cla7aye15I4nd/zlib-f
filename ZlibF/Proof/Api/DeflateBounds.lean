import ZlibF.Proof.Api.Deflate

namespace ZlibF.Spec.Api.Proofs
open ZlibF.Spec

private def BoundInvariant (s : DeflState) : Prop :=
  s.done = true → s.started = true ∧ (s.clean = true → s.produced.length ≤ s.bound s.input.length)

private theorem bound_run {st st' : DeflState} {c : DeflCall} {o : DeflOut}
    (hr : DeflRun st c o st') (hp : BoundInvariant st) : BoundInvariant st' := by
  rcases hr with ⟨hf, hparams, _, hstart, _, _, _, _, _, hend, _, _, _, _, hdone, _, _, hstable,
    _, hclean, _, _, hstarted, _⟩
  rcases hf with ⟨_, _, hi, ho, _, _, hd, hh⟩
  intro hdone'
  by_cases hd0 : st.done = true
  · refine ⟨hstarted (hp hd0).1, fun hc => ?_⟩
    have hb := (hp hd0).2 (hclean hc)
    have he := hstable hd0
    have hbound : st'.bound st'.input.length = st.bound st.input.length := by
      simp only [DeflState.bound, DeflState.header, DeflState.dictEff, hparams, hd, hh, hi,
        he.1, List.take_zero, List.append_nil]
      rfl
    simpa only [ho, he.2, List.append_nil, hbound] using hb
  · have hrc := (hdone.mp hdone').resolve_left hd0
    refine ⟨(hstart (Or.inr hrc)).1, fun hc => ?_⟩
    have hb := (hend hrc).2.2.2.2.2.2.2.2 (hclean hc)
    have hbound : st'.bound st'.input.length = st.bound (st.input ++ c.inp.take o.consumed).length := by
      simp only [DeflState.bound, DeflState.header, DeflState.dictEff, hparams, hd, hh, hi]
      rfl
    simpa only [ho, hbound] using hb

private theorem bound_step {st st' : DeflState} {c : DeflCall} {o : DeflOut}
    (hr : DeflStep st c o st') (hp : BoundInvariant st) : BoundInvariant st' := by
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
  exact bound_run (hr.2.2.2 ht hbuf hnfin hz) hp

private theorem bound_dict {st st' : DeflState} {d : List UInt8} {rc : Int}
    (hr : DeflSetDict st d rc st') (hp : BoundInvariant st) : BoundInvariant st' := by
  cases hw : st.params.wrap with
  | gzip =>
    simp only [DeflSetDict, hw] at hr
    rcases hr with ⟨_, rfl⟩
    exact hp
  | zlib =>
    simp only [DeflSetDict, hw] at hr
    split at hr
    · rcases hr with ⟨_, rfl⟩
      exact hp
    · rename_i hn
      rcases hr with ⟨_, rfl⟩
      intro hd
      exact (hn (hp hd).1).elim
  | raw =>
    simp only [DeflSetDict, hw] at hr
    split at hr
    · rcases hr with ⟨_, rfl⟩
      intro hd
      refine ⟨(hp hd).1, fun hc => ?_⟩
      have hb := (hp hd).2 hc
      simpa only [DeflState.bound, DeflState.header, DeflState.dictEff, hw] using hb
    · rcases hr with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact hp
      · intro hd
        refine ⟨(hp hd).1, fun hc => ?_⟩
        cases hc

private theorem bound_header {st st' : DeflState} {h : GzHead} {rc : Int}
    (hr : DeflSetHeader st h rc st') (hp : BoundInvariant st) : BoundInvariant st' := by
  unfold DeflSetHeader at hr
  split at hr
  · rcases hr with ⟨_, rfl⟩
    exact hp
  · rcases hr with ⟨_, hbad, hgood⟩
    by_cases hb : st.started = true ∨ ¬ h.Valid
    · obtain rfl := hbad hb
      intro hd
      refine ⟨(hp hd).1, fun hc => ?_⟩
      cases hc
    · obtain rfl := hgood hb
      intro hd
      exact (hb (Or.inl (hp hd).1)).elim

private theorem trace_bound {X : List UInt8} {st st' : DeflState} (ht : DeflTrace X st st')
    (hp : BoundInvariant st) : BoundInvariant st' := by
  induction ht with
  | nil => exact hp
  | step _ hm _ ih => exact ih (bound_step hm.1 hp)
  | dict hm _ ih => exact ih (bound_dict hm hp)
  | header hm _ ih => exact ih (bound_header hm hp)

/-- The abstract trace model bounds a clean completed stream. This does not establish the
corresponding refinement for translated C. -/
theorem deflate_bound_adequate : Goal.deflate_bound_adequate := by
  intro p x st _ ht hd hc
  exact (trace_bound ht (by simp [BoundInvariant, DeflState.fresh]) hd).2 hc

private theorem step_input_prefix {x : List UInt8} {st st' : DeflState} {c : DeflCall} {o : DeflOut}
    (hs : DeflStep st c o st') (hin : st.input <+: x) (hc : c.inp <+: x.drop st.input.length) :
    st'.input <+: x := by
  have hframe : st'.input = st.input ++ c.inp.take o.consumed := by
    by_cases ht : c.flush = .trees
    · rcases hs.1 ht with ⟨_, hz, _, rfl⟩
      simp [hz]
    by_cases hb : c.badBuf = true ∨ (st.finishing = true ∧ c.flush ≠ .finish)
    · rcases hs.2.1 ht hb with ⟨_, hz, _, rfl⟩
      simp [hz]
    have hbuf : c.badBuf = false := by cases h : c.badBuf <;> simp_all
    have hnfin : ¬ (st.finishing = true ∧ c.flush ≠ .finish) := fun h => hb (Or.inr h)
    by_cases hz : c.availOut = 0
    · rcases hs.2.2.1 ht hbuf hnfin hz with ⟨_, hn, _, rfl⟩
      simp [hn]
    exact (hs.2.2.2 ht hbuf hnfin hz).1.2.2.1
  rw [hframe]
  have htake : c.inp.take o.consumed <+: x.drop st.input.length :=
    (List.take_prefix _ _).trans hc
  obtain ⟨tail, htail⟩ := hin
  rw [← htail, List.drop_left] at htake
  obtain ⟨tail', htail'⟩ := htake
  refine ⟨tail', ?_⟩
  simp only [htail, htail', List.append_assoc]

private theorem dict_input {s s' : DeflState} {d : List UInt8} {r : Int}
    (hm : DeflSetDict s d r s') : s'.input = s.input := by
  cases hw : s.params.wrap with
  | gzip => simp only [DeflSetDict, hw] at hm; rcases hm with ⟨_, rfl⟩; rfl
  | zlib =>
    simp only [DeflSetDict, hw] at hm
    split at hm <;> rcases hm with ⟨_, rfl⟩ <;> rfl
  | raw =>
    simp only [DeflSetDict, hw] at hm
    split at hm
    · rcases hm with ⟨_, rfl⟩; rfl
    · rcases hm with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl

private theorem header_input {s s' : DeflState} {h : GzHead} {r : Int}
    (hm : DeflSetHeader s h r s') : s'.input = s.input := by
  unfold DeflSetHeader at hm
  split at hm
  · rcases hm with ⟨_, rfl⟩; rfl
  · rcases hm with ⟨_, hb, hg⟩
    by_cases he : s.started = true ∨ ¬ h.Valid
    · rw [hb he]
    · rw [hg he]

private theorem trace_input_prefix {x : List UInt8} {st st' : DeflState} (ht : DeflTrace x st st')
    (hin : st.input <+: x) : st'.input <+: x := by
  induction ht with
  | nil => exact hin
  | step hp hm _ ih => exact ih (step_input_prefix hm.1 hin hp)
  | dict hm _ ih => exact ih (by rw [dict_input hm]; exact hin)
  | header hm _ ih => exact ih (by rw [header_input hm]; exact hin)

/-- A finish call in the abstract model completes when the stated bound fits. -/
theorem deflate_completes : Goal.deflate_completes := by
  intro p x s c r s' _ ht hc hp hfin hd hbuf hflush hin hroom hbound hm
  have hprefix : s.input <+: x := trace_input_prefix ht (by simp [DeflState.fresh])
  have hcat : s.input ++ c.inp = x := by
    rw [hin]
    obtain ⟨tail, htail⟩ := hprefix
    rw [← htail, List.drop_left]
  have hrun : DeflRun s c r.out s' := by
    apply hm.1.2.2.2
    · rw [hflush]; decide
    · exact hbuf
    · rw [hfin]; simp
    · omega
  rcases hrun with ⟨hframe, _, _, _, _, _, _, _, _, hend, _, _, _, _, _, _, _, _, _, _, _, _, _, hlive⟩
  have hr : r.out.rc = Z.streamEnd := by
    apply hlive hflush hc hp hfin hd
    have hlen : s.input.length + c.inp.length = x.length := by
      have he := congrArg List.length hcat
      simpa only [List.length_append] using he
    simpa [hlen] using hbound
  have hend' := hend hr
  refine ⟨?_, hend'.2.2.1, ?_⟩
  · exact hm.2.trans hr
  · rw [hframe.2.2.1, hend'.2.1, List.take_length, hcat]

#print axioms deflate_bound_adequate
#print axioms deflate_completes
end ZlibF.Spec.Api.Proofs
