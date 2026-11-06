import ZlibF.Spec.Api.Examples

/-!
# Deflate model: validity of a completed stream

The proof uses only the existing model relations and format grammar. In particular, replacing a raw
preset dictionary after an empty-input stream is allowed; decoding an empty output does not depend
on the dictionary.
-/

namespace ZlibF.Spec.Api.Proofs
open ZlibF.Spec

private theorem copyBack_length (dict : List UInt8) (dist n : Nat) (h : List UInt8) :
    (copyBack dict dist n h).length = h.length + n := by
  induction n generalizing h with
  | zero => rfl
  | succ n ih => simp [copyBack, ih]; omega

private theorem symbols_empty_dict {L D : List Nat} {dict h out : List UInt8} {inp rest : List Bool}
    (hs : Symbols L D dict h inp rest out) (he : out = []) (dict' : List UInt8) :
    h = [] ∧ Symbols L D dict' [] inp rest [] := by
  induction hs with
  | eob hd => subst he; exact ⟨rfl, .eob hd⟩
  | lit hd hlt hs ih =>
    have hn := (ih he).1
    simp at hn
  | @copy h inp r1 r2 r3 r4 rest s d xl xd out hd h1 h2 hr1 hd2 h3 hr2 hb hs ih =>
    have hn := (ih he).1
    have hl := congrArg List.length hn
    rw [copyBack_length] at hl
    have hbase : 0 < lengthBases.getD (s - 257) 0 :=
      (by decide : ∀ i, i < 29 → 0 < lengthBases.getD i 0) (s - 257) (by omega)
    simp only [List.length_nil] at hl
    omega

private theorem body_empty_dict {dict h out : List UInt8} {bt : Nat} {inp rest : List Bool}
    (hs : Body dict bt h inp rest out) (he : out = []) (dict' : List UInt8) :
    h = [] ∧ Body dict' bt [] inp rest [] := by
  cases hs with
  | stored h1 h2 h3 h4 =>
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp he
    exact ⟨rfl, .stored h1 h2 h3 h4⟩
  | fixed hs =>
    obtain ⟨rfl, hs'⟩ := symbols_empty_dict hs he dict'
    exact ⟨rfl, .fixed hs'⟩
  | dynamic h1 h2 h3 hc h4 ha hl heob hL hD hs =>
    obtain ⟨rfl, hs'⟩ := symbols_empty_dict hs he dict'
    exact ⟨rfl, .dynamic h1 h2 h3 hc h4 ha hl heob hL hD hs'⟩

private theorem blocks_empty_dict {dict h out : List UInt8} {inp rest : List Bool}
    (hs : Blocks dict h inp rest out) (he : out = []) (dict' : List UInt8) :
    h = [] ∧ Blocks dict' [] inp rest [] := by
  induction hs with
  | last h1 h2 hb =>
    obtain ⟨rfl, hb'⟩ := body_empty_dict hb he dict'
    exact ⟨rfl, .last h1 h2 hb'⟩
  | more h1 h2 hb hs ih =>
    obtain ⟨hempty, hs'⟩ := ih he
    obtain ⟨rfl, hb'⟩ := body_empty_dict hb hempty dict'
    exact ⟨rfl, .more h1 h2 hb' hs'⟩

/-- An empty decoded raw stream remains empty after replacing its preset dictionary. -/
theorem deflate_empty_dictionary_independent {dict stream : List UInt8}
    (hs : Deflate.Decodes dict stream []) (dict' : List UInt8) : Deflate.Decodes dict' stream [] := by
  obtain ⟨rest, hblocks, hrest⟩ := hs
  exact ⟨rest, (blocks_empty_dict hblocks rfl dict').2, hrest⟩

private theorem valid_state_eq {st st' : DeflState} {produced input : List UInt8}
    (hp : st'.params = st.params) (hd : st'.dict = st.dict) (hh : st'.hdr = st.hdr)
    (hv : st.Valid produced input) : st'.Valid produced input := by
  simpa only [DeflState.Valid, DeflState.dictEff, DeflState.header, hp, hd, hh] using hv

private theorem run_preserves_complete {st st' : DeflState} {c : DeflCall} {o : DeflOut}
    (hr : DeflRun st c o st')
    (hprev : st.done = true → st.started = true ∧ (st.precise = true → st.Valid st.produced st.input)) :
    st'.done = true → st'.started = true ∧ (st'.precise = true → st'.Valid st'.produced st'.input) := by
  rcases hr with ⟨hf, hp, hpr, hstart, _, _, _, _, _, hend, _, _, _, _, hdone, _, _, hstable,
    _, _, _, _, hstarted, _⟩
  rcases hf with ⟨_, _, hi, ho, _, _, hd, hh⟩
  intro hdone'
  by_cases hd0 : st.done = true
  · have hstarted' := hstarted (hprev hd0).1
    refine ⟨hstarted', fun hprec' => ?_⟩
    have hprec : st.precise = true := hpr.symm.trans hprec'
    have hv := valid_state_eq hp hd hh ((hprev hd0).2 hprec)
    have hn := hstable hd0
    simpa only [hi, ho, hn.1, hn.2, List.take_zero, List.append_nil] using hv
  · have hrc := (hdone.mp hdone').resolve_left hd0
    obtain ⟨_, _, _, _, _, _, hv, _, _⟩ := hend hrc
    refine ⟨(hstart (Or.inr hrc)).1, fun hprec' => ?_⟩
    have hprec : st.precise = true := hpr.symm.trans hprec'
    have hvalid := valid_state_eq hp hd hh (hv hprec)
    simpa only [hi, ho] using hvalid

private theorem step_preserves_complete {st st' : DeflState} {c : DeflCall} {o : DeflOut}
    (hr : DeflStep st c o st')
    (hprev : st.done = true → st.started = true ∧ (st.precise = true → st.Valid st.produced st.input)) :
    st'.done = true → st'.started = true ∧ (st'.precise = true → st'.Valid st'.produced st'.input) := by
  by_cases ht : c.flush = .trees
  · have he := (hr.1 ht).2.2.2
    subst st'; exact hprev
  by_cases hb : c.badBuf = true ∨ (st.finishing = true ∧ c.flush ≠ .finish)
  · have he := (hr.2.1 ht hb).2.2.2
    subst st'; exact hprev
  have hbuf : c.badBuf = false := by cases h : c.badBuf <;> simp_all
  have hnfin : ¬ (st.finishing = true ∧ c.flush ≠ .finish) := fun h => hb (Or.inr h)
  by_cases hz : c.availOut = 0
  · have he := (hr.2.2.1 ht hbuf hnfin hz).2.2.2
    subst st'; exact hprev
  exact run_preserves_complete (hr.2.2.2 ht hbuf hnfin hz) hprev

private theorem dict_preserves_complete {st st' : DeflState} {d : List UInt8} {rc : Int}
    (hr : DeflSetDict st d rc st')
    (hprev : st.done = true → st.started = true ∧ (st.precise = true → st.Valid st.produced st.input)) :
    st'.done = true → st'.started = true ∧ (st'.precise = true → st'.Valid st'.produced st'.input) := by
  cases hw : st.params.wrap with
  | gzip =>
    simp only [DeflSetDict, hw] at hr
    rcases hr with ⟨_, rfl⟩
    exact hprev
  | zlib =>
    simp only [DeflSetDict, hw] at hr
    split at hr
    · rcases hr with ⟨_, rfl⟩
      exact hprev
    · rename_i hn
      rcases hr with ⟨_, rfl⟩
      intro hd
      exact (hn (hprev hd).1).elim
  | raw =>
    simp only [DeflSetDict, hw] at hr
    split at hr
    · rename_i hi
      rcases hr with ⟨_, rfl⟩
      intro hd
      refine ⟨(hprev hd).1, fun hprec => ?_⟩
      have hv := (hprev hd).2 hprec
      have hraw : Deflate.Decodes (st.dictEff.drop (st.dictEff.length - 2 ^ st.params.wbits)) st.produced [] := by
        simpa only [DeflState.Valid, hw, hi] using hv
      have hnew := deflate_empty_dictionary_independent hraw (d.drop (d.length - 2 ^ st.params.wbits))
      simpa only [DeflState.Valid, hw, DeflState.dictEff, Option.getD_some, hi] using hnew
    · rcases hr with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact hprev
      · intro hd
        refine ⟨(hprev hd).1, fun hprec => ?_⟩
        cases hprec

private theorem header_preserves_complete {st st' : DeflState} {h : GzHead} {rc : Int}
    (hr : DeflSetHeader st h rc st')
    (hprev : st.done = true → st.started = true ∧ (st.precise = true → st.Valid st.produced st.input)) :
    st'.done = true → st'.started = true ∧ (st'.precise = true → st'.Valid st'.produced st'.input) := by
  unfold DeflSetHeader at hr
  split at hr
  · rcases hr with ⟨_, rfl⟩
    exact hprev
  · rcases hr with ⟨_, hbad, hgood⟩
    by_cases hb : st.started = true ∨ ¬ h.Valid
    · obtain rfl := hbad hb
      intro hd
      refine ⟨(hprev hd).1, fun hprec => ?_⟩
      cases hprec
    · obtain rfl := hgood hb
      intro hd
      exact (hb (Or.inl (hprev hd).1)).elim

/-- A deflate trace preserves the validity of every precise completed stream and the fact that a
completed stream has started. This includes raw dictionary replacement after an empty-input stream. -/
theorem deflate_trace_completed {X : List UInt8} {st st' : DeflState} (ht : DeflTrace X st st')
    (hprev : st.done = true → st.started = true ∧ (st.precise = true → st.Valid st.produced st.input)) :
    st'.done = true → st'.started = true ∧ (st'.precise = true → st'.Valid st'.produced st'.input) := by
  induction ht with
  | nil => exact hprev
  | step _ hm _ ih => exact ih (step_preserves_complete hm.1 hprev)
  | dict hm _ ih => exact ih (dict_preserves_complete hm hprev)
  | header hm _ ih => exact ih (header_preserves_complete hm hprev)

/-- Every precise completed trace of the deflate model has produced a complete stream of its
configured wrapper for the input it accepted. The parameter and trace domains are exactly those
of `Goal.deflate_valid`. -/
theorem deflate_valid : Goal.deflate_valid := by
  intro p x st _ ht hd hprec
  exact (deflate_trace_completed ht (by simp [DeflState.fresh]) hd).2 hprec

/-- A buffer-error return after the example finished stream cannot clear its historical `started`
flag. This excludes the refusal-and-dictionary counterexample found before the monotonicity clause. -/
theorem deflate_refusal_keeps_started {c : DeflCall} {o : DeflOut} {st' : DeflState}
    (hr : DeflRun dDoneA c o st') (_hbuf : o.rc = Z.bufError) : st'.started = true := by
  rcases hr with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hstarted, _⟩
  exact hstarted rfl

end ZlibF.Spec.Api.Proofs
