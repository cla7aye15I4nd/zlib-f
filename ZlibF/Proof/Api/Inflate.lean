import ZlibF.Spec.Api.Goals
import ZlibF.Proof.Format.Api
import ZlibF.Proof.Api.InflateCausality
import ZlibF.Proof.Api.InflateDictionary

/-!
# Inflate model: determined output and regression proofs

These theorems concern the heap-free API model. They do not assert refinement of the
translated implementation.
-/

namespace ZlibF.Spec.Api.Proofs
open ZlibF.Spec

/-- Output from a complete stream is determined among all compatible complete streams. -/
theorem inflate_determined_of_decodes {w : Wrap} {b : Nat} {dict x out : List UInt8}
    (h : Layer.Decodes w b dict x out) : Layer.Determined w b dict x out := by
  intro stream decoded comparable hd
  rcases comparable with ⟨tail, heq⟩ | ⟨tail, heq⟩
  · have hx := Layer.ext h (by simpa only [← heq] using hd)
    simpa only [← hx.2] using (List.prefix_refl out)
  · have hx := Layer.ext hd (by simpa only [← heq] using h)
    simpa only [hx.2] using (List.prefix_refl out)

/-- The empty stored raw stream used by the speculative-output regression is valid. -/
theorem inflate_regression_raw_empty :
    Layer.Decodes .raw 15 [] [1, 0, 0, 255, 255] [] :=
  ⟨_, .last rfl rfl (.stored rfl rfl rfl rfl), by decide⟩

/-- A running OK call cannot invent `a` without consuming input from a fresh raw stream. -/
theorem inflate_no_input_ok_cannot_guess (after : InflState) :
    ¬ InflRunOk (InflStart .raw 15 []) ⟨[], 1, .block, false⟩ ⟨0, [97], Z.ok⟩ after := by
  intro h
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hd, _⟩
  have hp := hd ⟨rfl, rfl⟩ (Or.inl rfl) [] rfl [1, 0, 0, 255, 255] []
    (Or.inl List.nil_prefix) inflate_regression_raw_empty
  simp [InflStart, InflState.fresh] at hp

/-- The window-allocation-failure outcome also cannot invent `a` without consuming input. -/
theorem inflate_no_input_mem_cannot_guess (after : InflState) :
    ¬ InflRunMem (InflStart .raw 15 []) ⟨[], 1, .block, false⟩ ⟨0, [97], Z.memError⟩ after := by
  intro h
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hd, _⟩
  have hp := hd ⟨rfl, rfl⟩ [] rfl [1, 0, 0, 255, 255] []
    (Or.inl List.nil_prefix) inflate_regression_raw_empty
  simp [InflStart, InflState.fresh] at hp

private theorem fullWindow_prefix {w : Wrap} {b : Nat} {part stream : List UInt8}
    (hp : part <+: stream) (hw : FullWindow w b stream) : FullWindow w b part := by
  rcases hp with ⟨tail, rfl⟩
  cases part with
  | nil =>
    cases w with
    | raw => exact hw
    | gzip => exact hw
    | zlib => rcases hw with h | ⟨h, _⟩ <;> simp_all [FullWindow]
    | auto => rcases hw with h | ⟨h, _⟩ <;> simp_all [FullWindow]
  | cons x xs => cases w <;> simpa only [FullWindow, List.cons_append, List.head?_cons] using hw

private theorem needsDict_prefix {w : Wrap} {b : Nat} {part stream : List UInt8}
    (hp : part <+: stream) (hlen : 2 ≤ part.length) (hn : HdrNeedsDict w b stream) :
    HdrNeedsDict w b part := by
  rcases hp with ⟨tail, heq⟩
  cases part with
  | nil => simp at hlen
  | cons a rest =>
    cases rest with
    | nil => simp at hlen
    | cons f rest =>
      rcases hn with ⟨hw, cmf, flg, r, hz, hh, hb, hf⟩
      have hhead : a = cmf ∧ f = flg := by
        rw [← heq] at hz
        simp only [List.cons_append, List.cons.injEq] at hz
        exact ⟨hz.1, hz.2.1⟩
      obtain ⟨rfl, rfl⟩ := hhead
      refine ⟨hw, a, f, rest, rfl, hh, hb, ?_⟩
      simpa only [ZlibFits, ← heq, List.cons_append, List.head?_cons] using hf

private theorem needsDict_decoding_prefix_length {w : Wrap} {b : Nat}
    {d part stream out : List UInt8} (hp : part <+: stream)
    (hn : HdrNeedsDict w b stream) (hd : Layer.Decodes w b d part out) :
    6 ≤ part.length := by
  rcases hn with ⟨hw, cmf, flg, rest, hz, hh, hb, hf⟩
  have hzlib (hd' : Zlib.Decodes d part out) : 6 ≤ part.length := by
    rcases hd' with ⟨cmf', flg', pre, body, hs, hh', h0, h1⟩
    rcases hp with ⟨tail, heq⟩
    rw [hs, hz] at heq
    simp only [List.cons_append, List.cons.injEq] at heq
    obtain ⟨rfl, rfl, _⟩ := heq
    have hpre := (h1 hb).1
    rw [hs, hpre]
    simp [be32]
  rcases hw with rfl | rfl
  · exact hzlib hd.1
  · rcases hd with hd | hd
    · exact hzlib hd.1
    · obtain ⟨tail, hg⟩ := gzip_head hd
      rcases hp with ⟨tail', heq⟩
      rw [hg, hz] at heq
      simp only [List.cons_append, List.cons.injEq] at heq
      have hc : cmf = 31 := heq.1.symm
      rw [hc] at hh
      exact False.elim (absurd hh.1 (by decide))

private theorem dict_step_fields {st after : InflState} {dictionary : List UInt8} {rc : Int}
    (hd : InflSetDict st dictionary rc after) (hp : st.PermitsDictionary dictionary) :
    after.wrap = st.wrap ∧ after.wbits = st.wbits ∧ after.seen = st.seen ∧
      after.out = st.out ∧ after.precise = st.precise ∧ after.validate = st.validate ∧
      after.PermitsDictionary dictionary ∧
      (after.phase = .done → st.phase = .done) ∧
      (after.phase = .bad → st.phase = .bad) ∧
      (after.phase = .syncing → st.phase = .syncing) ∧
      (after.dict = none → after.phase = .running → st.dict = none ∧ st.phase = .running) := by
  cases hw : st.wrap <;> simp only [InflSetDict, hw] at hd
  · rcases hd with ⟨_, ⟨_, rfl⟩ | ⟨_, rfl⟩⟩ <;> simp_all [InflState.PermitsDictionary]
  all_goals
    split at hd
    · split at hd
      · rcases hd with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp_all [InflState.PermitsDictionary]
      · obtain ⟨_, rfl⟩ := hd
        simp_all
    · obtain ⟨_, rfl⟩ := hd
      simp_all

/-- A valid FDICT stream whose preset dictionary and decoded output are both empty. -/
theorem inflate_regression_fdict_empty :
    Layer.Decodes .zlib 15 []
      [120, 32, 0, 0, 0, 1, 1, 0, 0, 255, 255, 0, 0, 0, 1] [] := by
  refine ⟨?_, Or.inr ⟨120, rfl, by decide⟩⟩
  refine ⟨120, 32, [0, 0, 0, 1], _, rfl, by decide, ?_, ?_⟩
  · intro h; exact absurd h (by decide)
  · intro _
    refine ⟨by decide, _, .last rfl rfl (.stored rfl rfl rfl rfl), by decide⟩

/-- Reading only a legal FDICT header cannot justify a data-error result. -/
theorem inflate_fdict_header_cannot_fail (after : InflState) :
    ¬ InflRunOk (InflStart .zlib 15 []) ⟨[120, 32], 10, .block, false⟩
      ⟨2, [], Z.dataError⟩ after := by
  intro h
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hd, _⟩
  have hn := hd ⟨rfl, rfl⟩ rfl (Or.inl rfl) [] (Or.inl (by decide))
  apply hn
  exact Or.inr ⟨[0, 0, 0, 1, 1, 0, 0, 255, 255, 0, 0, 0, 1], [], 15,
    by simpa [InflStart, InflState.fresh] using inflate_regression_fdict_empty⟩

/-- An unknown preset dictionary does not rule out a valid wrapped input prefix.
The empty output is determined for every still-permitted dictionary. -/
theorem inflate_unknown_dictionary_prefix {w : Wrap} {b : Nat}
    {dictionary stream decoded : List UInt8} (hw : w ≠ .raw)
    (hd : Layer.Decodes w b dictionary stream decoded) (n : Nat) :
    (InflState.fresh w b).Consistent (stream.take n) [] ∧
      (InflState.fresh w b).Determined (stream.take n) [] := by
  constructor
  · exact output_evidence_nil (Or.inl hw) hd (stream.take n)
  · intro _ _ _ _ _ _
    exact List.nil_prefix

/-- Priming one low bit of minus one inserts a true bit. -/
theorem inflate_prime_negative_low_bit :
    InflPrime (InflState.fresh .raw 15) 1 (-1) Z.ok
      { InflState.fresh .raw 15 with pre := [true], precise := false } := by
  simp [InflPrime, InflState.fresh]

/-- The earlier false-bit result of priming minus one is rejected. -/
theorem inflate_prime_negative_rejects_false :
    ¬ InflPrime (InflState.fresh .raw 15) 1 (-1) Z.ok
      { InflState.fresh .raw 15 with pre := [false], precise := false } := by
  simp [InflPrime, InflState.fresh]

/-- Every model trace on a valid input preserves its decoding and ends at the exact boundary.
This is a theorem about the API model; implementation refinement is separate. -/
theorem inflate_decodes : Goal.inflate_decodes := by
  intro w b d z o final _ hdecode hwindow htrace
  let Inv (st : InflState) : Prop :=
    st.wrap = w ∧ st.wbits = b ∧ st.Exact ∧ st.PermitsDictionary d ∧
    st.phase ≠ .bad ∧ st.phase ≠ .syncing ∧ st.out <+: o ∧ st.seen <+: z ∧
    (st.phase = .done → st.out = o ∧ st.seen = z) ∧
    (st.dict = none → HdrNeedsDict w b z → st.phase = .running → st.seen.length < 6)
  have keep : ∀ {start stop}, InflTrace z d start stop → Inv start → Inv stop := by
    intro start stop trace
    induction trace with
    | nil => exact id
    | @dict s0 s1 s2 r hm ht ih =>
      intro hi
      apply ih
      obtain ⟨hw, hb, he, hp, hbad, hsync, ho, hz, hdone, hearly⟩ := hi
      obtain ⟨hw', hb', hz', ho', hprec', hval', hp', hdone', hbad', hsync', hearly'⟩ :=
        dict_step_fields hm hp
      refine ⟨hw'.trans hw, hb'.trans hb, ⟨hprec'.trans he.1, hval'.trans he.2⟩,
        hp', fun h => hbad (hbad' h), fun h => hsync (hsync' h), ?_, ?_, ?_, ?_⟩
      · simpa only [ho'] using ho
      · simpa only [hz'] using hz
      · intro h
        simpa only [ho', hz'] using hdone (hdone' h)
      · intro hn hd hr
        obtain ⟨hn', hr'⟩ := hearly' hn hr
        simpa only [hz'] using hearly hn' hd hr'
    | @step s0 s1 s2 c r hinput hm ht ih =>
      intro hi
      apply ih
      obtain ⟨hw, hb, he, hp, hbad, hsync, ho, hz, hdone, hearly⟩ := hi
      have hall : s0.seen ++ c.inp <+: z := by
        obtain ⟨tail, heq⟩ := hinput
        refine ⟨tail, ?_⟩
        rw [List.append_assoc, heq]
        obtain ⟨tail', rfl⟩ := hz
        simp
      have hnew : s0.seen ++ c.inp.take r.out.consumed <+: z := by
        apply List.IsPrefix.trans (l₂ := s0.seen ++ c.inp) _ hall
        refine ⟨c.inp.drop r.out.consumed, ?_⟩
        simp only [List.append_assoc, List.take_append_drop]
      have hdstate : Layer.Decodes s0.wrap s0.wbits d z o := by simpa only [hw, hb] using hdecode
      have hwstate : FullWindow s0.wrap s0.wbits (s0.seen ++ c.inp) :=
        fullWindow_prefix hall (by simpa only [hw, hb] using hwindow)
      obtain ⟨⟨hbuf, hvalidbuf⟩, _⟩ := hm
      cases hbf : c.badBuf with
      | true =>
        have heq := (hbuf hbf).2.2.2
        subst s1
        exact ⟨hw, hb, he, hp, hbad, hsync, ho, hz, hdone, hearly⟩
      | false =>
        have hrun := hvalidbuf hbf
        cases hphase : s0.phase with
        | bad => exact False.elim (hbad hphase)
        | syncing => exact False.elim (hsync hphase)
        | done | mem | needDict =>
          simp only [hphase] at hrun
          have heq := hrun.2.2.2
          subst s1
          exact ⟨hw, hb, he, hp, hbad, hsync, ho, hz, hdone, hearly⟩
        | running =>
          simp only [hphase] at hrun
          rcases hrun with hrun | hrun
          · rcases hrun with ⟨hcons, hprod, hseen, hout, _, _, hwrap, hbits, hdict,
              hprec, hvalidate, _, _, _, hrc, hok, hbuferr, hend, hbaderr, hneed,
              _, hdec, hdata, _, _, _, hneedlive, _, hdetermined, _⟩
            have hp' : s1.PermitsDictionary d := by
              simpa only [InflState.PermitsDictionary, hdict, hwrap] using hp
            refine ⟨hwrap.trans hw, hbits.trans hb, ⟨hprec.trans he.1, hvalidate.trans he.2⟩,
              hp', ?_⟩
            have hforces (hnone : s0.dict = none) (hneeddict : HdrNeedsDict w b z)
                (hlen : 6 ≤ (s0.seen ++ c.inp).length) : r.out.rc = Z.needDict := by
              have hnd : HdrNeedsDict s0.wrap s0.wbits (s0.seen ++ c.inp) := by
                simpa only [hw, hb] using needsDict_prefix hall (by omega) hneeddict
              exact (hneedlive hnone (hearly hnone hneeddict hphase) hlen hnd).1
            have hshort : s1.dict = none → HdrNeedsDict w b z → s1.phase = .running →
                s1.seen.length < 6 := by
              intro hn hnd hr
              have hn0 : s0.dict = none := hdict.symm.trans hn
              by_cases hlen : 6 ≤ (s0.seen ++ c.inp).length
              · have hph := (hneed (hforces hn0 hnd hlen)).1
                rw [hph] at hr
                cases hr
              · have hlen' : (s0.seen ++ c.inp.take r.out.consumed).length ≤
                    (s0.seen ++ c.inp).length := by
                  simp only [List.length_append, List.length_take]
                  omega
                rw [hseen]
                omega
            have hnotbad : r.out.rc ≠ Z.dataError := by
              intro herr
              have hnv := hdata he herr hwstate d hp
              apply hnv
              obtain ⟨tail, heq⟩ := hnew
              exact Or.inr ⟨tail, o, z.length, by simpa only [heq, List.take_length] using hdstate⟩
            have hprogress (hrunrc : r.out.rc = Z.ok ∨ r.out.rc = Z.bufError)
                (hph : s1.phase = .running) :
                s1.phase ≠ .bad ∧ s1.phase ≠ .syncing ∧ s1.out <+: o ∧ s1.seen <+: z ∧
                  (s1.phase = .done → s1.out = o ∧ s1.seen = z) ∧
                  (s1.dict = none → HdrNeedsDict w b z → s1.phase = .running → s1.seen.length < 6) := by
              refine ⟨by simp [hph], by simp [hph], ?_, ?_, ?_, hshort⟩
              · rw [hout]
                exact hdetermined he hrunrc d hp z o (Or.inl hnew) hdstate
              · simpa only [hseen] using hnew
              · intro h; rw [hph] at h; cases h
            rcases hrc with hrc | hrc | hrc | hrc | hrc
            · exact hprogress (Or.inl hrc) (hok hrc).2.2
            · have hdecode' := hdec he hrc
              have hdeceff : Layer.Decodes s0.wrap s0.wbits s0.dictEff z o := by
                by_cases heff : s0.dictEff = d
                · simpa only [heff] using hdstate
                · have hnone : s0.dict = none := by
                    cases hdict0 : s0.dict with
                    | none => rfl
                    | some known =>
                      have hk : d = known := by simpa only [InflState.PermitsDictionary, hdict0] using hp
                      exact False.elim (heff (by simp [InflState.dictEff, hdict0, hk]))
                  have hnraw : s0.wrap ≠ .raw := by
                    intro hr
                    have hk : d = [] := (by
                      simpa only [InflState.PermitsDictionary, hnone, hr, ne_eq, not_true_eq_false, false_or] using hp)
                    exact heff (by simp [InflState.dictEff, hnone, hk])
                  have hn : ¬ HdrNeedsDict w b z := by
                    intro hnd
                    have hlen := needsDict_decoding_prefix_length hnew hnd
                      (by simpa only [hw, hb] using hdecode')
                    have halllen : 6 ≤ (s0.seen ++ c.inp).length := by
                      simp only [List.length_append, List.length_take] at hlen ⊢
                      omega
                    have hc : Z.streamEnd = Z.needDict := hrc.symm.trans (hforces hnone hnd halllen)
                    exact absurd hc (by decide)
                  exact layer_decodes_dictionary_irrelevant hnraw (by simpa only [hw, hb] using hn) hdstate
              have hnewcopy := hnew
              obtain ⟨tail, heq⟩ := hnewcopy
              have hsame := Layer.ext hdecode' (by simpa only [← heq] using hdeceff)
              have hsfull : s0.seen ++ c.inp.take r.out.consumed = z := by simpa only [hsame.1, List.append_nil] using heq
              have hph := hend hrc
              refine ⟨by simp [hph], by simp [hph], ?_, ?_, ?_, hshort⟩
              · rw [hout, hsame.2]
                exact List.prefix_refl _
              · simpa only [hseen] using hnew
              · intro _
                exact ⟨hout.trans hsame.2, hseen.trans hsfull⟩
            · have hph := (hneed hrc).1
              have hnil := (hneed hrc).2.1
              refine ⟨by simp [hph], by simp [hph], ?_, ?_, ?_, hshort⟩
              · simpa only [hout, hnil, List.append_nil] using ho
              · simpa only [hseen] using hnew
              · intro h; rw [hph] at h; cases h
            · exact False.elim (hnotbad hrc)
            · exact hprogress (Or.inr hrc) (hbuferr hrc).2
          · rcases hrun with ⟨_, _, _, _, hphase', hseen, hout, _, _, _, hwrap, hbits,
              hdict, hprec, hvalidate, _, _, _, _, hdetermined, _⟩
            have hp' : s1.PermitsDictionary d := by
              simpa only [InflState.PermitsDictionary, hdict, hwrap] using hp
            refine ⟨hwrap.trans hw, hbits.trans hb, ⟨hprec.trans he.1, hvalidate.trans he.2⟩,
              hp', by simp [hphase'], by simp [hphase'], ?_, ?_, ?_, ?_⟩
            · rw [hout]
              exact hdetermined he d hp z o (Or.inl hnew) hdstate
            · simpa only [hseen] using hnew
            · intro h; rw [hphase'] at h; cases h
            · intro _ _ h; rw [hphase'] at h; cases h
  have initial : Inv (InflStart w b d) := by
    cases hw : w <;> simp [Inv, InflStart, InflState.fresh, InflState.Exact,
      InflState.PermitsDictionary, hw]
  have h := keep htrace initial
  exact ⟨h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1⟩

end ZlibF.Spec.Api.Proofs
