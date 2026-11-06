import ZlibF.Proof.Api.GzipRoundtrip

namespace ZlibF.Spec.Api.Proofs
open ZlibF.Spec

private theorem be32_inj (a b : UInt32) (h : be32 a.toNat = be32 b.toNat) : a = b := by
  apply UInt32.toNat_inj.mp
  simp only [be32, List.cons.injEq, and_true] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have h1 := congrArg UInt8.toNat h1
  have h2 := congrArg UInt8.toNat h2
  have h3 := congrArg UInt8.toNat h3
  have h4 := congrArg UInt8.toNat h4
  simp only [UInt8.toNat_ofNat', Nat.mod_mod, Nat.toUInt8] at h1 h2 h3 h4
  have ha : a.toNat < 2 ^ 32 := a.toFin.isLt
  have hb : b.toNat < 2 ^ 32 := b.toFin.isLt
  omega

/-- A completed zlib trace with a nonempty dictionary announces and decodes that dictionary. -/
theorem dict_trace_format {p : DeflParams} {d x : List UInt8} {sd : DeflState}
    (hc : DeflCfg p) (hw : p.wrap = .zlib) (ht : DeflTrace x (DeflState.fresh p) sd)
    (hd : sd.done = true) (hp : sd.precise = true) (hi : sd.input = x)
    (hdy : sd.dict = some d) (hn : d ≠ []) :
    Layer.Decodes .zlib 15 d sd.produced x ∧
      ∀ d', adler32 d' ≠ adler32 d → ¬ Zlib.Decodes d' sd.produced x := by
  have heff : sd.dictEff = d := by simp [DeflState.dictEff, hdy]
  have hz : Layer.Decodes .zlib 15 d sd.produced x := by
    simpa [heff] using zlib_trace_decodes hc hw ht hd hp hi (Or.inl rfl)
  refine ⟨hz, ?_⟩
  intro d' hne hz'
  have hparam : sd.params = p := by simpa [DeflState.fresh] using deflate_trace_params ht
  have hv := deflate_valid p x sd hc ht hd hp
  have hv' : Zlib.Decodes d sd.produced x ∧
      sd.produced.head?.map (·.toNat / 16 + 8) = some p.wbits ∧
      ∃ cmf flg r, sd.produced = cmf :: flg :: r ∧ (flg.toNat / 32 % 2 = 1 ↔ d ≠ []) := by
    simpa [DeflState.Valid, hparam, hw, hi, heff] using hv
  obtain ⟨cmf, flg, rest, hs, hflag⟩ := hv'.2.2
  have hset : flg.toNat / 32 % 2 = 1 := hflag.mpr hn
  obtain ⟨cmf1, flg1, pre1, body1, hs1, _, _, hdict1⟩ := hv'.1
  obtain ⟨cmf2, flg2, pre2, body2, hs2, _, _, hdict2⟩ := hz'
  have he1 := hs1
  rw [hs] at he1
  simp only [List.cons.injEq] at he1
  obtain ⟨rfl, rfl, _⟩ := he1
  have he2 := hs2
  rw [hs] at he2
  simp only [List.cons.injEq] at he2
  obtain ⟨rfl, rfl, _⟩ := he2
  have hpre1 := (hdict1 hset).1
  have hpre2 := (hdict2 hset).1
  rw [hpre1] at hs1
  rw [hpre2] at hs2
  rw [hs1] at hs2
  simp only [List.cons.injEq] at hs2
  have hid := List.append_inj_left hs2.2.2 (by simp [ZlibF.Spec.be32_length])
  exact hne (be32_inj _ _ hid.symm)

private def NeedInvariant (s : InflState) : Prop :=
  s.wrap = .zlib ∧ (s.phase = .needDict → s.seen.length = 6)

private theorem need_dict_step {s s' : InflState} {d : List UInt8} {rc : Int}
    (hd : InflSetDict s d rc s') (hinv : NeedInvariant s) : NeedInvariant s' := by
  obtain ⟨hw, hneed⟩ := hinv
  simp only [InflSetDict, hw] at hd
  split at hd
  · split at hd
    · rcases hd with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp [NeedInvariant]
    · rcases hd with ⟨_, rfl⟩
      exact ⟨hw, hneed⟩
  · rcases hd with ⟨_, rfl⟩
    exact ⟨hw, hneed⟩

private theorem need_inflate_step {s s' : InflState} {c : InflCall} {o : InflOut}
    (hr : InflStep s c o s') (hinv : NeedInvariant s) : NeedInvariant s' := by
  obtain ⟨hw, hneed⟩ := hinv
  by_cases hb : c.badBuf = true
  · rw [(hr.1 hb).2.2.2]
    exact ⟨hw, hneed⟩
  have hbuf : c.badBuf = false := by cases he : c.badBuf <;> simp_all
  have hrun := hr.2 hbuf
  cases hp : s.phase with
  | done | bad | mem | needDict | syncing =>
    simp only [hp] at hrun
    rw [hrun.2.2.2]
    exact ⟨hw, hneed⟩
  | running =>
    simp only [hp] at hrun
    rcases hrun with hrun | hrun
    · rcases hrun with ⟨_, _, hseen, _, _, _, hwrap, _, _, _, _, _, _, _, hrc, hok,
        hbuferr, hend, hbad, hneed', _, _, _, _, _, _, _, _, _, _⟩
      refine ⟨hwrap.trans hw, fun hphase => ?_⟩
      rcases hrc with hrc | hrc | hrc | hrc | hrc
      · have he := (hok hrc).2.2
        rw [he] at hphase; cases hphase
      · have he := hend hrc
        rw [he] at hphase; cases hphase
      · rw [hseen]
        exact (hneed' hrc).2.2.2.1
      · have he := hbad hrc
        rw [he] at hphase; cases hphase
      · have he := (hbuferr hrc).2
        rw [he] at hphase; cases hphase
    · rcases hrun with ⟨_, _, _, _, hphase', _, _, _, _, _, hwrap, _, _, _, _, _, _, _, _, _, _⟩
      refine ⟨hwrap.trans hw, fun he => ?_⟩
      rw [hphase'] at he; cases he

/-- A zlib trace can wait for a dictionary only after reading six bytes. -/
theorem need_dict_seen_length {z d : List UInt8} {s : InflState}
    (ht : InflTrace z d (InflState.fresh .zlib 15) s) (hn : s.phase = .needDict) :
    s.seen.length = 6 := by
  have keep : ∀ {a b : InflState}, InflTrace z d a b → NeedInvariant a → NeedInvariant b := by
    intro a b trace
    induction trace with
    | nil => exact id
    | step _ hm _ ih => intro h; exact ih (need_inflate_step hm.1 h)
    | dict hm _ ih => intro h; exact ih (need_dict_step hm h)
  have initial : NeedInvariant (InflState.fresh .zlib 15) := by simp [NeedInvariant, InflState.fresh]
  exact (keep ht initial).2 hn

/-- The full dictionary round trip in the abstract API and format models. -/
theorem dict_roundtrip : Goal.dict_roundtrip := by
  intro p d x sd hc hw ht hd hp hi hdict hnonempty
  obtain ⟨hdecode, hwrong⟩ := dict_trace_format hc hw ht hd hp hi hdict hnonempty
  refine ⟨hdecode, hwrong, ?_⟩
  intro st d' rc st' htrace hneed hset hneq
  have htrace' : InflTrace sd.produced d (InflStart .zlib 15 d) st := by
    simpa [InflStart] using htrace
  obtain ⟨hwrap, _, _, _, _, _, _, hprefix, _, _⟩ :=
    inflate_trace_fields hdecode (Or.inl rfl) htrace'
  have hlen := need_dict_seen_length htrace hneed
  have hseen : st.seen = sd.produced.take 6 := by
    have he := List.prefix_iff_eq_take.mp hprefix
    simpa [hlen] using he
  have hparam : sd.params = p := by simpa [DeflState.fresh] using deflate_trace_params ht
  have heff : sd.dictEff = d := by simp [DeflState.dictEff, hdict]
  have hv := deflate_valid p x sd hc ht hd hp
  have hv' : Zlib.Decodes d sd.produced x ∧
      sd.produced.head?.map (·.toNat / 16 + 8) = some p.wbits ∧
      ∃ cmf flg r, sd.produced = cmf :: flg :: r ∧ (flg.toNat / 32 % 2 = 1 ↔ d ≠ []) := by
    simpa [DeflState.Valid, hparam, hw, hi, heff] using hv
  obtain ⟨cmf, flg, rest, hs, hflag⟩ := hv'.2.2
  have hflag' : flg.toNat / 32 % 2 = 1 := hflag.mpr hnonempty
  obtain ⟨cmf', flg', pre, body, hs', _, _, hwith⟩ := hv'.1
  have hheads := hs'
  rw [hs] at hheads
  simp only [List.cons.injEq] at hheads
  obtain ⟨rfl, rfl, _⟩ := hheads
  have hpref := (hwith hflag').1
  rw [hpref] at hs'
  have hfirst : st.seen.drop 2 = be32 (adler32 d).toNat := by
    rw [hseen, hs']
    simp [be32]
  have hbad : st.seen.drop 2 ≠ be32 (adler32 d').toNat := by
    rw [hfirst]
    intro he
    exact hneq (be32_inj _ _ he.symm)
  simp [InflSetDict, hwrap, hneed, hbad] at hset
  exact hset.1

#print axioms dict_roundtrip
#print axioms need_dict_seen_length
#print axioms dict_trace_format
end ZlibF.Spec.Api.Proofs
