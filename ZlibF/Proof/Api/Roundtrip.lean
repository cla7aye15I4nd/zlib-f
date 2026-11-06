import ZlibF.Proof.Format.Dictionary
import ZlibF.Proof.Api.DeflateFlush
import ZlibF.Proof.Api.Inflate

namespace ZlibF.Spec.Api.Proofs
open ZlibF.Spec

/-- Configurations accepted by the deflate initializer use at most 15 window bits. -/
theorem deflate_config_window_limit (p : DeflParams) (h : DeflCfg p) : p.wbits ≤ 15 := by
  obtain ⟨level, method, bits, mem, strategy, he⟩ := h
  simp only [deflInit?] at he
  split at he <;> (try simp_all)
  all_goals split at he <;> (try simp_all)
  all_goals split at he <;> (try simp_all)
  all_goals obtain ⟨hc, hp⟩ := he
  all_goals subst p
  all_goals simp_all
  all_goals omega

/-- A completed raw deflate model trace is valid for a full-window raw decoder. -/
theorem raw_trace_decodes {p : DeflParams} {x : List UInt8} {s : DeflState}
    (hc : DeflCfg p) (hw : p.wrap = .raw) (ht : DeflTrace x (DeflState.fresh p) s)
    (hd : s.done = true) (hp : s.precise = true) (hi : s.input = x) :
    Layer.Decodes .raw 15 s.dictEff s.produced x := by
  have hparam : s.params = p := by simpa [DeflState.fresh] using deflate_trace_params ht
  have hv := deflate_valid p x s hc ht hd hp
  have hd : Deflate.Decodes (s.dictEff.drop (s.dictEff.length - 2 ^ p.wbits)) s.produced x := by
    simpa [DeflState.Valid, hparam, hw, hi] using hv
  exact ZlibF.Spec.Proofs.raw_full_window (deflate_config_window_limit p hc) hd

/-- The raw case of the abstract round trip, for every legal compressor window and dictionary.
Implementation refinement and the wrapped cases remain separate. -/
theorem roundtrip_raw {p : DeflParams} {x : List UInt8} {sd : DeflState} {si : InflState}
    (hc : DeflCfg p) (hw : p.wrap = .raw) (ht : DeflTrace x (DeflState.fresh p) sd)
    (hd : sd.done = true) (hp : sd.precise = true) (hi : sd.input = x)
    (hr : InflTrace sd.produced sd.dictEff (InflStart .raw 15 sd.dictEff) si) :
    si.phase ≠ .bad ∧ si.out <+: x ∧ (si.phase = .done → si.out = x ∧ si.seen = sd.produced) := by
  have hcfg : InflCfg .raw 15 := ⟨-15, by decide⟩
  have hwindow : FullWindow .raw 15 sd.produced := rfl
  have h := inflate_decodes .raw 15 sd.dictEff sd.produced x si hcfg
    (raw_trace_decodes hc hw ht hd hp hi) hwindow hr
  exact ⟨h.1, h.2.2.1, h.2.2.2.2⟩

/-- A completed zlib-wrapped trace is valid for a full-window zlib or auto decoder. -/
theorem zlib_trace_decodes {p : DeflParams} {x : List UInt8} {s : DeflState} {w : Wrap}
    (hc : DeflCfg p) (hw : p.wrap = .zlib) (ht : DeflTrace x (DeflState.fresh p) s)
    (hd : s.done = true) (hp : s.precise = true) (hi : s.input = x)
    (hwrap : w = .zlib ∨ w = .auto) :
    Layer.Decodes w 15 s.dictEff s.produced x := by
  have hparam : s.params = p := by simpa [DeflState.fresh] using deflate_trace_params ht
  have hv := deflate_valid p x s hc ht hd hp
  have hv' : Zlib.Decodes s.dictEff s.produced x ∧
      s.produced.head?.map (·.toNat / 16 + 8) = some p.wbits ∧
      ∃ cmf flg r, s.produced = cmf :: flg :: r ∧ (flg.toNat / 32 % 2 = 1 ↔ s.dictEff ≠ []) := by
    simpa [DeflState.Valid, hparam, hw, hi] using hv
  have hf : ZlibFits 15 s.produced := by
    cases hh : s.produced.head? with
    | none => simp [hh] at hv'
    | some c =>
      have he : c.toNat / 16 + 8 = p.wbits := by simpa [hh] using hv'.2.1
      exact Or.inr ⟨c, hh, by rw [he]; exact deflate_config_window_limit p hc⟩
  rcases hwrap with rfl | rfl
  · exact ⟨hv'.1, hf⟩
  · exact Or.inl ⟨hv'.1, hf⟩

/-- The zlib and automatic-detection cases of the abstract round trip. -/
theorem roundtrip_zlib {p : DeflParams} {x : List UInt8} {sd : DeflState} {si : InflState} {w : Wrap}
    (hc : DeflCfg p) (hw : p.wrap = .zlib) (ht : DeflTrace x (DeflState.fresh p) sd)
    (hd : sd.done = true) (hp : sd.precise = true) (hi : sd.input = x)
    (hwrap : w = .zlib ∨ w = .auto)
    (hr : InflTrace sd.produced sd.dictEff (InflStart w 15 sd.dictEff) si) :
    si.phase ≠ .bad ∧ si.out <+: x ∧ (si.phase = .done → si.out = x ∧ si.seen = sd.produced) := by
  have hcfg : InflCfg w 15 := by
    rcases hwrap with rfl | rfl
    · exact ⟨15, by decide⟩
    · exact ⟨47, by decide⟩
  have hwindow : FullWindow w 15 sd.produced := by
    rcases hwrap with rfl | rfl <;> exact Or.inl rfl
  have h := inflate_decodes w 15 sd.dictEff sd.produced x si hcfg
    (zlib_trace_decodes hc hw ht hd hp hi hwrap) hwindow hr
  exact ⟨h.1, h.2.2.1, h.2.2.2.2⟩

/-- With an empty effective dictionary, a zlib trace does not request one in its header. -/
theorem zlib_trace_no_dictionary {p : DeflParams} {x : List UInt8} {sd : DeflState} {w : Wrap}
    (hc : DeflCfg p) (hw : p.wrap = .zlib) (ht : DeflTrace x (DeflState.fresh p) sd)
    (hd : sd.done = true) (hp : sd.precise = true) (hi : sd.input = x) (hn : sd.dictEff = []) :
    ¬ HdrNeedsDict w 15 sd.produced := by
  have hparam : sd.params = p := by simpa [DeflState.fresh] using deflate_trace_params ht
  have hv := deflate_valid p x sd hc ht hd hp
  have hv' : Zlib.Decodes sd.dictEff sd.produced x ∧
      sd.produced.head?.map (·.toNat / 16 + 8) = some p.wbits ∧
      ∃ cmf flg r, sd.produced = cmf :: flg :: r ∧ (flg.toNat / 32 % 2 = 1 ↔ sd.dictEff ≠ []) := by
    simpa [DeflState.Valid, hparam, hw, hi] using hv
  have hflag := hv'.2.2
  rintro ⟨_, cmf, flg, rest, he, _, hset, _⟩
  obtain ⟨cmf', flg', rest', he', hf⟩ := hflag
  rw [he] at he'
  simp only [List.cons.injEq] at he'
  obtain ⟨rfl, rfl, _⟩ := he'
  exact (hf.mp hset) hn

/-- The no-dictionary zlib and auto round trips complete in the model with enough output space. -/
theorem roundtrip_zlib_completes {p : DeflParams} {x : List UInt8} {sd : DeflState}
    {si si' : InflState} {w : Wrap} {c : InflCall} {r : InflRes}
    (hc : DeflCfg p) (hw : p.wrap = .zlib) (ht : DeflTrace x (DeflState.fresh p) sd)
    (hd : sd.done = true) (hp : sd.precise = true) (hi : sd.input = x) (hn : sd.dictEff = [])
    (hwrap : w = .zlib ∨ w = .auto)
    (hr : InflTrace sd.produced [] (InflStart w 15 []) si) (hphase : si.phase = .running)
    (hbuf : c.badBuf = false) (hin : c.inp = sd.produced.drop si.seen.length)
    (hroom : x.length ≤ si.out.length + c.availOut)
    (hflush : c.flush = .noFlush ∨ c.flush = .syncFlush ∨ c.flush = .finish)
    (hm : InflModel si (.inflate c) r si') :
    (r.rc = Z.streamEnd ∧ r.out.produced = x.drop si.out.length) ∨ r.rc = Z.memError := by
  have hcfg : InflCfg w 15 := by
    rcases hwrap with rfl | rfl
    · exact ⟨15, by decide⟩
    · exact ⟨47, by decide⟩
  have hdecode : Layer.Decodes w 15 [] sd.produced x := by
    simpa [hn] using zlib_trace_decodes hc hw ht hd hp hi hwrap
  have hwindow : FullWindow w 15 sd.produced := by
    rcases hwrap with rfl | rfl <;> exact Or.inl rfl
  have hnodict := zlib_trace_no_dictionary (w := w) hc hw ht hd hp hi hn
  rcases inflate_completes w 15 [] sd.produced x si c r si' hcfg hdecode hwindow hnodict
      hr hphase hbuf hin hroom hflush hm with ⟨h1, _, h2⟩ | hmem
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr hmem

/-- The no-dictionary raw round trip completes in the model when output space is sufficient. -/
theorem roundtrip_raw_completes {p : DeflParams} {x : List UInt8} {sd : DeflState} {si si' : InflState}
    {c : InflCall} {r : InflRes}
    (hc : DeflCfg p) (hw : p.wrap = .raw) (ht : DeflTrace x (DeflState.fresh p) sd)
    (hd : sd.done = true) (hp : sd.precise = true) (hi : sd.input = x) (hn : sd.dictEff = [])
    (hr : InflTrace sd.produced [] (InflStart .raw 15 []) si) (hphase : si.phase = .running)
    (hbuf : c.badBuf = false) (hin : c.inp = sd.produced.drop si.seen.length)
    (hroom : x.length ≤ si.out.length + c.availOut)
    (hflush : c.flush = .noFlush ∨ c.flush = .syncFlush ∨ c.flush = .finish)
    (hm : InflModel si (.inflate c) r si') :
    (r.rc = Z.streamEnd ∧ r.out.produced = x.drop si.out.length) ∨ r.rc = Z.memError := by
  have hcfg : InflCfg .raw 15 := ⟨-15, by decide⟩
  have hdecode : Layer.Decodes .raw 15 [] sd.produced x := by
    simpa [hn] using raw_trace_decodes hc hw ht hd hp hi
  have hwindow : FullWindow .raw 15 sd.produced := rfl
  have hnodict : ¬ HdrNeedsDict .raw 15 sd.produced := by simp [HdrNeedsDict]
  rcases inflate_completes .raw 15 [] sd.produced x si c r si' hcfg hdecode hwindow hnodict
      hr hphase hbuf hin hroom hflush hm with ⟨h1, _, h2⟩ | hmem
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr hmem

#print axioms roundtrip_raw
#print axioms roundtrip_raw_completes
#print axioms roundtrip_zlib
#print axioms roundtrip_zlib_completes
end ZlibF.Spec.Api.Proofs
