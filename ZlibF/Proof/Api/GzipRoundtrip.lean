import ZlibF.Proof.Api.Roundtrip

namespace ZlibF.Spec.Api.Proofs
open ZlibF.Spec

private def HeaderInvariant (s : DeflState) : Prop := s.precise = true → s.header.Valid

private theorem header_run {st st' : DeflState} {c : DeflCall} {o : DeflOut}
    (hr : DeflRun st c o st') (hp : HeaderInvariant st) : HeaderInvariant st' := by
  have hh := hr.1.2.2.2.2.2.2.2
  have hprec := hr.2.2.1
  intro h
  have hv := hp (hprec.symm.trans h)
  simpa [DeflState.header, hh] using hv

private theorem header_step {st st' : DeflState} {c : DeflCall} {o : DeflOut}
    (hr : DeflStep st c o st') (hp : HeaderInvariant st) : HeaderInvariant st' := by
  by_cases ht : c.flush = .trees
  · rw [(hr.1 ht).2.2.2]; exact hp
  by_cases hb : c.badBuf = true ∨ (st.finishing = true ∧ c.flush ≠ .finish)
  · rw [(hr.2.1 ht hb).2.2.2]; exact hp
  have hbuf : c.badBuf = false := by cases h : c.badBuf <;> simp_all
  have hnfin : ¬ (st.finishing = true ∧ c.flush ≠ .finish) := fun h => hb (Or.inr h)
  by_cases hz : c.availOut = 0
  · rw [(hr.2.2.1 ht hbuf hnfin hz).2.2.2]; exact hp
  exact header_run (hr.2.2.2 ht hbuf hnfin hz) hp

private theorem header_dict {st st' : DeflState} {d : List UInt8} {rc : Int}
    (hr : DeflSetDict st d rc st') (hp : HeaderInvariant st) : HeaderInvariant st' := by
  cases hw : st.params.wrap with
  | gzip => simp only [DeflSetDict, hw] at hr; rcases hr with ⟨_, rfl⟩; exact hp
  | zlib =>
    simp only [DeflSetDict, hw] at hr
    split at hr <;> rcases hr with ⟨_, rfl⟩ <;> exact hp
  | raw =>
    simp only [DeflSetDict, hw] at hr
    split at hr
    · rcases hr with ⟨_, rfl⟩; exact hp
    · rcases hr with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact hp
      · intro h
        cases h

private theorem header_set {st st' : DeflState} {h : GzHead} {rc : Int}
    (hr : DeflSetHeader st h rc st') (hp : HeaderInvariant st) : HeaderInvariant st' := by
  unfold DeflSetHeader at hr
  split at hr
  · rcases hr with ⟨_, rfl⟩; exact hp
  · rcases hr with ⟨_, hbad, hgood⟩
    by_cases hb : st.started = true ∨ ¬ h.Valid
    · rw [hbad hb]
      intro he
      cases he
    · rw [hgood hb]
      intro _
      simpa [DeflState.header] using (not_or.mp hb).2

/-- A precise deflate model trace has a valid gzip header. -/
theorem deflate_trace_header_valid {X : List UInt8} {p : DeflParams} {st : DeflState}
    (ht : DeflTrace X (DeflState.fresh p) st) (hp : st.precise = true) : st.header.Valid := by
  have preserve : ∀ {a b : DeflState}, DeflTrace X a b → HeaderInvariant a → HeaderInvariant b := by
    intro a b trace
    induction trace with
    | nil => exact id
    | step _ hm _ ih => intro h; exact ih (header_step hm.1 h)
    | dict hm _ ih => intro h; exact ih (header_dict hm h)
    | header hm _ ih => intro h; exact ih (header_set hm h)
  apply preserve ht _ hp
  intro _
  simp [DeflState.fresh, DeflState.header, GzHead.default, GzHead.Valid]

private theorem header_flags (h : GzHead) :
    h.flg.toUInt8.toNat < 32 ∧ (h.flg.toUInt8.toNat / 2 % 2 = 1 ↔ h.hcrc = true) := by
  cases h with
  | mk text time os extra name comment hcrc =>
    cases text <;> cases hcrc <;> cases extra <;> cases name <;> cases comment <;> simp [GzHead.flg]

/-- The concrete header bytes of a valid header form a gzip member recognized by the format grammar. -/
theorem gzip_decode_with_header {p : DeflParams} {h : GzHead} {stream output : List UInt8}
    (hv : h.Valid) (hd : Gzip.DecodesWith (h.bytes p) stream output) :
    Gzip.Decodes stream output := by
  obtain ⟨rest, hs, hprefix⟩ := hd
  obtain ⟨hf, hhcrc⟩ := header_flags h
  refine ⟨h.flg.toUInt8, le32 h.time, (xflOf p).toUInt8, h.os.toUInt8,
    h.extra.getD [], h.name.getD [], h.comment.getD [], rest, hf, ?_, ?_, ?_, ?_, ?_, hprefix⟩
  · exact ZlibF.Spec.le32_length _
  · cases he : h.extra with
    | none => simp
    | some e => simpa [he] using hv.1 e he
  · cases hn : h.name with
    | none => simp
    | some name => simpa [hn] using hv.2.1 name hn
  · cases hc : h.comment with
    | none => simp
    | some comment => simpa [hc] using hv.2.2 comment hc
  · rw [hs]
    simp only [GzHead.bytes, GzHead.core]
    congr 1
    split <;> simp_all

/-- A precise completed gzip trace is a valid gzip stream. -/
theorem gzip_trace_decodes {p : DeflParams} {x : List UInt8} {s : DeflState}
    (hc : DeflCfg p) (hw : p.wrap = .gzip) (ht : DeflTrace x (DeflState.fresh p) s)
    (hd : s.done = true) (hp : s.precise = true) (hi : s.input = x) :
    Gzip.Decodes s.produced x := by
  have hparam : s.params = p := by simpa [DeflState.fresh] using deflate_trace_params ht
  have hv := deflate_valid p x s hc ht hd hp
  have hd' : Gzip.DecodesWith (s.header.bytes p) s.produced x := by
    simpa [DeflState.Valid, hparam, hw, hi] using hv
  exact gzip_decode_with_header (deflate_trace_header_valid ht hp) hd'

private theorem gzip_not_needs_dict {w : Wrap} {stream output : List UInt8}
    (hd : Gzip.Decodes stream output) : ¬ HdrNeedsDict w 15 stream := by
  obtain ⟨rest, hhead⟩ := ZlibF.Spec.gzip_head hd
  rintro ⟨_, cmf, flg, r, hs, hh, _, _⟩
  rw [hs] at hhead
  simp only [List.cons.injEq] at hhead
  have he : cmf = 31 := hhead.1
  rw [he] at hh
  exact (by decide : ¬ ((31 : UInt8).toNat % 16 = 8)) hh.1

/-- The gzip and automatic-detection cases of the abstract round trip. -/
theorem roundtrip_gzip {p : DeflParams} {x : List UInt8} {sd : DeflState} {si : InflState} {w : Wrap}
    (hc : DeflCfg p) (hw : p.wrap = .gzip) (ht : DeflTrace x (DeflState.fresh p) sd)
    (hd : sd.done = true) (hp : sd.precise = true) (hi : sd.input = x)
    (hwrap : w = .gzip ∨ w = .auto)
    (hr : InflTrace sd.produced sd.dictEff (InflStart w 15 sd.dictEff) si) :
    si.phase ≠ .bad ∧ si.out <+: x ∧ (si.phase = .done → si.out = x ∧ si.seen = sd.produced) := by
  have hcfg : InflCfg w 15 := by
    rcases hwrap with rfl | rfl
    · exact ⟨31, by decide⟩
    · exact ⟨47, by decide⟩
  have hwindow : FullWindow w 15 sd.produced := by
    rcases hwrap with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl rfl
  have hdecode : Layer.Decodes w 15 sd.dictEff sd.produced x := by
    have h := gzip_trace_decodes hc hw ht hd hp hi
    rcases hwrap with rfl | rfl
    · exact h
    · exact Or.inr h
  have h := inflate_decodes w 15 sd.dictEff sd.produced x si hcfg hdecode hwindow hr
  exact ⟨h.1, h.2.2.1, h.2.2.2.2⟩

/-- The gzip cases of the no-dictionary model round-trip completion goal. -/
theorem roundtrip_gzip_completes {p : DeflParams} {x : List UInt8} {sd : DeflState}
    {si si' : InflState} {w : Wrap} {c : InflCall} {r : InflRes}
    (hc : DeflCfg p) (hw : p.wrap = .gzip) (ht : DeflTrace x (DeflState.fresh p) sd)
    (hd : sd.done = true) (hp : sd.precise = true) (hi : sd.input = x) (_hn : sd.dictEff = [])
    (hwrap : w = .gzip ∨ w = .auto)
    (hr : InflTrace sd.produced [] (InflStart w 15 []) si) (hphase : si.phase = .running)
    (hbuf : c.badBuf = false) (hin : c.inp = sd.produced.drop si.seen.length)
    (hroom : x.length ≤ si.out.length + c.availOut)
    (hflush : c.flush = .noFlush ∨ c.flush = .syncFlush ∨ c.flush = .finish)
    (hm : InflModel si (.inflate c) r si') :
    (r.rc = Z.streamEnd ∧ r.out.produced = x.drop si.out.length) ∨ r.rc = Z.memError := by
  have hcfg : InflCfg w 15 := by
    rcases hwrap with rfl | rfl
    · exact ⟨31, by decide⟩
    · exact ⟨47, by decide⟩
  have hwindow : FullWindow w 15 sd.produced := by
    rcases hwrap with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl rfl
  have hformat := gzip_trace_decodes hc hw ht hd hp hi
  have hdecode : Layer.Decodes w 15 [] sd.produced x := by
    rcases hwrap with rfl | rfl
    · exact hformat
    · exact Or.inr hformat
  have hnodict := gzip_not_needs_dict (w := w) hformat
  rcases inflate_completes w 15 [] sd.produced x si c r si' hcfg hdecode hwindow hnodict
      hr hphase hbuf hin hroom hflush hm with ⟨h1, _, h2⟩ | hmem
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr hmem

/-- The abstract model round trip for every compatible wrapper and dictionary. -/
theorem roundtrip : Goal.roundtrip := by
  intro p x sd w b si hc hcompat ht hd hp hi hr
  obtain ⟨_, rfl, hwrap⟩ := hcompat
  rcases hwrap with ⟨hw, rfl⟩ | ⟨hw, hwrap⟩ | ⟨hw, hwrap⟩
  · exact roundtrip_raw hc hw ht hd hp hi hr
  · exact roundtrip_zlib hc hw ht hd hp hi hwrap hr
  · exact roundtrip_gzip hc hw ht hd hp hi hwrap hr

/-- The no-dictionary abstract round trip completes with enough output space, or reports allocation failure. -/
theorem roundtrip_completes : Goal.roundtrip_completes := by
  intro p x sd w b si c r si' hc hcompat ht hd hp hi hn hr hphase hbuf hin hroom hflush hm
  obtain ⟨_, rfl, hwrap⟩ := hcompat
  rcases hwrap with ⟨hw, rfl⟩ | ⟨hw, hwrap⟩ | ⟨hw, hwrap⟩
  · exact roundtrip_raw_completes hc hw ht hd hp hi hn hr hphase hbuf hin hroom hflush hm
  · exact roundtrip_zlib_completes hc hw ht hd hp hi hn hwrap hr hphase hbuf hin hroom hflush hm
  · exact roundtrip_gzip_completes hc hw ht hd hp hi hn hwrap hr hphase hbuf hin hroom hflush hm

#print axioms roundtrip
#print axioms roundtrip_completes
#print axioms gzip_decode_with_header
#print axioms deflate_trace_header_valid
end ZlibF.Spec.Api.Proofs
