import ZlibF.Proof.«public-inflate-init-valid»

/-!
# inflateInit2_ on every window parameter

An accepted window argument uses the proof for accepted arguments. An
invalid one allocates the state, fails the reset and frees the state. The
state table may then be longer, with an empty entry. Every object is
unchanged except the prepared stream record.
-/

namespace ZlibF.Spec.Public.Proofs.InflateInit
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec
set_option autoImplicit false

/-- `int inflateInit2_(z_streamp strm, int windowBits, const char *version, int stream_size)`.
Every signed window argument, every allocation outcome, version and size
refusal and null-stream refusal. -/
theorem inflate_init2_public : Goal.inflateInit2_ := by
  intro wb
  cases params : Api.inflWbits wb.toInt with
  | some p =>
    obtain ⟨wrap, bits⟩ := p
    exact inflate_init2_valid_public wb wrap bits params
  | none =>
    refine ⟨?_, ?_, ?_⟩
    · intro h p version head size hv hbad
      cases head with
      | none =>
        rcases hv with ⟨rfl, _⟩ | ⟨b, hb, _⟩
        · exact inflateInit2_version_null p wb size h
        · cases hb
      | some b =>
        obtain ⟨hn, hr⟩ := version_value_read hv
        by_cases hb : b = 49
        · subst b
          have hs : size ≠ 112 := by simpa using hbad
          exact inflateInit2_version_size p wb version size h hn hr hs
        · exact inflateInit2_version_char p wb version size h b hn hr hb
    · intro h version hv
      obtain ⟨hn, hr⟩ := version_value_read hv
      exact inflateInit2_nullstream wb version h hn hr
    · intro h r z version hf hu _ hz ha hv
      obtain ⟨hn, hr⟩ := version_value_read hv
      obtain ⟨hza, hzf⟩ := ha
      by_cases hok : h.allocOk h.nalloc = true
      · have translated := params_equiv wb
        rw [params] at translated
        change reset2Params wb = none at translated
        refine ⟨Z_STREAM_ERROR, initBadHeap h r z, ?_, ?_, ?_⟩
        · exact inflateInit2_badbits hz hf hok hza hzf hn hr translated
        · simp [initBadHeap, freeIst, allocIstHeap]
        · have hnot : h.allocOk h.nalloc ≠ false := by rw [hok]; decide
          simp only [hnot, params]
          refine ⟨trivial, ?_⟩
          have hnb : h.istates h.nextBlk = none :=
            (Heap.not_live.mp (hf h.nextBlk (Nat.le_refl _))).2.2.2.2.2.1
          have hist : ∀ b, (upd h.istates h.nextBlk none).get b = h.istates.get b := by
            intro b
            by_cases hb : b = h.nextBlk
            · subst hb
              simpa using hnb.symm
            · exact upd_ne _ _ _ _ hb
          cases r with
          | tab i =>
            simp only [ZStreamRef.get] at hz
            simp [SameObjectsUpToTableShape, initBadHeap, freeIst, allocIstHeap, ZStreamRef.put, hz,
              initStream2, preparedStream, initStream, upd_upd]
            exact hist
          | in_gzstate_strm i =>
            simp only [ZStreamRef.get] at hz
            obtain ⟨g, hg, hgz⟩ := Option.map_eq_some_iff.mp hz
            subst hgz
            simp [SameObjectsUpToTableShape, initBadHeap, freeIst, allocIstHeap, ZStreamRef.put, hg,
              initStream2, preparedStream, initStream, upd_upd]
            exact hist
      · have hfail : h.allocOk h.nalloc = false := by
          cases he : h.allocOk h.nalloc <;> simp_all
        refine ⟨Z_MEM_ERROR, initMemHeap h r z, ?_, ?_, ?_⟩
        · exact inflateInit2_memfail hz hf hok hza hzf hn hr
        · simp [initMemHeap]
        · simp only [hfail, ite_true]
          refine ⟨trivial, ?_⟩
          simp [SameObjects, initMemHeap, preparedStream, initStream]

end ZlibF.Spec.Public.Proofs.InflateInit
