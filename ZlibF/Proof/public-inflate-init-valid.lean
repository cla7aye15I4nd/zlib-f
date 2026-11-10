import ZlibF.Proof.«public-inflate-init»

/-!
# inflateInit2_ on every accepted window parameter

The original public contract is retained verbatim at each accepted
parameter. Version errors, a null stream and allocation failure remain
included. The false invalid-window cleanup postcondition is not used.
-/

namespace ZlibF.Spec.Public.Proofs.InflateInit
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec
set_option autoImplicit false

/-- `int inflateInit2_(z_streamp strm, int windowBits, const char *version, int stream_size)`.
The existing public contract for every accepted window argument: raw,
zlib, gzip and automatic wrapper selection, including deferred window
selection where accepted. Unlike Goal.inflateInit2_, this theorem explicitly
excludes invalid window arguments. It includes every allocation outcome,
version/size refusal and null-stream refusal, not just successful init. -/
theorem inflate_init2_valid_public (wb : Int32) (wrap : Api.Wrap) (bits : Nat)
    (params : Api.inflWbits wb.toInt = some (wrap, bits)) :
    InflateInitContract (fun p v size => inflateInit2_ p wb v size) wb := by
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
      change reset2Params wb = some (publicWrap wrap, Int32.ofInt bits) at translated
      refine ⟨Z_OK, initOkHeap h r z (publicWrap wrap) (Int32.ofInt bits), ?_, ?_, ?_⟩
      · exact inflateInit2_success hz hf hok hza hzf hn hr translated
      · simp [initOkHeap, reset2Heap_null _ _ (initState r) (by rfl), allocIstHeap, setI]
      · have hnot : h.allocOk h.nalloc ≠ false := by rw [hok]; decide
        simp only [hnot, params]
        exact ⟨trivial, init_any_initial hf hu hz hok hza hzf hn hr params⟩
    · have hfail : h.allocOk h.nalloc = false := by
        cases he : h.allocOk h.nalloc <;> simp_all
      refine ⟨Z_MEM_ERROR, initMemHeap h r z, ?_, ?_, ?_⟩
      · exact inflateInit2_memfail hz hf hok hza hzf hn hr
      · simp [initMemHeap]
      · simp only [hfail, ite_true]
        refine ⟨trivial, ?_⟩
        simp [SameObjects, initMemHeap, preparedStream, initStream]

end ZlibF.Spec.Public.Proofs.InflateInit
