import ZlibF.Proof.«gz.read-fetch-specs»

/-!
# gz read side: the read budget across `gz_avail`

With a budget (M7) `gz_avail` raises `avail_in` by the bytes it reads and the budget falls by the same bytes, so
the input left (`inputLeft`) does not rise, and a bounded budget stays bounded.
-/

namespace ZlibF.Spec.Public.GzRead
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib.Spec Zlib.Gzlib.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- **The budget across `gz_avail`**, and its error stays away from `Z_STREAM_END` (it is the old one, `Z_ERRNO` or
`Z_MEM_ERROR`). -/
theorem gz_avail_budget (i : Nat) (h : Heap) (fs : Fs) (s : GzState)
    (hu : GzInvUpToOutput h i s) (hm : s.mode = GZ_READ) (hfs : FileSystem fs) (hsz : s.size ≠ 0)
    {r : Int32} {fs' : Fs} {after : Heap}
    (run : Zlib.Gzread.gz_avail (gzSt i) fs h = .ok ((r, fs'), after)) :
    ∀ s', after.gzstates i = some s' →
      (ReadsFinite fs s.fd → ReadsFinite fs' s.fd ∧ inputLeft fs' s' ≤ inputLeft fs s) ∧
      (ReadsBounded fs s.fd → ReadsBounded fs' s.fd) ∧
      (s.err ≠ Z_STREAM_END → s'.err ≠ Z_STREAM_END) := by
  intro s' hs'
  obtain ⟨-, -, hpost⟩ := gz_avail_safe i h fs s hu hm hfs hsz
  obtain ⟨-, -, -, t, ht, hrec, hbud, hle, herr⟩ := hpost _ _ _ run
  have e : t = s' := Option.some.inj (ht.symm.trans hs')
  subst e
  have hfd : t.fd = s.fd := by rw [hrec]
  have fin : ReadsFinite fs s.fd → ReadsFinite fs' s.fd ∧ ∃ b b', fs.readBudget s.fd.toInt.toNat = some b ∧
      fs'.readBudget s.fd.toInt.toNat = some b' ∧ b' + (t.strm.avail_in.toNat - s.strm.avail_in.toNat) ≤ b := by
    rintro ⟨h0, hne⟩
    obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hne
    obtain ⟨b', hb', hle'⟩ := (hbud h0).2 b hb
    exact ⟨⟨h0, by rw [hb']; simp⟩, b, b', hb, hb', hle'⟩
  refine ⟨fun hf => ?_, fun hb => ?_, fun hne => ?_⟩
  · obtain ⟨hf', b, b', hb, hb', hle'⟩ := fin hf
    refine ⟨hf', ?_⟩
    unfold inputLeft
    rw [hfd, if_pos hf.1, if_pos hf.1, hb, hb']
    simp only [Option.getD_some]
    omega
  · obtain ⟨hf', b, b', hb0, hb', hle'⟩ := fin hb.1
    refine ⟨hf', ?_⟩
    have := hb.2
    rw [hb0] at this
    rw [hb']
    simp only [Option.getD_some] at this ⊢
    omega
  · rcases herr with e | e | e
    · rw [e]; exact hne
    · rw [e]; decide
    · rw [e]; decide

end ZlibF.Spec.Public.GzRead
#print axioms ZlibF.Spec.Public.GzRead.gz_avail_budget
