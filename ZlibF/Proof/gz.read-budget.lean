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
    (hnc : s.how ≠ GZ_COPY) {r : Int32} {fs' : Fs} {after : Heap}
    (run : Zlib.Gzread.gz_avail (gzSt i) fs h = .ok ((r, fs'), after)) :
    ∀ s', after.gzstates i = some s' →
      (HasBudget fs s.fd → HasBudget fs' s.fd ∧ inputLeft fs' s' ≤ inputLeft fs s) ∧
      (ReadsFinite fs s.fd → ReadsFinite fs' s.fd) ∧
      (s.err ≠ Z_STREAM_END → s'.err ≠ Z_STREAM_END) := by
  intro s' hs'
  obtain ⟨-, -, hpost⟩ := gz_avail_safe i h fs s hu hm hfs hsz hnc
  obtain ⟨-, -, -, t, ht, hrec, ⟨hbud, hle, herr⟩, -⟩ := hpost _ _ _ run
  have e : t = s' := Option.some.inj (ht.symm.trans hs')
  subst e
  have hfd : t.fd = s.fd := by rw [hrec]
  have fin : HasBudget fs s.fd → HasBudget fs' s.fd ∧ ∃ b b', fs.readBudget s.fd.toInt.toNat = some b ∧
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

/-! ## The rank of a reader, by parts -/

/-- The read budget of a descriptor (0 when negative or unbudgeted), the second term of `fetchRank`. -/
def budOf (fs : Fs) (fd : Int32) : Nat :=
  if 0 ≤ fd.toInt then (fs.readBudget fd.toInt.toNat).getD 0 else 0

open Classical in
/-- The member flag of `fetchRank`. -/
noncomputable def flagF (h : Heap) (s : GzState) : Nat := if s.how = GZIP ∧ ¬ InflateAtHead h s then 2 else 0

/-- The copy flag of `fetchRank`. -/
def flagW (s : GzState) : Nat := if s.how = GZ_COPY then 0 else 2

theorem fetchRank_eq (fs : Fs) (h : Heap) (s : GzState) :
    fetchRank fs h s = 4 * inputLeft fs s + budOf fs s.fd + flagF h s + flagW s := rfl

theorem budOf_acc {fd : Int32} {fs fs' : Fs} {n : Nat} (acc : BudgetAcc fd fs fs' n) (hb : HasBudget fs fd) :
    budOf fs' fd + n ≤ budOf fs fd := by
  obtain ⟨h0, hne⟩ := hb
  obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hne
  obtain ⟨-, k⟩ := acc h0
  obtain ⟨b', hb', hle⟩ := k b hb
  unfold budOf
  rw [if_pos h0, if_pos h0, hb, hb']
  simp only [Option.getD_some]
  omega

theorem flagF_le (h : Heap) (s : GzState) : flagF h s ≤ 2 := by
  unfold flagF; split <;> omega

theorem flagF_ne {h : Heap} {s : GzState} (hg : s.how ≠ GZIP) : flagF h s = 0 := by
  unfold flagF; rw [if_neg (fun hh => hg hh.1)]

theorem flagF_head {h : Heap} {s : GzState} (hd : InflateAtHead h s) : flagF h s = 0 := by
  unfold flagF; rw [if_neg (fun hh => hh.2 hd)]

theorem flagF_gzip {h : Heap} {s : GzState} (hg : s.how = GZIP) (hd : ¬ InflateAtHead h s) : flagF h s = 2 := by
  unfold flagF; rw [if_pos ⟨hg, hd⟩]

theorem flagW_copy {s : GzState} (hc : s.how = GZ_COPY) : flagW s = 0 := by
  unfold flagW; rw [if_pos hc]

theorem flagW_ne {s : GzState} (hc : s.how ≠ GZ_COPY) : flagW s = 2 := by
  unfold flagW; rw [if_neg hc]

theorem flagW_le (s : GzState) : flagW s ≤ 2 := by
  unfold flagW; split <;> omega

theorem flagW_look {s : GzState} (hl : s.how = LOOK) : flagW s = 2 := flagW_ne (by rw [hl]; decide)

theorem flagW_gzip {s : GzState} (hg : s.how = GZIP) : flagW s = 2 := flagW_ne (by rw [hg]; decide)

theorem flagF_look {h : Heap} {s : GzState} (hl : s.how = LOOK) : flagF h s = 0 := flagF_ne (by rw [hl]; decide)

theorem flagF_copy {h : Heap} {s : GzState} (hc : s.how = GZ_COPY) : flagF h s = 0 :=
  flagF_ne (by rw [hc]; decide)

/-- `InflateAtHead` survives a record write that keeps the stream's state pointer. -/
theorem atHead_put {h : Heap} {i : Nat} {s s' : GzState} (hd : InflateAtHead h s)
    (hst : s'.strm.state = s.strm.state) : InflateAtHead (putGz h i s') s' := by
  obtain ⟨k, st, a, b, c, d, e⟩ := hd
  exact ⟨k, st, by rw [hst]; exact a, b, c, d, e⟩

end ZlibF.Spec.Public.GzRead
#print axioms ZlibF.Spec.Public.GzRead.gz_avail_budget
