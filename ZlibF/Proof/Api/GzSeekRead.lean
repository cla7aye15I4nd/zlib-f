import ZlibF.Spec.Api.Goals

/-!
# Seek then read on the gz model

A successful seek of a reader keeps the handle a reader. The position
reported afterwards is the returned one, and the next read starts there.
-/

namespace ZlibF.Spec.Api.Proofs
set_option autoImplicit false

/-- `z_off_t gzseek(gzFile file, z_off_t offset, int whence)` then
`int gzread(gzFile file, voidp buf, unsigned len)`, on the abstract gz model. -/
theorem gz_seek_read : Goal.gz_seek_read := by
  intro h h1 h2 off whence ret n bytes ret2 hmode hpush hn hquirk hseek hret
  unfold GzSeek at hseek
  simp only [hmode, ite_true] at hseek
  obtain ⟨hbad, hgood⟩ := hseek
  by_cases hb : (h.err ≠ Z.ok ∧ h.err ≠ Z.bufError) ∨ (whence ≠ 0 ∧ whence ≠ 1) ∨
      (if whence = 0 then 0 else h.tell) + off < 0 ∨
      (GzMode.read = GzMode.write ∧ (if whence = 0 then 0 else h.tell) + off < h.tell)
  · have := (hbad hb).1
    omega
  · rcases hgood hb with ⟨hneg, _⟩ | ⟨hrt, hm, _, hread⟩
    · omega
    · obtain ⟨hdec, _, hback, hfwd⟩ := hread trivial
      rw [← hrt] at hback hfwd
      have key : h1.pushed = [] ∧ h1.past = false ∧ h1.rpos = ret.toNat := by
        by_cases hc : h.CopyMode ∨ ret < h.tell
        · obtain ⟨a, b, _, d⟩ := hback hc
          exact ⟨a, b, d⟩
        · have hnc : ¬ h.CopyMode := fun x => hc (Or.inl x)
          have hle : h.tell ≤ ret := Int.not_lt.mp (fun x => hc (Or.inr x))
          have hp : h.past = false := by
            rcases hquirk with x | x | x
            · exact x
            · exact absurd x hnc
            · omega
          obtain ⟨a, _, c, d⟩ := hfwd hnc hle
          have ht : h.tell = (h.rpos : Int) := by simp [GzHandle.tell, hp, hpush]
          refine ⟨by simp [c, hpush], by rw [a, hp], ?_⟩
          rw [d, hpush, ht]
          simp
          omega
      obtain ⟨kp, kpast, kr⟩ := key
      have htell : h1.tell = ret := by
        simp [GzHandle.tell, kp, kpast, kr]
        omega
      refine ⟨htell, fun _ hrd => ?_⟩
      have hr := hrd.2 hm
      have hnn : ¬ n > 2 ^ 31 - 1 := by omega
      simp only [hnn, ite_false] at hr
      split at hr
      · rename_i hs
        have hd := hs.2.2
        rw [kr, hdec] at hd
        rw [hr.2.1, hd]
        simp
      · rw [hr.1]
        simp [GzHandle.avail, kp, kr, hdec]
