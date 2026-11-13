import ZlibF.Proof.«public-gz-offset»

namespace ZlibF.Spec.Public.GzRewindProof
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib Zlib.Gzlib.Spec Zlib.Gzlib.Proofs ZlibF.Spec.Public.OffsetProof

private theorem gzrewind_null (fs : Fs) (h : Heap) : gzrewind none fs h = .ok ((-1, fs), h) := rfl

theorem gz_reset_record {h : Heap} {i : Nat} {s : GzState}
    (hs : h.gzstates i = some s)
    (hmsg : s.msg = .null ∨ ∃ b a, s.msg = .ref (.blk b) 0 ∧ h.bytes b = some a ∧ h.ro b = false)
    (hmem : s.err = Z_MEM_ERROR → s.msg = .null) :
    gz_reset (some (.tab i)) h = .ok ((), setS (freeStr h s.msg) i (resetRec s)) := by
  unfold gz_reset
  rcases hmsg with hn | ⟨mb,a,hm,ha,hro⟩
  · by_cases hmo : s.mode = GZ_READ <;> gsimp [hs, hn, hmo, gz_error, resetRec]
  · have hne : s.err ≠ Z_MEM_ERROR := fun he => by
      have hnull := hmem he
      rw [hm] at hnull
      cases hnull
    by_cases hmo : s.mode = GZ_READ <;>
      gsimp [hs, hm, hne, hmo, freeB_blk_setS ha hro, gz_error, resetRec]

/-- `int gzrewind(gzFile file)` gives the exact seek result and resets only on
success. It requires no invariant on inactive data buffers. -/
theorem gzrewind_record {h : Heap} {i : Nat} {s : GzState}
    (hs : h.gzstates i = some s)
    (hmsg : s.msg = .null ∨ ∃ b a, s.msg = .ref (.blk b) 0 ∧ h.bytes b = some a ∧ h.ro b = false)
    (hmem : s.err = Z_MEM_ERROR → s.msg = .null) (fs : Fs) :
    gzrewind (hnd i) fs h =
      if s.mode ≠ GZ_READ ∨ (s.err ≠ Z_OK ∧ s.err ≠ Z_BUF_ERROR) then .ok ((-1, fs), h)
      else if (lseekRes s.fd s.start SEEK_SET fs).1 = -1 then .ok ((-1, (lseekRes s.fd s.start SEEK_SET fs).2), h)
      else .ok ((0, (lseekRes s.fd s.start SEEK_SET fs).2), setS (freeStr h s.msg) i (resetRec s)) := by
  unfold gzrewind
  by_cases hc : s.mode ≠ GZ_READ ∨ (s.err ≠ Z_OK ∧ s.err ≠ Z_BUF_ERROR)
  · offsetsimp [hs, hc]
  · by_cases hl : (lseekRes s.fd s.start SEEK_SET fs).1 = -1
    · offsetsimp [hs, hc, hl]
    · offsetsimp [hs, hc, hl, gz_reset_record hs hmsg hmem]

theorem lseek_set_success_reg (fd : Int32) (off : Int64) (fs : Fs)
    (hok : (lseekResReg fd off SEEK_SET fs).1 ≠ -1) :
    ∃ file, (lseekResReg fd off SEEK_SET fs).2.fds[fd.toInt.toNat]? = some (some file) ∧
      file.pos = off.toInt.toNat := by
  by_cases hn : fd < 0
  · simp [lseekResReg, fsLseekReg, hn, pure_app] at hok
  · by_cases hi : fd.toInt ≥ (fs.fds.size : Int)
    · simp [lseekResReg, fsLseekReg, hn, hi, pure_app] at hok
    · have hidx : fd.toInt.toNat < fs.fds.size := by
        have hnonneg : ¬ fd.toInt < 0 := fun he => hn (Int32.lt_iff_toInt_lt.mpr (by simpa using he))
        omega
      change fd.toNatClampNeg < fs.fds.size at hidx
      have hget : fs.fds[fd.toNatClampNeg]! = fs.fds[fd.toNatClampNeg] := getElem!_pos fs.fds fd.toNatClampNeg hidx
      cases hf : fs.fds[fd.toNatClampNeg] with
      | none => simp [lseekResReg, fsLseekReg, hn, hi, hget, hf, pure_app] at hok
      | some f =>
        by_cases hneg : off.toInt < 0
        · simp [lseekResReg, fsLseekReg, hn, hi, hget, hf, SEEK_SET, hneg, pure_app] at hok
        · have hup : ¬ 9223372036854775807 < off.toInt := by have := off.toInt_lt; omega
          refine ⟨{ f with pos := off.toInt.toNat }, ?_, rfl⟩
          simp [lseekResReg, fsLseekReg, hn, hi, hget, hf, SEEK_SET, hneg, hup, pure_app,
            Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, hidx]

/-- On the regular instance, a successful `lseek(fd, off, SEEK_SET)` leaves the descriptor at `off`. -/
theorem lseek_set_success (fd : Int32) (off : Int64) (fs : Fs)
    (hc : fs.lseekChoice fs.nos = .regular) (he : fs.okErrno fs.nos = none)
    (hok : (lseekRes fd off SEEK_SET fs).1 ≠ -1) :
    ∃ file, (lseekRes fd off SEEK_SET fs).2.fds[fd.toInt.toNat]? = some (some file) ∧
      file.pos = off.toInt.toNat := by
  rw [lseekRes_regular hc he] at hok ⊢
  exact lseek_set_success_reg fd off (tickW fs) hok



/-- `int gzrewind(gzFile file)`
The exact public result, state, frame and ownership contract. -/
theorem rewind_public : Goal.gzrewind := by
  constructor
  · intro h fs
    exact gzrewind_null fs h
  · intro h fs i s hreach hv hro
    have hreg := hro.1 fs.nos (Nat.le_refl _)
    have hs := hv.1
    have hmsg : s.msg = .null ∨ ∃ b a, s.msg = .ref (.blk b) 0 ∧ h.bytes b = some a ∧ h.ro b = false := by
      rcases hv.2.2.2.2.2.2.1 with hn | ⟨msg,hc,b,a,hp,ha,hro,hsize⟩
      · exact Or.inl hn
      · exact Or.inr ⟨b,a,hp,ha,hro⟩
    have hmem : s.err = Z_MEM_ERROR → s.msg = .null := hv.2.2.2.2.2.2.2.1
    have hfree : freeStr h s.msg = dropWindow h s.msg := by
      rcases hmsg with hn | ⟨b,a,hp,ha,hro⟩
      · simp [hn, dropWindow]
      · simp [hp, dropWindow]
    have hr := gzrewind_record hs hmsg hmem fs
    by_cases hc : s.mode ≠ GZ_READ ∨ (s.err ≠ Z_OK ∧ s.err ≠ Z_BUF_ERROR)
    · refine ⟨-1,fs,h, ?_, Or.inl ⟨rfl,rfl⟩, fun _ => ⟨rfl,rfl⟩⟩
      simpa [hc, hnd] using hr
    · by_cases hl : (lseekRes s.fd s.start SEEK_SET fs).1 = -1
      · refine ⟨-1,(lseekRes s.fd s.start SEEK_SET fs).2,h, ?_, Or.inl ⟨rfl,rfl⟩, ?_⟩
        · simpa [hc,hl,hnd] using hr
        · intro bad
          exact (hc bad).elim
      · have hread : s.mode = GZ_READ := by
          by_cases hm : s.mode = GZ_READ
          · exact hm
          · exact (hc (Or.inl hm)).elim
        have hex := lseek_set_success s.fd s.start fs hreg.2.2.1 hreg.2.2.2.2.2.2 hl
        refine ⟨0,(lseekRes s.fd s.start SEEK_SET fs).2,setS (freeStr h s.msg) i (resetRec s), ?_, Or.inr ⟨rfl, ?_, hex⟩, ?_⟩
        · simpa [hc,hl,hnd] using hr
        · simp [setS, putGz, resetRec, rewoundState, hread, hfree]
        · intro bad
          exact (hc bad).elim


#print axioms rewind_public
end ZlibF.Spec.Public.GzRewindProof
