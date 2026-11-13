import ZlibF.Proof.«gzwrite.c.write-calls»

/-!
# gzwrite.c: the public calls `gzflush` and `gzsetparams`

`gzflush_step_of`: the skeleton statement `gzflush_step` (branch `skeleton/gz`, `gz.skeleton-write.lean`), from the
facts of `gz_error` (`GzErrorSpec`, `GzErrorOwn`). The callees are `zero_any` and `comp_any`
(`gzwrite.c.write-calls`): `gz_zero` and `gz_comp` on a writer with or without buffers.
-/

namespace ZlibF.Spec.Public.GzSkeleton
open C Zlib.GzFs Zlib.Gzguts ZlibF.Spec.Public
open Zlib.Gzwrite.SafeInit (GzErrorSpec GzErrorOwn)
set_option autoImplicit false

section flush
variable {i : Nat}

/-- `gzflush` from the compression on. -/
def flushTail (i : Nat) (flush : Int32) : G Int32 := do
  let _ ← Zlib.Gzwrite.gz_comp (gzSt i) flush
  return (← ldS (gzSt i)).err

theorem gzflush_eq (flush : Int32) :
    Zlib.Gzwrite.gzflush (some (.in_gzstate_x i)) flush = (do
      let s ← ldS (gzSt i)
      if s.mode != GZ_WRITE || (s.err != Z_OK && s.again == 0) then return Z_STREAM_ERROR
      Zlib.Gzlib.gz_error (gzSt i) Z_OK .null
      if flush < 0 || flush > Z_FINISH then return Z_STREAM_ERROR
      if (← ldS (gzSt i)).skip != 0 then
        if (← Zlib.Gzwrite.gz_zero (gzSt i)) == -1 then return (← ldS (gzSt i)).err
      flushTail i flush : G Int32) := rfl

theorem flushTail_ok (err : GzErrorSpec) (errOwn : GzErrorOwn) {h0 : Heap} {s0 : GzState} {fs0 fs : Fs} {H : Heap}
    {v : GzState} (flush : Int32) (hf : 0 ≤ flush.toInt ∧ flush.toInt ≤ 4) (E : GetcUngetc.Eff i h0 s0 fs0 fs H)
    (inv : GzInv H i v) (hw : v.mode = GZ_WRITE) :
    ∃ r fs' h', flushTail i flush fs H = .ok ((r, fs'), h') ∧ GetcUngetc.Eff i h0 s0 fs0 fs' h' := by
  obtain ⟨r, fs2, H2, run, k2, post⟩ := comp_any err errOwn inv E.2.1 hw flush hf
  have E2 := GetcUngetc.Eff.trans E inv post k2
  obtain ⟨-, -, s2, inv2, -⟩ := id E2
  have hS2 : ldS (gzSt i) H2 = .ok (s2, H2) := Zlib.Gzlib.Proofs.ldS_run inv2.common.record
  refine ⟨s2.err, fs2, H2, ?_, E2⟩
  unfold flushTail
  simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, run, hS2]

/-- **`gzflush_step`** (skeleton statement), given the facts of `gz_error`. -/
theorem gzflush_step_of (err : GzErrorSpec) (errOwn : GzErrorOwn) (i : Nat) (flush : Int32) :
    GzCallSafe i (.gzflush (some (.in_gzstate_x i)) flush) := by
  intro h fs s inv hfs _
  have R : Ok (Zlib.Gzwrite.gzflush (some (.in_gzstate_x i)) flush) fs h
      (fun _ fs' after => GetcUngetc.Eff i h s fs fs' after) := by
    rw [gzflush_eq]
    have hS : ldS (gzSt i) h = .ok (s, h) := Zlib.Gzlib.Proofs.ldS_run inv.common.record
    by_cases hm : (s.mode != GZ_WRITE || (s.err != Z_OK && s.again == 0)) = true
    · refine ⟨Z_STREAM_ERROR, fs, h, ?_, GetcUngetc.Eff.refl inv hfs⟩
      simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hS,
        hm, ↓reduceIte]
    have hm' := Bool.eq_false_iff.mpr hm
    have hw := mode_of hm'
    obtain ⟨run1, inv1, post1⟩ := clear_step (fs := fs) inv hfs
    have E1 : GetcUngetc.Eff i h s fs fs (okHeap h i s) :=
      GetcUngetc.Eff.trans (GetcUngetc.Eff.refl inv hfs) inv post1 (fun _ => Iff.rfl)
    by_cases hc : (decide (flush < 0) || decide (flush > Z_FINISH)) = true
    · refine ⟨Z_STREAM_ERROR, fs, okHeap h i s, ?_, E1⟩
      simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hS,
        hm', Bool.false_eq_true, ↓reduceIte, run1, hc]
    have hc' := Bool.eq_false_iff.mpr hc
    have hf : 0 ≤ flush.toInt ∧ flush.toInt ≤ 4 := by
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, Int32.lt_iff_toInt_lt, GT.gt] at hc'
      have z0 : (0 : Int32).toInt = 0 := rfl
      have f4 : Z_FINISH.toInt = 4 := rfl
      omega
    have hS1 : ldS (gzSt i) (okHeap h i s) = .ok (okRec s, okHeap h i s) :=
      Zlib.Gzlib.Proofs.ldS_run inv1.common.record
    by_cases hk : (okRec s).skip = 0
    · have hkB : ((okRec s).skip != 0) = false := by simp [hk]
      obtain ⟨r, fs', h', run, E'⟩ := flushTail_ok err errOwn flush hf E1 inv1 hw
      refine ⟨r, fs', h', ?_, E'⟩
      simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hS,
        hm', Bool.false_eq_true, ↓reduceIte, run1, hc', hS1, hkB]
      exact run
    · have hkB : ((okRec s).skip != 0) = true := by simpa using hk
      obtain ⟨r, fs2, H2, run2, hr, k2, post2, -⟩ := zero_any err errOwn inv1 hfs hw
      have E2 := GetcUngetc.Eff.trans E1 inv1 post2 k2
      obtain ⟨-, -, s2, inv2, hm2, -⟩ := id E2
      rcases hr with rfl | rfl
      · obtain ⟨r, fs', h', run, E'⟩ := flushTail_ok err errOwn flush hf E2 inv2 (hm2.trans hw)
        refine ⟨r, fs', h', ?_, E'⟩
        simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hS,
          hm', Bool.false_eq_true, ↓reduceIte, run1, hc', hS1, hkB, run2, int32_zero_ne_neg_one]
        exact run
      · have hS2 : ldS (gzSt i) H2 = .ok (s2, H2) := Zlib.Gzlib.Proofs.ldS_run inv2.common.record
        refine ⟨s2.err, fs2, H2, ?_, E2⟩
        simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hS,
          hm', Bool.false_eq_true, ↓reduceIte, run1, hc', hS1, hkB, run2, beq_self_eq_true, hS2]
  have RS := runSafe_of_ok R
  exact ⟨RS.1, fun _ => RS.2.1 trivial, fun v fs' after he => GetcUngetc.Eff.post rfl (RS.2.2 v fs' after he)⟩

end flush

end ZlibF.Spec.Public.GzSkeleton
