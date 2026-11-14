import ZlibF.Proof.«public-gz-offset»
import ZlibF.Spec.Public.GzClose
import ZlibF.Proof.«gzfs.oracle»
import ZlibF.Spec.Functional.Api.Compress

/-!
# gzread.c: closing a reader before lazy buffer allocation

This internal execution theorem covers `size = 0`, with the existing `GzGood`
representation invariant. It includes a pending error message and descriptor failure.
It does not prove the complete public close target or establish `GzGood` from public
histories. Initialized readers still require the decoder and buffer cleanup proof.
-/

namespace Zlib.Gzread.Proofs
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib Zlib.Gzlib.Spec Zlib.Gzlib.Proofs
open ZlibF.Spec.Public.OffsetProof

/-- The exact heap after freeing the message, path and handle of an unbuffered reader. -/
def closedHeap (h : Heap) (i : Nat) (s : GzState) : Heap :=
  let freed := freeStr (freeStr h s.msg) s.path
  { freed with gzstates := upd h.gzstates i none }

private theorem freeStr_gzstates (h : Heap) (p : BPtr) :
    (freeStr h p).gzstates = h.gzstates := by
  cases p with
  | null => rfl
  | ref r off => cases r <;> rfl

/-- The result and the world of `close(fd)` (any oracle value; it does not look at the heap). -/
def closeResult (fd : Int32) (fs : Fs) : Int32 × Fs :=
  match fsClose fd fs Heap.empty with
  | .ok (r, _) => r
  | .error _ => (-1, fs)

theorem fsClose_run (fd : Int32) (fs : Fs) (h : Heap) :
    fsClose fd fs h = .ok (closeResult fd fs, h) := by
  obtain ⟨x, hx⟩ := Zlib.GzFs.Proofs.fsClose_pure fd fs
  unfold closeResult
  rw [hx]
  rfl

/-- `int gzclose_r(gzFile file)` rejects NULL without heap or file effects. -/
theorem gzclose_r_null (fs : Fs) (h : Heap) :
    Zlib.Gzread.gzclose_r none fs h = .ok ((Z_STREAM_ERROR, fs), h) := rfl

/-- `int gzclose_r(gzFile file)` rejects every non-reader mode before any effect. -/
theorem gzclose_r_wrong_mode {h : Heap} {i : Nat} {s : GzState}
    (hs : h.gzstates i = some s) (hm : s.mode ≠ GZ_READ) (fs : Fs) :
    Zlib.Gzread.gzclose_r (hnd i) fs h = .ok ((Z_STREAM_ERROR, fs), h) := by
  unfold Zlib.Gzread.gzclose_r
  offsetsimp [hs, hm]

/-- `int gzclose_r(gzFile file)` closes an unbuffered reader completely.
This internal domain requires `GzGood` and `size = 0`; it is narrower than the public
API. No callee specification is assumed. The initialized-reader path remains open. -/
theorem gzclose_r_unbuffered {h : Heap} {i : Nat} {s : GzState}
    (hg : GzGood h i s) (hm : s.mode = GZ_READ) (hz : s.size = 0) (fs : Fs) :
    Zlib.Gzread.gzclose_r (hnd i) fs h =
      .ok (((if (closeResult s.fd fs).1 ≠ 0 then Z_ERRNO
        else if s.err = Z_BUF_ERROR then Z_BUF_ERROR else Z_OK),
        (closeResult s.fd fs).2), closedHeap h i s) := by
  have he := gz_error_null_run hg Z_OK
  have hg' := Zlib.Gzlib.Proofs.GzGood.afterErr hg Z_OK
  obtain ⟨pb, hp, a, ha, hro, _⟩ := hg'.path
  have hf := freeB_run hp ha hro
  have hm' : (s.mode != GZ_READ) = false := by simp [hm]
  have hz' : (s.size != 0) = false := by simp [hz]
  unfold Zlib.Gzread.gzclose_r
  simp only [hnd_isNone, Bool.false_eq_true, ↓reduceIte, castState_hnd]
  simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, G_bind_app, G_lift_app,
    ldS_run hg.hs, hm', hz', Bool.false_eq_true, ↓reduceIte, he, ldS_run hg'.hs, hf]
  simp [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, G_bind_app, G_lift_app,
    G_pure_app, fsClose_run, freeGzState, freeStr_setS, freeStr_gzstates, closedHeap, upd_upd, errNull]
  simp [setS, upd_upd, freeStr_gzstates]

/-- `int gzclose_r(gzFile file)` preserves unrelated allocations and does not allocate
on the unbuffered close path. The stated footprint includes the handle, path and message. -/
theorem gzclose_r_unbuffered_frame (h : Heap) (i : Nat) (s : GzState) :
    ZlibF.Spec.Public.Frame h (closedHeap h i s)
      (fun b => b = i ∨ ptrBlk s.path = some b ∨ ptrBlk s.msg = some b) ∧
    (closedHeap h i s).nalloc = h.nalloc ∧ (closedHeap h i s).nextBlk = h.nextBlk := by
  cases hp : s.path with
  | null =>
    cases hm : s.msg with
    | null => simp [ZlibF.Spec.Public.Frame, closedHeap, hp, hm, freeStr, ptrBlk, upd_apply] <;> intro b _ <;> intros <;> simp_all
    | ref r off => cases r <;>
        simp [ZlibF.Spec.Public.Frame, closedHeap, hp, hm, freeStr, ptrBlk, upd_apply, eq_comm] <;> intro b _ <;> intros <;> simp_all
  | ref r off =>
    cases r <;> cases hm : s.msg with
    | null => simp [ZlibF.Spec.Public.Frame, closedHeap, hp, hm, freeStr, ptrBlk, upd_apply, eq_comm] <;> intro b _ <;> intros <;> simp_all
    | ref r' off' => cases r' <;>
        simp [ZlibF.Spec.Public.Frame, closedHeap, hp, hm, freeStr, ptrBlk, upd_apply, eq_comm] <;> intro b _ <;> intros <;> simp_all

#print axioms gzclose_r_unbuffered
end Zlib.Gzread.Proofs
