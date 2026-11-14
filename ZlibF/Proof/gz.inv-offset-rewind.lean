import ZlibF.Proof.«gz.inv-seek»
import ZlibF.Proof.«public-gz-offset»

/-!
# gz safety: `gzoffset64`, `gzoffset` and `gzrewind` keep `GzInv`

`gzoffset64_step`, `gzoffset_step` and `gzrewind_step` (skeleton statements, unchanged), for every world of the
OS-call oracle.

- `gzoffset64` calls `lseek(fd, 0, SEEK_CUR)` and reads the record (`gzoffset64_record`). The heap is unchanged; the
  world is the one `lseek` leaves, which is a `FileSystem` with the same open descriptors (`lseekRes_fs`).
  `gzoffset` is `gzoffset64` (`gzoffset_eq`).
- `gzrewind` refuses with no change for a writer or a serious error. Otherwise it calls `lseek(fd, start, SEEK_SET)`;
  on failure only the world changes; on success `gz_reset` frees the message and resets the reader's scalars
  (`gzrewind_run_seek`), which keeps `GzInv` by `GzInv.clear_put_drop`, as in the back path of `gzseek64`.
-/

namespace ZlibF.Spec.Public.GzSkeleton
open C Zlib.GzFs Zlib.Gzguts ZlibF.Spec.Public
open Zlib.Gzlib.Spec (lseekRes resetRec setS hnd)
open Zlib.Gzlib.Proofs (freeStr gzrewind_run_seek)
set_option autoImplicit false

/-! ## gzoffset64, gzoffset -/

/-- `gzoffset64` on a handle in `GzInv` returns; the heap is unchanged and the world is the one
`lseek(fd, 0, SEEK_CUR)` leaves. -/
theorem gzoffset64_inv {h : Heap} {i : Nat} {s : GzState} (inv : GzInv h i s) (fs : Fs) :
    ∃ r, Zlib.Gzlib.gzoffset64 (hnd i) fs h = .ok ((r, (lseekRes s.fd 0 SEEK_CUR fs).2), h) := by
  have e := ZlibF.Spec.Public.OffsetProof.gzoffset64_record inv.common.record inv.common.mode fs
  have hL : ZlibF.Spec.Public.OffsetProof.lseekRes s.fd 0 SEEK_CUR fs = lseekRes s.fd 0 SEEK_CUR fs := rfl
  rw [hL] at e
  rw [e]
  by_cases hl : (lseekRes s.fd 0 SEEK_CUR fs).1 = -1
  · rw [ite_eq_left hl]
    exact ⟨_, rfl⟩
  · rw [ite_eq_right hl]
    by_cases hm : s.mode = GZ_READ
    · rw [ite_eq_left hm]
      exact ⟨_, rfl⟩
    · rw [ite_eq_right hm]
      exact ⟨_, rfl⟩

/-- `gzoffset64`, from `gzoffset64_public_goal` restated to `GzInv`: one `lseek` (M3: any result), no heap change. -/
theorem gzoffset64_step (i : Nat) : GzCallSafe i (.gzoffset64 (some (.in_gzstate_x i))) := by
  intro h fs s inv hfs _
  obtain ⟨r, e⟩ := gzoffset64_inv inv fs
  have e' : Call.execute (.gzoffset64 (some (.in_gzstate_x i))) fs h =
      .ok ((r, (lseekRes s.fd 0 SEEK_CUR fs).2), h) := e
  obtain ⟨hfs', hk⟩ := lseekRes_fs hfs s.fd 0 SEEK_CUR
  refine ⟨fun err he => ?_, fun _ => ⟨_, _, _, e'⟩, fun v fs2 a2 he => ?_⟩
  · rw [e'] at he
    cases he
  · rw [e'] at he
    cases he
    exact post_same inv hfs' hk rfl

/-- `gzoffset`, as `gzoffset64` (`gzoffset_eq`). -/
theorem gzoffset_step (i : Nat) : GzCallSafe i (.gzoffset (some (.in_gzstate_x i))) := by
  intro h fs s inv hfs ha
  have e : Call.execute (.gzoffset (some (.in_gzstate_x i))) fs h =
      Call.execute (.gzoffset64 (some (.in_gzstate_x i))) fs h :=
    Zlib.Gzlib.Proofs.gzoffset_eq _ fs h
  rw [e]
  exact gzoffset64_step i h fs s inv hfs ha

/-! ## gzrewind -/

/-- **`gzrewind` on a handle in `GzInv`, every world:** it returns, and the post-condition holds. -/
theorem gzrewind_inv {h : Heap} {i : Nat} {s : GzState} (inv : GzInv h i s) {fs : Fs} (hfs : FileSystem fs) :
    ∃ r fs' after, Zlib.Gzlib.gzrewind (hnd i) fs h = .ok ((r, fs'), after) ∧
      FdsKept fs fs' ∧ GzStepPost h i s (.gzrewind (some (.in_gzstate_x i))) fs' after := by
  have c := inv.common
  have hr : GzWriteRegions (.gzrewind (some (.in_gzstate_x i))) = [] := rfl
  have e := gzrewind_run_seek inv.seekGood fs
  by_cases hc : s.mode ≠ GZ_READ ∨ (s.err ≠ Z_OK ∧ s.err ≠ Z_BUF_ERROR)
  · rw [ite_eq_left hc] at e
    exact ⟨_, _, _, e, post_same inv hfs (fun _ => Iff.rfl) hr⟩
  rw [ite_eq_right hc] at e
  have hm : s.mode = GZ_READ := Classical.byContradiction fun hn => hc (Or.inl hn)
  obtain ⟨hfs', hk⟩ := lseekRes_fs hfs s.fd s.start SEEK_SET
  generalize lseekRes s.fd s.start SEEK_SET fs = L at e hfs' hk
  by_cases hl : L.1 = -1
  · rw [ite_eq_left hl] at e
    exact ⟨_, _, _, e, post_same inv hfs' hk hr⟩
  · rw [ite_eq_right hl] at e
    have hmo' : (s.mode == GZ_READ) = true := by simpa using hm
    have hR : resetRec s = resetRd s := by
      unfold resetRec resetRd
      rw [hmo']
      rfl
    rw [hR] at e
    refine ⟨_, _, _, e, ?_⟩
    obtain ⟨inv1, own1, live1, fr1⟩ := inv.clear_put_drop hm (resetRd s)
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ ⟨c.want.1, c.want.2, Or.inr rfl⟩
      ⟨by show (0 : Int) ≤ (0 : Int64).toInt; decide,
        by show (0 : Int64).toInt + (0 : Int64).toInt ≤ 9223372036854775807; decide,
        by show (0 : Int) ≤ (0 : Int64).toInt + ((0 : UInt32).toNat : Int); decide⟩
      (by show (0 : UInt32).toNat ≤ _; exact Nat.zero_le _)
      ⟨Or.inl rfl, fun e => absurd e (by show ¬ (LOOK = GZ_COPY); decide),
        fun e => absurd e (by show ¬ (LOOK = GZIP); decide), Or.inl rfl,
        Or.inl rfl, Or.inl rfl, Or.inl rfl, fun _ => rfl, fun _ => rfl,
        by show (0 : Int64).toInt + ((0 : UInt32).toNat : Int) ≤ 9223372036854775807; decide,
        fun hz => absurd rfl hz, fun he => absurd rfl he⟩
      (fun hc => absurd hc (by show ¬ (LOOK = GZ_COPY); decide))
    exact post_gen inv hfs' hk hr inv1 rfl rfl _ inv.msg_owned own1 live1 fr1

/-- `gzrewind`, from `rewind_public` restated to `GzInv` (`lseek` M3, `gz_reset`: local patch for R-3). -/
theorem gzrewind_step (i : Nat) : GzCallSafe i (.gzrewind (some (.in_gzstate_x i))) := by
  intro h fs s inv hfs _
  obtain ⟨r, fs', after, e, post⟩ := gzrewind_inv inv hfs
  have e' : Call.execute (.gzrewind (some (.in_gzstate_x i))) fs h = .ok ((r, fs'), after) := e
  refine ⟨fun err he => ?_, fun _ => ⟨r, fs', after, e'⟩, fun v fs2 a2 he => ?_⟩
  · rw [e'] at he
    cases he
  · rw [e'] at he
    cases he
    exact post

end ZlibF.Spec.Public.GzSkeleton
