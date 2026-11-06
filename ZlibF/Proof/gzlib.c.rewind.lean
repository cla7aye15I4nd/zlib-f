import ZlibF.Proof.«gzlib.c.simple»

namespace Zlib.Gzlib.Spec
open C Zlib.GzFs Zlib.Gzguts

/-- The result and the world of `lseek(fd, off, whence)` (it does not look at the heap). -/
def lseekRes (fd : Int32) (off : Int64) (wh : Int32) (w : Fs) : Int64 × Fs :=
  match fsLseek fd off wh w Heap.empty with
  | .ok (r, _) => r
  | .error _ => (-1, w)

end Zlib.Gzlib.Spec

namespace Zlib.Gzlib.Proofs
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib Zlib.Gzlib.Spec

theorem fsLseek_pure (fd : Int32) (off : Int64) (wh : Int32) (w : Fs) :
    ∃ x, fsLseek fd off wh w = (pure x : M (Int64 × Fs)) ∧ (x.1 = -1 ∨ 0 ≤ x.1.toInt) := by
  unfold fsLseek
  repeat' first
    | exact ⟨_, rfl, Or.inl rfl⟩
    | (refine ⟨_, rfl, Or.inr ?_⟩
       simp only []
       rw [i64_toInt_ofInt (by omega) (by omega)]
       omega)
    | split
    | dsimp only

theorem fsLseek_eq (fd : Int32) (off : Int64) (wh : Int32) (w : Fs) (h : Heap) :
    fsLseek fd off wh w h = .ok (lseekRes fd off wh w, h) := by
  obtain ⟨x, hx, -⟩ := fsLseek_pure fd off wh w
  unfold lseekRes
  rw [hx]
  rfl

/-- `lseek` returns `-1` or a position that is not negative. -/
theorem lseekRes_ret (fd : Int32) (off : Int64) (wh : Int32) (w : Fs) :
    (lseekRes fd off wh w).1 = -1 ∨ 0 ≤ (lseekRes fd off wh w).1.toInt := by
  obtain ⟨x, hx, hp⟩ := fsLseek_pure fd off wh w
  unfold lseekRes
  rw [hx]
  exact hp

theorem G_bind_app {α β : Type} (m : G α) (f : α → G β) (fs : Fs) (h : Heap) :
    (m >>= f) fs h = match m fs h with | .ok ((a, fs1), h1) => f a fs1 h1 | .error e => .error e := by
  simp only [bind, StateT.bind]
  cases hm : m fs h with
  | error e => rfl
  | ok v => obtain ⟨⟨a, fs1⟩, h1⟩ := v; rfl

theorem G_pure_app {α : Type} (a : α) (fs : Fs) (h : Heap) : (pure a : G α) fs h = .ok ((a, fs), h) := rfl

theorem G_lift_app {α : Type} (m : M α) (fs : Fs) (h : Heap) :
    (StateT.lift m : G α) fs h = match m h with | .ok (a, h1) => .ok ((a, fs), h1) | .error e => .error e := rfl

/-- Evaluate a straight-line `G` computation on a `gz_state` record: the lifts, the binds, the field accesses and the
file calls. -/
macro "ggsimp" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, G_bind_app, G_pure_app, G_lift_app,
    bind_app, pure_app, ldS_eq, updS_eq, updX_eq, ldZ_eq, updZ_eq, castState_hnd, fsLseek_eq, $ts,*])

/-- `gzrewind` on a handle that satisfies the invariant. -/
theorem gzrewind_run {h : Heap} {gs : Nat} {s : GzState} (hG : GzGood h gs s) (fs : Fs) :
    gzrewind (hnd gs) fs h =
      if s.mode ≠ GZ_READ ∨ (s.err ≠ Z_OK ∧ s.err ≠ Z_BUF_ERROR) then .ok ((-1, fs), h)
      else if (lseekRes s.fd s.start SEEK_SET fs).1 = -1 then .ok ((-1, (lseekRes s.fd s.start SEEK_SET fs).2), h)
      else .ok ((0, (lseekRes s.fd s.start SEEK_SET fs).2), setS (freeStr h s.msg) gs (resetRec s)) := by
  have hs := hG.hs
  unfold gzrewind
  by_cases hc : s.mode ≠ GZ_READ ∨ (s.err ≠ Z_OK ∧ s.err ≠ Z_BUF_ERROR)
  · ggsimp [hs, hc]
  · by_cases hl : (lseekRes s.fd s.start SEEK_SET fs).1 = -1
    · ggsimp [hs, hc, hl]
    · ggsimp [hs, hc, hl, gz_reset_run hG]




/-- `gzrewind(NULL)` returns -1; the world and the heap are unchanged. No precondition. -/
theorem gzrewind_null (fs : Fs) (h : Heap) : gzrewind none fs h = .ok ((-1, fs), h) := rfl

/-- **gzrewind.** On a handle that satisfies the invariant: `-1` and no change when the handle is not a reader or has a
serious error; `-1` and only the world changed (`errno`) when `lseek` to `start` fails; otherwise `0`, the world is the one
`lseek` leaves (the descriptor is at `start`), and the state is reset (`gz_reset`). -/
theorem gzrewind_spec {h : Heap} {gs : Nat} {s : GzState} (hG : GzGood h gs s) (fs : Fs) :
    ∃ r fs' h', gzrewind (hnd gs) fs h = .ok ((r, fs'), h') ∧
      ((s.mode ≠ GZ_READ ∨ (s.err ≠ Z_OK ∧ s.err ≠ Z_BUF_ERROR)) ∧ r = -1 ∧ fs' = fs ∧ h' = h ∨
       ¬(s.mode ≠ GZ_READ ∨ (s.err ≠ Z_OK ∧ s.err ≠ Z_BUF_ERROR)) ∧ (lseekRes s.fd s.start SEEK_SET fs).1 = -1 ∧
         r = -1 ∧ fs' = (lseekRes s.fd s.start SEEK_SET fs).2 ∧ h' = h ∨
       ¬(s.mode ≠ GZ_READ ∨ (s.err ≠ Z_OK ∧ s.err ≠ Z_BUF_ERROR)) ∧ (lseekRes s.fd s.start SEEK_SET fs).1 ≠ -1 ∧
         r = 0 ∧ fs' = (lseekRes s.fd s.start SEEK_SET fs).2 ∧ h' = setS (freeStr h s.msg) gs (resetRec s) ∧
         GzGood h' gs (resetRec s) ∧ (∀ S, h.Owns S → h'.Owns (fun b => S b ∧ s.msg ≠ .ref (.blk b) 0))) := by
  have e := gzrewind_run hG fs
  by_cases hc : s.mode ≠ GZ_READ ∨ (s.err ≠ Z_OK ∧ s.err ≠ Z_BUF_ERROR)
  · rw [if_pos hc] at e
    exact ⟨_, _, _, e, Or.inl ⟨hc, rfl, rfl, rfl⟩⟩
  · rw [if_neg hc] at e
    by_cases hl : (lseekRes s.fd s.start SEEK_SET fs).1 = -1
    · rw [if_pos hl] at e
      exact ⟨_, _, _, e, Or.inr (Or.inl ⟨hc, hl, rfl, rfl, rfl⟩)⟩
    · rw [if_neg hl] at e
      obtain ⟨h1, -, he, hg, ho⟩ := gz_reset_safe hG
      subst he
      exact ⟨_, _, _, e, Or.inr (Or.inr ⟨hc, hl, rfl, rfl, rfl, hg, ho⟩)⟩


/-! ## gzoffset64, gzoffset -/

/-- `gzoffset64(NULL)` returns -1; the world and the heap are unchanged. No precondition. -/
theorem gzoffset64_null (fs : Fs) (h : Heap) : gzoffset64 none fs h = .ok ((-1, fs), h) := rfl

/-- `gzoffset64`. The result is `-1` when `lseek(fd, 0, SEEK_CUR)` fails; otherwise the descriptor's position, less the
input the inflate stream holds but has not used (`strm.avail_in`) for a reader. -/
theorem gzoffset64_run {h : Heap} {gs : Nat} {s : GzState} (hG : GzGood h gs s) (fs : Fs) :
    gzoffset64 (hnd gs) fs h =
      if (lseekRes s.fd 0 SEEK_CUR fs).1 = -1 then .ok ((-1, (lseekRes s.fd 0 SEEK_CUR fs).2), h)
      else if s.mode = GZ_READ then
        .ok ((Int64.ofInt ((lseekRes s.fd 0 SEEK_CUR fs).1.toInt - s.strm.avail_in.toNat), (lseekRes s.fd 0 SEEK_CUR fs).2), h)
      else .ok (((lseekRes s.fd 0 SEEK_CUR fs).1, (lseekRes s.fd 0 SEEK_CUR fs).2), h) := by
  have hs := hG.hs
  have hr := lseekRes_ret s.fd 0 SEEK_CUR fs
  have hav := s.strm.avail_in.toNat_lt
  unfold gzoffset64
  by_cases hl : (lseekRes s.fd 0 SEEK_CUR fs).1 = -1
  · rcases hG.mode with hm | hm <;> ggsimp [hs, hm, hl, GZ_READ, GZ_WRITE]
  · have hr' : 0 ≤ (lseekRes s.fd 0 SEEK_CUR fs).1.toInt := hr.resolve_left hl
    have hlt := (lseekRes s.fd 0 SEEK_CUR fs).1.toInt_lt
    have e := i64sub_run (lseekRes s.fd 0 SEEK_CUR fs).1 (u32ToI64 s.strm.avail_in)
      (by rw [u32ToI64_toInt]; omega) (by rw [u32ToI64_toInt]; omega) h
    rw [u32ToI64_toInt] at e
    rcases hG.mode with hm | hm
    · ggsimp [hs, hm, hl, GZ_READ, GZ_WRITE, e]
    · ggsimp [hs, hm, hl, GZ_READ, GZ_WRITE]

/-- `gzoffset` is `gzoffset64` (`z_off_t` is `long`, so the range check `ret == (z_off_t)ret` always holds). -/
theorem gzoffset_eq (file : GzFilePtr) (fs : Fs) (h : Heap) : gzoffset file fs h = gzoffset64 file fs h := by
  unfold gzoffset
  simp only [G_bind_app]
  cases hh : gzoffset64 file fs h with
  | error e => rfl
  | ok v => obtain ⟨⟨a, fs1⟩, h1⟩ := v; simp [G_pure_app]

end Zlib.Gzlib.Proofs
