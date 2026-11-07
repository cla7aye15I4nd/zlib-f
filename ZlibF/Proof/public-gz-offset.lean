import ZlibF.Spec.Public.GzControl
import ZlibF.Proof.«gzlib.c.simple»

namespace ZlibF.Spec.Public.OffsetProof
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib Zlib.Gzlib.Spec Zlib.Gzlib.Proofs

def lseekRes (fd : Int32) (off : Int64) (wh : Int32) (w : Fs) : Int64 × Fs :=
  match fsLseek fd off wh w Heap.empty with
  | .ok (r, _) => r
  | .error _ => (-1, w)


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
macro "offsetsimp" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, G_bind_app, G_pure_app, G_lift_app,
    bind_app, pure_app, ldS_eq, updS_eq, updX_eq, ldZ_eq, updZ_eq, castState_hnd, fsLseek_eq, $ts,*])

theorem gzoffset64_null (fs : Fs) (h : Heap) : gzoffset64 none fs h = .ok ((-1, fs), h) := rfl

theorem gzoffset_eq (file : GzFilePtr) (fs : Fs) (h : Heap) : gzoffset file fs h = gzoffset64 file fs h := by
  unfold gzoffset
  simp only [G_bind_app]
  cases hh : gzoffset64 file fs h with
  | error e => rfl
  | ok v => obtain ⟨⟨a, fs1⟩, h1⟩ := v; simp [G_pure_app]


theorem lseek_current_public (fd : Int32) (fs : Fs)
    (hpos : ∀ (i : Nat) (f : OFile), fs.fds[i]? = some (some f) → f.pos ≤ 2 ^ 63 - 1) :
    { (lseekRes fd 0 SEEK_CUR fs).2 with errno := fs.errno } = fs ∧
    (if fd.toInt < 0 then (lseekRes fd 0 SEEK_CUR fs).1 = -1 else
      match fs.fds[fd.toInt.toNat]? with
      | some (some file) => (lseekRes fd 0 SEEK_CUR fs).1.toInt = (file.pos : Int)
      | _ => (lseekRes fd 0 SEEK_CUR fs).1 = -1) := by
  by_cases hn : fd.toInt < 0
  · have hf : fd < 0 := Int32.lt_iff_toInt_lt.mpr (by simpa using hn)
    simp [lseekRes, fsLseek, hn, hf, pure_app]
  · have hfd : ¬ fd < 0 := fun hf => hn (by simpa using Int32.lt_iff_toInt_lt.mp hf)
    by_cases hi : fd.toInt.toNat < fs.fds.size
    · have hbound : ¬ fd.toInt ≥ (fs.fds.size : Int) := by omega
      have hget := Array.getElem?_eq_getElem hi
      cases hf : fs.fds[fd.toInt.toNat] with
      | none =>
        have hget' : fs.fds[fd.toInt.toNat]! = none := by rw [getElem!_pos fs.fds _ hi, hf]
        simp only [lseekRes, fsLseek, hfd, hbound, Bool.false_eq_true, Bool.false_or, ite_false,
          hget', pure_app, hget, hf, hn, ite_eq_right]
        simp [pure_app]
      | some f =>
        have hvalid : fs.fds[fd.toInt.toNat]? = some (some f) := by rw [hget, hf]
        have hp := hpos _ _ hvalid
        have hget' : fs.fds[fd.toInt.toNat]! = some f := by rw [getElem!_pos fs.fds _ hi, hf]
        have hself : fs.fds.set! fd.toInt.toNat (some f) = fs.fds := by
          rw [← hf, Array.set!_eq_setIfInBounds]
          simp [Array.setIfInBounds, hi]
        simp only [lseekRes, fsLseek, hfd, hbound, Bool.false_eq_true, Bool.false_or, ite_false,
          hget', pure_app, hvalid, hn, ite_eq_right, SEEK_CUR, SEEK_SET, beq_iff_eq, Int.reduceEq,
          Int64.toInt_ofNat_of_lt, ite_true, Int.reduceAdd,
          Int.toNat_natCast, hself, Prod.fst, Prod.snd]
        have hne : ¬ (f.pos : Int) < 0 := by omega
        have hmax : ¬ (9223372036854775807 : Int) < f.pos := by omega
        have hnat : f.pos < 2 ^ 63 := by omega
        simp only [Array.set!_eq_setIfInBounds] at hself
        change fs.fds.setIfInBounds fd.toNatClampNeg (some f) = fs.fds at hself
        have hto : (Int64.ofInt (f.pos : Int)).toInt = (f.pos : Int) :=
          i64_toInt_ofInt (by omega) (by omega)
        simp [pure_app, hne, hmax, hself, hto, SEEK_CUR, SEEK_SET]
    · have hbound : fd.toInt ≥ (fs.fds.size : Int) := by omega
      have hnone : fs.fds[fd.toInt.toNat]? = none := Array.getElem?_eq_none (by omega)
      change fs.fds[fd.toNatClampNeg]? = none at hnone
      simp [lseekRes, fsLseek, hn, hfd, hbound, hnone, pure_app]

/-- `z_off64_t gzoffset64(gzFile file)` has the exact result of the descriptor
query on any existing state record with a supported mode. -/
theorem gzoffset64_record {h : Heap} {i : Nat} {s : GzState}
    (hs : h.gzstates i = some s) (hm : s.mode = GZ_READ ∨ s.mode = GZ_WRITE) (fs : Fs) :
    gzoffset64 (hnd i) fs h =
      if (lseekRes s.fd 0 SEEK_CUR fs).1 = -1 then .ok ((-1, (lseekRes s.fd 0 SEEK_CUR fs).2), h)
      else if s.mode = GZ_READ then
        .ok ((Int64.ofInt ((lseekRes s.fd 0 SEEK_CUR fs).1.toInt - s.strm.avail_in.toNat),
          (lseekRes s.fd 0 SEEK_CUR fs).2), h)
      else .ok (((lseekRes s.fd 0 SEEK_CUR fs).1, (lseekRes s.fd 0 SEEK_CUR fs).2), h) := by
  have hr := lseekRes_ret s.fd 0 SEEK_CUR fs
  have hav := s.strm.avail_in.toNat_lt
  unfold gzoffset64
  by_cases hl : (lseekRes s.fd 0 SEEK_CUR fs).1 = -1
  · rcases hm with hm | hm <;> offsetsimp [hs, hm, hl, GZ_READ, GZ_WRITE]
  · have hr' : 0 ≤ (lseekRes s.fd 0 SEEK_CUR fs).1.toInt := hr.resolve_left hl
    have hlt := (lseekRes s.fd 0 SEEK_CUR fs).1.toInt_lt
    have e := i64sub_run (lseekRes s.fd 0 SEEK_CUR fs).1 (u32ToI64 s.strm.avail_in)
      (by rw [u32ToI64_toInt]; omega) (by rw [u32ToI64_toInt]; omega) h
    rw [u32ToI64_toInt] at e
    rcases hm with hm | hm
    · offsetsimp [hs, hm, hl, GZ_READ, GZ_WRITE, e]
    · offsetsimp [hs, hm, hl, GZ_READ, GZ_WRITE]

/-- `z_off64_t gzoffset64(gzFile file)` returns the descriptor position less
buffered input. The heap and all filesystem fields except errno are unchanged. -/
theorem gzoffset64_public {h : Heap} {i : Nat} {s : GzState}
    (hs : h.gzstates i = some s) (hm : s.mode = GZ_READ ∨ s.mode = GZ_WRITE) (fs : Fs)
    (hpos : ∀ (j : Nat) (f : OFile), fs.fds[j]? = some (some f) → f.pos ≤ 2 ^ 63 - 1) :
    ∃ value fs', gzoffset64 (hnd i) fs h = .ok ((value, fs'), h) ∧
      { fs' with errno := fs.errno } = fs ∧
      (if s.fd.toInt < 0 then value = -1 else match fs.fds[s.fd.toInt.toNat]? with
       | some (some file) => value.toInt = (file.pos : Int) -
           (if s.mode = GZ_READ then s.strm.avail_in.toNat else 0)
       | _ => value = -1) := by
  obtain ⟨hfs, hres⟩ := lseek_current_public s.fd fs hpos
  have hex := gzoffset64_record hs hm fs
  by_cases hfd : s.fd.toInt < 0
  · have he : (lseekRes s.fd 0 SEEK_CUR fs).1 = -1 := by simpa [hfd] using hres
    exact ⟨-1, _, by simpa [he] using hex, hfs, by simp [hfd]⟩
  · cases hf : fs.fds[s.fd.toInt.toNat]? with
    | none =>
      have he : (lseekRes s.fd 0 SEEK_CUR fs).1 = -1 := by
        rw [ite_eq_right hfd, hf] at hres
        exact hres
      exact ⟨-1, _, by simpa [he] using hex, hfs, by simp [hfd, hf]⟩
    | some slot =>
      cases slot with
      | none =>
        have he : (lseekRes s.fd 0 SEEK_CUR fs).1 = -1 := by
          rw [ite_eq_right hfd, hf] at hres
          exact hres
        exact ⟨-1, _, by simpa [he] using hex, hfs, by simp [hfd, hf]⟩
      | some file =>
        have hr : (lseekRes s.fd 0 SEEK_CUR fs).1.toInt = (file.pos : Int) := by
          rw [ite_eq_right hfd, hf] at hres
          exact hres
        have he : (lseekRes s.fd 0 SEEK_CUR fs).1 ≠ -1 := by
          intro he
          rw [he] at hr
          have : (0 : Int) ≤ file.pos := by omega
          have : (-1 : Int) = file.pos := by simpa using hr
          omega
        by_cases hread : s.mode = GZ_READ
        · refine ⟨Int64.ofInt ((lseekRes s.fd 0 SEEK_CUR fs).1.toInt - s.strm.avail_in.toNat), _,
            by simpa [he, hread] using hex, hfs, ?_⟩
          simp only [hfd, ite_false, hf, hread, ite_true]
          rw [i64_toInt_ofInt (by have := s.strm.avail_in.toNat_lt; omega)
            (by have := (lseekRes s.fd 0 SEEK_CUR fs).1.toInt_lt; omega), hr]
        · exact ⟨_, _, by simpa [he, hread] using hex, hfs, by simpa [hfd, hf, hread] using hr⟩

/-- `z_off_t gzoffset(gzFile file)` has the same LP64 result as `gzoffset64`. -/
theorem gzoffset_public {h : Heap} {i : Nat} {s : GzState}
    (hs : h.gzstates i = some s) (hm : s.mode = GZ_READ ∨ s.mode = GZ_WRITE) (fs : Fs)
    (hpos : ∀ (j : Nat) (f : OFile), fs.fds[j]? = some (some f) → f.pos ≤ 2 ^ 63 - 1) :
    ∃ value fs', gzoffset (hnd i) fs h = .ok ((value, fs'), h) ∧
      { fs' with errno := fs.errno } = fs ∧
      (if s.fd.toInt < 0 then value = -1 else match fs.fds[s.fd.toInt.toNat]? with
       | some (some file) => value.toInt = (file.pos : Int) -
           (if s.mode = GZ_READ then s.strm.avail_in.toNat else 0)
       | _ => value = -1) := by
  obtain ⟨value, fs', hr, hf, hv⟩ := gzoffset64_public hs hm fs hpos
  exact ⟨value, fs', by rw [gzoffset_eq]; exact hr, hf, hv⟩


/-- `z_off64_t gzoffset64(gzFile file)`
The exact public result, state, frame and ownership contract. -/
theorem gzoffset64_public_goal : Goal.gzoffset64 := by
  constructor
  · intro h fs
    exact gzoffset64_null fs h
  · intro h fs i s _ hv hfs
    have hpos : ∀ (j : Nat) (f : OFile), fs.fds[j]? = some (some f) → f.pos ≤ 2 ^ 63 - 1 := by
      intro j f hf
      exact (hfs.2.2.1 j f hf).2.1
    exact gzoffset64_public hv.1 hv.2.1 fs hpos

/-- `z_off_t gzoffset(gzFile file)`; the LP64 wrapper has the same physical-position contract.
The exact public result, state, frame and ownership contract. -/
theorem gzoffset_public_goal : Goal.gzoffset := by
  constructor
  · intro h fs
    rw [gzoffset_eq]
    exact gzoffset64_null fs h
  · intro h fs i s _ hv hfs
    have hpos : ∀ (j : Nat) (f : OFile), fs.fds[j]? = some (some f) → f.pos ≤ 2 ^ 63 - 1 := by
      intro j f hf
      exact (hfs.2.2.1 j f hf).2.1
    exact gzoffset_public hv.1 hv.2.1 fs hpos


#print axioms gzoffset64_public_goal
#print axioms gzoffset_public_goal
end ZlibF.Spec.Public.OffsetProof
