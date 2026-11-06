import ZlibF.Proof.«gzlib.c.error»

/-!
# gzlib.c: `gz_intmax`, `GT_OFF`, `gzbuffer`, `gzeof`, `gztell64`, `gztell`, `gzerror`, `gzclearerr`

The functions that read or write a few fields. Each theorem says exactly what is returned and what the heap becomes;
the null-handle case is separate (`*_null`).

`PosInv s` is the numeric part of the position bookkeeping (`docs/spec/functions/gz-file.md`, "Position bookkeeping"):
`skip` is not negative and `x.pos + skip` is a `z_off64_t`. `gz_reset` establishes it (`resetRec_posInv`), `gzseek64`
keeps it (`gzlib.c.seek`); the read and write functions have to keep it, and `gztell64` needs it to avoid signed overflow.
-/

namespace Zlib.Gzlib.Spec
open C Zlib.GzFs Zlib.Gzguts

/-- The distance `gztell64` adds to `x.pos`: `skip`, unless a read has come up short. -/
def tellSkip (s : GzState) : Int64 := if s.past != 0 then 0 else s.skip

/-- `gztell64`'s result as a number. -/
def tellPos (s : GzState) : Int := s.x.pos.toInt + (tellSkip s).toInt

/-- The numeric invariant of the position fields. -/
structure PosInv (s : GzState) : Prop where
  skip_nonneg : 0 ≤ s.skip.toInt
  lo : -9223372036854775808 ≤ tellPos s
  hi : tellPos s < 9223372036854775808

/-- `z_off_t` is `long`: the same 64 bits as `z_off64_t`. -/
def IsLit (r : BPtr) (t : String) : Prop := ∃ i, r = .ref (.str i) 0 ∧ strTable[i]? = some t

/-- The record `gzclearerr` has before it calls `gz_error`: a reader clears `eof` and `past`. -/
def clearRec (s : GzState) : GzState := if s.mode == GZ_READ then { s with eof := 0, past := 0 } else s

end Zlib.Gzlib.Spec

namespace Zlib.Gzlib.Proofs
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib Zlib.Gzlib.Spec

/-! ## gz_intmax, GT_OFF -/

/-- `gz_intmax()` returns `INT_MAX` (2147483647) and does not change the heap. No precondition. -/
theorem gz_intmax_run (h : Heap) : gz_intmax h = .ok (2147483647, h) := rfl

/-- `GT_OFF(x)` is false for every `x`: `sizeof(int) == sizeof(z_off64_t)` is false, and `gz_intmax` is not called. -/
theorem GT_OFF_run (x : UInt32) (h : Heap) : GT_OFF x h = .ok (false, h) := by
  simp [GT_OFF]

/-! ## gzbuffer -/

/-- `gzbuffer(NULL, size)` returns -1 and does not change the heap, for every `size`. -/
theorem gzbuffer_null (size : UInt32) (h : Heap) : gzbuffer none size h = .ok (-1, h) := rfl

/-- Doubling `size` overflows exactly when `size` is `2^31` or more. -/
theorem double_overflow_iff (size : UInt32) : (size <<< 1) < size ↔ 2 ^ 31 ≤ size.toNat := by
  rw [UInt32.lt_iff_toNat_lt, UInt32.toNat_shiftLeft]
  have := size.toNat_lt
  simp only [UInt32.toNat_ofNat, Nat.reducePow] at *
  rcases Nat.lt_or_ge size.toNat (2 ^ 31) with h1 | h1
  · have : (1 : UInt32).toNat % 32 = 1 := rfl
    simp [this]; omega
  · have : (1 : UInt32).toNat % 32 = 1 := rfl
    simp [this]; omega

/-- **gzbuffer.** `-1` and no change when buffers exist (`size ≠ 0`) or `size` cannot be doubled; otherwise `want` becomes
`max(size, 8)` and the result is 0. -/
theorem gzbuffer_run {h : Heap} {gs : Nat} {s : GzState} (hG : GzGood h gs s) (size : UInt32) :
    gzbuffer (hnd gs) size h =
      if s.size ≠ 0 ∨ (size <<< 1) < size then .ok (-1, h)
      else .ok (0, setS h gs { s with want := if size < 8 then 8 else size }) := by
  have hs := hG.hs
  have hm : s.mode = GZ_READ ∨ s.mode = GZ_WRITE := hG.mode
  have hne : s.mode ≠ GZ_READ ∨ s.mode ≠ GZ_WRITE := by
    rcases hm with h1 | h1 <;> simp [h1, GZ_READ, GZ_WRITE]
  unfold gzbuffer
  by_cases h1 : s.size ≠ 0
  · gsimp [hs, h1, hm]
  · have h1' : s.size = 0 := by simpa using h1
    by_cases h2 : (size <<< 1) < size
    · gsimp [hs, h1', h2, hm]
    · rcases hm with hm | hm <;> gsimp [hs, h1', h2, hm, GZ_READ, GZ_WRITE]

/-- `gzbuffer` on a handle with `GzGood`: no fault; either the result is -1 and the heap is unchanged (buffers exist, or `size >= 2^31`), or the result is 0, `want` is `max(size, 8)`, nothing else changes and `GzGood` still holds. Caller condition: a handle returned by `gzopen`/`gzdopen`, not closed. -/
theorem gzbuffer_safe {h : Heap} {gs : Nat} {s : GzState} (hG : GzGood h gs s) (size : UInt32) :
    ∃ r h', C.run (gzbuffer (hnd gs) size) h = .ok (r, h') ∧
      ((s.size ≠ 0 ∨ 2 ^ 31 ≤ size.toNat) ∧ r = -1 ∧ h' = h ∨
       (s.size = 0 ∧ size.toNat < 2 ^ 31) ∧ r = 0 ∧
        h' = setS h gs { s with want := if size < 8 then 8 else size } ∧
        GzGood h' gs { s with want := if size < 8 then 8 else size }) := by
  have hr := gzbuffer_run hG size
  have hd := double_overflow_iff size
  by_cases hc : s.size ≠ 0 ∨ (size <<< 1) < size
  · rw [if_pos hc] at hr
    refine ⟨-1, h, hr, Or.inl ⟨?_, rfl, rfl⟩⟩
    rcases hc with hc | hc
    · exact Or.inl hc
    · exact Or.inr (hd.mp hc)
  · rw [if_neg hc] at hr
    have hc1 : s.size = 0 := Classical.byContradiction fun hh => hc (Or.inl hh)
    have hc2 : ¬ (size <<< 1) < size := fun hh => hc (Or.inr hh)
    refine ⟨0, _, hr, Or.inr ⟨⟨hc1, ?_⟩, rfl, rfl, ?_⟩⟩
    · exact Classical.byContradiction fun hh => hc2 (hd.mpr (by omega))
    · exact GzGood.withRec hG (Or.inl rfl) rfl rfl rfl rfl (fun hh => hG.memerr hh)

/-! ## gzeof -/

/-- `gzeof(NULL)` returns 0 and does not change the heap. -/
theorem gzeof_null (h : Heap) : gzeof none h = .ok (0, h) := rfl

/-- `gzeof` on a handle with `GzGood`: returns `past` for a reader and 0 for a writer; the heap is unchanged. -/
theorem gzeof_run {h : Heap} {gs : Nat} {s : GzState} (hG : GzGood h gs s) :
    gzeof (hnd gs) h = .ok ((if s.mode = GZ_READ then s.past else 0), h) := by
  have hs := hG.hs
  unfold gzeof
  rcases hG.mode with hm | hm
  · gsimp [hs, hm]
  · gsimp [hs, hm, GZ_READ, GZ_WRITE]

/-! ## gztell64, gztell -/

/-- `gztell64(NULL)` returns -1 and does not change the heap. -/
theorem gztell64_null (h : Heap) : gztell64 none h = .ok (-1, h) := rfl

theorem gztell64_run {h : Heap} {gs : Nat} {s : GzState} (hG : GzGood h gs s) (hP : PosInv s) :
    gztell64 (hnd gs) h = .ok (Int64.ofInt (tellPos s), h) := by
  have hs := hG.hs
  have e := i64add_run s.x.pos (tellSkip s) (by have := hP.lo; unfold tellPos at this; omega)
    (by have := hP.hi; unfold tellPos at this; omega) h
  unfold gztell64
  rcases hG.mode with hm | hm
  · by_cases hp : s.past = 0
    · gsimp [hs, hm, hp]
      simpa [tellSkip, tellPos, hp] using e
    · gsimp [hs, hm, hp]
      simpa [tellSkip, tellPos, hp] using e
  · by_cases hp : s.past = 0
    · gsimp [hs, hm, hp, GZ_READ, GZ_WRITE]
      simpa [tellSkip, tellPos, hp] using e
    · gsimp [hs, hm, hp, GZ_READ, GZ_WRITE]
      simpa [tellSkip, tellPos, hp] using e

/-- **gztell64.** The result is `x.pos + (past ? 0 : skip)` as a number; the heap is unchanged. -/
theorem gztell64_spec {h : Heap} {gs : Nat} {s : GzState} (hG : GzGood h gs s) (hP : PosInv s) :
    ∃ r, C.run (gztell64 (hnd gs)) h = .ok (r, h) ∧ r.toInt = tellPos s := by
  refine ⟨_, gztell64_run hG hP, i64_toInt_ofInt hP.lo hP.hi⟩

/-- `gztell` on a handle with `GzGood` and `PosInv`: returns `x.pos + (past ? 0 : skip)` as a number; no fault (`PosInv` rules out signed overflow); the heap is unchanged. -/
theorem gztell_run {h : Heap} {gs : Nat} {s : GzState} (hG : GzGood h gs s) (hP : PosInv s) :
    gztell (hnd gs) h = .ok (Int64.ofInt (tellPos s), h) := by
  unfold gztell
  simp [bind_app, gztell64_run hG hP]

/-- `gztell(NULL)` returns -1 and does not change the heap. -/
theorem gztell_null (h : Heap) : gztell none h = .ok (-1, h) := rfl

/-! ## gzerror -/

/-- `gzerror(NULL, errnum)` returns NULL and does not change the heap, whatever `errnum` is. -/
theorem gzerror_null_file (errnum : BPtr) (h : Heap) : gzerror none errnum h = .ok (.null, h) := rfl

/-- **gzerror, no `errnum`.** The result is the static text `"out of memory"` for `Z_MEM_ERROR`, else the message of the
handle, else the static empty text. The heap is unchanged. -/
theorem gzerror_run {h : Heap} {gs : Nat} {s : GzState} (hG : GzGood h gs s) :
    ∃ r, gzerror (hnd gs) .null h = .ok (r, h) ∧
      ((s.err = Z_MEM_ERROR ∧ IsLit r "out of memory") ∨
       (s.err ≠ Z_MEM_ERROR ∧ s.msg = .null ∧ IsLit r "") ∨
       (s.err ≠ Z_MEM_ERROR ∧ s.msg ≠ .null ∧ r = s.msg)) := by
  have hs := hG.hs
  have lit : ∀ t : String, t ∈ strTable → ∃ r, strLit t h = .ok (r, h) ∧ IsLit r t := fun t ht => by
    obtain ⟨i, e, hi⟩ := strLitRef_of_mem (h := h) ht
    exact ⟨_, e, i, rfl, hi⟩
  have hm : s.mode = GZ_READ ∨ s.mode = GZ_WRITE := hG.mode
  by_cases he : s.err = Z_MEM_ERROR
  · obtain ⟨r, e1, e2⟩ := lit "out of memory" (by decide +kernel)
    refine ⟨r, ?_, Or.inl ⟨he, e2⟩⟩
    unfold gzerror
    rcases hm with hm | hm <;> gsimp [hs, hm, he, GZ_READ, GZ_WRITE, e1]
  · by_cases hn : s.msg = .null
    · obtain ⟨r, e1, e2⟩ := lit "" (by decide +kernel)
      refine ⟨r, ?_, Or.inr (Or.inl ⟨he, hn, e2⟩)⟩
      unfold gzerror
      rcases hm with hm | hm <;> gsimp [hs, hm, he, hn, GZ_READ, GZ_WRITE, e1]
    · refine ⟨s.msg, ?_, Or.inr (Or.inr ⟨he, hn, rfl⟩)⟩
      unfold gzerror
      rcases hm with hm | hm <;> gsimp [hs, hm, he, hn, GZ_READ, GZ_WRITE]


/-! ## gzclearerr -/

/-- `gzclearerr(NULL)` does nothing: no fault, the heap is unchanged. -/
theorem gzclearerr_null (h : Heap) : gzclearerr none h = .ok ((), h) := rfl

theorem GzGood.clearRec {h : Heap} {gs : Nat} {s : GzState} (hG : GzGood h gs s) : GzGood (setS h gs (clearRec s)) gs (clearRec s) := by
  refine GzGood.withRec hG (Or.inl (by unfold Spec.clearRec; split <;> rfl)) (by unfold Spec.clearRec; split <;> rfl)
    (by unfold Spec.clearRec; split <;> rfl) (by unfold Spec.clearRec; split <;> rfl) (by unfold Spec.clearRec; split <;> rfl)
    (by intro hh; have := hG.memerr (by unfold Spec.clearRec at hh; split at hh <;> exact hh); unfold Spec.clearRec; split <;> exact this)

/-- `gzclearerr` on a handle with `GzGood`: a reader clears `eof` and `past`; the error code becomes `Z_OK` and the message block is freed (`gz_error(state, Z_OK, NULL)`); nothing else changes. Caller condition: an open handle. -/
theorem gzclearerr_run {h : Heap} {gs : Nat} {s : GzState} (hG : GzGood h gs s) :
    gzclearerr (hnd gs) h = .ok ((), setS (freeStr h s.msg) gs (errNull (clearRec s) Z_OK)) := by
  have hs := hG.hs
  unfold gzclearerr
  rcases hG.msg with hn | ⟨mb, hm, a, ha, hro, k, hz⟩
  · rcases hG.mode with hmo | hmo <;> gsimp [hs, hn, hmo, gz_error, clearRec, errNull, GZ_READ, GZ_WRITE]
  · have hne : s.err ≠ Z_MEM_ERROR := fun h' => by have := hG.memerr h'; rw [hm] at this; cases this
    rcases hG.mode with hmo | hmo <;>
      gsimp [hs, hm, hne, hmo, freeB_blk_setS ha hro, freeB_blk_run ha hro, gz_error, clearRec, errNull, GZ_READ, GZ_WRITE]

/-- **gzclearerr, safety and effect.** -/
theorem gzclearerr_safe {h : Heap} {gs : Nat} {s : GzState} (hG : GzGood h gs s) :
    ∃ h', C.run (gzclearerr (hnd gs)) h = .ok ((), h') ∧ h' = setS (freeStr h s.msg) gs (errNull (clearRec s) Z_OK) ∧
      GzGood h' gs (errNull (clearRec s) Z_OK) := by
  refine ⟨_, gzclearerr_run hG, rfl, ?_⟩
  have := GzGood.afterErr (GzGood.clearRec hG) Z_OK
  have e : (clearRec s).msg = s.msg := by unfold Spec.clearRec; split <;> rfl
  rw [e] at this
  simpa using this

end Zlib.Gzlib.Proofs
