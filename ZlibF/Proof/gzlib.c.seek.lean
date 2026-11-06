import ZlibF.Proof.«gzlib.c.rewind»

/-!
# gzlib.c: `gzseek64`, `gzseek`

`t` is the target position: `0` for `SEEK_SET`, `gztell64` for `SEEK_CUR`, plus `offset`. The function refuses
(`-1`, nothing changes) when `t` is not a `z_off64_t` that is not negative; otherwise it returns `t`.

The unpatched C faults in two places that the earlier repository patched (R-1, `docs/translation-notes/gz-files.md`):
`SEEK_CUR` while `gztell64 < 0` (the check `offset > GZ_OFF_MAX - pos` overflows), and `offset = pos - x.pos` while
`x.pos < 0` (after `gzungetc` at the start). The theorems below that say what the function returns carry the
hypothesis `0 ≤ x.pos`, which excludes both; the `*_ub` theorems show the fault in the excluded states.
-/

namespace Zlib.Gzlib.Spec
open C Zlib.GzFs Zlib.Gzguts

/-- `GZ_OFF_MAX` as a number. -/
def OffMax : Int := 9223372036854775807

/-- The position `gzseek64` starts from: 0 for `SEEK_SET`, the current position for `SEEK_CUR`. -/
def seekBase (s : GzState) (whence : Int32) : Int := if whence = SEEK_SET then 0 else tellPos s

/-- The position `gzseek64` goes to. -/
def seekT (s : GzState) (offset : Int64) (whence : Int32) : Int := seekBase s whence + offset.toInt

/-- A position `gzseek64` accepts. -/
def SeekOk (t : Int) : Prop := 0 ≤ t ∧ t ≤ OffMax

instance (t : Int) : Decidable (SeekOk t) := by unfold SeekOk; infer_instance

theorem OffMax_val : OffMax = 9223372036854775807 := rfl


/-- The fields a seek does not change. -/
def SameCfg (s s' : GzState) : Prop :=
  s'.mode = s.mode ∧ s'.fd = s.fd ∧ s'.path = s.path ∧ s'.size = s.size ∧ s'.want = s.want ∧ s'.in = s.in ∧
  s'.out = s.out ∧ s'.direct = s.direct ∧ s'.start = s.start ∧ s'.level = s.level ∧ s'.strategy = s.strategy

/-- What every outcome of `gzseek64` has in common: the handle still satisfies the invariants, and either nothing changed
(result `-1`) or the result is the target `t` and the position fields say so: `gztell64` is `t`, except for a reader that
has read past the end (`past`), whose `gztell64` is `x.pos` (the position of the end; the returned `t` is not what
`gztell64` then reports, see the migration note). -/
def SeekPost (h : Heap) (gs : Nat) (s : GzState) (t : Int) (r : Int64) (h' : Heap) (s' : GzState) : Prop :=
  GzGood h' gs s' ∧ PosInv s' ∧ NextOk h' s' ∧ SameCfg s s' ∧
  ((r = -1 ∧ h' = h ∧ s' = s) ∨
   (SeekOk t ∧ r.toInt = t ∧ (s'.past = 0 → tellPos s' = t) ∧
     (s'.past ≠ 0 → tellPos s' = s'.x.pos.toInt ∧ s'.x.pos.toInt ≤ t)))

/-- The record after a seek inside the raw area (`how == COPY`): nothing buffered, the position is `t`, no pending skip,
no error and no message, the stream has no input. -/
def copyRec (s : GzState) (t : Int) : GzState :=
  { s with x := { s.x with «have» := 0, pos := Int64.ofInt t }, eof := 0, past := 0, skip := 0, msg := .null, err := Z_OK,
           strm := { s.strm with avail_in := 0 } }

/-- How many buffered bytes a forward seek skips by advancing `x.next`: all of the distance if the buffer is longer than
the distance, else the whole buffer. -/
def fwdN (s : GzState) (off : Int) : Nat := if off < s.x.«have».toNat then off.toNat else s.x.«have».toNat

/-- The record after a forward seek of a reader (target `t`, not before `x.pos`): the buffered bytes before the target
are consumed, the rest of the distance becomes `skip`. -/
def skipFwd (s : GzState) (t : Int) : GzState :=
  let off := t - s.x.pos.toInt
  let n := fwdN s off
  { s with x := { «have» := s.x.«have» - UInt32.ofNat n, next := padv s.x.next n, pos := Int64.ofInt (s.x.pos.toInt + n) },
           skip := Int64.ofInt (off - n) }

/-- The code of `gzseek64` after `pos += offset` (`s` is the record read at the start). Written as in
`gzlib.c.lean`; `gzseek64_head` shows that `gzseek64` is the checks followed by this. -/
def seekTail (file : GzFilePtr) (s : GzState) (pos : Int64) : G Int64 := do
  let state := castState file
  -- if (state->mode == GZ_READ && state->how == COPY) { ... }
  if s.mode == GZ_READ && s.how == GZ_COPY then
    let d ← i64sub (← i64sub pos s.x.pos) (u32ToI64 s.x.«have»)
    let ret ← fsLseek s.fd d SEEK_CUR
    if ret == -1 then return -1
    updX state fun x => { x with «have» := 0 }
    updS state fun s => { s with eof := 0, past := 0, skip := 0 }
    gz_error state Z_OK .null
    updZ (strmOf state) fun z => { z with avail_in := 0 }
    updX state fun x => { x with pos := pos }
    return pos
  -- if (pos < state->x.pos) { if (state->mode != GZ_READ) return -1; if (gzrewind(file) == -1) return -1; }
  let s ← ldS state
  if pos < s.x.pos then
    if s.mode != GZ_READ then return -1
    if (← gzrewind file) == -1 then return -1
  -- offset = pos - state->x.pos;
  let s ← ldS state
  let mut offset ← i64sub pos s.x.pos
  -- if (state->mode == GZ_READ) { ... }
  if s.mode == GZ_READ then
    let s ← ldS state
    let n : UInt32 ← if (← GT_OFF s.x.«have») || u32ToI64 s.x.«have» > offset then pure offset.toUInt64.toUInt32
      else pure s.x.«have»
    updX state fun x => { x with «have» := x.«have» - n }
    let s ← ldS state
    let nx ← s.x.next.add n.toNat
    updX state fun x => { x with next := nx }
    let s ← ldS state
    let np ← i64add s.x.pos (u32ToI64 n)
    updX state fun x => { x with pos := np }
    offset ← i64sub offset (u32ToI64 n)
  -- state->skip = offset; return pos;
  updS state fun s => { s with skip := offset }
  return pos

end Zlib.Gzlib.Spec

namespace Zlib.Gzlib.Proofs
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib Zlib.Gzlib.Spec

theorem GZ_OFF_MAX_toInt : GZ_OFF_MAX.toInt = OffMax := by
  unfold GZ_OFF_MAX OffMax
  exact i64_toInt_ofInt (by omega) (by omega)

theorem int64_toInt_ge (x : Int64) : -9223372036854775808 ≤ x.toInt := x.le_toInt
theorem int64_toInt_lt (x : Int64) : x.toInt < 9223372036854775808 := x.toInt_lt

theorem i64_gt_iff (a b : Int64) : a > b ↔ b.toInt < a.toInt := by
  show b < a ↔ _
  exact Int64.lt_iff_toInt_lt

theorem i64_lt_iff (a b : Int64) : a < b ↔ a.toInt < b.toInt := Int64.lt_iff_toInt_lt

/-- The addition at the start of `gzseek64` for `SEEK_CUR`. -/
theorem tell_add_run {s : GzState} (hP : PosInv s) (h : Heap) :
    i64add s.x.pos (if s.past != 0 then 0 else s.skip) h = .ok (Int64.ofInt (tellPos s), h) := by
  have e := i64add_run s.x.pos (tellSkip s) (by have := hP.lo; unfold tellPos at this; omega)
    (by have := hP.hi; unfold tellPos at this; omega) h
  simpa [tellSkip, tellPos] using e


theorem tellPos_nonneg {s : GzState} (hP : PosInv s) (hnn : 0 ≤ s.x.pos.toInt) : 0 ≤ tellPos s := by
  have := hP.skip_nonneg
  unfold tellPos tellSkip
  by_cases hp : s.past != 0
  · simp [hp]; omega
  · simp [hp]; omega

theorem seekBase_nonneg {s : GzState} (hP : PosInv s) (hnn : 0 ≤ s.x.pos.toInt) (whence : Int32) :
    0 ≤ seekBase s whence := by
  unfold seekBase; split
  · exact Int.le_refl 0
  · exact tellPos_nonneg hP hnn

theorem seekBase_le {s : GzState} (hP : PosInv s) (whence : Int32) : seekBase s whence ≤ OffMax := by
  have := hP.hi
  have hOM := OffMax_val
  unfold seekBase; split
  · omega
  · omega

/-- The three checks of `gzseek64` (`offset > GZ_OFF_MAX - pos`, `offset < -pos`, `pos += offset`) for `pos = p0`
with `0 ≤ p0`: what they evaluate to. -/
theorem seek_checks {p0 : Int64} (offset : Int64) (hp0 : 0 ≤ p0.toInt) (h : Heap) :
    ∃ q1 q3 : Int64, i64sub GZ_OFF_MAX p0 h = .ok (q1, h) ∧ i64neg p0 h = .ok (q3, h) ∧
      (q1 < offset ↔ OffMax < p0.toInt + offset.toInt) ∧ (offset < q3 ↔ p0.toInt + offset.toInt < 0) ∧
      ((¬ OffMax < p0.toInt + offset.toInt) → ¬ (p0.toInt + offset.toInt < 0) →
        ∃ q5 : Int64, i64add p0 offset h = .ok (q5, h) ∧ q5 = Int64.ofInt (p0.toInt + offset.toInt) ∧
          q5.toInt = p0.toInt + offset.toInt) := by
  have hOM := OffMax_val
  have hg := GZ_OFF_MAX_toInt
  have hlt := p0.toInt_lt
  have f1 := i64sub_run GZ_OFF_MAX p0 (by omega) (by omega) h
  have f3 := i64neg_run p0 (by omega) (by omega) h
  have hq1 : (Int64.ofInt (GZ_OFF_MAX.toInt - p0.toInt)).toInt = OffMax - p0.toInt := by
    rw [hg]; exact i64_toInt_ofInt (by omega) (by omega)
  have hq3 : (Int64.ofInt (-p0.toInt)).toInt = -p0.toInt := i64_toInt_ofInt (by omega) (by omega)
  refine ⟨_, _, f1, f3, ?_, ?_, ?_⟩
  · rw [i64_lt_iff, hq1]; omega
  · rw [i64_lt_iff, hq3]; omega
  · intro h1 h2
    exact ⟨_, i64add_run p0 offset (by omega) (by omega) h, rfl, i64_toInt_ofInt (by omega) (by omega)⟩

/-- `gzseek64` on a handle with `GzGood` and `PosInv`, `x.pos >= 0`, no serious error and `whence` in {SEEK_SET, SEEK_CUR}: it is the checks followed by `seekTail`. The result is -1 with the heap unchanged when the target is outside `[0, GZ_OFF_MAX]`, otherwise `seekTail` at the target. -/
theorem gzseek64_head {h : Heap} {gs : Nat} {s : GzState} (hG : GzGood h gs s) (hP : PosInv s)
    (hnn : 0 ≤ s.x.pos.toInt) (he : s.err = Z_OK ∨ s.err = Z_BUF_ERROR) {whence : Int32}
    (hw : whence = SEEK_SET ∨ whence = SEEK_CUR) (offset : Int64) (fs : Fs) :
    gzseek64 (hnd gs) offset whence fs h =
      if SeekOk (seekT s offset whence) then seekTail (hnd gs) s (Int64.ofInt (seekT s offset whence)) fs h
      else Except.ok ((-1, fs), h) := by
  have hs := hG.hs
  have hOM := OffMax_val
  have hb0 := seekBase_nonneg hP hnn whence
  have hb1 := seekBase_le hP whence
  have hne : ¬(¬ s.err = Z_OK ∧ ¬ s.err = Z_BUF_ERROR) := by rcases he with h1 | h1 <;> simp [h1]
  have hmo : ¬ (s.mode ≠ GZ_READ ∧ s.mode ≠ GZ_WRITE) := by rcases hG.mode with h1 | h1 <;> simp [h1]
  have hSC : SEEK_CUR ≠ SEEK_SET := by decide
  have eT : i64add s.x.pos (if s.past = 0 then s.skip else 0) h = .ok (Int64.ofInt (tellPos s), h) := by
    have := tell_add_run hP h
    by_cases hh : s.past = 0
    · simpa [hh] using this
    · simpa [hh] using this
  obtain ⟨p0, hp0⟩ : ∃ p0 : Int64, p0 = Int64.ofInt (seekBase s whence) := ⟨_, rfl⟩
  have hp0i : p0.toInt = seekBase s whence := by rw [hp0]; exact i64_toInt_ofInt (by omega) (by omega)
  obtain ⟨q1, q3, f1, f3, c1, c2, c5⟩ := seek_checks (p0 := p0) offset (by omega) h
  rw [hp0i] at c1 c2 c5
  have hbt : seekBase s whence + offset.toInt = seekT s offset whence := rfl
  rw [hbt] at c1 c2 c5
  have hpp : p0 = if whence = SEEK_SET then 0 else Int64.ofInt (tellPos s) := by
    rw [hp0]; unfold seekBase; split
    · rfl
    · rfl
  unfold gzseek64
  by_cases r1 : OffMax < seekT s offset whence
  · have hrhs : ¬ SeekOk (seekT s offset whence) := fun hh => by have := hh.2; omega
    rw [if_neg hrhs]
    rcases hw with hw | hw <;> subst hw
    · rw [if_pos rfl] at hpp; subst hpp
      ggsimp [hs, hmo, hne, f1, f3, c1, c2, r1]
    · rw [if_neg (by decide)] at hpp; subst hpp
      ggsimp [hs, hmo, hne, f1, f3, c1, c2, r1, eT, hSC]
  · by_cases r2 : seekT s offset whence < 0
    · have hrhs : ¬ SeekOk (seekT s offset whence) := fun hh => by have := hh.1; omega
      rw [if_neg hrhs]
      rcases hw with hw | hw <;> subst hw
      · rw [if_pos rfl] at hpp; subst hpp
        ggsimp [hs, hmo, hne, f1, f3, c1, c2, r1, r2]
      · rw [if_neg (by decide)] at hpp; subst hpp
        ggsimp [hs, hmo, hne, f1, f3, c1, c2, r1, r2, eT, hSC]
    · obtain ⟨q5, f5, hq5, hq5i⟩ := c5 r1 r2
      have hrhs : SeekOk (seekT s offset whence) := ⟨by omega, by omega⟩
      rw [if_pos hrhs, ← hq5]
      rcases hw with hw | hw <;> subst hw
      · rw [if_pos rfl] at hpp; subst hpp
        ggsimp [hs, hmo, hne, f1, f3, c1, c2, r1, r2, f5, seekTail]
      · rw [if_neg (by decide)] at hpp; subst hpp
        ggsimp [hs, hmo, hne, f1, f3, c1, c2, r1, r2, eT, hSC, f5, seekTail]

/-- `gzseek64` on a writer (preconditions as in `gzseek64_head`): the result is the target `t` and `skip` becomes `t - x.pos` when `t` is in range and not before `x.pos`; otherwise -1 and nothing changes. The world is unchanged. -/
theorem gzseek64_write_run {h : Heap} {gs : Nat} {s : GzState} (hG : GzGood h gs s) (hP : PosInv s)
    (hnn : 0 ≤ s.x.pos.toInt) (he : s.err = Z_OK ∨ s.err = Z_BUF_ERROR) {whence : Int32}
    (hw : whence = SEEK_SET ∨ whence = SEEK_CUR) (hm : s.mode = GZ_WRITE) (offset : Int64) (fs : Fs) :
    gzseek64 (hnd gs) offset whence fs h =
      if SeekOk (seekT s offset whence) ∧ s.x.pos.toInt ≤ seekT s offset whence then
        Except.ok ((Int64.ofInt (seekT s offset whence), fs),
          setS h gs { s with skip := Int64.ofInt (seekT s offset whence - s.x.pos.toInt) })
      else Except.ok ((-1, fs), h) := by
  have hs := hG.hs
  have hOM := OffMax_val
  have hb0 := seekBase_nonneg hP hnn whence
  have hb1 := seekBase_le hP whence
  have hne : ¬(¬ s.err = Z_OK ∧ ¬ s.err = Z_BUF_ERROR) := by rcases he with h1 | h1 <;> simp [h1]
  have hWR : GZ_WRITE ≠ GZ_READ := by decide
  have hSC : SEEK_CUR ≠ SEEK_SET := by decide
  have eT : i64add s.x.pos (if s.past = 0 then s.skip else 0) h = .ok (Int64.ofInt (tellPos s), h) := by
    have := tell_add_run hP h
    by_cases hh : s.past = 0
    · simpa [hh] using this
    · simpa [hh] using this
  obtain ⟨p0, hp0⟩ : ∃ p0 : Int64, p0 = Int64.ofInt (seekBase s whence) := ⟨_, rfl⟩
  have hp0i : p0.toInt = seekBase s whence := by rw [hp0]; exact i64_toInt_ofInt (by omega) (by omega)
  obtain ⟨q1, q3, f1, f3, c1, c2, c5⟩ := seek_checks (p0 := p0) offset (by omega) h
  rw [hp0i] at c1 c2 c5
  have hbt : seekBase s whence + offset.toInt = seekT s offset whence := rfl
  rw [hbt] at c1 c2 c5
  have hpf : True ∧ (whence = SEEK_CUR → i64add s.x.pos (if s.past != 0 then 0 else s.skip) h =
      .ok (Int64.ofInt (tellPos s), h)) := ⟨trivial, fun _ => tell_add_run hP h⟩
  have hpp : p0 = if whence = SEEK_SET then 0 else Int64.ofInt (tellPos s) := by
    rw [hp0]; unfold seekBase; split
    · rfl
    · rfl
  unfold gzseek64
  have hcases : (whence = SEEK_SET ∨ whence = SEEK_CUR) := hw
  by_cases r1 : OffMax < seekT s offset whence
  · have hrhs : ¬ (SeekOk (seekT s offset whence) ∧ s.x.pos.toInt ≤ seekT s offset whence) := fun hh => by
      have := hh.1.2; omega
    rw [if_neg hrhs]
    rcases hw with hw | hw <;> subst hw
    · rw [if_pos rfl] at hpp; subst hpp
      ggsimp [hs, hm, hne, hWR, f1, f3, c1, c2, r1]
    · rw [if_neg (by decide)] at hpp; subst hpp
      ggsimp [hs, hm, hne, hWR, f1, f3, c1, c2, r1, eT, hSC]
  · by_cases r2 : seekT s offset whence < 0
    · have hrhs : ¬ (SeekOk (seekT s offset whence) ∧ s.x.pos.toInt ≤ seekT s offset whence) := fun hh => by
        have := hh.1.1; omega
      rw [if_neg hrhs]
      rcases hw with hw | hw <;> subst hw
      · rw [if_pos rfl] at hpp; subst hpp
        ggsimp [hs, hm, hne, hWR, f1, f3, c1, c2, r1, r2]
      · rw [if_neg (by decide)] at hpp; subst hpp
        ggsimp [hs, hm, hne, hWR, f1, f3, c1, c2, r1, r2, eT, hSC]
    · obtain ⟨q5, f5, hq5, hq5i⟩ := c5 r1 r2
      have c6 : q5 < s.x.pos ↔ seekT s offset whence < s.x.pos.toInt := by rw [i64_lt_iff, hq5i]
      have hlt := s.x.pos.toInt_lt
      have f7 := i64sub_run q5 s.x.pos (by rw [hq5i]; omega) (by rw [hq5i]; omega) h
      rw [hq5i] at f7
      by_cases r3 : seekT s offset whence < s.x.pos.toInt
      · have hrhs : ¬ (SeekOk (seekT s offset whence) ∧ s.x.pos.toInt ≤ seekT s offset whence) := fun hh => by
          have := hh.2; omega
        rw [if_neg hrhs]
        rcases hw with hw | hw <;> subst hw
        · rw [if_pos rfl] at hpp; subst hpp
          ggsimp [hs, hm, hne, hWR, f1, f3, c1, c2, r1, r2, f5, c6, r3]
        · rw [if_neg (by decide)] at hpp; subst hpp
          ggsimp [hs, hm, hne, hWR, f1, f3, c1, c2, r1, r2, eT, hSC, f5, c6, r3]
      · have hrhs : SeekOk (seekT s offset whence) ∧ s.x.pos.toInt ≤ seekT s offset whence :=
          ⟨⟨by omega, by omega⟩, by omega⟩
        rw [if_pos hrhs, ← hq5]
        rcases hw with hw | hw <;> subst hw
        · rw [if_pos rfl] at hpp; subst hpp
          ggsimp [hs, hm, hne, hWR, f1, f3, c1, c2, r1, r2, f5, c6, r3, f7]
        · rw [if_neg (by decide)] at hpp; subst hpp
          ggsimp [hs, hm, hne, hWR, f1, f3, c1, c2, r1, r2, eT, hSC, f5, c6, r3, f7]


theorem OffMax_lt : OffMax < 9223372036854775808 := by decide

/-- **Seek inside the raw area** (`how == COPY`, a reader that passes the file through). The descriptor moves by
`t - x.pos - have` (the bytes read ahead are given back); if `lseek` fails nothing changes but the world; otherwise
the buffer is dropped (`have = 0`), the error is cleared (the message block is freed), `x.pos = t`. The hypothesis
`hraw` is the signed-overflow condition of the C expression `pos - x.pos - have` (it fails only for positions within
`2^32` of `2^63`). -/
theorem seekTail_copy {h : Heap} {gs : Nat} {s : GzState} (hG : GzGood h gs s) (hm : s.mode = GZ_READ)
    (hcopy : s.how = GZ_COPY) (hnn : 0 ≤ s.x.pos.toInt) {t : Int} (ht : SeekOk t)
    (hraw : -9223372036854775808 ≤ t - s.x.pos.toInt - s.x.«have».toNat) (fs : Fs) :
    seekTail (hnd gs) s (Int64.ofInt t) fs h =
      if (lseekRes s.fd (Int64.ofInt (t - s.x.pos.toInt - s.x.«have».toNat)) SEEK_CUR fs).1 = -1 then
        Except.ok ((-1, (lseekRes s.fd (Int64.ofInt (t - s.x.pos.toInt - s.x.«have».toNat)) SEEK_CUR fs).2), h)
      else
        Except.ok ((Int64.ofInt t, (lseekRes s.fd (Int64.ofInt (t - s.x.pos.toInt - s.x.«have».toNat)) SEEK_CUR fs).2),
          setS (freeStr h s.msg) gs (copyRec s t)) := by
  have hs := hG.hs
  have hOM := OffMax_val
  have hhv := s.x.«have».toNat_lt
  have hlt := s.x.pos.toInt_lt
  have hqi : (Int64.ofInt t).toInt = t := i64_toInt_ofInt (by have := ht.1; omega) (by have := ht.2; omega)
  obtain ⟨q2, hq2d⟩ : ∃ q2 : Int64, q2 = Int64.ofInt (t - s.x.pos.toInt) := ⟨_, rfl⟩
  have hq2 : q2.toInt = t - s.x.pos.toInt := by
    rw [hq2d]; exact i64_toInt_ofInt (by have := ht.1; omega) (by have := ht.2; omega)
  have fa : i64sub (Int64.ofInt t) s.x.pos h = .ok (q2, h) := by
    have := i64sub_run (Int64.ofInt t) s.x.pos (by rw [hqi]; have := ht.1; omega) (by rw [hqi]; have := ht.2; omega) h
    rw [hqi, ← hq2d] at this; exact this
  obtain ⟨q3, hq3d⟩ : ∃ q3 : Int64, q3 = Int64.ofInt (t - s.x.pos.toInt - s.x.«have».toNat) := ⟨_, rfl⟩
  have fb : i64sub q2 (u32ToI64 s.x.«have») h = .ok (q3, h) := by
    have := i64sub_run q2 (u32ToI64 s.x.«have») (by rw [hq2, u32ToI64_toInt]; omega)
      (by rw [hq2, u32ToI64_toInt]; have := ht.2; omega) h
    rw [hq2, u32ToI64_toInt, ← hq3d] at this; exact this
  obtain ⟨q, hqd⟩ : ∃ q : Int64, q = Int64.ofInt t := ⟨_, rfl⟩
  rw [← hqd] at fa ⊢
  rw [← hq3d]
  unfold seekTail
  by_cases hl : (lseekRes s.fd q3 SEEK_CUR fs).1 = -1
  · rw [if_pos hl]
    ggsimp [hs, hm, hcopy, fa, fb, hl]
  · rw [if_neg hl]
    rcases hG.msg with hn | ⟨mb, hmm, a, ha, hro, k, hz⟩
    · ggsimp [hs, hm, hcopy, fa, fb, hl, hn, gz_error, copyRec, ← hqd]
    · have hne : s.err ≠ Z_MEM_ERROR := fun h' => by have := hG.memerr h'; rw [hmm] at this; cases this
      ggsimp [hs, hm, hcopy, fa, fb, hl, hmm, hne, freeB_blk_setS ha hro, freeB_blk_run ha hro, gz_error, copyRec, ← hqd]


theorem space_get_setS (h : Heap) (gs : Nat) (s' : GzState) (r : BRef) : Space.get (setS h gs s') r = Space.get h r := by
  cases r <;> rfl

theorem i64_toU32_toNat (x : Int64) (hx : 0 ≤ x.toInt) : x.toUInt64.toUInt32.toNat = x.toInt.toNat % 2 ^ 32 := by
  have h0 : (0 : Int64) ≤ x := by rw [Int64.le_iff_toInt_le]; simpa using hx
  rw [UInt64.toNat_toUInt32, Int64.toNat_toUInt64_of_le h0, Int64.toNat_toInt]

/-- `x.next + n` for `n ≤ x.have`: the pointer advanced by `n`. -/
theorem next_add_run {h : Heap} {s : GzState} (hN : NextOk h s) {n : Nat} (hn : n ≤ s.x.«have».toNat) (gs : Nat) (s' : GzState) :
    Ptr.add s.x.next (n : Int) (setS h gs s') = .ok (padv s.x.next n, setS h gs s') := by
  rcases hN.1 with ⟨hnl, hh0⟩ | ⟨r, a, off, hr, hg, hle⟩
  · have : n = 0 := by rw [hh0] at hn; simpa using hn
    subst this
    rw [hnl]
    simp [Ptr.add, padv]
  · rw [hr]
    have hg' : Space.get (setS h gs s') r = some a := by rw [space_get_setS]; exact hg
    have := Ptr.add_nat_ok (R := BRef) (h := setS h gs s') hg' (n := n) (off := off) (by omega)
    exact this


/-- The part of `gzseek64` after the checks, for a reader that is not in the raw area, with the target not before `x.pos`, `x.pos >= 0` and `NextOk`: the buffered bytes before the target are consumed (`have`, `next`, `pos` advance by `n`), the rest of the distance becomes `skip`; the result is the target; no fault. -/
theorem seekTail_fwd {h : Heap} {gs : Nat} {s : GzState} (hG : GzGood h gs s) (hm : s.mode = GZ_READ)
    (hhow : s.how ≠ GZ_COPY) (hnn : 0 ≤ s.x.pos.toInt) {t : Int} (ht : SeekOk t) (hfw : s.x.pos.toInt ≤ t)
    (hN : NextOk h s) (fs : Fs) :
    seekTail (hnd gs) s (Int64.ofInt t) fs h = Except.ok ((Int64.ofInt t, fs), setS h gs (skipFwd s t)) := by
  have hs := hG.hs
  have hOM := OffMax_val
  have ht1 := ht.1
  have ht2 := ht.2
  have hhv := s.x.«have».toNat_lt
  have hlt := s.x.pos.toInt_lt
  have hqi : (Int64.ofInt t).toInt = t := i64_toInt_ofInt (by have := ht.1; omega) (by have := ht.2; omega)
  obtain ⟨q, hqd⟩ : ∃ q : Int64, q = Int64.ofInt t := ⟨_, rfl⟩
  have hqi' : q.toInt = t := by rw [hqd]; exact hqi
  obtain ⟨q2, hq2d⟩ : ∃ q2 : Int64, q2 = Int64.ofInt (t - s.x.pos.toInt) := ⟨_, rfl⟩
  have hq2 : q2.toInt = t - s.x.pos.toInt := by
    rw [hq2d]; exact i64_toInt_ofInt (by have := ht.1; omega) (by have := ht.2; omega)
  have fa : ∀ h', i64sub q s.x.pos h' = .ok (q2, h') := fun h' => by
    have := i64sub_run q s.x.pos (by rw [hqi']; have := ht.1; omega) (by rw [hqi']; have := ht.2; omega) h'
    rw [hqi', ← hq2d] at this; exact this
  have c6 : ¬ (q < s.x.pos) := by rw [i64_lt_iff, hqi']; omega
  have c : q2 < u32ToI64 s.x.«have» ↔ t - s.x.pos.toInt < s.x.«have».toNat := by
    rw [i64_lt_iff, hq2, u32ToI64_toInt]
  obtain ⟨nU, hA, hB, hnU, hn1, hn2⟩ : ∃ nU : UInt32, (q2 < u32ToI64 s.x.«have» → nU = q2.toUInt64.toUInt32) ∧
      (¬ q2 < u32ToI64 s.x.«have» → nU = s.x.«have») ∧ nU.toNat = fwdN s (t - s.x.pos.toInt) ∧
      nU.toNat ≤ s.x.«have».toNat ∧ (nU.toNat : Int) ≤ t - s.x.pos.toInt := by
    by_cases hc : q2 < u32ToI64 s.x.«have»
    · have hc' := c.mp hc
      have h0 : 0 ≤ q2.toInt := by rw [hq2]; have := ht.1; omega
      have e := i64_toU32_toNat q2 h0
      rw [hq2] at e
      have hl : (t - s.x.pos.toInt).toNat < 2 ^ 32 := by omega
      rw [Nat.mod_eq_of_lt hl] at e
      refine ⟨q2.toUInt64.toUInt32, fun _ => rfl, fun hh => absurd hc hh, ?_, ?_, ?_⟩
      · rw [e]; unfold fwdN; rw [if_pos hc']
      · rw [e]; omega
      · rw [e]; omega
    · have hc' : ¬ (t - s.x.pos.toInt < s.x.«have».toNat) := fun hh => hc (c.mpr hh)
      refine ⟨s.x.«have», fun hh => absurd hh hc, fun _ => rfl, ?_, Nat.le_refl _, ?_⟩
      · unfold fwdN; rw [if_neg hc']
      · omega
  have fn := next_add_run hN hn1 gs
  have fpos : ∀ h', i64add s.x.pos (u32ToI64 nU) h' =
      .ok (Int64.ofInt (s.x.pos.toInt + nU.toNat), h') := fun h' => by
    have := i64add_run s.x.pos (u32ToI64 nU) (by rw [u32ToI64_toInt]; omega) (by rw [u32ToI64_toInt]; have := ht.2; omega) h'
    rw [u32ToI64_toInt] at this; exact this
  have fsk : ∀ h', i64sub q2 (u32ToI64 nU) h' = .ok (Int64.ofInt ((t - s.x.pos.toInt) - nU.toNat), h') := fun h' => by
    have := i64sub_run q2 (u32ToI64 nU) (by rw [hq2, u32ToI64_toInt]; omega) (by rw [hq2, u32ToI64_toInt]; omega) h'
    rw [hq2, u32ToI64_toInt] at this; exact this
  rw [← hqd]
  unfold seekTail
  ggsimp [hs, hm, hhow, fa, c6, GT_OFF_run]
  by_cases hc : q2 < u32ToI64 s.x.«have»
  · rw [if_pos hc, ← hA hc]
    ggsimp [hs, fn, fpos, fsk, skipFwd, ← hnU]
  · rw [if_neg hc, ← hB hc]
    ggsimp [hs, fn, fpos, fsk, skipFwd, ← hnU]


theorem freeStr_get_other (h : Heap) (p : BPtr) (r : BRef) (hr : ∀ b, r ≠ .blk b) :
    Space.get (freeStr h p) r = Space.get h r := by
  cases r with
  | blk b => exact absurd rfl (hr b)
  | _ => cases p with
    | null => rfl
    | ref q o => cases q <;> rfl

/-- `x.next + n` after `gz_reset` freed the message block: the pointer does not point into it. -/
theorem next_add_run_reset {h : Heap} {s : GzState} (hN : NextOk h s) {n : Nat} (hn : n ≤ s.x.«have».toNat) (gs : Nat)
    (s' : GzState) :
    Ptr.add s.x.next (n : Int) (setS (freeStr h s.msg) gs s') = .ok (padv s.x.next n, setS (freeStr h s.msg) gs s') := by
  rcases hN.1 with ⟨hnl, hh0⟩ | ⟨r, a, off, hr, hg, hle⟩
  · have : n = 0 := by rw [hh0] at hn; simpa using hn
    subst this
    rw [hnl]
    simp [Ptr.add, padv]
  · rw [hr]
    have hg' : Space.get (setS (freeStr h s.msg) gs s') r = some a := by
      rw [space_get_setS]
      cases r with
      | blk b =>
        have hb := hN.2 b (by rw [hr]; rfl)
        cases hm : s.msg with
        | null => simpa [hm, freeStr] using hg
        | ref q o =>
          cases q with
          | blk mb =>
            have : mb ≠ b := fun e => hb (by rw [hm, e]; rfl)
            simpa [hm, freeStr, upd_ne _ _ _ _ this.symm] using hg
          | _ => simpa [hm, freeStr] using hg
      | str i => rw [freeStr_get_other _ _ _ (by intro b; simp)]; exact hg
      | dstate_depth i => rw [freeStr_get_other _ _ _ (by intro b; simp)]; exact hg
      | st_dist_code => rw [freeStr_get_other _ _ _ (by intro b; simp)]; exact hg
      | st_length_code => rw [freeStr_get_other _ _ _ (by intro b; simp)]; exact hg
    exact Ptr.add_nat_ok (R := BRef) (h := setS (freeStr h s.msg) gs s') hg' (n := n) (off := off) (by omega)


theorem padv_zero (p : BPtr) : padv p 0 = p := by cases p <;> rfl

/-- The part of `gzseek64` after the checks, for a reader that is not in the raw area, with the target before `x.pos` and `NextOk`: `gzrewind`, which fails with -1 and no change of the heap if `lseek` fails, otherwise the state is reset and the whole distance becomes `skip`; no fault. -/
theorem seekTail_back {h : Heap} {gs : Nat} {s : GzState} (hG : GzGood h gs s) (hm : s.mode = GZ_READ)
    (hhow : s.how ≠ GZ_COPY) (he : s.err = Z_OK ∨ s.err = Z_BUF_ERROR) (hnn : 0 ≤ s.x.pos.toInt) {t : Int}
    (ht : SeekOk t) (hlt : t < s.x.pos.toInt) (hN : NextOk h s) (fs : Fs) :
    seekTail (hnd gs) s (Int64.ofInt t) fs h =
      if (lseekRes s.fd s.start SEEK_SET fs).1 = -1 then Except.ok ((-1, (lseekRes s.fd s.start SEEK_SET fs).2), h)
      else Except.ok ((Int64.ofInt t, (lseekRes s.fd s.start SEEK_SET fs).2),
        setS (freeStr h s.msg) gs (skipFwd (resetRec s) t)) := by
  have hs := hG.hs
  have hOM := OffMax_val
  have ht1 := ht.1
  have ht2 := ht.2
  have hqi : (Int64.ofInt t).toInt = t := i64_toInt_ofInt (by omega) (by omega)
  obtain ⟨q, hqd⟩ : ∃ q : Int64, q = Int64.ofInt t := ⟨_, rfl⟩
  have hqi' : q.toInt = t := by rw [hqd]; exact hqi
  have c6 : q < s.x.pos := by rw [i64_lt_iff, hqi']; omega
  have hrw := gzrewind_run hG fs
  have hcond : ¬ (s.mode ≠ GZ_READ ∨ (s.err ≠ Z_OK ∧ s.err ≠ Z_BUF_ERROR)) := by
    rintro (h1 | ⟨h1, h2⟩)
    · exact h1 hm
    · rcases he with e | e <;> simp_all
  rw [if_neg hcond] at hrw
  rw [← hqd]
  unfold seekTail
  by_cases hl : (lseekRes s.fd s.start SEEK_SET fs).1 = -1
  · rw [if_pos hl]
    rw [if_pos hl] at hrw
    ggsimp [hs, hm, hhow, c6, hrw, hl]
  · rw [if_neg hl]
    rw [if_neg hl] at hrw
    have z0 : (0 : Int64).toInt = 0 := rfl
    have hq0 : ¬ q < 0 := by rw [i64_lt_iff, hqi', z0]; omega
    have fa0 : ∀ h', i64sub q 0 h' = .ok (q, h') := fun h' => by
      have := i64sub_run q 0 (by rw [hqi', z0]; omega) (by rw [hqi', z0]; omega) h'
      simpa [hqi', ← hqd] using this
    have fb0 : ∀ h', i64sub q (u32ToI64 0) h' = .ok (q, h') := fun h' => by
      have := fa0 h'
      simpa [u32ToI64] using this
    have fc0 : ∀ h', i64add 0 (u32ToI64 0) h' = .ok (0, h') := fun h' => by
      simp [i64add, i64chk, u32ToI64]
    have fn0 : ∀ s', Ptr.add s.x.next 0 (setS (freeStr h s.msg) gs s') = .ok (s.x.next, setS (freeStr h s.msg) gs s') := fun s' => by
      have := next_add_run_reset hN (n := 0) (Nat.zero_le _) gs s'
      simpa [padv_zero] using this
    have hGT : ¬ (u32ToI64 0 > q) := by rw [i64_gt_iff, u32ToI64_toInt, hqi']; simp; omega
    have hnt : ¬ t < 0 := by omega
    ggsimp [hs, hm, hhow, c6, hrw, hl, fa0, fb0, fc0, fn0, hGT, skipFwd, fwdN, resetRec, padv_zero, GT_OFF_run, hnt, ← hqd]


/-! ### The invariants after a seek -/

theorem fwdN_le {s : GzState} (off : Int) : fwdN s off ≤ s.x.«have».toNat := by
  unfold fwdN; split <;> omega

theorem fwdN_le_off {s : GzState} {off : Int} (h0 : 0 ≤ off) : (fwdN s off : Int) ≤ off := by
  unfold fwdN; split <;> omega

theorem GzGood.skipFwd {h : Heap} {gs : Nat} {s : GzState} (hG : GzGood h gs s) (t : Int) :
    GzGood (setS h gs (skipFwd s t)) gs (skipFwd s t) :=
  GzGood.withRec hG (Or.inl rfl) rfl rfl rfl rfl (fun hh => hG.memerr hh)

theorem PosInv_skipFwd {s : GzState} (hnn : 0 ≤ s.x.pos.toInt) {t : Int} (ht : SeekOk t) (hfw : s.x.pos.toInt ≤ t) :
    PosInv (skipFwd s t) ∧ (s.past = 0 → tellPos (skipFwd s t) = t) ∧
      (s.past ≠ 0 → tellPos (skipFwd s t) = s.x.pos.toInt + fwdN s (t - s.x.pos.toInt)) := by
  have hOM := OffMax_val
  have ht1 := ht.1
  have ht2 := ht.2
  have h1 := fwdN_le_off (s := s) (off := t - s.x.pos.toInt) (by omega)
  have hlt := s.x.pos.toInt_lt
  obtain ⟨P, hPd⟩ : ∃ P : Int64, P = Int64.ofInt (s.x.pos.toInt + (fwdN s (t - s.x.pos.toInt) : Int)) := ⟨_, rfl⟩
  obtain ⟨K, hKd⟩ : ∃ K : Int64, K = Int64.ofInt (t - s.x.pos.toInt - (fwdN s (t - s.x.pos.toInt) : Int)) := ⟨_, rfl⟩
  have e1 : P.toInt = s.x.pos.toInt + fwdN s (t - s.x.pos.toInt) := by
    rw [hPd]; exact i64_toInt_ofInt (by omega) (by omega)
  have e2 : K.toInt = t - s.x.pos.toInt - fwdN s (t - s.x.pos.toInt) := by
    rw [hKd]; exact i64_toInt_ofInt (by omega) (by omega)
  have hskip : (skipFwd s t).skip = K := by rw [hKd]; rfl
  have hpos : (skipFwd s t).x.pos = P := by rw [hPd]; rfl
  have hpast : (skipFwd s t).past = s.past := rfl
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [hskip, e2]; omega
  · unfold tellPos tellSkip; rw [hpast, hpos]
    by_cases hp : s.past != 0 <;> simp [hp, e1, hskip, e2] <;> omega
  · unfold tellPos tellSkip; rw [hpast, hpos]
    by_cases hp : s.past != 0 <;> simp [hp, e1, hskip, e2] <;> omega
  · intro hp0
    unfold tellPos tellSkip; rw [hpast, hpos]
    simp [hp0, e1, hskip, e2]; omega
  · intro hp0
    unfold tellPos tellSkip; rw [hpast, hpos]
    have : (s.past != 0) = true := by simpa using hp0
    simp [this, e1]

theorem NextOk_skipFwd {h : Heap} {s : GzState} (hN : NextOk h s) (t : Int) : NextOk h (skipFwd s t) := by
  have hle := fwdN_le (s := s) (t - s.x.pos.toInt)
  refine ⟨?_, ?_⟩
  · rcases hN.1 with ⟨hnl, hh0⟩ | ⟨r, a, off, hr, hg, hl⟩
    · have : fwdN s (t - s.x.pos.toInt) = 0 := by rw [hh0] at hle; simpa using hle
      left; refine ⟨?_, ?_⟩
      · show padv s.x.next _ = _; rw [hnl, this]; rfl
      · show s.x.«have» - UInt32.ofNat _ = 0; rw [hh0, this]; rfl
    · right
      refine ⟨r, a, off + fwdN s (t - s.x.pos.toInt), ?_, hg, ?_⟩
      · show padv s.x.next _ = _; rw [hr]; rfl
      · show _ + (s.x.«have» - UInt32.ofNat _).toNat ≤ a.size
        have hh := s.x.«have».toNat_lt
        have hn32 : (UInt32.ofNat (fwdN s (t - s.x.pos.toInt))).toNat = fwdN s (t - s.x.pos.toInt) :=
          UInt32.toNat_ofNat_of_lt' (by have hsz : UInt32.size = 4294967296 := rfl; omega)
        have : (s.x.«have» - UInt32.ofNat (fwdN s (t - s.x.pos.toInt))).toNat = s.x.«have».toNat - fwdN s (t - s.x.pos.toInt) := by
          rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le, hn32]; omega), hn32]
        rw [this]; omega
  · intro b hb
    have : (skipFwd s t).x.next = padv s.x.next (fwdN s (t - s.x.pos.toInt)) := rfl
    rw [this] at hb
    have hb' : ptrBlk s.x.next = some b := by
      cases hp : s.x.next with
      | null => rw [hp] at hb; simp [padv, ptrBlk] at hb
      | ref r o => rw [hp] at hb; cases r <;> simp [padv, ptrBlk] at hb ⊢ <;> exact hb
    have := hN.2 b hb'
    exact this


theorem get_after_free {h : Heap} {s : GzState} (hn : ∀ b, ptrBlk s.x.next = some b → ptrBlk s.msg ≠ some b)
    {r : BRef} {off : Nat} (hr : s.x.next = .ref r off) {a : Array UInt8} (hg : Space.get h r = some a) (gs : Nat)
    (z : GzState) : Space.get (setS (freeStr h s.msg) gs z) r = some a := by
  rw [space_get_setS]
  cases r with
  | blk b =>
    have hb := hn b (by rw [hr]; rfl)
    cases hm : s.msg with
    | null => simpa [hm, freeStr] using hg
    | ref q o =>
      cases q with
      | blk mb =>
        have : mb ≠ b := fun e => hb (by rw [hm, e]; rfl)
        simpa [hm, freeStr, upd_ne _ _ _ _ this.symm] using hg
      | _ => simpa [hm, freeStr] using hg
  | str i => rw [freeStr_get_other _ _ _ (by intro b; simp)]; exact hg
  | dstate_depth i => rw [freeStr_get_other _ _ _ (by intro b; simp)]; exact hg
  | st_dist_code => rw [freeStr_get_other _ _ _ (by intro b; simp)]; exact hg
  | st_length_code => rw [freeStr_get_other _ _ _ (by intro b; simp)]; exact hg

/-- After a call that frees the message block and leaves `x.next` alone, `x.next` is still usable. -/
theorem NextOk_free {h : Heap} {s s' : GzState} (hN : NextOk h s) (gs : Nat) (z : GzState)
    (hnx : s'.x.next = s.x.next) (hhv : s'.x.«have».toNat ≤ s.x.«have».toNat)
    (hnull : s'.x.next = .null → s'.x.«have» = 0) (hm : s'.msg = .null) :
    NextOk (setS (freeStr h s.msg) gs z) s' := by
  refine ⟨?_, ?_⟩
  · rcases hN.1 with ⟨hnl, hh0⟩ | ⟨r, a, off, hr, hg, hl⟩
    · exact Or.inl ⟨by rw [hnx]; exact hnl, hnull (by rw [hnx]; exact hnl)⟩
    · exact Or.inr ⟨r, a, off, by rw [hnx]; exact hr, get_after_free hN.2 hr hg gs z, by omega⟩
  · intro b hb; rw [hm]; simp [ptrBlk]

theorem PosInv_resetRec (s : GzState) : PosInv (resetRec s) ∧ tellPos (resetRec s) = 0 := by
  have e1 : (resetRec s).skip = 0 := by unfold resetRec; split <;> rfl
  have e2 : (resetRec s).x.pos = 0 := by unfold resetRec; split <;> rfl
  have e3 : (resetRec s).past = 0 := by unfold resetRec; split <;> rfl
  have z0 : (0 : Int64).toInt = 0 := rfl
  have ht : tellPos (resetRec s) = 0 := by
    unfold tellPos tellSkip; rw [e2, e3]; simp [z0, e1]
  exact ⟨⟨by rw [e1, z0]; omega, by rw [ht]; omega, by rw [ht]; omega⟩, ht⟩

theorem GzGood.afterCopy {h : Heap} {gs : Nat} {s : GzState} (hG : GzGood h gs s) (t : Int) :
    GzGood (setS (freeStr h s.msg) gs (copyRec s t)) gs (copyRec s t) := by
  have h1 := GzGood.withRec (GzGood.afterErr hG Z_OK) (s' := copyRec s t) (Or.inl rfl) rfl rfl rfl rfl (fun _ => rfl)
  simpa using h1

theorem PosInv_copyRec (s : GzState) {t : Int} (ht : SeekOk t) : PosInv (copyRec s t) ∧ tellPos (copyRec s t) = t := by
  have hOM := OffMax_val
  have ht1 := ht.1
  have ht2 := ht.2
  have e1 : (copyRec s t).skip = 0 := rfl
  have e2 : (copyRec s t).x.pos = Int64.ofInt t := rfl
  have e3 : (copyRec s t).past = 0 := rfl
  have z0 : (0 : Int64).toInt = 0 := rfl
  have hq : (Int64.ofInt t).toInt = t := i64_toInt_ofInt (by omega) (by omega)
  have htt : tellPos (copyRec s t) = t := by
    unfold tellPos tellSkip; rw [e2, e3]; simp [z0, e1, hq, -Int64.toInt_ofInt]
  exact ⟨⟨by rw [e1, z0]; omega, by rw [htt]; omega, by rw [htt]; omega⟩, htt⟩


theorem sameCfg_refl (s : GzState) : SameCfg s s := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem SameCfg.trans {a b c : GzState} (h1 : SameCfg a b) (h2 : SameCfg b c) : SameCfg a c := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := h1
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩ := h2
  exact ⟨b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4, b5.trans a5, b6.trans a6, b7.trans a7, b8.trans a8,
    b9.trans a9, b10.trans a10, b11.trans a11⟩

theorem sameCfg_resetRec (s : GzState) : SameCfg s (resetRec s) := by
  unfold resetRec; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem sameCfg_skipFwd (s : GzState) (t : Int) : SameCfg s (skipFwd s t) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem sameCfg_copyRec (s : GzState) (t : Int) : SameCfg s (copyRec s t) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem NextOk_setS {h : Heap} {s' : GzState} (hN : NextOk h s') (gs : Nat) (z : GzState) : NextOk (setS h gs z) s' := by
  refine ⟨?_, hN.2⟩
  rcases hN.1 with hn | ⟨r, a, off, hr, hg, hl⟩
  · exact Or.inl hn
  · exact Or.inr ⟨r, a, off, hr, by rw [space_get_setS]; exact hg, hl⟩

theorem seek_write_safe {h : Heap} {gs : Nat} {s : GzState} (hG : GzGood h gs s) (hP : PosInv s)
    (hnn : 0 ≤ s.x.pos.toInt) (he : s.err = Z_OK ∨ s.err = Z_BUF_ERROR) {whence : Int32}
    (hw : whence = SEEK_SET ∨ whence = SEEK_CUR) (hm : s.mode = GZ_WRITE) (hN : NextOk h s) (offset : Int64) (fs : Fs) :
    ∃ r h' s', gzseek64 (hnd gs) offset whence fs h = .ok ((r, fs), h') ∧ SeekPost h gs s (seekT s offset whence) r h' s' := by
  have hrun := gzseek64_write_run hG hP hnn he hw hm offset fs
  have hOM := OffMax_val
  by_cases hc : SeekOk (seekT s offset whence) ∧ s.x.pos.toInt ≤ seekT s offset whence
  · rw [if_pos hc] at hrun
    obtain ⟨⟨ht1, ht2⟩, hfw⟩ := hc
    have hlt := s.x.pos.toInt_lt
    have eK : (Int64.ofInt (seekT s offset whence - s.x.pos.toInt)).toInt = seekT s offset whence - s.x.pos.toInt :=
      i64_toInt_ofInt (by omega) (by omega)
    obtain ⟨K, hKd⟩ : ∃ K : Int64, K = Int64.ofInt (seekT s offset whence - s.x.pos.toInt) := ⟨_, rfl⟩
    rw [← hKd] at hrun
    have eK' : K.toInt = seekT s offset whence - s.x.pos.toInt := by rw [hKd]; exact eK
    have hG' := GzGood.withRec hG (s' := { s with skip := K }) (Or.inl rfl) rfl rfl rfl rfl (fun hh => hG.memerr hh)
    have hts : ∀ pp : Int, tellPos { s with skip := K } = (if s.past != 0 then s.x.pos.toInt else s.x.pos.toInt + K.toInt) := by
      intro _; unfold tellPos tellSkip; by_cases hp : s.past != 0 <;> simp [hp]
    refine ⟨_, _, { s with skip := K }, hrun, hG', ⟨?_, ?_, ?_⟩, NextOk_setS hN gs _, ?_, Or.inr ⟨⟨ht1, ht2⟩, ?_, ?_, ?_⟩⟩
    · exact eK' ▸ (by omega)
    · rw [hts 0]; split <;> omega
    · rw [hts 0]; split <;> omega
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · exact i64_toInt_ofInt (by omega) (by omega)
    · intro hp0; rw [hts 0]; have : ¬ (s.past != 0) = true := by simpa using hp0
      simp [this]; omega
    · intro hp0; have : (s.past != 0) = true := by simpa using hp0
      rw [hts 0]; simp [this]; omega
  · rw [if_neg hc] at hrun
    exact ⟨_, _, s, hrun, hG, hP, hN, sameCfg_refl s, Or.inl ⟨rfl, rfl, rfl⟩⟩


theorem skipFwd_pos {s : GzState} (hnn : 0 ≤ s.x.pos.toInt) {t : Int} (ht : SeekOk t) (hfw : s.x.pos.toInt ≤ t) :
    (skipFwd s t).x.pos.toInt = s.x.pos.toInt + fwdN s (t - s.x.pos.toInt) ∧ (skipFwd s t).x.pos.toInt ≤ t := by
  have hOM := OffMax_val
  have ht1 := ht.1
  have ht2 := ht.2
  have h1 := fwdN_le_off (s := s) (off := t - s.x.pos.toInt) (by omega)
  have hlt := s.x.pos.toInt_lt
  have e : (skipFwd s t).x.pos.toInt = s.x.pos.toInt + fwdN s (t - s.x.pos.toInt) :=
    i64_toInt_ofInt (by omega) (by omega)
  exact ⟨e, by omega⟩

theorem tell_past {s : GzState} (hp : s.past ≠ 0) : tellPos s = s.x.pos.toInt := by
  have : (s.past != 0) = true := by simpa using hp
  unfold tellPos tellSkip; simp [this]

theorem seek_fwd_safe {h : Heap} {gs : Nat} {s : GzState} (hG : GzGood h gs s) (hP : PosInv s)
    (hnn : 0 ≤ s.x.pos.toInt) (he : s.err = Z_OK ∨ s.err = Z_BUF_ERROR) {whence : Int32}
    (hw : whence = SEEK_SET ∨ whence = SEEK_CUR) (hm : s.mode = GZ_READ) (hhow : s.how ≠ GZ_COPY) (hN : NextOk h s)
    (offset : Int64) (fs : Fs) (ht : SeekOk (seekT s offset whence)) (hfw : s.x.pos.toInt ≤ seekT s offset whence) :
    ∃ r h' s', gzseek64 (hnd gs) offset whence fs h = .ok ((r, fs), h') ∧ SeekPost h gs s (seekT s offset whence) r h' s' := by
  have hhead := gzseek64_head hG hP hnn he hw offset fs
  rw [if_pos ht, seekTail_fwd hG hm hhow hnn ht hfw hN fs] at hhead
  have hpp := PosInv_skipFwd hnn ht hfw
  have hps := skipFwd_pos hnn ht hfw
  have hq : (Int64.ofInt (seekT s offset whence)).toInt = seekT s offset whence :=
    i64_toInt_ofInt (by have := ht.1; omega) (by have := ht.2; have := OffMax_val; omega)
  refine ⟨_, _, skipFwd s (seekT s offset whence), hhead, GzGood.skipFwd hG _, hpp.1,
    NextOk_setS (NextOk_skipFwd hN _) gs _, sameCfg_skipFwd _ _, Or.inr ⟨ht, hq, hpp.2.1, ?_⟩⟩
  intro hp0
  have hpast : (skipFwd s (seekT s offset whence)).past ≠ 0 := hp0
  exact ⟨tell_past hpast, hps.2⟩


theorem seek_copy_safe {h : Heap} {gs : Nat} {s : GzState} (hG : GzGood h gs s) (hP : PosInv s)
    (hnn : 0 ≤ s.x.pos.toInt) (he : s.err = Z_OK ∨ s.err = Z_BUF_ERROR) {whence : Int32}
    (hw : whence = SEEK_SET ∨ whence = SEEK_CUR) (hm : s.mode = GZ_READ) (hcopy : s.how = GZ_COPY) (hN : NextOk h s)
    (offset : Int64) (fs : Fs) (ht : SeekOk (seekT s offset whence))
    (hraw : -9223372036854775808 ≤ seekT s offset whence - s.x.pos.toInt - s.x.«have».toNat) :
    ∃ r fs' h', gzseek64 (hnd gs) offset whence fs h = .ok ((r, fs'), h') ∧
      (∃ s', SeekPost h gs s (seekT s offset whence) r h' s') := by
  have hhead := gzseek64_head hG hP hnn he hw offset fs
  rw [if_pos ht, seekTail_copy hG hm hcopy hnn ht hraw fs] at hhead
  have hq : (Int64.ofInt (seekT s offset whence)).toInt = seekT s offset whence :=
    i64_toInt_ofInt (by have := ht.1; omega) (by have := ht.2; have := OffMax_val; omega)
  by_cases hl : (lseekRes s.fd (Int64.ofInt (seekT s offset whence - s.x.pos.toInt - s.x.«have».toNat)) SEEK_CUR fs).1 = -1
  · rw [if_pos hl] at hhead
    exact ⟨_, _, _, hhead, s, hG, hP, hN, sameCfg_refl s, Or.inl ⟨rfl, rfl, rfl⟩⟩
  · rw [if_neg hl] at hhead
    have hpc := PosInv_copyRec s ht
    refine ⟨_, _, _, hhead, copyRec s (seekT s offset whence), GzGood.afterCopy hG _, hpc.1,
      NextOk_free hN gs _ rfl (by show (0 : UInt32).toNat ≤ _; simp) (fun _ => rfl) rfl, sameCfg_copyRec _ _,
      Or.inr ⟨ht, hq, fun _ => hpc.2, fun hp0 => absurd rfl hp0⟩⟩

theorem fwdN_reset (s : GzState) {t : Int} (ht : 0 ≤ t) : fwdN (resetRec s) (t - (resetRec s).x.pos.toInt) = 0 := by
  have e1 : (resetRec s).x.«have» = 0 := by unfold resetRec; split <;> rfl
  have e2 : (resetRec s).x.pos = 0 := by unfold resetRec; split <;> rfl
  have z0 : (0 : Int64).toInt = 0 := rfl
  unfold fwdN; rw [e1, e2, z0]; simp; omega

theorem seek_back_safe {h : Heap} {gs : Nat} {s : GzState} (hG : GzGood h gs s) (hP : PosInv s)
    (hnn : 0 ≤ s.x.pos.toInt) (he : s.err = Z_OK ∨ s.err = Z_BUF_ERROR) {whence : Int32}
    (hw : whence = SEEK_SET ∨ whence = SEEK_CUR) (hm : s.mode = GZ_READ) (hhow : s.how ≠ GZ_COPY) (hN : NextOk h s)
    (offset : Int64) (fs : Fs) (ht : SeekOk (seekT s offset whence)) (hlt : seekT s offset whence < s.x.pos.toInt) :
    ∃ r fs' h', gzseek64 (hnd gs) offset whence fs h = .ok ((r, fs'), h') ∧
      (∃ s', SeekPost h gs s (seekT s offset whence) r h' s') := by
  have hhead := gzseek64_head hG hP hnn he hw offset fs
  rw [if_pos ht, seekTail_back hG hm hhow he hnn ht hlt hN fs] at hhead
  have hq : (Int64.ofInt (seekT s offset whence)).toInt = seekT s offset whence :=
    i64_toInt_ofInt (by have := ht.1; omega) (by have := ht.2; have := OffMax_val; omega)
  by_cases hl : (lseekRes s.fd s.start SEEK_SET fs).1 = -1
  · rw [if_pos hl] at hhead
    exact ⟨_, _, _, hhead, s, hG, hP, hN, sameCfg_refl s, Or.inl ⟨rfl, rfl, rfl⟩⟩
  · rw [if_neg hl] at hhead
    have hz : (resetRec s).x.pos.toInt = 0 := by
      have e2 : (resetRec s).x.pos = 0 := by unfold resetRec; split <;> rfl
      rw [e2]; rfl
    have hfw : (resetRec s).x.pos.toInt ≤ seekT s offset whence := by rw [hz]; exact ht.1
    have hpp := PosInv_skipFwd (s := resetRec s) (by rw [hz]; exact Int.le_refl 0) ht hfw
    have hF := fwdN_reset s ht.1
    have hGr := GzGood.skipFwd (GzGood.afterReset hG) (seekT s offset whence)
    simp only [setS_setS] at hGr
    have hpast : (resetRec s).past = 0 := by unfold resetRec; split <;> rfl
    refine ⟨_, _, _, hhead, skipFwd (resetRec s) (seekT s offset whence), hGr, hpp.1, ?_,
      SameCfg.trans (sameCfg_resetRec s) (sameCfg_skipFwd _ _), Or.inr ⟨ht, hq, fun _ => hpp.2.1 hpast, fun hp0 => absurd hpast hp0⟩⟩
    refine NextOk_free hN gs _ ?_ ?_ ?_ rfl
    · show padv (resetRec s).x.next _ = _
      rw [hF]; unfold resetRec; split <;> simp [padv_zero]
    · show ((resetRec s).x.«have» - _).toNat ≤ _
      have e1 : (resetRec s).x.«have» = 0 := by unfold resetRec; split <;> rfl
      rw [e1]; rw [hF]; simp
    · intro _
      show (resetRec s).x.«have» - _ = 0
      have e1 : (resetRec s).x.«have» = 0 := by unfold resetRec; split <;> rfl
      rw [e1, hF]; rfl


/-- `gzseek64(NULL, offset, whence)` returns -1; the world and the heap are unchanged. -/
theorem gzseek64_null (offset : Int64) (whence : Int32) (fs : Fs) (h : Heap) :
    gzseek64 none offset whence fs h = .ok ((-1, fs), h) := rfl

/-- **gzseek64, safety and effect** (reachable states with `x.pos ≥ 0`: no `gzungetc` right after `gzopen`, the case
the unpatched C faults in; `NextOk`: `x.next` is not dangling; `hraw`: positions within `2^32` of `2^63`).
The call does not fault; on success the handle satisfies the invariants again; the result is `-1` and nothing but the
world changed, or it is the target `t` (the position `gztell64` reports is `t`, except after a read past the end). -/
theorem gzseek64_safe {h : Heap} {gs : Nat} {s : GzState} (hG : GzGood h gs s) (hP : PosInv s)
    (hnn : 0 ≤ s.x.pos.toInt) (he : s.err = Z_OK ∨ s.err = Z_BUF_ERROR) {whence : Int32}
    (hw : whence = SEEK_SET ∨ whence = SEEK_CUR) (hN : NextOk h s) (offset : Int64) (fs : Fs)
    (hraw : s.mode = GZ_READ → s.how = GZ_COPY → SeekOk (seekT s offset whence) →
      -9223372036854775808 ≤ seekT s offset whence - s.x.pos.toInt - s.x.«have».toNat) :
    ∃ r fs' h' s', gzseek64 (hnd gs) offset whence fs h = .ok ((r, fs'), h') ∧
      SeekPost h gs s (seekT s offset whence) r h' s' := by
  by_cases ht : SeekOk (seekT s offset whence)
  · rcases hG.mode with hm | hm
    · by_cases hc : s.how = GZ_COPY
      · obtain ⟨r, fs', h', e, s', hp⟩ := seek_copy_safe hG hP hnn he hw hm hc hN offset fs ht (hraw hm hc ht)
        exact ⟨r, fs', h', s', e, hp⟩
      · by_cases hb : seekT s offset whence < s.x.pos.toInt
        · obtain ⟨r, fs', h', e, s', hp⟩ := seek_back_safe hG hP hnn he hw hm hc hN offset fs ht hb
          exact ⟨r, fs', h', s', e, hp⟩
        · obtain ⟨r, h', s', e, hp⟩ := seek_fwd_safe hG hP hnn he hw hm hc hN offset fs ht (by omega)
          exact ⟨r, fs, h', s', e, hp⟩
    · obtain ⟨r, h', s', e, hp⟩ := seek_write_safe hG hP hnn he hw hm hN offset fs
      exact ⟨r, fs, h', s', e, hp⟩
  · have hhead := gzseek64_head hG hP hnn he hw offset fs
    rw [if_neg ht] at hhead
    exact ⟨_, _, _, s, hhead, hG, hP, hN, sameCfg_refl s, Or.inl ⟨rfl, rfl, rfl⟩⟩

/-- `gzseek64` refuses a handle with a serious error, and a `whence` other than `SEEK_SET` and `SEEK_CUR`: `-1`,
nothing changes. -/
theorem gzseek64_refuse {h : Heap} {gs : Nat} {s : GzState} (hG : GzGood h gs s) {whence : Int32} (offset : Int64) (fs : Fs)
    (hb : (s.err ≠ Z_OK ∧ s.err ≠ Z_BUF_ERROR) ∨ (whence ≠ SEEK_SET ∧ whence ≠ SEEK_CUR)) :
    gzseek64 (hnd gs) offset whence fs h = .ok ((-1, fs), h) := by
  have hs := hG.hs
  have hmo : ¬ (s.mode ≠ GZ_READ ∧ s.mode ≠ GZ_WRITE) := by rcases hG.mode with h1 | h1 <;> simp [h1]
  unfold gzseek64
  rcases hb with hb | hb
  · ggsimp [hs, hmo, hb]
  · by_cases he : ¬ s.err = Z_OK ∧ ¬ s.err = Z_BUF_ERROR
    · ggsimp [hs, hmo, he]
    · ggsimp [hs, hmo, he, hb]

/-- `gzseek` is `gzseek64` (`z_off_t` is `long`: the range check `ret == (z_off_t)ret` always holds). -/
theorem gzseek_eq (file : GzFilePtr) (offset : Int64) (whence : Int32) (fs : Fs) (h : Heap) :
    gzseek file offset whence fs h = gzseek64 file offset whence fs h := by
  unfold gzseek
  simp only [G_bind_app]
  cases hh : gzseek64 file offset whence fs h with
  | error e => rfl
  | ok v => obtain ⟨⟨a, fs1⟩, h1⟩ := v; simp [G_pure_app]


/-! ### The undefined behaviour of the unpatched C (R-1)

`gzseek(file, offset, SEEK_CUR)` while `gztell` is negative (right after `gzungetc` at the start of a file): the check
`offset > GZ_OFF_MAX - pos` computes `GZ_OFF_MAX - pos` with `pos < 0`, which overflows. And `gzseek(file, offset,
SEEK_SET)` with a negative `x.pos` and `offset - x.pos >= 2^63`: the subtraction `pos - x.pos` overflows. Both are
`Fault.ub` in the translation. -/

/-- The undefined behaviour of the unpatched C (the negative-position seek report in `docs/findings.md`): `SEEK_CUR` while `gztell` is negative (after `gzungetc` at the start of a file) makes `GZ_OFF_MAX - pos` overflow: `Fault.ub`, for every `offset`. -/
theorem gzseek64_cur_negpos_ub {h : Heap} {gs : Nat} {s : GzState} (hG : GzGood h gs s)
    (he : s.err = Z_OK ∨ s.err = Z_BUF_ERROR) (hneg : tellPos s < 0) (hlo : -9223372036854775808 ≤ tellPos s)
    (offset : Int64) (fs : Fs) :
    gzseek64 (hnd gs) offset SEEK_CUR fs h = .error (.ub "signed overflow (long)") := by
  have hs := hG.hs
  have hOM := OffMax_val
  have hne : ¬(¬ s.err = Z_OK ∧ ¬ s.err = Z_BUF_ERROR) := by rcases he with h1 | h1 <;> simp [h1]
  have hmo : ¬ (s.mode ≠ GZ_READ ∧ s.mode ≠ GZ_WRITE) := by rcases hG.mode with h1 | h1 <;> simp [h1]
  have hSC : SEEK_CUR ≠ SEEK_SET := by decide
  have eT : i64add s.x.pos (if s.past = 0 then s.skip else 0) h = .ok (Int64.ofInt (tellPos s), h) := by
    have := i64add_run s.x.pos (tellSkip s) (by unfold tellPos at hlo; omega) (by unfold tellPos at hneg; omega) h
    by_cases hh : s.past = 0
    · simpa [hh, tellSkip, tellPos] using this
    · simpa [hh, tellSkip, tellPos] using this
  have hp0 : (Int64.ofInt (tellPos s)).toInt = tellPos s := i64_toInt_ofInt hlo (by omega)
  have hg := GZ_OFF_MAX_toInt
  have fo : i64sub GZ_OFF_MAX (Int64.ofInt (tellPos s)) h = .error (.ub "signed overflow (long)") :=
    i64sub_ub _ _ h (by rw [hp0, hg]; omega)
  unfold gzseek64
  ggsimp [hs, hmo, hne, hSC, eT, fo]

/-- The undefined behaviour of the unpatched C: `SEEK_SET` at a negative `x.pos` with `offset - x.pos >= 2^63` makes `pos - x.pos` overflow: `Fault.ub`. -/
theorem gzseek64_set_negpos_ub {h : Heap} {gs : Nat} {s : GzState} (hG : GzGood h gs s)
    (he : s.err = Z_OK ∨ s.err = Z_BUF_ERROR) (hneg : s.x.pos.toInt < 0) (offset : Int64) (hoff : 0 ≤ offset.toInt)
    (hbig : 9223372036854775808 ≤ offset.toInt - s.x.pos.toInt) (fs : Fs) :
    gzseek64 (hnd gs) offset SEEK_SET fs h = .error (.ub "signed overflow (long)") := by
  have hs := hG.hs
  have hOM := OffMax_val
  have hne : ¬(¬ s.err = Z_OK ∧ ¬ s.err = Z_BUF_ERROR) := by rcases he with h1 | h1 <;> simp [h1]
  have hmo : ¬ (s.mode ≠ GZ_READ ∧ s.mode ≠ GZ_WRITE) := by rcases hG.mode with h1 | h1 <;> simp [h1]
  have hSC : SEEK_SET ≠ SEEK_CUR := by decide
  have z0 : (0 : Int64).toInt = 0 := rfl
  have hlt := offset.toInt_lt
  have hgt := s.x.pos.le_toInt
  obtain ⟨q1, q3, f1, f3, c1, c2, c5⟩ := seek_checks (p0 := 0) offset (by rw [z0]; exact Int.le_refl 0) h
  rw [z0] at c1 c2 c5
  obtain ⟨q5, f5, hq5, hq5i⟩ := c5 (by omega) (by omega)
  have c6 : ¬ (q5 < s.x.pos) := by rw [i64_lt_iff, hq5i]; omega
  have fo : ∀ h', i64sub q5 s.x.pos h' = .error (.ub "signed overflow (long)") := fun h' =>
    i64sub_ub _ _ h' (by rw [hq5i]; omega)
  unfold gzseek64
  have r1 : ¬ OffMax < offset.toInt := by omega
  have r2 : ¬ offset.toInt < 0 := by omega
  by_cases hc : s.mode = GZ_READ ∧ s.how = GZ_COPY
  · ggsimp [hs, hmo, hne, hSC, f1, f3, f5, c1, c2, c6, fo, r1, r2, hc]
  · ggsimp [hs, hmo, hne, hSC, f1, f3, f5, c1, c2, c6, fo, r1, r2, hc]


/-- **The dangling `x.next` (R-4).** A reader that is not in the raw area executes `x.next += n` on every forward seek;
when `x.next` points to an object that no longer exists (the caller's buffer after a direct decompression, freed by the
caller), the translation faults, although `n` is 0 and nothing is read through the pointer. Every other fault of the
translation is excluded by the hypotheses. -/
theorem seekTail_dangling_ub {h : Heap} {gs : Nat} {s : GzState} (hG : GzGood h gs s) (hm : s.mode = GZ_READ)
    (hhow : s.how ≠ GZ_COPY) (hnn : 0 ≤ s.x.pos.toInt) {t : Int} (ht : SeekOk t) (hfw : s.x.pos.toInt ≤ t)
    {r : BRef} {off : Nat} (hr : s.x.next = .ref r off) (hd : Space.get h r = none) (fs : Fs) :
    seekTail (hnd gs) s (Int64.ofInt t) fs h = .error (.ub "arithmetic on a dangling pointer") := by
  have hs := hG.hs
  have hOM := OffMax_val
  have ht1 := ht.1
  have ht2 := ht.2
  have hqi : (Int64.ofInt t).toInt = t := i64_toInt_ofInt (by omega) (by omega)
  obtain ⟨q, hqd⟩ : ∃ q : Int64, q = Int64.ofInt t := ⟨_, rfl⟩
  have hqi' : q.toInt = t := by rw [hqd]; exact hqi
  obtain ⟨q2, hq2d⟩ : ∃ q2 : Int64, q2 = Int64.ofInt (t - s.x.pos.toInt) := ⟨_, rfl⟩
  have hlt := s.x.pos.toInt_lt
  have hq2 : q2.toInt = t - s.x.pos.toInt := by
    rw [hq2d]; exact i64_toInt_ofInt (by omega) (by omega)
  have fa : ∀ h', i64sub q s.x.pos h' = .ok (q2, h') := fun h' => by
    have := i64sub_run q s.x.pos (by rw [hqi']; omega) (by rw [hqi']; omega) h'
    rw [hqi', ← hq2d] at this; exact this
  have c6 : ¬ (q < s.x.pos) := by rw [i64_lt_iff, hqi']; omega
  have fn : ∀ (k : Int) (z : GzState), Ptr.add s.x.next k (setS h gs z) = .error (.ub "arithmetic on a dangling pointer") := by
    intro k z
    rw [hr]
    have : Space.get (setS h gs z) r = none := by rw [space_get_setS]; exact hd
    simp [Ptr.add, this]
  rw [← hqd]
  unfold seekTail
  ggsimp [hs, hm, hhow, fa, c6, GT_OFF_run, fn]
  by_cases hc : q2 < u32ToI64 s.x.«have»
  · ggsimp [hs, hc, fn]
  · ggsimp [hs, hc, fn]


/-- The dangling `x.next` (the borrowed seek-pointer report in `docs/findings.md`): a forward seek of a reader outside the raw area executes `x.next += n` on a pointer to an object that no longer exists: `Fault.ub`, although nothing is read through it. -/
theorem gzseek64_dangling_next_ub {h : Heap} {gs : Nat} {s : GzState} (hG : GzGood h gs s) (hP : PosInv s)
    (hnn : 0 ≤ s.x.pos.toInt) (he : s.err = Z_OK ∨ s.err = Z_BUF_ERROR) {whence : Int32}
    (hw : whence = SEEK_SET ∨ whence = SEEK_CUR) (hm : s.mode = GZ_READ) (hhow : s.how ≠ GZ_COPY)
    (offset : Int64) (fs : Fs) (ht : SeekOk (seekT s offset whence)) (hfw : s.x.pos.toInt ≤ seekT s offset whence)
    {r : BRef} {off : Nat} (hr : s.x.next = .ref r off) (hd : Space.get h r = none) :
    gzseek64 (hnd gs) offset whence fs h = .error (.ub "arithmetic on a dangling pointer") := by
  rw [gzseek64_head hG hP hnn he hw offset fs, if_pos ht, seekTail_dangling_ub hG hm hhow hnn ht hfw hr hd fs]

/-- A seek inside the raw area faults exactly when `hraw` of `seekTail_copy` fails: the C expression
`pos - x.pos - have` overflows (positions within `2^32` of `2^63`). -/
theorem seekTail_copy_ub {h : Heap} {gs : Nat} {s : GzState} (hG : GzGood h gs s) (hm : s.mode = GZ_READ)
    (hcopy : s.how = GZ_COPY) (hnn : 0 ≤ s.x.pos.toInt) {t : Int} (ht : SeekOk t)
    (hraw : t - s.x.pos.toInt - s.x.«have».toNat < -9223372036854775808) (fs : Fs) :
    seekTail (hnd gs) s (Int64.ofInt t) fs h = .error (.ub "signed overflow (long)") := by
  have hs := hG.hs
  have hOM := OffMax_val
  have ht1 := ht.1
  have ht2 := ht.2
  have hhv := s.x.«have».toNat_lt
  have hlt := s.x.pos.toInt_lt
  have hqi : (Int64.ofInt t).toInt = t := i64_toInt_ofInt (by omega) (by omega)
  obtain ⟨q2, hq2d⟩ : ∃ q2 : Int64, q2 = Int64.ofInt (t - s.x.pos.toInt) := ⟨_, rfl⟩
  have hq2 : q2.toInt = t - s.x.pos.toInt := by
    rw [hq2d]; exact i64_toInt_ofInt (by omega) (by omega)
  have fa : i64sub (Int64.ofInt t) s.x.pos h = .ok (q2, h) := by
    have := i64sub_run (Int64.ofInt t) s.x.pos (by rw [hqi]; omega) (by rw [hqi]; omega) h
    rw [hqi, ← hq2d] at this; exact this
  have fb : i64sub q2 (u32ToI64 s.x.«have») h = .error (.ub "signed overflow (long)") :=
    i64sub_ub _ _ h (by rw [hq2, u32ToI64_toInt]; omega)
  unfold seekTail
  ggsimp [hs, hm, hcopy, fa, fb]

end Zlib.Gzlib.Proofs
