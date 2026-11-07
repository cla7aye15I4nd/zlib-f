import ZlibF.Proof.«inflate.c.main.check0»
import ZlibF.Proof.«crc32.c»
import ZlibF.Proof.«adler32.c»

/-!
# inflate.c: the trailer modes `LENGTH` and `CHECK`

`case LENGTH:` and `case CHECK:` of `inflate()`, and the fall-through `DONE`. Every exit and every error message.
`CHECK` calls `crc32` or `adler32` on the output written by this call; the callee theorems `crc32_z_correct` and
`adler32_z_correct` give the value.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec

/-- `UPDATE_CHECK(check, buf, len)` on `len` bytes of a byte block: the CRC-32 of the bytes when `state->flags` is set, else the
Adler-32 (`crc32` / `adler32` of `zlib.h`). No fault, the heap is unchanged. The Adler-32 value is the specification's
whenever `len ≠ 1` or the high half of `check` is a canonical sum (`< 65521`: true of every value `adler32` returns); for `len = 1`
and a non-canonical `check` the value is whatever `adler32` computes. `StaticsOK`: the static CRC tables of the heap hold their
contents. -/
theorem UPDATE_CHECK_run {h : Heap} {zs : Nat} {s : InflateState} {blk off : Nat} {a : Array UInt8} {len : UInt32}
    (hS : Zlib.Crc32.Proofs.StaticsOK h) (hs : h.istates zs = some s) (hb : h.bytes blk = some a)
    (hfit : off + len.toNat ≤ a.size) (check : UInt64) :
    ∃ v, UPDATE_CHECK (some (.tab zs)) check (.ref (.blk blk) off) len h = .ok (v, h) ∧
      (s.flags ≠ 0 → v = (ZlibF.Spec.crc32Update check.toUInt32 ((a.toList.drop off).take len.toNat)).toUInt64) ∧
      (s.flags = 0 → (len ≠ 1 ∨ (check >>> 16 &&& 65535).toNat < 65521) →
        v.toNat = Zlib.Adler32.Spec.adler32 check.toNat (Zlib.Adler32.Proofs.seg a off len.toNat)) := by
  by_cases hf : s.flags = 0
  · have hL : len.toNat < 2 ^ 64 := by have := UInt32.toNat_lt len; omega
    have e64 : len.toNat.toUInt64 = len.toUInt64 := by simp
    obtain ⟨v, hv⟩ := Zlib.Adler32.Proofs.adler32_safe h blk a hb check off len.toNat hfit (UInt32.toNat_lt len)
    have e32 : len.toNat.toUInt32 = len := by simp at *
    rw [e32] at hv
    refine ⟨v, ?_, fun h1 => absurd hf h1, fun _ hv' => ?_⟩
    · unfold UPDATE_CHECK
      simp [bind_app, rdI_eq, hs, hf]
      exact hv
    · by_cases h1 : len = 1
      · subst h1
        have hv2 := hv'.resolve_left (by simp)
        have := Zlib.Adler32.Proofs.adler32_z_correct h blk a hb check off 1 hfit (by decide) hv2
        obtain ⟨r, hr, hrv⟩ := this
        have hv1 : C.run (Zlib.Adler32.adler32 check (.ref (.blk blk) off) 1) h = .ok (v, h) := hv
        unfold Zlib.Adler32.adler32 at hv1
        have : (1 : UInt32).toUInt64 = (1 : Nat).toUInt64 := rfl
        rw [this] at hv1
        rw [hr] at hv1
        cases hv1
        exact hrv
      · obtain ⟨r, hr, hrv⟩ := Zlib.Adler32.Proofs.adler32_z_correct_ne_one h blk a hb check off len.toNat hfit hL
          (fun e => h1 (by apply UInt32.toNat_inj.mp; simpa using e))
        have hv1 : C.run (Zlib.Adler32.adler32 check (.ref (.blk blk) off) len) h = .ok (v, h) := hv
        unfold Zlib.Adler32.adler32 at hv1
        rw [show len.toUInt64 = len.toNat.toUInt64 by simp, hr] at hv1
        cases hv1
        exact hrv
  · obtain hc := Zlib.Crc32.Proofs.crc32_correct h hS check blk off a hb len hfit
    refine ⟨_, ?_, fun _ => rfl, fun h1 => absurd h1 hf⟩
    unfold UPDATE_CHECK
    have hf' : ¬ s.flags = 0 := hf
    simp [bind_app, rdI_eq, hs, hf']
    exact hc

/-- `case LENGTH:` with no length to check (`wrap = 0` or `flags = 0`): `state->mode = DONE; ret = Z_STREAM_END;
goto inf_leave`. -/
theorem inflate_LENGTH_skip {c : Ctx} {l : IL} {h : Heap} {zs : Nat} {s : InflateState}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s) (hno : s.wrap = 0 ∨ s.flags = 0) :
    runX (inflate_LENGTH c) l h =
      .ok ((.error Ex.leave, { l with ret := Z_STREAM_END }), setI h zs { s with mode := DONE }) := by
  have hb : ¬ (¬ s.wrap = 0 ∧ ¬ s.flags = 0) := by
    rcases hno with e | e <;> simp [e]
  unfold inflate_LENGTH
  rw [hc]
  simp [runX_bind, runX_lift, ldI_eq, hs, hb, runX_pure, setMode, wrI_eq, inflate_DONE, runX_modify, runX_throw]

/-- `case LENGTH:` with a length to check (`wrap ≠ 0`, `flags ≠ 0`): `NEEDBITS(32)`; if the input ran out, `goto inf_leave` with
the registers of that moment; else, when `(wrap & 4)` is set and `hold` differs from the low 32 bits of `total`, the error
"incorrect length check" (`BAD`, `break`); else `INITBITS`, `mode = DONE`, `ret = Z_STREAM_END`, `goto inf_leave`.
`bs` are the input bytes not yet pulled; the bit stream is preserved. -/
theorem inflate_LENGTH_run {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {bs : List UInt8} (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (hz : r.get h = some z)
    (hs : h.istates zs = some s) (hw : s.wrap ≠ 0) (hf : s.flags ≠ 0) (B : BitInv h l bs) :
    ∃ rr l' j, runX (NEEDBITS 32) l h = .ok ((rr, l'), h) ∧ j ≤ bs.length ∧ BitInv h l' (bs.drop j) ∧
      stream l' (bs.drop j) = stream l bs ∧
      (rr = .error Ex.leave → l'.have_ = 0 ∧ j = bs.length ∧ l'.bits.toNat < 32 ∧
        runX (inflate_LENGTH c) l h = .ok ((.error Ex.leave, l'), h)) ∧
      (rr = .ok () → 32 ≤ l'.bits.toNat ∧
        ((s.wrap &&& 4) ≠ 0 → l'.hold ≠ (s.total &&& 0xffffffff) →
          ∃ i, strTable[i]? = some "incorrect length check" ∧
            runX (inflate_LENGTH c) l h = .ok ((.ok (), l'), tcBadHeap h r zs z s i)) ∧
        (¬ ((s.wrap &&& 4) ≠ 0 ∧ l'.hold ≠ (s.total &&& 0xffffffff)) →
          runX (inflate_LENGTH c) l h = .ok ((.error Ex.leave, { l' with hold := 0, bits := 0, ret := Z_STREAM_END }),
            setI h zs { s with mode := DONE }))) := by
  obtain ⟨rr, l', j, hrun, hj, B', hS, hbits, hshape, hmax, hid, hok, hleave⟩ := NEEDBITS_run B 32 (by decide)
  have hw' : ¬ s.wrap = 0 := hw
  have hf' : ¬ s.flags = 0 := hf
  refine ⟨rr, l', j, hrun, hj, B', hS, ?_, ?_⟩
  · intro e
    obtain ⟨h1, h2, h3⟩ := hleave e
    refine ⟨h2, h1, h3, ?_⟩
    unfold inflate_LENGTH
    rw [hc]
    simp [runX_bind, runX_lift, ldI_eq, hs, hw', hf', hrun, e, runX_throw]
  · intro e
    refine ⟨hok e, ?_, ?_⟩
    · intro h4 hne
      obtain ⟨i, hi, hbad⟩ := tcBadMode_run (c := c) "incorrect length check" lit_length_check hr hc hz hs
      refine ⟨i, hi, ?_⟩
      unfold inflate_LENGTH
      rw [hc]
      simp [runX_bind, runX_lift, ldI_eq, hs, hw', hf', hrun, e, runX_get, h4, hne, hbad, runX_pure]
    · intro hn
      unfold inflate_LENGTH
      rw [hc]
      have hn' : ¬ (¬ s.wrap &&& 4 = 0 ∧ ¬ l'.hold = s.total &&& 4294967295) := hn
      simp [runX_bind, runX_lift, ldI_eq, hs, hw', hf', hrun, e, runX_get, hn', runX_pure, runX_INITBITS, setMode, wrI_eq,
        inflate_DONE, runX_modify, runX_throw]

/-! ### `case CHECK:` -/

/-- The condition of `if ((state->wrap & 4) && out) strm->adler = state->check = UPDATE_CHECK(...)`. -/
def chkCond (s : InflateState) (out : UInt32) : Bool := (s.wrap &&& 4) != 0 && out != 0

/-- The stream record after the accounting of `CHECK`: `total_out += out` and, when the check is updated, `adler = v`. -/
def chkZ (z : ZStream) (s : InflateState) (out : UInt32) (v : UInt64) : ZStream :=
  { z with total_out := z.total_out + out.toUInt64, adler := if chkCond s out then v else z.adler }

/-- The state record after the accounting of `CHECK`: `total += out` and, when the check is updated, `check = v`. -/
def chkS (s : InflateState) (out : UInt32) (v : UInt64) : InflateState :=
  { s with total := s.total + out.toUInt64, check := if chkCond s out then v else s.check }

/-- The heap after the accounting of `CHECK`. -/
def chkH (h : Heap) (r : ZStreamRef) (zs : Nat) (z : ZStream) (s : InflateState) (out : UInt32) (v : UInt64) : Heap :=
  setI (r.put h (chkZ z s out v)) zs (chkS s out v)

/-- `case CHECK:` with `wrap = 0`: no check; `state->mode = LENGTH` and the fall-through into `LENGTH`. -/
theorem inflate_CHECK_nowrap {c : Ctx} {l : IL} {h : Heap} {zs : Nat} {s : InflateState}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s) (hw : s.wrap = 0) :
    runX (inflate_CHECK c) l h = runX (inflate_LENGTH c) l (setI h zs { s with mode := LENGTH }) := by
  unfold inflate_CHECK
  rw [hc]
  simp [runX_bind, runX_lift, ldI_eq, hs, hw, setMode, wrI_eq, runX_pure]

/-- `put` addresses the byte `off` of the block `blk` (bytes `a`), and the `out` bytes before it are inside the block. -/
def PutAt (h : Heap) (put : BPtr) (out : UInt32) (blk off : Nat) (a : Array UInt8) : Prop :=
  put = .ref (.blk blk) off ∧ h.bytes blk = some a ∧ out.toNat ≤ off ∧ off ≤ a.size

/-- `case CHECK:` with `wrap ≠ 0`. `NEEDBITS(32)`; if the input ran out, `goto inf_leave` with the registers of that moment;
else `out -= left` (`out` below), `total_out` and `total` grow by `out`, and when `(wrap & 4)` is set and `out ≠ 0` the check
becomes `UPDATE_CHECK(check, put - out, out)` (`v`), also copied to `strm->adler`; then `out = left`; then when `(wrap & 4)` is set
and the stream's check word (`hold`, byte-swapped for a zlib stream) differs from the check, the error "incorrect data check"
(`BAD`, `break`); else `INITBITS`, `mode = LENGTH` and the fall-through into `LENGTH` (the theorems `inflate_LENGTH_*`).
Precondition on the output: whenever the check is updated, `put` addresses a byte block with the `out` bytes written by this
call just before it (`PutAt`), which holds in every state `inflate` reaches (`put = next_out + (out - left)` at the start of
the call, advanced by one for every byte written). `v` is the value `UPDATE_CHECK` returns: the CRC-32 or the Adler-32 of those
bytes (for Adler-32 and `out = 1` only when the old check is a canonical sum, true of every value `adler32` returns). -/
theorem inflate_CHECK_run {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {bs : List UInt8} (out : UInt32) (hout : out = l.out_ - l.left)
    (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (hz : r.get h = some z)
    (hs : h.istates zs = some s) (hw : s.wrap ≠ 0) (B : BitInv h l bs) (hS : Zlib.Crc32.Proofs.StaticsOK h)
    (hput : chkCond s out = true → ∃ blk off a, PutAt h l.put out blk off a) :
    ∃ rr l' j, runX (NEEDBITS 32) l h = .ok ((rr, l'), h) ∧ j ≤ bs.length ∧ BitInv h l' (bs.drop j) ∧
      stream l' (bs.drop j) = stream l bs ∧
      (rr = .error Ex.leave → l'.have_ = 0 ∧ j = bs.length ∧ l'.bits.toNat < 32 ∧
        runX (inflate_CHECK c) l h = .ok ((.error Ex.leave, l'), h)) ∧
      (rr = .ok () → 32 ≤ l'.bits.toNat ∧ ∃ v,
        (chkCond s out = true → ∀ blk off a, PutAt h l.put out blk off a →
          (s.flags ≠ 0 → v = (ZlibF.Spec.crc32Update s.check.toUInt32 ((a.toList.drop (off - out.toNat)).take out.toNat)).toUInt64) ∧
          (s.flags = 0 → (out ≠ 1 ∨ (s.check >>> 16 &&& 65535).toNat < 65521) →
            v.toNat = Zlib.Adler32.Spec.adler32 s.check.toNat (Zlib.Adler32.Proofs.seg a (off - out.toNat) out.toNat))) ∧
        ((s.wrap &&& 4) ≠ 0 → (if s.flags ≠ 0 then l'.hold else ZSWAP32 l'.hold) ≠ (chkS s out v).check →
          ∃ i, strTable[i]? = some "incorrect data check" ∧
            runX (inflate_CHECK c) l h =
              .ok ((.ok (), { l' with out_ := l.left }), tcBadHeap (chkH h r zs z s out v) r zs (chkZ z s out v) (chkS s out v) i)) ∧
        (¬ ((s.wrap &&& 4) ≠ 0 ∧ (if s.flags ≠ 0 then l'.hold else ZSWAP32 l'.hold) ≠ (chkS s out v).check) →
          runX (inflate_CHECK c) l h =
            runX (inflate_LENGTH c) { l' with out_ := l.left, hold := 0, bits := 0 }
              (setI (chkH h r zs z s out v) zs { chkS s out v with mode := LENGTH }))) := by
  obtain ⟨rr, l', j, hrun, hj, B', hS', hbits, hshape, hmax, hid, hok, hleave⟩ := NEEDBITS_run B 32 (by decide)
  have hw' : ¬ s.wrap = 0 := hw
  have hput' : l'.put = l.put := by rw [hshape]
  have hleft' : l'.left = l.left := by rw [hshape]
  have hout' : l'.out_ = l.out_ := by rw [hshape]
  refine ⟨rr, l', j, hrun, hj, B', hS', ?_, ?_⟩
  · intro e
    obtain ⟨h1, h2, h3⟩ := hleave e
    refine ⟨h2, h1, h3, ?_⟩
    unfold inflate_CHECK
    rw [hc]
    simp [runX_bind, runX_lift, ldI_eq, hs, hw', hrun, e, runX_throw]
  · intro e
    refine ⟨hok e, ?_⟩
    by_cases hcond : chkCond s out = true
    · obtain ⟨blk, off, a, hP⟩ := hput hcond
      obtain ⟨hp, hb, ho1, ho2⟩ := hP
      have hct' : chkCond s (l.out_ - l.left) = true := by rw [← hout]; exact hcond
      have hct3 : ¬ s.wrap &&& 4 = 0 ∧ ¬ l.out_ - l.left = 0 := by
        simpa [chkCond, ← hout] using hcond
      -- the heap after `total_out += out; total += out`
      let h1 : Heap := setI (r.put h { z with total_out := z.total_out + out.toUInt64 }) zs
        { s with total := s.total + out.toUInt64 }
      have hb1 : h1.bytes blk = some a := by simpa [h1] using hb
      have hs1 : h1.istates zs = some { s with total := s.total + out.toUInt64 } := by simp [h1]
      have hst1 : h1.static = h.static := by simp [h1, setI]
      have hS1 : Zlib.Crc32.Proofs.StaticsOK h1 := by
        unfold Zlib.Crc32.Proofs.StaticsOK at hS ⊢
        rw [hst1]; exact hS
      have hg1 : (Space.get h1 (BRef.blk blk) : Option (Array UInt8)) = some a := hb1
      have hptr : Ptr.add l.put (-(out.toNat : Int)) h1 = .ok (.ref (.blk blk) (off - out.toNat), h1) := by
        rw [hp]; exact Ptr.sub_nat_ok hg1 ho1 ho2
      obtain ⟨v, hv, hvf, hva⟩ := UPDATE_CHECK_run (zs := zs) (blk := blk) (off := off - out.toNat) (a := a) (len := out)
        hS1 hs1 hb1 (by omega) s.check
      have hspec : ∀ blk' off' a', PutAt h l.put out blk' off' a' →
          (s.flags ≠ 0 → v = (ZlibF.Spec.crc32Update s.check.toUInt32 ((a.toList.drop (off - out.toNat)).take out.toNat)).toUInt64) ∧
          (s.flags = 0 → (out ≠ 1 ∨ (s.check >>> 16 &&& 65535).toNat < 65521) →
            v.toNat = Zlib.Adler32.Spec.adler32 s.check.toNat (Zlib.Adler32.Proofs.seg a (off - out.toNat) out.toNat)) := by
        intro blk' off' a' hP'
        obtain ⟨hp', hb', -, -⟩ := hP'
        rw [hp] at hp'
        obtain ⟨e1, e2⟩ := Ptr.ref.inj hp'
        have e1' := BRef.blk.inj e1
        subst e1' e2
        rw [hb] at hb'
        cases hb'
        exact ⟨hvf, hva⟩
      have hptr2 := hptr
      have hv2 := hv
      simp [h1, hout] at hptr2 hv2
      refine ⟨v, fun _ blk' off' a' hP' => ?_, ?_, ?_⟩
      · have := hspec blk' off' a' hP'
        obtain ⟨hp', hb', -, -⟩ := hP'
        rw [hp] at hp'
        obtain ⟨e1, e2⟩ := Ptr.ref.inj hp'
        have e1' := BRef.blk.inj e1
        subst e1' e2
        rw [hb] at hb'
        cases hb'
        exact this
      · intro hbad hne
        have hz2 : r.get (chkH h r zs z s out v) = some (chkZ z s out v) := by
          simp [chkH, hz]
        have hs2 : (chkH h r zs z s out v).istates zs = some (chkS s out v) := by simp [chkH]
        obtain ⟨i, hi, hbm⟩ := tcBadMode_run (c := c) "incorrect data check" lit_data_check hr hc hz2 hs2
        refine ⟨i, hi, ?_⟩
        simp [chkH, chkZ, chkS, tcBadHeap, hcond, hct', hout] at hbm
        have hbad2 : (¬ s.wrap &&& 4 = 0 ∧ ¬ (if s.flags = 0 then ZSWAP32 l'.hold else l'.hold) = v) := by
          refine ⟨hbad, ?_⟩
          simp only [chkS, hcond, ↓reduceIte] at hne
          by_cases hf0 : s.flags = 0
          · rw [ite_eq_left hf0]
            rw [ite_eq_right (by simpa using hf0)] at hne
            exact hne
          · rw [ite_eq_right hf0]
            rw [ite_eq_left hf0] at hne
            exact hne
        unfold inflate_CHECK
        rw [hc]
        simp [runX_bind, runX_lift, ldI_eq, hs, hw', hrun, e, hr, runX_modify, runX_get, wrZ_eq, wrI_eq, hz,
          hout, hout', hleft', runX_pure, hct3, hct', hbad2, setMode, runX_INITBITS, chkH, chkZ, chkS, hcond, hbm, chkCond,
          hput', hptr2, hv2]
        simp [tcBadHeap]
      · intro hn
        have hn2 : ¬ (¬ s.wrap &&& 4 = 0 ∧ ¬ (if s.flags = 0 then ZSWAP32 l'.hold else l'.hold) = v) := by
          rintro ⟨ha, hb⟩
          apply hn
          refine ⟨ha, ?_⟩
          simp only [chkS, hcond, ↓reduceIte]
          by_cases hf0 : s.flags = 0
          · rw [ite_eq_left hf0] at hb
            rw [ite_eq_right (by simpa using hf0)]
            exact hb
          · rw [ite_eq_right hf0] at hb
            rw [ite_eq_left hf0]
            exact hb
        have hn3 : (if s.flags = 0 then ZSWAP32 l'.hold else l'.hold) = v := by
          by_cases hh : (if s.flags = 0 then ZSWAP32 l'.hold else l'.hold) = v
          · exact hh
          · exact absurd ⟨hct3.1, hh⟩ hn2
        unfold inflate_CHECK
        rw [hc]
        simp [runX_bind, runX_lift, ldI_eq, hs, hw', hrun, e, hr, runX_modify, runX_get, wrZ_eq, wrI_eq, hz,
          hout, hout', hleft', runX_pure, hct3, hct', hn3, setMode, runX_INITBITS, chkH, chkZ, chkS, hcond, chkCond,
          hput', hptr2, hv2]
    · have hcf : chkCond s out = false := by simpa using hcond
      have hcf' : chkCond s (l.out_ - l.left) = false := by rw [← hout]; exact hcf
      have hcf2 : ¬ ((s.wrap &&& 4) != 0 && (l.out_ - l.left) != 0) = true := by
        simpa [chkCond, ← hout] using hcond
      have hcf3 : ¬ (¬ s.wrap &&& 4 = 0 ∧ ¬ l.out_ - l.left = 0) := by
        simpa [chkCond, ← hout] using hcond
      refine ⟨s.check, fun h' => absurd h' hcond, ?_, ?_⟩
      · intro hbad hne
        have hz2 : r.get (chkH h r zs z s out s.check) = some (chkZ z s out s.check) := by
          simp [chkH, hz]
        have hs2 : (chkH h r zs z s out s.check).istates zs = some (chkS s out s.check) := by simp [chkH]
        obtain ⟨i, hi, hbm⟩ := tcBadMode_run (c := c) "incorrect data check" lit_data_check hr hc hz2 hs2
        refine ⟨i, hi, ?_⟩
        have hcf4 : l.out_ - l.left = 0 := by
          by_cases hz0 : l.out_ - l.left = 0
          · exact hz0
          · exact absurd ⟨hbad, hz0⟩ hcf3
        simp [chkH, chkZ, chkS, tcBadHeap, hcf, hcf', hout, hcf4, chkCond] at hbm
        have hbad2 : (¬ s.wrap &&& 4 = 0 ∧ ¬ (if s.flags = 0 then ZSWAP32 l'.hold else l'.hold) = s.check) := by
          refine ⟨hbad, ?_⟩
          simp only [chkS, hcf, Bool.false_eq_true, ↓reduceIte, ite_self] at hne
          by_cases hf0 : s.flags = 0
          · rw [ite_eq_left hf0]
            rw [ite_eq_right (by simpa using hf0)] at hne
            exact hne
          · rw [ite_eq_right hf0]
            rw [ite_eq_left hf0] at hne
            exact hne
        unfold inflate_CHECK
        rw [hc]
        simp [runX_bind, runX_lift, ldI_eq, hs, hw', hrun, e, hr, runX_modify, runX_get, wrZ_eq, wrI_eq, hz,
          hout, hout', hleft', runX_pure, hcf3, hcf4, hcf', hbad2, setMode, runX_INITBITS, chkH, chkZ, chkS, hcf, hbm, chkCond]
        simp [tcBadHeap]
      · intro hn
        have hn2 : ¬ (¬ s.wrap &&& 4 = 0 ∧ ¬ (if s.flags = 0 then ZSWAP32 l'.hold else l'.hold) = s.check) := by
          rintro ⟨ha, hb⟩
          apply hn
          refine ⟨ha, ?_⟩
          simp only [chkS, hcf, Bool.false_eq_true, ↓reduceIte]
          by_cases hf0 : s.flags = 0
          · rw [ite_eq_left hf0] at hb
            rw [ite_eq_right (by simpa using hf0)]
            exact hb
          · rw [ite_eq_right hf0] at hb
            rw [ite_eq_left hf0]
            exact hb
        unfold inflate_CHECK
        rw [hc]
        simp [runX_bind, runX_lift, ldI_eq, hs, hw', hrun, e, hr, runX_modify, runX_get, wrZ_eq, wrI_eq, hz, hcf2,
          hout, hout', hleft', runX_pure, hcf3, hcf', hn2, setMode, runX_INITBITS, chkH, chkZ, chkS, hcf]

end Zlib.Inflate.Proofs
