import ZlibF.Proof.«gz.inv-put-scalars»
import ZlibF.Zlib.«gzread.c»

/-!
# gzread.c: `gz_skip_have` keeps `GzInv`

`gz_skip_have` consumes `n = min(x.have, skip)` buffered bytes: `x.have -= n`, `x.next += n` (only when `n != 0`,
patch 0005), `x.pos += n`, `skip -= n`. It does not fault: `n ≤ x.have` keeps `x.next + n` inside its block
(`GzCommon.next`), and `n ≤ skip` with `x.pos + skip ≤ GZ_OFF_MAX` (`GzCommon.pos`) keeps both signed operations in
range. `GT_OFF` is false on this platform.

`GzInv.put_consume` is `GzInv.put_scalars_of` with `x.next` allowed to advance by `k` bytes when `x.have` drops by at
least `k`.
-/

namespace ZlibF.Spec.Public
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib.Spec Zlib.Gzlib.Proofs
set_option autoImplicit false

theorem padv_zero' (p : BPtr) : padv p 0 = p := by cases p <;> rfl

theorem padv_padv (p : BPtr) (a b : Nat) : padv (padv p a) b = padv p (a + b) := by
  cases p <;> simp [padv, Nat.add_assoc]

/-- **A write of the record that consumes `k` buffered bytes keeps `GzInv`**: as `GzInv.put_scalars_of`, except
that `x.next` advances by `k` and `x.have` drops by at least `k`. -/
theorem GzInv.put_consume {h : Heap} {i : Nat} {s s' : GzState} (inv : GzInv h i s)
    (same : s'.path = s.path ∧ s'.msg = s.msg ∧ s'.«in» = s.«in» ∧ s'.out = s.out ∧ s'.size = s.size ∧
      s'.mode = s.mode ∧ s'.direct = s.direct ∧ s'.strm = s.strm ∧ s'.err = s.err)
    (k : Nat) (hnext : s'.x.next = padv s.x.next k) (hk : k + s'.x.have.toNat ≤ s.x.have.toNat)
    (want : 8 ≤ s'.want.toNat ∧ s'.want.toNat < 2 ^ 31 ∧ (s.size = 0 ∨ s'.want = s.want))
    (pos : 0 ≤ s'.skip.toInt ∧ s'.x.pos.toInt + s'.skip.toInt ≤ 9223372036854775807 ∧
      -(2 * s'.size.toNat : Int) ≤ s'.x.pos.toInt)
    (rd : s.mode = GZ_READ → (s'.how = LOOK ∨ s'.how = GZ_COPY ∨ s'.how = GZIP) ∧ (s'.how = GZ_COPY → s'.direct = 1) ∧
      (s'.how = GZIP → s'.direct = 0) ∧ (s'.junk = -1 ∨ s'.junk = 0 ∨ s'.junk = 1) ∧
      (s'.eof = 0 ∨ s'.eof = 1) ∧ (s'.past = 0 ∨ s'.past = 1) ∧ (s'.again = 0 ∨ s'.again = 1) ∧
      (s.size = 0 → s'.how = LOOK))
    (wr : s.mode = GZ_WRITE → s'.reset = 0 ∨ s'.reset = 1) :
    GzInv (putGz h i s') i s' := by
  obtain ⟨hpath, hmsg, hin, hout, hsize, hmode, hdirect, hstrm, herr⟩ := same
  have hrec := inv.common.recordFree
  have c := inv.common
  have hs := c.record
  have hso : ∀ b, StreamOwned (putGz h i s') (gzStrm i) b = StreamOwned h (gzStrm i) b :=
    putGz_streamOwned hs hstrm
  have hown : ∀ b, GzOwned (putGz h i s') i s' b ↔ GzOwned h i s b :=
    putGz_owned hs ⟨hpath, hmsg, hin, hout, hsize, hmode, hdirect, hstrm⟩
  have hptrs : ownedPtrs s' = ownedPtrs s := by
    unfold ownedPtrs
    rw [hpath, hmsg, hsize, hin, hmode, hdirect, hout]
  have have_le : s'.x.have.toNat ≤ s.x.have.toNat := by omega
  have hzero : s.x.have = 0 → s'.x.have = 0 := by
    intro e
    have h0 : s'.x.have.toNat = 0 := by
      have := have_le
      rw [e] at this
      exact Nat.le_zero.mp this
    exact UInt32.toNat_inj.mp (by rw [h0]; rfl)
  have hk0 : s.x.have = 0 → k = 0 := by
    intro e
    have := hk
    rw [e] at this
    simp at this
    omega
  have hget := putGz_get (s' := s') hs hstrm
  refine ⟨?_, ?_, ?_⟩
  · exact {
      record := by simp [putGz]
      mode := by rw [hmode]; exact c.mode
      fresh := putGz_fresh hs c.fresh
      uniq := putGz_uniq hs c.uniq
      globals := c.globals
      fit := putGz_fit c.fit
      path := by
        obtain ⟨p, hp, hm⟩ := c.path
        exact ⟨p, by rw [hpath, putGz_cstring]; exact hp, by rw [hpath]; exact hm⟩
      msg := by
        rcases c.msg with hn | ⟨m, hm, hb⟩
        · exact Or.inl (by rw [hmsg]; exact hn)
        · exact Or.inr ⟨m, by rw [hmsg, putGz_cstring]; exact hm, by rw [hmsg]; exact hb⟩
      memerr := by rw [herr, hmsg]; exact c.memerr
      want := ⟨want.1, want.2.1⟩
      size := by
        rcases c.size with e | e
        · exact Or.inl (by rw [hsize]; exact e)
        · rcases want.2.2 with z | w
          · exact Or.inl (by rw [hsize]; exact z)
          · exact Or.inr (by rw [hsize, e, w])
      distinct := by
        rw [hptrs]
        simp only [hso]
        exact c.distinct
      live := fun b hb => (putGz_live hs b).2 (c.live b ((hown b).1 hb))
      pos := pos
      next := by
        rcases c.next with hn | ⟨b, off, a, hx, hbi, ho, hmb, hb, hle⟩
        · exact Or.inl (by rw [hnext, hn]; rfl)
        · exact Or.inr ⟨b, off + k, a, by rw [hnext, hx]; rfl, hbi, (hown b).2 ho, by rw [hmsg]; exact hmb, hb,
            by omega⟩
      nullHave := fun hn => by
        rcases c.next with hn0 | ⟨b, off, a, hx, _⟩
        · exact hzero (c.nullHave hn0)
        · rw [hnext, hx] at hn
          simp [padv] at hn
      recordFree := by rw [hso]; exact c.recordFree }
  · intro hm'
    have hm : s.mode = GZ_READ := by rw [← hmode]; exact hm'
    have r := inv.reader hm
    obtain ⟨hhow, hcopy, hgzip, hjunk, heof, hpast, hagain, hlook⟩ := rd hm
    exact {
      how := hhow
      copyDirect := hcopy
      gzipDirect := hgzip
      direct := by rw [hdirect]; exact r.direct
      junk := hjunk
      flags := ⟨heof, hpast, hagain⟩
      unalloc := fun hz => by
        have hz0 : s.size = 0 := by rw [← hsize]; exact hz
        obtain ⟨hh, ha, _, hn⟩ := r.unalloc hz0
        exact ⟨hzero hh, by rw [hstrm]; exact ha, hlook hz0, by rw [hstrm]; exact hn⟩
      bufs := fun hz => by
        rw [hin, hout, hsize]
        exact r.bufs (by rw [← hsize]; exact hz)
      input := by
        rw [hstrm, hin, hsize]
        exact r.input
      output := fun hh => by
        have hh' : s.x.have ≠ 0 := fun e => hh (hzero e)
        obtain ⟨c0, hx, hle⟩ := r.output hh'
        exact ⟨c0 + k, by rw [hnext, hout, hx, padv_padv], by rw [hsize]; omega⟩
      codec := fun hz => by
        have hz0 : s.size ≠ 0 := by rw [← hsize]; exact hz
        obtain ⟨reach, z, k, st, hzget, hzst, hk, hhead⟩ := r.codec hz0
        exact ⟨StreamReachable.rebuffer reach (putGz_rebuffer inv hstrm hrec) (fun _ => putGz_fit c.fit),
          z, k, st, by rw [hget]; exact hzget, hzst, hk, hhead⟩ }
  · intro hm'
    have hm : s.mode = GZ_WRITE := by rw [← hmode]; exact hm'
    have w := inv.writer hm
    have hnext' : s'.x.next = s.x.next := by rw [hnext, hk0 w.have0, padv_zero']
    exact {
      have0 := hzero w.have0
      direct := by rw [hdirect]; exact w.direct
      reset := wr hm
      unalloc := fun hz => by
        rw [hstrm]
        exact w.unalloc (by rw [← hsize]; exact hz)
      bufs := fun hz => by
        rw [hin, hout, hsize, hdirect]
        exact w.bufs (by rw [← hsize]; exact hz)
      input := by
        rw [hstrm, hin, hsize]
        exact w.input
      output := fun hd hz => by
        rw [hstrm, hout, hsize, hnext']
        exact w.output (by rw [← hdirect]; exact hd) (by rw [← hsize]; exact hz)
      codec := fun hd hz => by
        obtain ⟨reach, z, k, d, hzget, hzst, hk, hhead⟩ :=
          w.codec (by rw [← hdirect]; exact hd) (by rw [← hsize]; exact hz)
        exact ⟨StreamReachable.rebuffer reach (putGz_rebuffer inv hstrm hrec) (fun e => nomatch e),
          z, k, d, by rw [hget]; exact hzget, hzst, hk, hhead⟩
      transparent := fun hd => by
        rw [hstrm]
        exact w.transparent (by rw [← hdirect]; exact hd) }

/-! ## The run of `gz_skip_have` -/

/-- The count `gz_skip_have` consumes: `(z_off64_t)x.have > skip ? (unsigned)skip : x.have` (`GT_OFF` is false). -/
def skipN (s : GzState) : UInt32 :=
  if (s.x.have.toNat : Int) > s.skip.toInt then s.skip.toUInt64.toUInt32 else s.x.have

/-- The record after `gz_skip_have`. -/
def skipRec (s : GzState) : GzState :=
  { s with
    x := { s.x with «have» := s.x.have - skipN s,
                    next := if skipN s = 0 then s.x.next else padv s.x.next (skipN s).toNat,
                    pos := Int64.ofInt (s.x.pos.toInt + (skipN s).toNat) },
    skip := Int64.ofInt (s.skip.toInt - (skipN s).toNat) }

theorem skipN_toNat {s : GzState} (hp : 0 ≤ s.skip.toInt) :
    (skipN s).toNat = min s.x.have.toNat s.skip.toInt.toNat := by
  have hl := s.x.have.toNat_lt
  unfold skipN
  by_cases hc : (s.x.have.toNat : Int) > s.skip.toInt
  · rw [if_pos hc]
    have h0 : (0 : Int64) ≤ s.skip := by rw [Int64.le_iff_toInt_le]; simpa using hp
    rw [UInt64.toNat_toUInt32, Int64.toNat_toUInt64_of_le h0, ← Int64.toNat_toInt]
    have : s.skip.toInt.toNat < 2 ^ 32 := by omega
    rw [Nat.mod_eq_of_lt this]
    omega
  · rw [if_neg hc]
    omega

theorem skipN_le_have {s : GzState} (hp : 0 ≤ s.skip.toInt) : (skipN s).toNat ≤ s.x.have.toNat := by
  rw [skipN_toNat hp]; exact Nat.min_le_left _ _

theorem skipN_le_skip {s : GzState} (hp : 0 ≤ s.skip.toInt) : ((skipN s).toNat : Int) ≤ s.skip.toInt := by
  rw [skipN_toNat hp]; omega

theorem skipRec_have_toNat (s : GzState) (hp : 0 ≤ s.skip.toInt) :
    (skipRec s).x.have.toNat = s.x.have.toNat - (skipN s).toNat := by
  show (s.x.have - skipN s).toNat = _
  rw [UInt32.toNat_sub_of_le]
  exact UInt32.le_iff_toNat_le.mpr (skipN_le_have hp)

theorem skipRec_next (s : GzState) : (skipRec s).x.next = padv s.x.next (skipN s).toNat := by
  show (if skipN s = 0 then s.x.next else padv s.x.next (skipN s).toNat) = _
  split
  · next e => rw [e]; exact (padv_zero' _).symm
  · rfl

theorem skipRec_pos (s : GzState) (hp : 0 ≤ s.skip.toInt)
    (hb : s.x.pos.toInt + s.skip.toInt ≤ 9223372036854775807) (hlo : -(2 ^ 33 : Int) ≤ s.x.pos.toInt) :
    (skipRec s).x.pos.toInt = s.x.pos.toInt + (skipN s).toNat := by
  have := skipN_le_skip hp
  exact i64_toInt_ofInt (by omega) (by omega)

theorem skipRec_skip (s : GzState) (hp : 0 ≤ s.skip.toInt) :
    (skipRec s).skip.toInt = s.skip.toInt - (skipN s).toNat := by
  have := skipN_le_skip hp
  have := s.skip.toInt_lt
  exact i64_toInt_ofInt (by omega) (by omega)

theorem skipN_lt_iff (s : GzState) :
    s.skip < u32ToI64 s.x.have ↔ (s.x.have.toNat : Int) > s.skip.toInt := by
  rw [Int64.lt_iff_toInt_lt, u32ToI64_toInt]

theorem GT_OFF_false (x : UInt32) (h : Heap) : Zlib.Gzlib.GT_OFF x h = .ok (false, h) := by
  simp [Zlib.Gzlib.GT_OFF]

/-- **The run of `gz_skip_have`** on a handle with `GzCommon`: no fault, and the record becomes `skipRec s`. -/
theorem gz_skip_have_eq {h : Heap} {i : Nat} {s : GzState} (c : GzCommon h i s) :
    C.run (Zlib.Gzread.gz_skip_have (gzSt i)) h = .ok ((), putGz h i (skipRec s)) := by
  have hs := c.record
  obtain ⟨hp, hb, hlo⟩ := c.pos
  have hsz := s.size.toNat_lt
  have hle := skipN_le_have (s := s) hp
  have hsk := skipN_le_skip (s := s) hp
  have hlt := s.skip.toInt_lt
  have fpos : ∀ h', i64add s.x.pos (u32ToI64 (skipN s)) h' =
      .ok (Int64.ofInt (s.x.pos.toInt + (skipN s).toNat), h') := fun h' => by
    have := i64add_run s.x.pos (u32ToI64 (skipN s)) (by rw [u32ToI64_toInt]; omega)
      (by rw [u32ToI64_toInt]; omega) h'
    rw [u32ToI64_toInt] at this; exact this
  have fsk : ∀ h', i64sub s.skip (u32ToI64 (skipN s)) h' =
      .ok (Int64.ofInt (s.skip.toInt - (skipN s).toNat), h') := fun h' => by
    have := i64sub_run s.skip (u32ToI64 (skipN s)) (by rw [u32ToI64_toInt]; omega)
      (by rw [u32ToI64_toInt]; omega) h'
    rw [u32ToI64_toInt] at this; exact this
  have fadd : skipN s ≠ 0 → ∀ s1 : GzState, Ptr.add s.x.next ((skipN s).toNat : Int) (setS h i s1) =
      .ok (padv s.x.next (skipN s).toNat, setS h i s1) := by
    intro hz s1
    rcases c.next with hn | ⟨b, off, a, hx, _, _, _, hba, hoff⟩
    · exfalso
      have h0 := c.nullHave hn
      rw [h0] at hle
      exact hz (UInt32.toNat_inj.mp (by simp at hle; simp [hle]))
    · rw [hx]
      have hg : Space.get (setS h i s1) (BRef.blk b) = some a := hba
      exact Ptr.add_nat_ok (R := BRef) hg (by omega)
  unfold Zlib.Gzread.gz_skip_have skipRec
  by_cases hc : (s.x.have.toNat : Int) > s.skip.toInt
  · have e : skipN s = s.skip.toUInt64.toUInt32 := if_pos hc
    have hc' : s.skip < u32ToI64 s.x.have := (skipN_lt_iff s).mpr hc
    simp only [C.run, gzSt, bind_app, pure_app, ldS_eq, hs, GT_OFF_false, Bool.false_or, decide_eq_true_eq,
      gt_iff_lt, hc', if_true, ← e, updX_eq, setS_gz_same, setS_setS]
    by_cases hz : skipN s = 0
    · rw [if_neg (show ¬ (skipN s != 0) = true by simp [hz]), if_pos hz]
      simp only [bind_app, pure_app, ldS_eq, setS_gz_same, fpos, fsk, updX_eq, updS_eq, setS_setS, gzSt]
      rfl
    · rw [if_pos (show (skipN s != 0) = true by simp [hz]), if_neg hz]
      simp only [bind_app, pure_app, ldS_eq, setS_gz_same, fadd hz, fpos, fsk, updX_eq, updS_eq, setS_setS, gzSt]
      rfl
  · have e : skipN s = s.x.have := if_neg hc
    have hc' : ¬ s.skip < u32ToI64 s.x.have := fun x => hc ((skipN_lt_iff s).mp x)
    rw [e] at fpos fsk fadd ⊢
    simp only [C.run, gzSt, bind_app, pure_app, ldS_eq, hs, GT_OFF_false, Bool.false_or, decide_eq_true_eq,
      gt_iff_lt, hc', if_false, updX_eq, setS_gz_same, setS_setS]
    by_cases hz : s.x.have = 0
    · rw [if_neg (show ¬ (s.x.have != 0) = true by simp [hz]), if_pos hz]
      simp only [bind_app, pure_app, ldS_eq, setS_gz_same, fpos, fsk, updX_eq, updS_eq, setS_setS, gzSt]
      rfl
    · rw [if_pos (show (s.x.have != 0) = true by simp [hz]), if_neg hz]
      simp only [bind_app, pure_app, ldS_eq, setS_gz_same, fadd hz, fpos, fsk, updX_eq, updS_eq, setS_setS, gzSt]
      rfl

/-- **`gz_skip_have`, explicit form.** On a handle in `GzInv` it does not fault; the record becomes `skipRec s`, which
is in `GzInv`; it consumes `n = min(x.have, skip)` bytes (`skipN s`), after which `x.have = 0` or `skip = 0`; the
skip target `x.pos + skip` is unchanged. -/
theorem gz_skip_have_run {h : Heap} {i : Nat} {s : GzState} (inv : GzInv h i s) :
    C.run (Zlib.Gzread.gz_skip_have (gzSt i)) h = .ok ((), putGz h i (skipRec s)) ∧
      GzInv (putGz h i (skipRec s)) i (skipRec s) ∧
      ((skipRec s).x.have = 0 ∨ (skipRec s).skip = 0) ∧
      (skipN s).toNat ≤ s.x.have.toNat ∧ (skipN s).toNat = min s.x.have.toNat s.skip.toInt.toNat ∧
      (skipRec s).skip.toInt + (skipRec s).x.pos.toInt = s.skip.toInt + s.x.pos.toInt := by
  have c := inv.common
  obtain ⟨hp, hb, hlo⟩ := c.pos
  have hsz := s.size.toNat_lt
  have hmin := skipN_toNat (s := s) hp
  have hle := skipN_le_have (s := s) hp
  have hsk := skipN_le_skip (s := s) hp
  have hhv := skipRec_have_toNat s hp
  have hpos := skipRec_pos s hp hb (by omega)
  have hski := skipRec_skip s hp
  refine ⟨gz_skip_have_eq c, ?_, ?_, hle, hmin, by rw [hpos, hski]; omega⟩
  · refine inv.put_consume ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (skipN s).toNat (skipRec_next s)
      (by rw [hhv]; omega) ⟨c.want.1, c.want.2, Or.inr rfl⟩ ⟨by rw [hski]; omega, by rw [hpos, hski]; omega,
        by rw [hpos]; exact Int.le_trans hlo (by omega)⟩ ?_ ?_
    · intro hm
      have r := inv.reader hm
      exact ⟨r.how, r.copyDirect, r.gzipDirect, r.junk, r.flags.1, r.flags.2.1, r.flags.2.2,
        fun hz => (r.unalloc hz).2.2.1⟩
    · intro hm
      exact (inv.writer hm).reset
  · by_cases hh : s.x.have.toNat ≤ s.skip.toInt.toNat
    · left
      apply UInt32.toNat_inj.mp
      rw [hhv]
      show _ = 0
      omega
    · right
      apply Int64.toInt_inj.mp
      rw [hski]
      show _ = 0
      omega

/-- **Skeleton statement**: `gz_skip_have` on a reader in `GzInv` does not fault, keeps `GzInv`, writes only the
record, and keeps the skip target `x.pos + skip`. -/
theorem gz_skip_have_safe (i : Nat) (h : Heap) (s : GzState) (inv : GzInv h i s) (hm : s.mode = GZ_READ) :
    ∃ after s', C.run (Zlib.Gzread.gz_skip_have (gzSt i)) h = .ok ((), after) ∧ GzInv after i s' ∧
      after = putGz h i s' ∧ s'.skip.toInt + s'.x.pos.toInt = s.skip.toInt + s.x.pos.toInt := by
  have _ := hm
  obtain ⟨hr, hinv, _, _, _, hk⟩ := gz_skip_have_run inv
  exact ⟨_, skipRec s, hr, hinv, rfl, hk⟩

#print axioms GzInv.put_consume
#print axioms gz_skip_have_run
#print axioms gz_skip_have_safe

end ZlibF.Spec.Public
