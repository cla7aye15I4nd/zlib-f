import ZlibF.Proof.«gz.read-fetch-specs»
import ZlibF.Proof.«gzlib.c.error-inv-premises»

/-!
# gzread.c: `gz_skip` from the statement of `gz_fetch`

`gz_skip_run_fetch` and `gz_skip_safe_fetch`: the skeleton's `gz_skip_safe`, proved from `GzFetchSafe`
(`gz.read-fetch-specs`), with the closed facts on `gz_error` (`gzErrorSpec_holds`, `gzErrorOwn_holds`) and
`gz_skip_have` (`gz_skip_have_run'`).

Premises beyond the skeleton statement:
- `msg`, `err`, `copy` on the record: `GzFetchSafe` asks for them at entry. They are to become clauses of `GzInv`
  (**open**); the loop carries them from `GzFetchSafe`'s post.
- `skip : s.skip ≠ 0`, a **statement correction** of the skeleton's `gz_skip_safe`, which is false without it. With
  `skip = 0`, `x.pos = GZ_OFF_MAX`, `x.have = 0` and input left, the do-while still calls `gz_fetch`; its COPY or GZIP
  branch has room 0 and loads or decodes one byte (`room ? room : 1`), and the loop ends with `x.have = 1`: then
  `x.pos + x.have > GZ_OFF_MAX`, against `GzReadInv.posHave`, so the post `GzInv` fails. Every caller (`gz_read`,
  `gzgetc_`, `gzgets`) tests `state->skip` first, so the premise holds at every call.

The record between the trips of the loop is in `GzInvUpToSkip` (`upToSkip_of_out` rebuilds it from `GzInvOut`
and the position bound of `GzFetchSafe`).

**Termination.** The loop has `2^64` trips of fuel. Its measure (`skipMeasureF`) is additive:
`skip / 8 + fetchRank + phase + 2·[err ∈ {Z_OK, Z_BUF_ERROR}]`, where the phase is 0 at the end of the input with
nothing buffered, 1 for a fetch from a dead stream (bad error, GZIP, inflate `Stuck`), 3 for any other fetch, 2 for
buffered output that is large (16 bytes or more), reaches the skip, is at the end of the input or is dead, and 4 for
other buffered output. A `gz_skip_have` trip lowers `skip / 8` by 2 (large output) or the phase; a fetch trip lowers
the phase, the rank (`GzFetchSafe`'s rank clauses), or the error term (a `-1` with output leaves a bad error, and a
bad error stays bad). Under `ReadsFinite` (budget below `2^61`) the measure is below `2^64`.
-/

namespace ZlibF.Spec.Public.GzRead
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib.Spec Zlib.Gzlib.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-! ## Buffered output into the invariant -/

/-- The record `t` with `a` buffered bytes at `p` and the skip `sk`. -/
abbrev withOut (t : GzState) (a : UInt32) (p : BPtr) (sk : Int64) : GzState :=
  { t with x := { t.x with «have» := a, next := p }, skip := sk }

/-- **Buffered output inside `out` keeps `GzInv`**: from a reader with nothing buffered, a write of `x.have`,
`x.next` and `skip` with the output window inside `out`, the end of the output a representable position, and no
skip pending with output. -/
theorem GzInv.put_out {H : Heap} {i : Nat} {t : GzState} (inv : GzInv H i t) (hm : t.mode = GZ_READ)
    (h0 : t.x.have = 0) (a : UInt32) (p : BPtr) (sk : Int64)
    (win : a ≠ 0 → ∃ c, p = padv t.out c ∧ c + a.toNat ≤ 2 * t.size.toNat)
    (hph : t.x.pos.toInt + a.toNat ≤ 9223372036854775807)
    (hsk : 0 ≤ sk.toInt ∧ t.x.pos.toInt + sk.toInt ≤ 9223372036854775807) (hhs : a ≠ 0 → sk = 0) :
    GzInv (putGz H i (withOut t a p sk)) i (withOut t a p sk) := by
  have c := inv.common
  have r := inv.reader hm
  have hs := c.record
  have hrec := c.recordFree
  have hstrm : (withOut t a p sk).strm = t.strm := rfl
  have hso : ∀ b, StreamOwned (putGz H i (withOut t a p sk)) (gzStrm i) b = StreamOwned H (gzStrm i) b :=
    putGz_streamOwned hs hstrm
  have hown : ∀ b, GzOwned (putGz H i (withOut t a p sk)) i (withOut t a p sk) b ↔ GzOwned H i t b :=
    putGz_owned hs ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hptrs : ownedPtrs (withOut t a p sk) = ownedPtrs t := rfl
  have hget := putGz_get (s' := withOut t a p sk) hs hstrm
  have hpos0 : 0 ≤ t.x.pos.toInt := by
    have := c.pos.2.2
    rw [h0] at this
    simpa using this
  have hsz_of : a ≠ 0 → t.size ≠ 0 := by
    intro ha e
    obtain ⟨c0, -, hle⟩ := win ha
    rw [e] at hle
    have : a.toNat ≠ 0 := fun e0 => ha (UInt32.toNat_inj.mp (by rw [e0]; rfl))
    simp at hle
    omega
  have outb : a ≠ 0 → ∃ c0 ob arr, p = .ref (.blk ob) c0 ∧ ob ≠ i ∧ GzOwned H i t ob ∧
      blkOf t.msg ≠ some ob ∧ H.bytes ob = some arr ∧ c0 + a.toNat ≤ arr.size := by
    intro ha
    obtain ⟨c0, hp, hle⟩ := win ha
    have hsz := hsz_of ha
    obtain ⟨ob, arr, hout, hb, -, hsize⟩ := (r.bufs hsz).2
    have mem : t.out ∈ ownedPtrs t := by
      unfold ownedPtrs
      rw [if_pos hsz, if_pos (Or.inl hm)]
      simp
    have hbk : blkOf t.out = some ob := by rw [hout]; rfl
    refine ⟨c0, ob, arr, by rw [hp, hout]; simp [padv], (c.distinct.2 _ mem ob hbk).1,
      Or.inr (Or.inr (Or.inr ⟨hsz, Or.inr ⟨Or.inl hm, Or.inl hout⟩⟩)), fun e => ?_, hb, by omega⟩
    exact ((inv.msg_separate e).2.2.2 hsz).2 (Or.inl hm) hout
  refine ⟨?_, fun _ => ?_, fun hw => absurd (hm.symm.trans hw) (by decide)⟩
  · exact {
      record := by simp [putGz]
      mode := c.mode
      fresh := putGz_fresh hs c.fresh
      uniq := putGz_uniq hs c.uniq
      globals := c.globals
      fit := putGz_fit c.fit
      path := by
        obtain ⟨q, hq, hmb⟩ := c.path
        exact ⟨q, (putGz_cstring _ _).2 hq, hmb⟩
      msg := by
        rcases c.msg with hn | ⟨m, hq, hmb⟩
        · exact Or.inl hn
        · exact Or.inr ⟨m, (putGz_cstring _ _).2 hq, hmb⟩
      memerr := c.memerr
      want := c.want
      size := c.size
      distinct := by
        rw [hptrs]
        simp only [hso]
        exact c.distinct
      live := fun b hb => (putGz_live hs b).2 (c.live b ((hown b).1 hb))
      pos := ⟨hsk.1, hsk.2, by show 0 ≤ t.x.pos.toInt + (a.toNat : Int); omega⟩
      next := fun ha => by
        obtain ⟨c0, ob, arr, hp, h1, h2, h3, h4, h5⟩ := outb ha
        exact ⟨ob, c0, arr, hp, h1, (hown ob).2 h2, h3, h4, h5⟩
      nullHave := fun hn => Classical.byContradiction fun ha => by
        obtain ⟨c0, ob, arr, hp, -⟩ := outb ha
        have hn' : p = .null := hn
        rw [hp] at hn'
        cases hn'
      recordFree := by rw [hso]; exact hrec }
  · exact {
      how := r.how
      copyDirect := r.copyDirect
      gzipDirect := r.gzipDirect
      direct := r.direct
      junk := r.junk
      flags := r.flags
      unalloc := fun hz => by
        obtain ⟨-, hav, hl, hn⟩ := r.unalloc hz
        exact ⟨Classical.byContradiction fun ha => hsz_of ha hz, hav, hl, hn⟩
      bufs := r.bufs
      input := r.input
      output := fun ha => win ha
      codec := fun hz => by
        obtain ⟨reach, z, k, st, hzget, hzst, hk, hhead⟩ := r.codec hz
        exact ⟨StreamReachable.rebuffer reach (putGz_rebuffer inv hstrm hrec) (fun _ => putGz_fit c.fit),
          z, k, st, by rw [hget]; exact hzget, hzst, hk, hhead⟩
      posHave := hph
      againSize := r.againSize
      haveSkip := hhs
      againEof := r.againEof }

/-- The invariant after a fetch (`GzInvOut`), with the end of the output a representable position and the skip
bounds, is the invariant up to the pending skip. -/
theorem upToSkip_of_out {h : Heap} {i : Nat} {s : GzState} (hu : GzInvOut h i s) (hm : s.mode = GZ_READ)
    (hph : s.x.pos.toInt + s.x.have.toNat ≤ 9223372036854775807) (hp : 0 ≤ s.skip.toInt)
    (hb : s.x.pos.toInt + s.skip.toInt ≤ 9223372036854775807) : GzInvUpToSkip h i s := by
  obtain ⟨⟨hrec, inv⟩, win⟩ := hu
  have hpl := s.x.pos.toInt_lt
  have z : (0 : Int64).toInt = 0 := by decide
  have := GzInv.put_out inv hm rfl s.x.have s.x.next 0 win hph
    ⟨by rw [z]; exact Int.le_refl _, by show s.x.pos.toInt + (0 : Int64).toInt ≤ _; rw [z]; omega⟩
    (fun _ => rfl)
  rw [putGz_putGz] at this
  exact ⟨hrec, this, hp, hb⟩

/-- A reader in `GzInv` with nothing buffered is in the invariant up to the buffered output. -/
theorem upToOutput_of_inv {h : Heap} {i : Nat} {s : GzState} (inv : GzInv h i s) (hm : s.mode = GZ_READ)
    (h0 : s.x.have = 0) : GzInvUpToOutput h i s := by
  have c := inv.common
  have hpl := s.x.pos.toInt_lt
  have := GzInv.put_out inv hm h0 0 .null s.skip (fun e => absurd rfl e)
    (by show s.x.pos.toInt + ((0 : UInt32).toNat : Int) ≤ _; simp; omega) ⟨c.pos.1, c.pos.2.1⟩
    (fun e => absurd rfl e)
  exact ⟨c.record, this⟩

/-- With buffered output, a reader in `GzInvUpToSkip` has buffers of at least 8 bytes. -/
theorem size_of_have {h : Heap} {i : Nat} {s : GzState} (u : GzInvUpToSkip h i s) (hm : s.mode = GZ_READ)
    (hh : s.x.have ≠ 0) : 8 ≤ s.size.toNat := by
  have c := u.2.1.common
  have r := u.reader hm
  rcases c.size with e | e
  · exact absurd (r.unalloc e).1 hh
  · have e' : s.size = s.want := e
    rw [e']
    exact c.want.1

/-! ## The measure -/

/-- At the end of the input: `eof` set, no pending input. -/
def SkipEof (s : GzState) : Prop := s.eof ≠ 0 ∧ s.strm.avail_in = 0

/-- The error is not fatal for `gz_fetch` (`Z_OK` or `Z_BUF_ERROR`). -/
def SkipErrGood (s : GzState) : Prop := s.err = Z_OK ∨ s.err = Z_BUF_ERROR

/-- A dead stream: a fatal error, GZIP, and inflate in mode BAD or MEM. A fetch from it gives no output. -/
def SkipDead (h : Heap) (s : GzState) : Prop := ¬ SkipErrGood s ∧ s.how = GZIP ∧ Stuck h s

open Classical in
/-- The phase of a trip of `gz_skip`'s loop (see the module docstring). -/
noncomputable def skipPhase (h : Heap) (s : GzState) : Nat :=
  if s.x.have = 0 then (if SkipEof s then 0 else if SkipDead h s then 1 else 3)
  else if 16 ≤ s.x.have.toNat ∨ s.skip.toInt ≤ (s.x.have.toNat : Int) ∨ SkipEof s ∨ SkipDead h s then 2 else 4

open Classical in
/-- The error term: 2 while the error is not fatal. -/
noncomputable def skipGterm (s : GzState) : Nat := if SkipErrGood s then 2 else 0

/-- **The measure of `gz_skip`'s loop.** -/
noncomputable def skipMeasureF (fs : Fs) (h : Heap) (s : GzState) : Nat :=
  s.skip.toInt.toNat / 8 + fetchRank fs h s + skipPhase h s + skipGterm s

section measure
variable {h : Heap} {s : GzState}

theorem skipPhase_le (h : Heap) (s : GzState) : skipPhase h s ≤ 4 := by
  unfold skipPhase; repeat' split
  all_goals omega

theorem skipPhase_zero_le (hh : s.x.have = 0) : skipPhase h s ≤ 3 := by
  unfold skipPhase; rw [if_pos hh]; repeat' split
  all_goals omega

theorem skipPhase_eof (hh : s.x.have = 0) (hE : SkipEof s) : skipPhase h s = 0 := by
  unfold skipPhase; rw [if_pos hh, if_pos hE]

theorem skipPhase_dead (hh : s.x.have = 0) (hE : ¬ SkipEof s) (hD : SkipDead h s) : skipPhase h s = 1 := by
  unfold skipPhase; rw [if_pos hh, if_neg hE, if_pos hD]

theorem skipPhase_fetch (hh : s.x.have = 0) (hE : ¬ SkipEof s) (hD : ¬ SkipDead h s) : skipPhase h s = 3 := by
  unfold skipPhase; rw [if_pos hh, if_neg hE, if_neg hD]

theorem skipPhase_big (hh : s.x.have ≠ 0)
    (hb : 16 ≤ s.x.have.toNat ∨ s.skip.toInt ≤ (s.x.have.toNat : Int) ∨ SkipEof s ∨ SkipDead h s) :
    skipPhase h s = 2 := by
  unfold skipPhase; rw [if_neg hh, if_pos hb]

theorem skipPhase_small (hh : s.x.have ≠ 0)
    (hb : ¬ (16 ≤ s.x.have.toNat ∨ s.skip.toInt ≤ (s.x.have.toNat : Int) ∨ SkipEof s ∨ SkipDead h s)) :
    skipPhase h s = 4 := by
  unfold skipPhase; rw [if_neg hh, if_neg hb]

theorem skipGterm_le (s : GzState) : skipGterm s ≤ 2 := by
  unfold skipGterm; split <;> omega

theorem skipGterm_good (g : SkipErrGood s) : skipGterm s = 2 := by
  unfold skipGterm; rw [if_pos g]

theorem skipGterm_bad (g : ¬ SkipErrGood s) : skipGterm s = 0 := by
  unfold skipGterm; rw [if_neg g]

theorem skipGterm_mono {s' : GzState}
    (f1 : s.err ≠ Z_OK → s.err ≠ Z_BUF_ERROR → s'.err ≠ Z_OK ∧ s'.err ≠ Z_BUF_ERROR) :
    skipGterm s' ≤ skipGterm s := by
  by_cases g : SkipErrGood s
  · rw [skipGterm_good g]; exact skipGterm_le s'
  · have k := f1 (fun e => g (Or.inl e)) (fun e => g (Or.inr e))
    have g' : ¬ SkipErrGood s' := by
      rintro (e | e)
      · exact k.1 e
      · exact k.2 e
    rw [skipGterm_bad g, skipGterm_bad g']
    exact Nat.le_refl _

theorem fetchRank_lt {fs : Fs} (hb : ReadsFinite fs s.fd) : fetchRank fs h s < 5 * 2 ^ 61 + 2 ^ 35 := by
  unfold fetchRank inputLeft
  have h1 := hb.2
  have h2 := s.strm.avail_in.toNat_lt
  repeat' split
  all_goals omega

/-- Under `ReadsFinite` the measure is below the fuel. -/
theorem skipMeasureF_lt {fs : Fs} (hb : ReadsFinite fs s.fd) : skipMeasureF fs h s < 2 ^ 64 := by
  have h1 := fetchRank_lt (h := h) hb
  have h2 := skipPhase_le h s
  have h3 := skipGterm_le s
  have h4 := s.skip.toInt_lt
  unfold skipMeasureF
  omega

/-- **A `gz_skip_have` trip that leaves a skip lowers the measure.** -/
theorem skipMeasureF_have {fs : Fs} {i : Nat} (hp : 0 ≤ s.skip.toInt) (hh : s.x.have ≠ 0)
    (hne : (skipRec s).skip ≠ 0) :
    skipMeasureF fs (putGz h i (skipRec s)) (skipRec s) < skipMeasureF fs h s := by
  have hmin := skipN_toNat (s := s) hp
  have hhv := skipRec_have_toNat s hp
  have hski := skipRec_skip s hp
  have hne' : (skipRec s).skip.toInt ≠ 0 := fun e0 => hne (Int64.toInt_inj.mp (by rw [e0]; rfl))
  have hh0 : s.x.have.toNat ≠ 0 := fun e0 => hh (UInt32.toNat_inj.mp (by rw [e0]; rfl))
  have hlt : s.x.have.toNat < s.skip.toInt.toNat := by omega
  have hz : (skipRec s).x.have = 0 := UInt32.toNat_inj.mp (by rw [hhv]; show _ = 0; omega)
  have eR : fetchRank fs (putGz h i (skipRec s)) (skipRec s) = fetchRank fs h s := rfl
  have eG : skipGterm (skipRec s) = skipGterm s := rfl
  have eE : SkipEof (skipRec s) ↔ SkipEof s := Iff.rfl
  have eD : SkipDead (putGz h i (skipRec s)) (skipRec s) ↔ SkipDead h s := Iff.rfl
  have hS : (skipRec s).skip.toInt.toNat = s.skip.toInt.toNat - s.x.have.toNat := by omega
  unfold skipMeasureF
  rw [eR, eG, hS]
  have p1 := skipPhase_zero_le (h := putGz h i (skipRec s)) hz
  by_cases hE : SkipEof s
  · rw [skipPhase_eof hz (eE.2 hE), skipPhase_big hh (Or.inr (Or.inr (Or.inl hE)))]
    omega
  by_cases hD : SkipDead h s
  · rw [skipPhase_dead hz (fun x => hE (eE.1 x)) (eD.2 hD), skipPhase_big hh (Or.inr (Or.inr (Or.inr hD)))]
    omega
  by_cases h16 : 16 ≤ s.x.have.toNat
  · rw [skipPhase_big hh (Or.inl h16)]
    omega
  · have hsm : ¬ (16 ≤ s.x.have.toNat ∨ s.skip.toInt ≤ (s.x.have.toNat : Int) ∨ SkipEof s ∨ SkipDead h s) := by
      rintro (a | a | a | a)
      · exact h16 a
      · omega
      · exact hE a
      · exact hD a
    rw [skipPhase_small hh hsm]
    omega

/-- **A fetch trip that continues the loop lowers the measure**, from the clauses of `GzFetchSafe` (with a budget). -/
theorem skipMeasureF_fetch {fs fs' : Fs} {h' : Heap} {s' : GzState} {r : Int32}
    (hh : s.x.have = 0) (hE : ¬ SkipEof s) (hskip : s'.skip = s.skip) (hpos : s'.x.pos = s.x.pos)
    (hpb : s.x.pos.toInt + s.skip.toInt ≤ 9223372036854775807)
    (hsize : s'.x.have ≠ 0 → 8 ≤ s'.size.toNat) (cont : r = 0 ∨ s'.x.have ≠ 0)
    (hR : fetchRank fs' h' s' ≤ fetchRank fs h s)
    (c0 : s'.x.have = 0 → r = 0 →
      (s'.eof ≠ 0 ∧ s'.strm.avail_in = 0) ∨ fetchRank fs' h' s' < fetchRank fs h s)
    (c1 : s'.x.have ≠ 0 → s'.x.have.toNat = 2 * s'.size.toNat ∨ r = -1 ∨
      9223372036854775807 ≤ s'.x.pos.toInt + s'.x.have.toNat ∨ (s'.eof ≠ 0 ∧ s'.strm.avail_in = 0) ∨
      fetchRank fs' h' s' + 2 ≤ fetchRank fs h s)
    (f1 : s.err ≠ Z_OK → s.err ≠ Z_BUF_ERROR → s'.err ≠ Z_OK ∧ s'.err ≠ Z_BUF_ERROR)
    (f2 : r = -1 → (s'.err ≠ Z_OK ∧ s'.err ≠ Z_BUF_ERROR) ∨ (s'.eof ≠ 0 ∧ s'.strm.avail_in = 0))
    (f3 : s.err ≠ Z_OK → s.err ≠ Z_BUF_ERROR → s'.x.have ≠ 0 →
      s'.x.have.toNat = 2 * s'.size.toNat ∨ 9223372036854775807 ≤ s'.x.pos.toInt + s'.x.have.toNat ∨
      (s'.eof ≠ 0 ∧ s'.strm.avail_in = 0) ∨ fetchRank fs' h' s' + 2 ≤ fetchRank fs h s ∨
      (s'.how = GZIP ∧ Stuck h' s' ∧ ¬ Stuck h s))
    (f4 : s.err ≠ Z_OK → s.err ≠ Z_BUF_ERROR → s.how = GZIP → Stuck h s →
      s'.x.have = 0 ∧ (r = -1 ∨ (s'.eof ≠ 0 ∧ s'.strm.avail_in = 0))) :
    skipMeasureF fs' h' s' < skipMeasureF fs h s := by
  have eS : s'.skip.toInt.toNat = s.skip.toInt.toNat := by rw [hskip]
  have hG := skipGterm_mono (s := s) (s' := s') f1
  unfold skipMeasureF
  rw [eS]
  by_cases hD : SkipDead h s
  · obtain ⟨hz, hr⟩ := f4 (fun e => hD.1 (Or.inl e)) (fun e => hD.1 (Or.inr e)) hD.2.1 hD.2.2
    have hr0 : r = 0 := cont.resolve_right (fun x => x hz)
    have hE' : SkipEof s' := hr.resolve_left (fun e => absurd (hr0.symm.trans e) (by decide))
    rw [skipPhase_dead hh hE hD, skipPhase_eof hz hE']
    omega
  rw [skipPhase_fetch hh hE hD]
  by_cases hz : s'.x.have = 0
  · have hr0 : r = 0 := cont.resolve_right (fun x => x hz)
    rcases c0 hz hr0 with hE' | hlt
    · rw [skipPhase_eof hz hE']
      omega
    · have := skipPhase_zero_le (h := h') hz
      omega
  · by_cases hbig : 16 ≤ s'.x.have.toNat ∨ s'.skip.toInt ≤ (s'.x.have.toNat : Int) ∨ SkipEof s' ∨ SkipDead h' s'
    · rw [skipPhase_big hz hbig]
      omega
    · rw [skipPhase_small hz hbig]
      have n16 : ¬ 16 ≤ s'.x.have.toNat := fun a => hbig (Or.inl a)
      have nsk : ¬ s'.skip.toInt ≤ (s'.x.have.toNat : Int) := fun a => hbig (Or.inr (Or.inl a))
      have nE : ¬ (s'.eof ≠ 0 ∧ s'.strm.avail_in = 0) := fun a => hbig (Or.inr (Or.inr (Or.inl a)))
      have nD : ¬ SkipDead h' s' := fun a => hbig (Or.inr (Or.inr (Or.inr a)))
      have n2 : ¬ s'.x.have.toNat = 2 * s'.size.toNat := fun a => by have := hsize hz; omega
      have nmax : ¬ 9223372036854775807 ≤ s'.x.pos.toInt + s'.x.have.toNat := fun a => by
        rw [hpos] at a
        rw [hskip] at nsk
        omega
      rcases c1 hz with a | a | a | a | a
      · exact absurd a n2
      · by_cases g : SkipErrGood s
        · rcases f2 a with b | b
          · have g' : ¬ SkipErrGood s' := by
              rintro (e | e)
              · exact b.1 e
              · exact b.2 e
            rw [skipGterm_good g, skipGterm_bad g']
            omega
          · exact absurd b nE
        · rcases f3 (fun e => g (Or.inl e)) (fun e => g (Or.inr e)) hz with b | b | b | b | b
          · exact absurd b n2
          · exact absurd b nmax
          · exact absurd b nE
          · omega
          · have k := f1 (fun e => g (Or.inl e)) (fun e => g (Or.inr e))
            have g' : ¬ SkipErrGood s' := by
              rintro (e | e)
              · exact k.1 e
              · exact k.2 e
            exact absurd ⟨g', b.1, b.2.1⟩ nD
      · exact absurd a nmax
      · exact absurd a nE
      · omega

end measure

/-! ## The loop -/

/-- The entry facts of `gz_fetch` that are not yet clauses of `GzInv` (**open**). -/
def SkipEnt (s : GzState) : Prop :=
  MsgLit s ∧ s.err ≠ Z_STREAM_END ∧ (s.how = GZ_COPY → s.strm.avail_in = 0)

/-- What holds between the trips of `gz_skip`: the effect so far up to the pending skip, `ReadsFinite` and
`HasBudget` kept, the buffers' size kept, and the entry facts of `gz_fetch` on the record. -/
def SkipInvF (h : Heap) (i : Nat) (s : GzState) (fs : Fs) (fsc : Fs) (hc : Heap) : Prop :=
  AccU h i s fs [] fsc hc ∧ (ReadsFinite fs s.fd → ReadsFinite fsc s.fd) ∧
    (s.size ≠ 0 → ∀ sc, hc.gzstates i = some sc → sc.size = s.size) ∧
    (HasBudget fs s.fd → HasBudget fsc s.fd) ∧ (∀ sc, hc.gzstates i = some sc → SkipEnt sc)

/-- **`gz_skip`, the three halves, from `GzFetchSafe`**, with no skip left on success, the size of the buffers kept,
`ReadsFinite` and `HasBudget` kept, and the entry facts of `gz_fetch` kept on the final record (for `gz_read`). Premises beyond the skeleton statement: `fetch`; `msg`, `err`, `copy` (the entry facts of `gz_fetch`, to become
clauses of `GzInv`, **open**); and `skip : s.skip ≠ 0`, a statement correction: without it the skeleton statement
is false (with `skip = 0`, `x.pos = GZ_OFF_MAX`, nothing buffered and input left, the do-while fetches one byte and
ends with `x.pos + x.have > GZ_OFF_MAX`, against `GzReadInv.posHave`). Every caller (`gz_read`, `gzgetc_`, `gzgets`)
tests `skip != 0` before calling `gz_skip`. -/
theorem gz_skip_run_fetch (fetch : GzFetchSafe)
    (i : Nat) (h : Heap) (fs : Fs) (s : GzState) (inv : GzInv h i s) (hfs : FileSystem fs) (hm : s.mode = GZ_READ)
    (msg : MsgLit s) (err : s.err ≠ Z_STREAM_END) (copy : s.how = GZ_COPY → s.strm.avail_in = 0)
    (skip : s.skip ≠ 0) :
    RunSafe (Zlib.Gzread.gz_skip (gzSt i)) fs h (ReadsFinite fs s.fd) fun r fs' after =>
      (r = 0 ∨ r = -1) ∧ FdsKept fs fs' ∧ GzPost h i s [] fs' after GzInv ∧
      (r = 0 → ∀ s', after.gzstates i = some s' → s'.skip = 0) ∧
      (∀ s', after.gzstates i = some s' → s.size ≠ 0 → s'.size = s.size) ∧
      (ReadsFinite fs s.fd → ReadsFinite fs' s.fd) ∧ (HasBudget fs s.fd → HasBudget fs' s.fd) ∧
      (∀ s', after.gzstates i = some s' →
        MsgLit s' ∧ s'.err ≠ Z_STREAM_END ∧ (s'.how = GZ_COPY → s'.strm.avail_in = 0)) := by
  have V := views_nil (StartChanged h i s)
  unfold Zlib.Gzread.gz_skip
  dsimp only
  refine RunSafe.bind (P := fun y fs' h' => (y = none ∨ y = some 0 ∨ y = some (-1)) ∧ SkipInvF h i s fs fs' h' ∧
      SkipEnd y h' i ∧ (y = none → ∀ sc, h'.gzstates i = some sc → sc.skip = 0))
    (RunSafe.doWhile (fun k _ fs' h' => SkipInvF h i s fs fs' h' ∧
        ∃ sc, h'.gzstates i = some sc ∧ sc.skip ≠ 0 ∧ SkipEnt sc ∧ k = skipMeasureF fs' h' sc)
      (fun k y fs' h' => (y = none ∨ y = some 0 ∨ y = some (-1)) ∧ SkipInvF h i s fs fs' h' ∧
        (y = none → ∀ sc, h'.gzstates i = some sc → sc.skip ≠ 0 →
          SkipEnt sc ∧ (ReadsFinite fs s.fd → skipMeasureF fs' h' sc < k)) ∧ SkipEnd y h' i) _ ?_ ?_
      (k := skipMeasureF fs h s) (fun f => skipMeasureF_lt f)
      ⟨⟨AccU.refl [] inv.upToSkip hfs, id, fun _ sc hsc => by rw [Option.some.inj (inv.cur.symm.trans hsc)], fun x => x,
        fun sc hsc => by rw [← Option.some.inj (inv.cur.symm.trans hsc)]; exact ⟨msg, err, copy⟩⟩,
        s, inv.cur, skip, ⟨msg, err, copy⟩, rfl⟩) ?_
  · rintro k _ fsc hc ⟨⟨acc, hfin, hsz, hbud, -⟩, sk, hsk, hskc, ⟨emsg, eerr, ecopy⟩, rfl⟩
    obtain ⟨sc, invc, hmc, hfdc⟩ := acc.cur
    have e := Option.some.inj (invc.cur.symm.trans hsk)
    subst e
    have hmr : sc.mode = GZ_READ := hmc.trans hm
    have hp : 0 ≤ sc.skip.toInt := invc.2.2.1
    have hpb : sc.x.pos.toInt + sc.skip.toInt ≤ 9223372036854775807 := invc.2.2.2
    refine RunSafe.bind_lift (ldS_run invc.cur) ?_
    refine RunSafe.ite (fun hh => ?_) (fun hh => ?_)
    · -- buffered output: `gz_skip_have`
      have hh' : sc.x.have ≠ 0 := by simpa using hh
      obtain ⟨hr, hinv, -, -, -, -⟩ := gz_skip_have_run' invc
      refine RunSafe.bind_lift hr ?_
      refine RunSafe.pure' ⟨Or.inl rfl, ⟨acc.put invc hinv.upToSkip ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl V,
        hfin, fun hs0 s' hs' => ?_, hbud, fun s' hs' => by
          simp only [putGz, upd_same, Option.some.injEq] at hs'
          subst hs'
          exact ⟨emsg, eerr, ecopy⟩⟩, fun _ s' hs' hne => ?_, fun _ _ => ⟨fun e => (by cases e), fun e => by cases e⟩⟩
      · simp only [putGz, upd_same, Option.some.injEq] at hs'
        subst hs'
        exact hsz hs0 sc invc.cur
      · simp only [putGz, upd_same, Option.some.injEq] at hs'
        subst hs'
        exact ⟨⟨emsg, eerr, ecopy⟩, fun _ => skipMeasureF_have hp hh' hne⟩
    · have h0 : sc.x.have = 0 := by simpa using hh
      have invg : GzInv hc i sc := invc.inv (Or.inl h0)
      refine RunSafe.bind_lift (ldZ_run invc.cur) ?_
      refine RunSafe.ite (fun he => ?_) (fun he => ?_)
      · -- end of the input: break
        refine RunSafe.ite (fun _ => ?_) (fun _ => ?_)
        · obtain ⟨pl, hpl, ⟨t, ht⟩, hroot⟩ := lit_eof hc
          have hmsg : pl = .null ∨ ∃ t, CString hc pl t ∧ ∀ b, ByteRoot pl b → ¬ GzOwned hc i sc b :=
            Or.inr ⟨t, ht, fun b hb => absurd hb (hroot b)⟩
          obtain ⟨after, s', hrun, inv', hs', herr, fr, lc⟩ := gzErrorSpec_holds invg Z_BUF_ERROR pl hmsg
          refine RunSafe.bind_lift hpl (RunSafe.bind_lift hrun ?_)
          have acc2 := acc.step invc ((post_of_gz_error invg inv' hs' fr lc
            (gzErrorOwn_holds hc i sc _ _ after invg hmsg hrun) acc.fsys).mono fun _ x => x.upToSkip)
            (fun _ => Iff.rfl) V
          have hsize' : s'.size = sc.size := by rw [hs']
          have ent' : SkipEnt s' := by
            have hstrm : s'.strm = sc.strm := by rw [hs']
            have hhow : s'.how = sc.how := by rw [hs']
            refine ⟨fun hz => ?_, ?_, fun hcp => ?_⟩
            · rw [hstrm]
              exact emsg (by rw [← hsize']; exact hz)
            · rcases herr with e | ⟨e, -⟩ <;> rw [e] <;> decide
            · rw [hstrm]
              exact ecopy (by rw [← hhow]; exact hcp)
          refine RunSafe.bind_lift (updS_run inv'.cur _) ?_
          refine RunSafe.pure' ⟨Or.inr (Or.inl rfl), ⟨acc2.put inv'.upToSkip
            (inv'.put_past (by rw [hs']; exact hmr)).upToSkip
            ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl V, hfin, fun hs0 s2 hs2 => ?_, hbud, fun s2 hs2 => by
              simp only [setS, upd_same, Option.some.injEq] at hs2
              subst hs2
              exact ent'⟩, fun e => (by cases e),
            fun s2 hs2 => ⟨fun e => (by cases e), fun _ => ?_⟩⟩
          · simp only [setS, upd_same, Option.some.injEq] at hs2
            subst hs2
            exact hsize'.trans (hsz hs0 sc invc.cur)
          · simp only [setS, upd_same, Option.some.injEq] at hs2
            subst hs2
            rfl
        · refine RunSafe.bind_lift (updS_run invc.cur _) ?_
          refine RunSafe.pure' ⟨Or.inr (Or.inl rfl), ⟨acc.put invc (invg.put_past hmr).upToSkip
            ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl V, hfin, fun hs0 s2 hs2 => ?_, hbud, fun s2 hs2 => by
              simp only [setS, upd_same, Option.some.injEq] at hs2
              subst hs2
              exact ⟨emsg, eerr, ecopy⟩⟩, fun e => (by cases e),
            fun s2 hs2 => ⟨fun e => (by cases e), fun _ => ?_⟩⟩
          · simp only [setS, upd_same, Option.some.injEq] at hs2
            subst hs2
            exact hsz hs0 sc invc.cur
          · simp only [setS, upd_same, Option.some.injEq] at hs2
            subst hs2
            rfl
      · -- `gz_fetch`
        have hnend : ¬ SkipEof sc := fun ⟨a, b⟩ => he (by simp [a, b])
        have hu0 : GzInvUpToOutput hc i sc := upToOutput_of_inv invg hmr h0
        have F := (fetch i hc fsc sc hu0 h0 acc.fsys hmr eerr ecopy emsg).fin_mono
          (fun f => by rw [hfdc]; exact hfin f)
        refine RunSafe.bind F ?_
        rintro r fs2 h2 ⟨hr01, kept, post, hb1, hrf1, -, s2, hs2, keeps, msg2, -, -, -, ent2, ecopy2, -, hph2, hR,
          c0, c1, f1, f2, f3, f4⟩
        have hm2 : s2.mode = GZ_READ := keeps.1.trans hmr
        have hsk2 : s2.skip = sc.skip := keeps.2.2.1
        have hpos2 : s2.x.pos = sc.x.pos := keeps.2.2.2.1
        have hposlt : sc.x.pos.toInt < 9223372036854775807 := by
          have : sc.skip.toInt ≠ 0 := fun e0 => hskc (Int64.toInt_inj.mp (by rw [e0]; rfl))
          omega
        have hph2' : s2.x.pos.toInt + s2.x.have.toNat ≤ 9223372036854775807 := by
          rcases hph2 with a | ⟨a, _⟩
          · exact a
          · rw [hpos2] at a
            omega
        have u2 : GzInvOut h2 i s2 → GzInvUpToSkip h2 i s2 := fun ht =>
          upToSkip_of_out ht hm2 hph2' (by rw [hsk2]; exact hp) (by rw [hsk2, hpos2]; exact hpb)
        have post' : GzPost hc i sc [] fs2 h2 GzInvUpToSkip := post.mono fun t ht => by
          have e := Option.some.inj (ht.1.1.symm.trans hs2)
          rw [e] at ht ⊢
          exact u2 ht
        have acc2 := acc.step invc post' kept V
        have SI : SkipInvF h i s fs fs2 h2 := by
          refine ⟨acc2, fun f => by rw [← hfdc]; exact hrf1 (by rw [hfdc]; exact hfin f), fun hs0 sc' hsc' => ?_,
            fun f => by rw [← hfdc]; exact hb1 (by rw [hfdc]; exact hbud f), fun sc' hsc' => by
              rw [← Option.some.inj (hs2.symm.trans hsc')]
              exact ⟨msg2, ent2, ecopy2⟩⟩
          rw [← Option.some.inj (hs2.symm.trans hsc')]
          have e1 := hsz hs0 sc invc.cur
          rw [(keeps.2.2.2.2 (by rw [e1]; exact hs0)).1, e1]
        refine RunSafe.bind_lift (ldS_run hs2) ?_
        refine RunSafe.ite (fun hc1 => RunSafe.pure' ⟨by simp, SI, fun e => (by cases e),
          fun sc' hsc' => ⟨fun _ => ?_, fun e => by cases e⟩⟩) (fun hne => ?_)
        · rw [← Option.some.inj (hs2.symm.trans hsc')]
          simp at hc1
          exact hc1.2
        refine RunSafe.pure' ⟨by simp, SI, fun _ sc' hsc' _ => ?_, fun _ _ => ⟨fun e => (by cases e), fun e => by cases e⟩⟩
        rw [← Option.some.inj (hs2.symm.trans hsc')]
        refine ⟨⟨msg2, ent2, ecopy2⟩, fun f => ?_⟩
        have hB : HasBudget fsc sc.fd := by rw [hfdc]; exact (hfin f).1
        have cont : r = 0 ∨ s2.x.have ≠ 0 := by
          rcases hr01 with e | e
          · exact Or.inl e
          · exact Or.inr fun hz => hne (by simp [e, hz])
        obtain ⟨u, invu, -, -⟩ := acc2.cur
        have eu : u = s2 := Option.some.inj (invu.cur.symm.trans hs2)
        have invu2 : GzInvUpToSkip h2 i s2 := by rw [← eu]; exact invu
        have hsize : s2.x.have ≠ 0 → 8 ≤ s2.size.toNat := fun hz => size_of_have invu2 hm2 hz
        exact skipMeasureF_fetch h0 hnend hsk2 hpos2 hpb hsize cont (hR hB) (c0 hB) (c1 hB) f1 f2 (f3 hB) f4
  · rintro k y fsc hc ⟨hy, si, hlt, hend⟩
    obtain ⟨sc, invc, -, -⟩ := si.1.cur
    refine RunSafe.ite (fun hsome => RunSafe.pure' ⟨fun e => (by cases e), fun _ => ⟨hy, si, hend, fun hn => ?_⟩⟩)
      (fun hs => ?_)
    · subst hn
      simp at hsome
    refine RunSafe.bind_lift (ldS_run invc.cur) ?_
    have hyn : y = none := by
      cases y with
      | none => rfl
      | some _ => simp at hs
    refine RunSafe.pure' ⟨fun hc0 => ?_, fun hc0 => ⟨hy, si, hend, fun _ sc' hsc' => ?_⟩⟩
    · have hne : sc.skip ≠ 0 := by simpa using hc0
      obtain ⟨ent, hm'⟩ := hlt hyn sc invc.cur hne
      exact ⟨skipMeasureF fsc hc sc, hm', si, sc, invc.cur, hne, ent, rfl⟩
    · rw [← Option.some.inj (invc.cur.symm.trans hsc')]
      simpa using hc0
  · rintro y fs' h' ⟨hy, si, hend, hnone⟩
    have hr : y.getD 0 = 0 ∨ y.getD 0 = -1 := by rcases hy with rfl | rfl | rfl <;> simp
    have hend' : ∀ sc, h'.gzstates i = some sc → (y.getD 0 = -1 → sc.x.have = 0) ∧ (y.getD 0 = 0 → sc.skip = 0) := by
      intro sc hsc
      obtain ⟨e1, e2⟩ := hend sc hsc
      rcases hy with rfl | rfl | rfl
      · exact ⟨fun e => absurd e (by decide), fun _ => hnone rfl sc hsc⟩
      · exact ⟨fun e => absurd e (by decide), fun _ => e2 rfl⟩
      · exact ⟨fun _ => e1 rfl, fun e => absurd e (by decide)⟩
    exact RunSafe.pure' ⟨hr, si.1.1, skip_post_inv hr si.1 hend', fun h0 sc hsc => (hend' sc hsc).2 h0,
      fun sc hsc hs0 => si.2.2.1 hs0 sc hsc, si.2.1, si.2.2.2.1, fun sc hsc => si.2.2.2.2 sc hsc⟩

/-- **`gz_skip_safe`** (skeleton statement, branch `skeleton/gz`) from `GzFetchSafe`, with the entry facts of
`gz_fetch` (`msg`, `err`, `copy`, **open**) and the statement correction `skip : s.skip ≠ 0` (see
`gz_skip_run_fetch`). -/
theorem gz_skip_safe_fetch (fetch : GzFetchSafe)
    (i : Nat) (h : Heap) (fs : Fs) (s : GzState) (inv : GzInv h i s) (hfs : FileSystem fs) (hm : s.mode = GZ_READ)
    (msg : MsgLit s) (err : s.err ≠ Z_STREAM_END) (copy : s.how = GZ_COPY → s.strm.avail_in = 0)
    (skip : s.skip ≠ 0) :
    RunSafe (Zlib.Gzread.gz_skip (gzSt i)) fs h (ReadsFinite fs s.fd) fun r fs' after =>
      (r = 0 ∨ r = -1) ∧ FdsKept fs fs' ∧ GzPost h i s [] fs' after GzInv :=
  (gz_skip_run_fetch fetch i h fs s inv hfs hm msg err copy skip).mono fun _ _ _ x => ⟨x.1, x.2.1, x.2.2.1⟩

/-- `gz_skip` in the shape of the read side's `GzSkipRead` (premise of `gz_read_safe_of`, `gz.read-read`, not yet on
`dev`): the same proposition, so that `gzSkipRead_holds` is `gz_skip_read_fetch fetch` once that definition lands. -/
theorem gz_skip_read_fetch (fetch : GzFetchSafe) :
    ∀ (i : Nat) (h : Heap) (fs : Fs) (s : GzState), GzInv h i s → FileSystem fs → s.mode = GZ_READ → s.skip ≠ 0 →
      s.err ≠ Z_STREAM_END → (s.how = GZ_COPY → s.strm.avail_in = 0) → MsgLit s →
      RunSafe (Zlib.Gzread.gz_skip (gzSt i)) fs h (ReadsFinite fs s.fd) fun r fs' after =>
        (r = 0 ∨ r = -1) ∧ FdsKept fs fs' ∧ GzPost h i s [] fs' after GzInv ∧
        (ReadsFinite fs s.fd → ReadsFinite fs' s.fd) ∧
        ∃ s', after.gzstates i = some s' ∧ MsgLit s' ∧ s'.err ≠ Z_STREAM_END ∧
          (s'.how = GZ_COPY → s'.strm.avail_in = 0) ∧ (r = 0 → s'.skip = 0) :=
  fun i h fs s inv hfs hm skip err copy msg =>
    (gz_skip_run_fetch fetch i h fs s inv hfs hm msg err copy skip).mono fun _ _ _ x => by
      obtain ⟨hr, kept, post, hsk, -, hrf, -, hent⟩ := x
      obtain ⟨s', inv', -⟩ := post.2
      have hrec := inv'.cur
      have e := hent s' hrec
      exact ⟨hr, kept, post, hrf, s', hrec, e.1, e.2.1, e.2.2, fun h0 => hsk h0 s' hrec⟩

#print axioms GzInv.put_out
#print axioms skipMeasureF_fetch
#print axioms gz_skip_run_fetch
#print axioms gz_skip_safe_fetch
#print axioms gz_skip_read_fetch

end ZlibF.Spec.Public.GzRead
