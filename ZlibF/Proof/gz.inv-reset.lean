import ZlibF.Proof.«gz.inv-clearerr»

/-!
# gz safety: `gz_reset` keeps `GzInv`

`GzInv.drop_input`: setting `strm.avail_in = 0` keeps the invariant (a rebuffer of the codec). With
`GzInv.clear_message` and `GzInv.put_scalars` it gives `GzInv.gz_reset` (skeleton statement, unchanged).
-/

namespace ZlibF.Spec.Public
open C Zlib.GzFs
open Zlib.Gzlib.Proofs (freeStr)
set_option autoImplicit false

/-- **Dropping the buffered input of the codec keeps `GzInv`.** -/
theorem GzInv.drop_input {h : Heap} {i : Nat} {s : GzState} (inv : GzInv h i s) :
    GzInv (putGz h i { s with strm := { s.strm with avail_in := 0 } }) i
      { s with strm := { s.strm with avail_in := 0 } } := by
  have c := inv.common
  have hs := c.record
  have gH : ZStreamRef.get (putGz h i { s with strm := { s.strm with avail_in := 0 } }) (gzStrm i) =
      some { s.strm with avail_in := 0 } := by
    simp [ZStreamRef.get, gzStrm, putGz]
  have gh : ZStreamRef.get h (gzStrm i) = some s.strm := by simp [ZStreamRef.get, gzStrm, hs]
  have hso : ∀ b, StreamOwned (putGz h i { s with strm := { s.strm with avail_in := 0 } }) (gzStrm i) b ↔
      StreamOwned h (gzStrm i) b := by
    intro b
    unfold StreamOwned
    rw [gH, gh]
    simp only [Option.some.injEq, exists_eq_left']
    try rfl
  have hso' : ∀ b, StreamOwned (putGz h i { s with strm := { s.strm with avail_in := 0 } })
      (.in_gzstate_strm i) b ↔ StreamOwned h (.in_gzstate_strm i) b := hso
  have hown : ∀ b, GzOwned (putGz h i { s with strm := { s.strm with avail_in := 0 } }) i
      { s with strm := { s.strm with avail_in := 0 } } b ↔ GzOwned h i s b := by
    intro b
    unfold GzOwned
    dsimp only
    rw [hso']
  have hreb : Rebuffer h (putGz h i { s with strm := { s.strm with avail_in := 0 } }) (gzStrm i) := by
    refine ⟨putGz_fresh hs c.fresh, putGz_uniq hs c.uniq, c.globals, ?_, s.strm,
      { s.strm with avail_in := 0 }, gh, gH, rfl⟩
    refine ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, ?_⟩
    intro b _ hb
    have hbi : b ≠ i := by
      intro e
      subst e
      exact hb c.recordFree
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, by simp [putGz, upd_ne _ _ _ _ hbi], rfl⟩
  have fitH := putGz_fit (s' := { s with strm := { s.strm with avail_in := 0 } }) (i := i) c.fit
  refine ⟨?_, ?_, ?_⟩
  · exact {
      record := by simp [putGz]
      mode := c.mode
      fresh := putGz_fresh hs c.fresh
      uniq := putGz_uniq hs c.uniq
      globals := c.globals
      fit := fitH
      path := by
        obtain ⟨p, hp, hm⟩ := c.path
        exact ⟨p, (putGz_cstring _ _).2 hp, hm⟩
      msg := by
        rcases c.msg with hn | ⟨m, hm, hb⟩
        · exact Or.inl hn
        · exact Or.inr ⟨m, (putGz_cstring _ _).2 hm, hb⟩
      memerr := c.memerr
      want := c.want
      size := c.size
      distinct := ⟨c.distinct.1, fun p hp b hb =>
        ⟨(c.distinct.2 p hp b hb).1, by rw [hso]; exact (c.distinct.2 p hp b hb).2⟩⟩
      live := fun b hb => (putGz_live hs b).2 (c.live b ((hown b).1 hb))
      pos := c.pos
      next := fun hh => by
        obtain ⟨b, off, a, hx, hbi, ho, hmb, hb, hle⟩ := c.next hh
        exact ⟨b, off, a, hx, hbi, (hown b).2 ho, hmb, hb, hle⟩
      nullHave := c.nullHave
      recordFree := by rw [hso]; exact c.recordFree }
  · intro hm
    have r := inv.reader hm
    exact {
      how := r.how
      copyDirect := r.copyDirect
      gzipDirect := r.gzipDirect
      direct := r.direct
      junk := r.junk
      flags := r.flags
      unalloc := fun hz => by
        obtain ⟨h1, _, h3, h4⟩ := r.unalloc hz
        exact ⟨h1, rfl, h3, h4⟩
      bufs := r.bufs
      input := Or.inl rfl
      output := r.output
      codec := fun hz => by
        obtain ⟨reach, z, k, st, hzget, hzst, hk, hhead⟩ := r.codec hz
        have hz' : z = s.strm := by rw [gh] at hzget; exact (Option.some.inj hzget).symm
        subst hz'
        exact ⟨StreamReachable.rebuffer reach hreb (fun _ => fitH), _, k, st, gH, hzst, hk, hhead⟩
      posHave := r.posHave
      againSize := r.againSize
      haveSkip := r.haveSkip
      againEof := fun _ _ => rfl
      errEnd := r.errEnd
      copyIn := fun _ => rfl
      msgLit := r.msgLit }
  · intro hm
    have w := inv.writer hm
    exact {
      have0 := w.have0
      direct := w.direct
      reset := w.reset
      unalloc := w.unalloc
      bufs := w.bufs
      input := w.input.imp (fun hn => ⟨hn.1, rfl⟩) (fun ⟨hz, a, ha, hle⟩ => ⟨hz, a, ha, by simp <;> omega⟩)
      output := w.output
      codec := fun hd hz => by
        obtain ⟨reach, z, k, d, hzget, hzst, hk, hhead⟩ := w.codec hd hz
        have hz' : z = s.strm := by rw [gh] at hzget; exact (Option.some.inj hzget).symm
        subst hz'
        exact ⟨StreamReachable.rebuffer reach hreb (fun e => nomatch e), _, k, d, gH, hzst, hk, hhead⟩
      transparent := w.transparent }

/-- The run of `gz_reset` on a handle in `GzInv` (as `gz_reset_run`). -/
theorem gz_reset_inv_run {h : Heap} {i : Nat} {s : GzState} (inv : GzInv h i s) :
    Zlib.Gzlib.gz_reset (gzSt i) h =
      .ok ((), Zlib.Gzlib.Spec.setS (freeStr h s.msg) i (Zlib.Gzlib.Spec.resetRec s)) := by
  have hs := inv.common.record
  have hmem := inv.common.memerr
  show Zlib.Gzlib.gz_reset (some (.tab i)) h = _
  unfold Zlib.Gzlib.gz_reset
  rcases inv.common.msg with hn | ⟨_, _, mb, a, hm, ha, hro, _⟩
  · by_cases hmo : s.mode = GZ_READ
    · gsimp [hs, hn, hmo, Zlib.Gzlib.gz_error, Zlib.Gzlib.Spec.resetRec]
    · gsimp [hs, hn, hmo, Zlib.Gzlib.gz_error, Zlib.Gzlib.Spec.resetRec]
  · have hne : s.err ≠ Z_MEM_ERROR := fun h' => by have := hmem h'; rw [hm] at this; cases this
    by_cases hmo : s.mode = GZ_READ
    · gsimp [hs, hm, hne, hmo, Zlib.Gzlib.Proofs.freeB_blk_setS ha hro, Zlib.Gzlib.gz_error,
        Zlib.Gzlib.Spec.resetRec]
    · gsimp [hs, hm, hne, hmo, Zlib.Gzlib.Proofs.freeB_blk_setS ha hro, Zlib.Gzlib.gz_error,
        Zlib.Gzlib.Spec.resetRec]

/-- Interface: `gz_reset` keeps the invariant and clears the buffered output, the position and the skip.
Relies on the local patch for R-3 (`gz_reset` writes `x.next`). -/
theorem GzInv.gz_reset {h : Heap} {i : Nat} {s : GzState} (inv : GzInv h i s) :
    ∃ after s', C.run (Zlib.Gzlib.gz_reset (gzSt i)) h = .ok ((), after) ∧ GzInv after i s' ∧
      s'.x.have = 0 ∧ s'.x.pos = 0 ∧ s'.skip = 0 ∧ s'.err = Z_OK ∧ s'.msg = .null ∧
      Frame h after (fun b => b = i ∨ blkOf s.msg = some b) ∧
      LiveChange h after (fun _ => False) (fun b => blkOf s.msg = some b) := by
  have hs := inv.common.record
  -- step 1: the message
  obtain ⟨inv1, own1, live1, frame1⟩ := inv.clear_message s.eof s.past Z_OK (by decide)
    (fun hm => ⟨(inv.reader hm).flags.1, (inv.reader hm).flags.2.1, (inv.reader hm).againEof⟩)
  -- step 2: the scalars of `resetRec`
  have h0 : (0 : Int64).toInt = 0 := rfl
  have main : ∃ s2 : GzState,
      GzInv (putGz (putGz (freeStr h s.msg) i { s with eof := s.eof, past := s.past, msg := .null, err := Z_OK })
        i s2) i s2 ∧ { s2 with strm := { s2.strm with avail_in := 0 } } = Zlib.Gzlib.Spec.resetRec s := by
    by_cases hmo : s.mode = GZ_READ
    · have hmo' : (s.mode == GZ_READ) = true := by simpa using hmo
      refine ⟨{ s with eof := 0, how := LOOK, junk := -1, x := { s.x with «have» := 0, pos := 0 },
                       past := 0, again := 0, skip := 0, msg := .null, err := Z_OK }, ?_, ?_⟩
      · exact inv1.put_scalars ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
          ⟨inv.common.want.1, inv.common.want.2, Or.inr rfl⟩
          ⟨by show (0 : Int) ≤ (0 : Int64).toInt; decide,
            by show (0 : Int64).toInt + (0 : Int64).toInt ≤ 9223372036854775807; decide,
            by show (0 : Int) ≤ (0 : Int64).toInt + ((0 : UInt32).toNat : Int); decide⟩
          (by show (0 : UInt32).toNat ≤ _; exact Nat.zero_le _)
          (fun _ => ⟨Or.inl rfl, fun e => absurd e (by show ¬ (LOOK = GZ_COPY); decide),
            fun e => absurd e (by show ¬ (LOOK = GZIP); decide), Or.inl rfl,
            Or.inl rfl, Or.inl rfl, Or.inl rfl, fun _ => rfl, fun _ => rfl,
            by show (0 : Int64).toInt + ((0 : UInt32).toNat : Int) ≤ 9223372036854775807; decide, fun _ => rfl,
            fun h0 _ => absurd rfl h0⟩)
          (fun hw => absurd (hmo.symm.trans hw) (by decide)) (fun _ => (fun hc => absurd hc (by show ¬ (LOOK = GZ_COPY); decide)))
      · unfold Zlib.Gzlib.Spec.resetRec
        rw [hmo']
        rfl
    · have hmo' : (s.mode == GZ_READ) = false := by simpa using hmo
      refine ⟨{ s with reset := 0, x := { s.x with «have» := 0, pos := 0 },
                       past := 0, again := 0, skip := 0, msg := .null, err := Z_OK }, ?_, ?_⟩
      · exact inv1.put_scalars ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
          ⟨inv.common.want.1, inv.common.want.2, Or.inr rfl⟩
          ⟨by show (0 : Int) ≤ (0 : Int64).toInt; decide,
            by show (0 : Int64).toInt + (0 : Int64).toInt ≤ 9223372036854775807; decide,
            by show (0 : Int) ≤ (0 : Int64).toInt + ((0 : UInt32).toNat : Int); decide⟩
          (by show (0 : UInt32).toNat ≤ _; exact Nat.zero_le _)
          (fun hr => absurd hr hmo)
          (fun _ => Or.inl rfl) (fun hr => absurd hr hmo)
      · unfold Zlib.Gzlib.Spec.resetRec
        rw [hmo']
        rfl
  obtain ⟨s2, inv2, hrr⟩ := main
  -- step 3: the input of the codec
  have inv3 := inv2.drop_input
  have heq : putGz (putGz (putGz (freeStr h s.msg) i
      { s with eof := s.eof, past := s.past, msg := .null, err := Z_OK }) i s2) i
        { s2 with strm := { s2.strm with avail_in := 0 } } =
      Zlib.Gzlib.Spec.setS (freeStr h s.msg) i (Zlib.Gzlib.Spec.resetRec s) := by
    rw [hrr]
    simp [putGz, Zlib.Gzlib.Spec.setS, upd_upd]
  rw [heq, hrr] at inv3
  refine ⟨_, _, gz_reset_inv_run inv, inv3, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Zlib.Gzlib.Spec.resetRec]
  · simp only [Zlib.Gzlib.Spec.resetRec]
  · simp only [Zlib.Gzlib.Spec.resetRec]
  · simp only [Zlib.Gzlib.Spec.resetRec]
  · simp only [Zlib.Gzlib.Spec.resetRec]
  · refine ⟨frame1.1, frame1.2.1, frame1.2.2.1, frame1.2.2.2.1, frame1.2.2.2.2.1, ?_⟩
    intro b hl hb
    obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := frame1.2.2.2.2.2 b hl hb
    have hbi : b ≠ i := fun e => hb (Or.inl e)
    exact ⟨e1, e2, e3, e4, e5, e6, by simp [Zlib.Gzlib.Spec.setS, putGz, upd_ne _ _ _ _ hbi] at e7 ⊢; exact e7, e8⟩
  · have hsD : (freeStr h s.msg).gzstates i = some s := by
      unfold freeStr
      split <;> exact hs
    intro b
    have := live1 b
    have hl : (Zlib.Gzlib.Spec.setS (freeStr h s.msg) i (Zlib.Gzlib.Spec.resetRec s)).live b ↔
        (putGz (freeStr h s.msg) i { s with eof := s.eof, past := s.past, msg := .null, err := Z_OK }).live b := by
      exact (putGz_live hsD b).trans (putGz_live hsD b).symm
    rw [hl, this]
    simp

end ZlibF.Spec.Public
