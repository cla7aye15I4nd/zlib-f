import ZlibF.Proof.«gz.read-fetch-specs»
import ZlibF.Proof.«gzread.c.getc-ungetc»
import ZlibF.Proof.«gzlib.c.error-inv-premises»
import ZlibF.Proof.«gz.read-look»
import ZlibF.Proof.«gz.read-fetch»
import ZlibF.Proof.«gz.read-decomp»
import ZlibF.Proof.«inflate.c.stuck-no-output»

/-!
# gz read side: shared facts for the public read leaves

Facts that `gzdirect`, `gzgets`, `gzungetc` and `gzgetc` use to move between the invariants of a reading call:

- `GzInv.put_next`: with nothing buffered (`x.have = 0`), `x.next` may be anything (`GzCommon.next`,
  `GzReadInv.output` speak only of buffered output), so a write of `x.next` alone keeps `GzInv`.
- `GzInv.upToOutput`: a reader in `GzInv` with nothing buffered is in `GzInvUpToOutput`.
- `GzInvUpToOutput.inv0`: back, when nothing is buffered.
- `GzInvOut.upToSkip`: the invariant after a fetching helper (`GzInvOut`) gives the invariant up to the pending
  skip, when the end of the buffered output is a representable position.
-/

namespace ZlibF.Spec.Public.GzRead
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib.Spec Zlib.Gzlib.Proofs ZlibF.Spec.Public
set_option autoImplicit false

private theorem read_ne_write' : GZ_READ ≠ GZ_WRITE := by decide

/-- **A write of `x.next` with nothing buffered keeps `GzInv`** (reader). -/
theorem GzInv.put_next {h : Heap} {i : Nat} {s : GzState} (inv : GzInv h i s) (hm : s.mode = GZ_READ)
    (h0 : s.x.have = 0) (p : BPtr) :
    GzInv (putGz h i { s with x := { s.x with next := p } }) i { s with x := { s.x with next := p } } := by
  have c := inv.common
  have hs := c.record
  have hrec := c.recordFree
  have hso : ∀ b, StreamOwned (putGz h i { s with x := { s.x with next := p } }) (gzStrm i) b =
      StreamOwned h (gzStrm i) b := putGz_streamOwned hs rfl
  have hown : ∀ b, GzOwned (putGz h i { s with x := { s.x with next := p } }) i
      { s with x := { s.x with next := p } } b ↔ GzOwned h i s b :=
    putGz_owned hs ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hget := putGz_get (s' := { s with x := { s.x with next := p } }) hs rfl
  refine ⟨?_, ?_, ?_⟩
  · exact {
      record := by simp [putGz]
      mode := c.mode
      fresh := putGz_fresh hs c.fresh
      uniq := putGz_uniq hs c.uniq
      globals := c.globals
      fit := putGz_fit c.fit
      path := by
        obtain ⟨q, hq, hmb⟩ := c.path
        exact ⟨q, by rw [putGz_cstring]; exact hq, hmb⟩
      msg := by
        rcases c.msg with hn | ⟨m, hmm, hb⟩
        · exact Or.inl hn
        · exact Or.inr ⟨m, by rw [putGz_cstring]; exact hmm, hb⟩
      memerr := c.memerr
      want := c.want
      size := c.size
      distinct := by
        simp only [hso]
        exact c.distinct
      live := fun b hb => (putGz_live hs b).2 (c.live b ((hown b).1 hb))
      pos := c.pos
      next := fun hh => absurd h0 hh
      nullHave := fun _ => h0
      recordFree := by rw [hso]; exact c.recordFree }
  · intro _
    have r := inv.reader hm
    exact {
      how := r.how
      copyDirect := r.copyDirect
      gzipDirect := r.gzipDirect
      direct := r.direct
      junk := r.junk
      flags := r.flags
      unalloc := r.unalloc
      bufs := r.bufs
      input := r.input
      output := fun hh => absurd h0 hh
      codec := fun hz => by
        obtain ⟨reach, z, k, st, hzget, hzst, hk, hhead⟩ := r.codec hz
        exact ⟨StreamReachable.rebuffer reach (putGz_rebuffer inv rfl hrec) (fun _ => putGz_fit c.fit),
          z, k, st, by rw [hget]; exact hzget, hzst, hk, hhead⟩
      posHave := r.posHave
      againSize := r.againSize
      haveSkip := r.haveSkip
      againEof := r.againEof
      errEnd := r.errEnd
      copyIn := r.copyIn
      msgLit := r.msgLit }
  · intro hw
    exact absurd (hm.symm.trans hw) read_ne_write'

theorem putGz_putGz₂ (h : Heap) (i : Nat) (v w : GzState) : putGz (putGz h i v) i w = putGz h i w := by
  simp [putGz, upd_upd]

theorem putGz_self₂ {H : Heap} {i : Nat} {s : GzState} (hs : H.gzstates i = some s) : putGz H i s = H := by
  show { H with gzstates := upd H.gzstates i (some s) } = H
  rw [upd_self _ _ _ hs]

/-- A reader in `GzInv` with nothing buffered is in `GzInvUpToOutput`. -/
theorem GzInv.upToOutput {h : Heap} {i : Nat} {s : GzState} (inv : GzInv h i s) (hm : s.mode = GZ_READ)
    (h0 : s.x.have = 0) : GzInvUpToOutput h i s := by
  refine ⟨inv.common.record, ?_⟩
  have e : clearOut s = { s with x := { s.x with next := .null } } := by
    simp only [clearOut, h0]
  rw [e]
  exact GzInv.put_next inv hm h0 .null

/-- `GzInvUpToOutput` with nothing buffered is `GzInv`. -/
theorem GzInvUpToOutput.inv0 {h : Heap} {i : Nat} {s : GzState} (hu : GzInvUpToOutput h i s)
    (hm : s.mode = GZ_READ) (h0 : s.x.have = 0) : GzInv h i s := by
  obtain ⟨hs, inv⟩ := hu
  have := GzInv.put_next inv hm rfl s.x.next
  have e1 : { clearOut s with x := { (clearOut s).x with next := s.x.next } } = s := by
    simp only [clearOut, ← h0]
  rw [e1, putGz_putGz₂, putGz_self₂ hs] at this
  exact this

theorem rec_have0 (s : GzState) (h0 : s.x.have = 0) : { s with x := { s.x with «have» := 0 } } = s := by
  obtain ⟨x⟩ := s
  all_goals (cases x; simp_all)

/-- **The invariant after a fetching helper gives the invariant up to the pending skip**, when the end of the
buffered output, `x.pos + x.have`, is a representable position (`GzReadInv.posHave`). The buffered output then
is the window of `OutWindow`, inside the handle's `out`. -/
theorem GzInvOut.upToSkip {h : Heap} {i : Nat} {s : GzState} (ho : GzInvOut h i s) (hm : s.mode = GZ_READ)
    (hph : s.x.pos.toInt + s.x.have.toNat ≤ 9223372036854775807) : GzInvUpToSkip h i s := by
  obtain ⟨⟨hs, inv⟩, ow⟩ := ho
  have hmc : (clearOut s).mode = GZ_READ := hm
  have c := inv.common
  have rd := inv.reader hmc
  have hpl := s.x.pos.toInt_lt
  have z : (0 : Int64).toInt = 0 := by decide
  have p0 : 0 ≤ s.x.pos.toInt := by
    have := c.pos.2.2
    simpa [clearOut] using this
  refine ⟨hs, ?_, c.pos.1, c.pos.2.1⟩
  -- the record with nothing buffered and no pending skip
  have invA := inv.put_scalars (s' := clearSkip (clearOut s)) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    ⟨c.want.1, c.want.2, Or.inr rfl⟩
    ⟨by show 0 ≤ (0 : Int64).toInt; rw [z]; exact Int.le_refl _,
      by show s.x.pos.toInt + (0 : Int64).toInt ≤ _; rw [z]; omega,
      by show 0 ≤ s.x.pos.toInt + ((0 : UInt32).toNat : Int); simpa using p0⟩
    (Nat.le_refl _) (fun _ => ⟨rd.how, rd.copyDirect, rd.gzipDirect, rd.junk, rd.flags.1, rd.flags.2.1,
      rd.flags.2.2, fun hz => (rd.unalloc hz).2.2.1, rd.againSize,
      by show s.x.pos.toInt + ((0 : UInt32).toNat : Int) ≤ _; simp; omega, fun _ => rfl, rd.againEof⟩)
    (fun hw => absurd (hm.symm.trans hw) read_ne_write') (fun _ hc => rd.copyIn hc)
  rw [putGz_putGz₂] at invA
  have hmA : (clearSkip (clearOut s)).mode = GZ_READ := hm
  by_cases h0 : s.x.have = 0
  · have inv1 := GzInv.put_next invA hmA rfl s.x.next
    rw [putGz_putGz₂] at inv1
    have e : { clearSkip (clearOut s) with x := { (clearSkip (clearOut s)).x with next := s.x.next } } =
        clearSkip s := by
      have := rec_have0 (clearSkip s) h0
      rw [← this]
      rfl
    rw [e] at inv1
    exact inv1
  · obtain ⟨c0, hx, hc0⟩ := ow h0
    have hz : (clearSkip (clearOut s)).size ≠ 0 := by
      intro hz
      have hz' : s.size.toNat = 0 := by
        show (clearSkip (clearOut s)).size.toNat = 0; rw [hz]; rfl
      have : s.x.have.toNat = 0 := by omega
      exact h0 (UInt32.toNat_inj.mp (by rw [this]; rfl))
    obtain ⟨ob, a, hout, -, -, -⟩ := GetcUngetc.out_buf invA hmA hz
    have hout' : s.out = .ref (BRef.blk ob) 0 := hout
    have := GetcUngetc.put_push (s' := clearSkip s) invA hmA hz
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hout
      (c0 := c0) (by show s.x.next = _; rw [hx, hout']; simp [padv]) hc0 rd.flags.2.1
      (by show s.x.pos.toInt + (0 : Int64).toInt ≤ _; rw [z]; omega)
      (by show 0 ≤ s.x.pos.toInt + (s.x.have.toNat : Int); omega)
      hph (fun _ => rfl)
    rw [putGz_putGz₂] at this
    exact this

/-! ## `gz_skip` over the facts of `gz_fetch` it uses -/

/-- **What `gz_skip` uses of `gz_fetch`**: called from its loop (a reader in `GzInv`, nothing buffered, a pending
skip), `gz_fetch` does not fault, and when it returns, the record is in the invariant up to the pending skip (the
end of the buffered output is a representable position, since `x.pos + skip ≤ GZ_OFF_MAX` and `skip > 0` leave
room), the skip is kept and the buffers keep their size. Derived from `GzFetchSafe` in `gzFetchFacts_of`. -/
def FetchFacts : Prop :=
  ∀ (i : Nat) (h : Heap) (fs : Fs) (s : GzState), GzInv h i s → FileSystem fs → s.mode = GZ_READ →
    s.x.have = 0 → s.skip ≠ 0 →
    RunSafe (Zlib.Gzread.gz_fetch (gzSt i)) fs h False fun r fs' after =>
      (r = 0 ∨ r = -1) ∧ FdsKept fs fs' ∧ GzPost h i s [] fs' after GzInvUpToSkip ∧
      (ReadsFinite fs s.fd → ReadsFinite fs' s.fd) ∧
      ∀ s', after.gzstates i = some s' → s'.skip = s.skip ∧ (s.size ≠ 0 → s'.size = s.size)

/-- What holds between the rounds of `gz_skip`. -/
def SkipInv' (h : Heap) (i : Nat) (s : GzState) (fs : Fs) (fsc : Fs) (hc : Heap) : Prop :=
  AccU h i s fs [] fsc hc ∧ (s.size ≠ 0 → ∀ sc, hc.gzstates i = some sc → sc.size = s.size) ∧
    (ReadsFinite fs s.fd → ReadsFinite fsc s.fd)

/-- **`gz_skip`, no fault and the post-condition** (termination apart), from a reader in the invariant up to the
pending skip with a pending skip. It ends with no skip left (`0`), or with nothing buffered (`-1`), and the buffers
keep their size. -/
theorem gz_skip_post (fetch : FetchFacts) (i : Nat) (h : Heap) (fs : Fs) (s : GzState)
    (inv : GzInvUpToSkip h i s) (hfs : FileSystem fs) (hm : s.mode = GZ_READ) (hsk : s.skip ≠ 0) :
    RunSafe (Zlib.Gzread.gz_skip (gzSt i)) fs h False fun r fs' after =>
      (r = 0 ∨ r = -1) ∧ SkipInv' h i s fs fs' after ∧
      ∀ sc, after.gzstates i = some sc → (r = -1 → sc.x.have = 0) ∧ (r = 0 → sc.skip = 0) := by
  have V := views_nil (StartChanged h i s)
  have gzerr : GzErrorSpec := gzErrorSpec_holds
  have gzerrOwn : GzErrorOwn := gzErrorOwn_holds
  unfold Zlib.Gzread.gz_skip
  dsimp only
  refine RunSafe.bind (P := fun y fs' h' => (y = none ∨ y = some 0 ∨ y = some (-1)) ∧ SkipInv' h i s fs fs' h' ∧
      SkipEnd y h' i ∧ (y = none → ∀ sc, h'.gzstates i = some sc → sc.skip = 0))
    (RunSafe.doWhile (fun _ _ fs' h' => SkipInv' h i s fs fs' h' ∧ ∃ sc, h'.gzstates i = some sc ∧ sc.skip ≠ 0)
      (fun _ y fs' h' => (y = none ∨ y = some 0 ∨ y = some (-1)) ∧ SkipInv' h i s fs fs' h' ∧ SkipEnd y h' i) _
      ?_ ?_ (k := 0) (fun f => f.elim)
      ⟨⟨AccU.refl [] inv hfs, fun _ sc hsc => by rw [Option.some.inj (inv.cur.symm.trans hsc)], id⟩, s, inv.cur,
        hsk⟩) ?_
  · rintro k _ fsc hc ⟨⟨acc, hsz, hrf⟩, sk, hsk', hskne⟩
    obtain ⟨sc, invc, hmc, hfdc⟩ := acc.cur
    have e := Option.some.inj (invc.cur.symm.trans hsk')
    subst e
    have hmr : sc.mode = GZ_READ := hmc.trans hm
    refine RunSafe.bind_lift (ldS_run invc.cur) ?_
    refine RunSafe.ite (fun hh => ?_) (fun hh => ?_)
    · obtain ⟨hr, hinv, -, -, -, -⟩ := gz_skip_have_run' invc
      refine RunSafe.bind_lift hr ?_
      refine RunSafe.pure' ⟨Or.inl rfl, ⟨acc.put invc hinv.upToSkip ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl V,
        fun hs0 s' hs' => ?_, hrf⟩, fun _ _ => ⟨fun e => (by cases e), fun e => by cases e⟩⟩
      simp only [putGz, upd_same, Option.some.injEq] at hs'
      subst hs'
      exact hsz hs0 sc invc.cur
    · have h0 : sc.x.have = 0 := by simpa using hh
      have invg : GzInv hc i sc := invc.inv (Or.inl h0)
      refine RunSafe.bind_lift (ldZ_run invc.cur) ?_
      refine RunSafe.ite (fun he => ?_) (fun he => ?_)
      · refine RunSafe.ite (fun _ => ?_) (fun _ => ?_)
        · obtain ⟨p, hp, ⟨t, ht⟩, hroot⟩ := lit_eof hc
          have hmsg : p = .null ∨ ∃ t, CString hc p t ∧ ∀ b, ByteRoot p b → ¬ GzOwned hc i sc b :=
            Or.inr ⟨t, ht, fun b hb => absurd hb (hroot b)⟩
          obtain ⟨after, s', hrun, inv', hs', -, fr, lc⟩ := gzerr invg Z_BUF_ERROR p hmsg (by decide)
          refine RunSafe.bind_lift hp (RunSafe.bind_lift hrun ?_)
          have acc2 := acc.step invc ((post_of_gz_error invg inv' hs' fr lc
            (gzerrOwn hc i sc _ _ after invg hmsg (by decide) hrun) acc.fsys).mono fun _ x => x.upToSkip) (fun _ => Iff.rfl) V
          have hsize' : s'.size = sc.size := by rw [hs']
          refine RunSafe.bind_lift (updS_run inv'.cur _) ?_
          refine RunSafe.pure' ⟨Or.inr (Or.inl rfl), ⟨acc2.put inv'.upToSkip
            (inv'.put_past (by rw [hs']; exact hmr)).upToSkip
            ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl V, fun hs0 s2 hs2 => ?_, hrf⟩,
            fun s2 hs2 => ⟨fun e => (by cases e), fun _ => ?_⟩⟩
          · simp only [setS, upd_same, Option.some.injEq] at hs2
            subst hs2
            exact hsize'.trans (hsz hs0 sc invc.cur)
          · simp only [setS, upd_same, Option.some.injEq] at hs2
            subst hs2
            rfl
        · refine RunSafe.bind_lift (updS_run invc.cur _) ?_
          refine RunSafe.pure' ⟨Or.inr (Or.inl rfl), ⟨acc.put invc (invg.put_past hmr).upToSkip
            ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl V, fun hs0 s2 hs2 => ?_, hrf⟩,
            fun s2 hs2 => ⟨fun e => (by cases e), fun _ => ?_⟩⟩
          · simp only [setS, upd_same, Option.some.injEq] at hs2
            subst hs2
            exact hsz hs0 sc invc.cur
          · simp only [setS, upd_same, Option.some.injEq] at hs2
            subst hs2
            rfl
      · have F := fetch i hc fsc sc invg acc.fsys hmr h0 hskne
        refine RunSafe.bind F ?_
        rintro r fs2 h2 ⟨hr01, kept, post, rf2, keep⟩
        have acc2 := acc.step invc post kept V
        obtain ⟨s2, inv2, -, -⟩ := acc2.cur
        obtain ⟨-, hsz2'⟩ := keep s2 inv2.cur
        have hsz2 : s.size ≠ 0 → ∀ sc', h2.gzstates i = some sc' → sc'.size = s.size := by
          intro hs0 sc' hsc'
          have e2 := Option.some.inj (inv2.cur.symm.trans hsc')
          subst e2
          have := hsz hs0 sc invc.cur
          rw [hsz2' (by rw [this]; exact hs0), this]
        refine RunSafe.bind_lift (ldS_run inv2.cur) ?_
        have hrf2 : ReadsFinite fs s.fd → ReadsFinite fs2 s.fd := fun f => by
          rw [← hfdc]; exact rf2 (by rw [hfdc]; exact hrf f)
        refine RunSafe.ite (fun hc1 => RunSafe.pure' ⟨by simp, ⟨acc2, hsz2, hrf2⟩,
          fun sc' hsc' => ⟨fun _ => ?_, fun e => by cases e⟩⟩) (fun _ => ?_)
        · rw [← Option.some.inj (inv2.cur.symm.trans hsc')]
          simp at hc1
          exact hc1.2
        exact RunSafe.pure' ⟨by simp, ⟨acc2, hsz2, hrf2⟩, fun _ _ => ⟨fun e => (by cases e), fun e => by cases e⟩⟩
  · rintro k y fsc hc ⟨hy, si, hend⟩
    obtain ⟨sc, invc, -, -⟩ := si.1.cur
    refine RunSafe.ite (fun hsome => RunSafe.pure' ⟨fun e => (by cases e), fun _ => ⟨hy, si, hend, fun hn => ?_⟩⟩)
      (fun hs => ?_)
    · subst hn; simp_all
    refine RunSafe.bind_lift (ldS_run invc.cur) ?_
    refine RunSafe.pure' ⟨fun hc0 => ⟨0, fun f => f.elim, si, sc, invc.cur, by simpa using hc0⟩,
      fun hc0 => ⟨hy, si, hend, fun _ sc' hsc' => ?_⟩⟩
    rw [← Option.some.inj (invc.cur.symm.trans hsc')]
    simpa using hc0
  · rintro y fs' h' ⟨hy, si, hend, hnone⟩
    refine RunSafe.pure' ⟨?_, si, fun sc hsc => ?_⟩
    · rcases hy with rfl | rfl | rfl <;> simp
    · obtain ⟨e1, e2⟩ := hend sc hsc
      rcases hy with rfl | rfl | rfl
      · exact ⟨fun e => absurd e (by decide), fun _ => hnone rfl sc hsc⟩
      · exact ⟨fun e => absurd e (by decide), fun _ => e2 rfl⟩
      · exact ⟨fun _ => e1 rfl, fun e => absurd e (by decide)⟩

/-- **The statement `gzungetc` and `gzgets` use for `gz_skip`**: batch 3's `GzSkipSpec'` with the premise
`skip ≠ 0` (both call `gz_skip` only then). Without it the statement is false: with `skip = 0`, `x.pos = GZ_OFF_MAX`,
nothing buffered and COPY mode, the first trip fetches one byte (patch 0004's `room ? room : 1`) and `gz_skip`
returns with `x.pos + x.have > GZ_OFF_MAX`, outside `GzInv`. -/
def GzSkipSpecNZ : Prop :=
  ∀ (i : Nat) (h : Heap) (fs : Fs) (s : GzState), GzInvUpToSkip h i s → FileSystem fs → s.mode = GZ_READ →
    s.skip ≠ 0 →
    RunSafe (Zlib.Gzread.gz_skip (gzSt i)) fs h (ReadsFinite fs s.fd) fun r fs' after =>
      (r = 0 ∨ r = -1) ∧ FdsKept fs fs' ∧ GzPost h i s [] fs' after GzInv ∧
      (r = 0 → ∀ s', after.gzstates i = some s' → s'.skip = 0) ∧
      (∀ s', after.gzstates i = some s' → s.size ≠ 0 → s'.size = s.size) ∧
      (ReadsFinite fs s.fd → ReadsFinite fs' s.fd)

/-- **The termination of `gz_skip`** (a premise): from a reader in the invariant up to the pending skip, with a
pending skip and the read budget of `ReadsFinite`, `gz_skip` returns within the fuel of the model. The progress
clause of `GzFetchSafe` (output, the end of the input, or a stall that lowered the budget) bounds the trips by
`2·skip + budget + 2`, which can pass the `2^64` trips of `gdoWhile`; the real bound needs how much output a
`gz_fetch` delivers. -/
def GzSkipTerminates : Prop :=
  ∀ (i : Nat) (h : Heap) (fs : Fs) (s : GzState), GzInvUpToSkip h i s → FileSystem fs → s.mode = GZ_READ →
    s.skip ≠ 0 → ReadsFinite fs s.fd → ∃ r fs' after, Zlib.Gzread.gz_skip (gzSt i) fs h = .ok ((r, fs'), after)

/-- `GzSkipSpecNZ` from the facts of `gz_fetch` and the termination premise. -/
theorem gzSkipSpecNZ_of (fetch : FetchFacts) (term : GzSkipTerminates) : GzSkipSpecNZ := by
  intro i h fs s u hfs hm hsk
  have R := gz_skip_post fetch i h fs s u hfs hm hsk
  refine ⟨R.1, fun hf => term i h fs s u hfs hm hsk hf, fun r fs' after he => ?_⟩
  obtain ⟨hr, ⟨⟨k, post⟩, hsz, hrf⟩, hend⟩ := R.2.2 r fs' after he
  exact ⟨hr, k, skip_post_inv hr ⟨k, post⟩ hend, fun h0 s' hs' => (hend s' hs').2 h0,
    fun s' hs' hs0 => hsz hs0 s' hs', hrf⟩

/-! ## Facts of the callees, from their statements on `dev` -/

/-- **The open fact of `inflate`** behind `gz_decomp_safe_of`: a call from `BAD` or `MEM` moves nothing
(`InflateStuckNoOutput`). -/
def DecompFacts : Prop := InflateStuckNoOutput

/-- **The three reader facts** that `GzFetchSafe` and `GzLookSpec` take as premises: the embedded stream's message
is `NULL` or a literal (`MsgLit`), `err ≠ Z_STREAM_END`, and COPY mode has no pending input. They are clauses of
`GzReadInv` (`msgLit`, `errEnd`, `copyIn`); `readInvFacts_holds` reads them off. -/
structure ReadInvFacts : Prop where
  msgLit : ∀ (h : Heap) (i : Nat) (s : GzState), GzInv h i s → s.mode = GZ_READ → MsgLit s
  noEnd : ∀ (h : Heap) (i : Nat) (s : GzState), GzInv h i s → s.mode = GZ_READ → s.err ≠ Z_STREAM_END
  copyIn : ∀ (h : Heap) (i : Nat) (s : GzState), GzInv h i s → s.mode = GZ_READ → s.how = GZ_COPY →
    s.strm.avail_in = 0

theorem readInvFacts_holds : ReadInvFacts :=
  ⟨fun _ _ _ inv hm => (inv.reader hm).msgLit, fun _ _ _ inv hm => (inv.reader hm).errEnd,
    fun _ _ _ inv hm => (inv.reader hm).copyIn⟩

/-- **`gz_look` that fails leaves nothing buffered** (`gzLookFailEmpty_holds`, from the `-1` clause of `GzLookSpec`). -/
def GzLookFailEmpty : Prop :=
  ∀ (i : Nat) (h : Heap) (fs : Fs) (s : GzState) (fs' : Fs) (after : Heap),
    GzInvUpToOutput h i s → s.x.have = 0 → FileSystem fs → s.mode = GZ_READ → s.how = LOOK → MsgLit s →
    Zlib.Gzread.gz_look (gzSt i) fs h = .ok ((-1, fs'), after) → ∀ s', after.gzstates i = some s' → s'.x.have = 0

/-- **`gz_fetch` buffers only what fits before `GZ_OFF_MAX`**, or one byte at `GZ_OFF_MAX` (`gzFetchRoom_holds`, from
the position clause of `GzFetchSafe`). -/
def GzFetchRoom : Prop :=
  ∀ (i : Nat) (h : Heap) (fs : Fs) (s : GzState) (r : Int32) (fs' : Fs) (after : Heap),
    GzInvUpToOutput h i s → s.x.have = 0 → FileSystem fs → s.mode = GZ_READ → s.err ≠ Z_STREAM_END →
    (s.how = GZ_COPY → s.strm.avail_in = 0) → MsgLit s →
    Zlib.Gzread.gz_fetch (gzSt i) fs h = .ok ((r, fs'), after) → ∀ s', after.gzstates i = some s' →
      s'.x.pos.toInt + s'.x.have.toNat ≤ 9223372036854775807 ∨ s'.x.pos.toInt = 9223372036854775807

theorem gzLookFailEmpty_holds : GzLookFailEmpty := by
  intro i h fs s fs' after hu h0 hfs hm hlk hml he s' hs'
  have L := gz_look_safe i h fs s hu h0 hfs hm hlk hml
  obtain ⟨-, -, -, -, -, -, s'', hs'', -, -, -, -, -, hrm1, -⟩ := L.2.2 (-1) fs' after he
  have e : s' = s'' := Option.some.inj (hs'.symm.trans hs'')
  subst e
  exact (hrm1 rfl).2.2

theorem gzFetchRoom_holds (head : DecompFacts) : GzFetchRoom := by
  intro i h fs s r fs' after hu h0 hfs hm hne hc hml he s' hs'
  have F := gz_fetch_safe_of gz_look_safe (gz_decomp_safe_of head) i h fs s hu h0 hfs hm hne hc hml
  obtain ⟨-, -, -, -, -, -, s'', hs'', -, -, -, -, -, -, -, -, hpos, -⟩ := F.2.2 r fs' after he
  have e : s' = s'' := Option.some.inj (hs'.symm.trans hs'')
  subst e
  rcases hpos with hb | ⟨hb, -⟩
  · exact Or.inl hb
  · exact Or.inr hb

/-- The facts of `gz_fetch` that `gz_skip` uses, from `gz_fetch_safe_of`, `gz_look_safe`, `gz_decomp_safe_of` and the
open premises. -/
theorem fetchFacts_of (P : ReadInvFacts) (head : DecompFacts) (room : GzFetchRoom) : FetchFacts := by
  intro i h fs s inv hfs hm h0 hsk
  have hu := GzInv.upToOutput inv hm h0
  have F := gz_fetch_safe_of gz_look_safe (gz_decomp_safe_of head) i h fs s hu h0 hfs hm (P.noEnd h i s inv hm)
    (P.copyIn h i s inv hm) (P.msgLit h i s inv hm)
  refine ⟨F.1, fun f => f.elim, fun r fs' after he => ?_⟩
  obtain ⟨hr, k, post, -, rf, -, s', hs', keep, -⟩ := F.2.2 r fs' after he
  have hroom := room i h fs s r fs' after hu h0 hfs hm (P.noEnd h i s inv hm) (P.copyIn h i s inv hm)
    (P.msgLit h i s inv hm) he s' hs'
  have c := inv.common
  have hsk1 : 1 ≤ s.skip.toInt := by
    have := c.pos.1
    have : s.skip.toInt ≠ 0 := fun e => hsk (Int64.toInt_inj.mp (by rw [e]; rfl))
    omega
  have hpos : s'.x.pos = s.x.pos := keep.2.2.2.1
  have hb : s'.x.pos.toInt + s'.x.have.toNat ≤ 9223372036854775807 := by
    rcases hroom with hb | hb
    · exact hb
    · have := c.pos.2.1
      rw [hpos] at hb
      omega
  refine ⟨hr, k, post.mono fun t ht => ?_, rf, fun s'' hs'' => ?_⟩
  · have e : t = s' := Option.some.inj (ht.1.1.symm.trans hs')
    subst e
    exact GzInvOut.upToSkip ht (keep.1.trans hm) hb
  · have e : s'' = s' := Option.some.inj (hs''.symm.trans hs')
    subst e
    exact ⟨keep.2.2.1, fun hz => (keep.2.2.2.2 hz).1⟩

/-- A record write after a step, as one more step with no caller region (any invariant that names the record). -/
theorem post_put_any {I : Heap → Nat → GzState → Prop} {h2 : Heap} {i : Nat} {s2 s3 : GzState} {fs : Fs}
    (hs2 : h2.gzstates i = some s2) (live2 : ∀ b, GzOwned h2 i s2 b → h2.live b)
    (inv3 : I (putGz h2 i s3) i s3)
    (same : s3.path = s2.path ∧ s3.msg = s2.msg ∧ s3.«in» = s2.«in» ∧ s3.out = s2.out ∧ s3.size = s2.size ∧
      s3.mode = s2.mode ∧ s3.direct = s2.direct ∧ s3.strm = s2.strm) (hfd : s3.fd = s2.fd) (hfs : FileSystem fs) :
    GzPost h2 i s2 [] fs (putGz h2 i s3) I := by
  have hown := putGz_owned (s' := s3) hs2 same
  refine ⟨hfs, s3, inv3, same.2.2.2.2.2.1, hfd, BufferFrame.nil_of_frame ?_, ?_, fun b hb => Or.inl ((hown b).1 hb)⟩
  · refine ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, ?_⟩
    intro b _ hb
    have hbi : b ≠ i := fun e => hb (Or.inl e)
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, by simp [putGz, upd_ne _ _ _ _ hbi], rfl⟩
  · intro b
    have := putGz_live (s' := s3) hs2 b
    have ho := hown b
    have := live2 b
    grind

end ZlibF.Spec.Public.GzRead
