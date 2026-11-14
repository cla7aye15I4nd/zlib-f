import ZlibF.Proof.«gz.read-leaf-common»
import ZlibF.Proof.«gzread.c.skip-fetch»

/-!
# gzread.c: `gz_skip` from the invariant up to the pending skip, and its termination

`gzungetc` calls `gz_skip` right after `gz_look`, whose COPY branch may leave output buffered while a skip is pending,
so its entry is `GzInvUpToSkip`, not `GzInv`. `gz_skip_run_upto` is `gz_skip_run_fetch` (`gzread.c.skip-fetch`) from
that entry: the loop of `gz_skip_run_fetch` already runs on `GzInvUpToSkip` records, and the entry facts of
`gz_fetch` (`MsgLit`, `err ≠ Z_STREAM_END`, COPY → `avail_in = 0`) are clauses of the reader invariant of the record
with the skip cleared (`GzReadInv.msgLit`, `errEnd`, `copyIn`), which name no field that `clearSkip` changes. The
position bound `x.pos + x.have ≤ GZ_OFF_MAX` is `GzReadInv.posHave` of that record. The proof text of the loop is
the one of `gz_skip_run_fetch`, with the entry changed.

`gzSkipTerminates_holds`: the termination premise `GzSkipTerminates` of `gz.read-leaf-common`, from `GzFetchSafe`
alone (the termination half of `gz_skip_run_upto`).
-/

namespace ZlibF.Spec.Public.GzRead
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib.Spec Zlib.Gzlib.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- **`gz_skip` from the invariant up to the pending skip**, from `GzFetchSafe`: `gz_skip_run_fetch` with the entry
`GzInvUpToSkip` (the entry facts of `gz_fetch` are read off the reader invariant). -/
theorem gz_skip_run_upto (fetch : GzFetchSafe)
    (i : Nat) (h : Heap) (fs : Fs) (s : GzState) (u : GzInvUpToSkip h i s) (hfs : FileSystem fs)
    (hm : s.mode = GZ_READ) (skip : s.skip ≠ 0) :
    RunSafe (Zlib.Gzread.gz_skip (gzSt i)) fs h (ReadsFinite fs s.fd) fun r fs' after =>
      (r = 0 ∨ r = -1) ∧ FdsKept fs fs' ∧ GzPost h i s [] fs' after GzInv ∧
      (r = 0 → ∀ s', after.gzstates i = some s' → s'.skip = 0) ∧
      (∀ s', after.gzstates i = some s' → s.size ≠ 0 → s'.size = s.size) ∧
      (ReadsFinite fs s.fd → ReadsFinite fs' s.fd) ∧ (HasBudget fs s.fd → HasBudget fs' s.fd) ∧
      (∀ s', after.gzstates i = some s' →
        MsgLit s' ∧ s'.err ≠ Z_STREAM_END ∧ (s'.how = GZ_COPY → s'.strm.avail_in = 0)) := by
  have rd := u.reader hm
  have msg : MsgLit s := rd.msgLit
  have err : s.err ≠ Z_STREAM_END := rd.errEnd
  have copy : s.how = GZ_COPY → s.strm.avail_in = 0 := rd.copyIn
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
      ⟨⟨AccU.refl [] u hfs, id, fun _ sc hsc => by rw [Option.some.inj (u.cur.symm.trans hsc)], fun x => x,
        fun sc hsc => by rw [← Option.some.inj (u.cur.symm.trans hsc)]; exact ⟨msg, err, copy⟩⟩,
        s, u.cur, skip, ⟨msg, err, copy⟩, rfl⟩) ?_
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
          obtain ⟨after, s', hrun, inv', hs', herr, fr, lc⟩ := gzErrorSpec_holds invg Z_BUF_ERROR pl hmsg (by decide)
          refine RunSafe.bind_lift hpl (RunSafe.bind_lift hrun ?_)
          have acc2 := acc.step invc ((post_of_gz_error invg inv' hs' fr lc
            (gzErrorOwn_holds hc i sc _ _ after invg hmsg (by decide) hrun) acc.fsys).mono fun _ x => x.upToSkip)
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

/-- **`GzSkipTerminates`** (`gz.read-leaf-common`) from `GzFetchSafe`. -/
theorem gzSkipTerminates_holds (fetch : GzFetchSafe) : GzSkipTerminates :=
  fun i h fs s u hfs hm hsk hf => (gz_skip_run_upto fetch i h fs s u hfs hm hsk).2.1 hf

#print axioms gz_skip_run_upto
#print axioms gzSkipTerminates_holds

end ZlibF.Spec.Public.GzRead
