import ZlibF.Proof.«gz.read-leaf-common»
import ZlibF.Proof.«gz.read-read»
import ZlibF.Proof.«gz.read-assembly»

/-!
# gz read side: `gzgetc` and `gzungetc`, aligned with the skeleton statements

`gzread.c.getc-ungetc` (batch 3) proves `gzgetc_step_of` and `gzungetc_step_of` over premise definitions. This file
derives the skeleton statements from proved theorems where they exist, and restates `gzungetc` where a premise
definition of batch 3 is false.

- `gzgetc_step`: `GetcUngetc.gzgetc_step_of` with its premises discharged: `gz_error` (`gzErrorSpec_holds`,
  `gzErrorOwn_holds`) and `GzReadSpec`, from the read-side owner's `gz_read_safe_stuck` and the proved
  `inflateStuckNoOutput_holds`. No premise is left.
- `gzungetc`: batch 3's `GzSkipSpec'` quantifies over every pending skip, also `0`, and is false there (see
  `GzSkipSpecNZ`); it rested on `GzFetchProgress`, which is false. The stages `tLook` and `tAgain` are re-proved here
  over `GzSkipSpecNZ` and `LookFacts` (`gz_look` called only in LOOK mode with nothing buffered, as `gzungetc` does).
  `tSkip_run` is reused. `gzungetc_step_of_term` has one open premise, `GzSkipTerminates`: the termination of `gz_skip`
  from the invariant up to the pending skip. `gzungetc` calls `gz_skip` after `gz_look`, whose COPY branch may leave
  output buffered with a skip pending; batch 3's `gz_skip_safe_fetch` starts from `GzInv` and does not cover that
  record.
-/

namespace ZlibF.Spec.Public.GzRead
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib.Spec Zlib.Gzlib.Proofs ZlibF.Spec.Public
open ZlibF.Spec.Public.GetcUngetc (EffI Eff good_skip good_inv tSkip_run again_run again_step tLook tAgain
  gzungetc_eq)
set_option autoImplicit false

/-! ## `gzgetc` -/

/-- **`gzgetc_step`** (skeleton statement) from the skeleton statement of `gz_read_safe` (`GzReadSpec`). -/
theorem gzgetc_step_of' (read : GetcUngetc.GzReadSpec) (i : Nat) : GzCallSafe i (.gzgetc (some (.in_gzstate_x i))) :=
  GetcUngetc.gzgetc_step_of read GetcUngetc.gzErrorSpec_holds GetcUngetc.gzErrorOwn_holds i

/-! ## `gzungetc` -/

/-- **What `gzungetc` and `gzdirect` use of `gz_look`**: on a reader in `GzInv` in LOOK mode with nothing buffered,
`gz_look` does not fault and returns; afterwards the record is in the invariant up to the pending skip, no buffers
means a serious error, and the read budget stays finite. Derived from `gz_look_safe` in `lookFacts_of`. -/
def LookFacts : Prop :=
  ∀ (i : Nat) (h : Heap) (fs : Fs) (s : GzState), GzInv h i s → FileSystem fs → s.mode = GZ_READ →
    s.x.have = 0 → s.how = LOOK →
    RunSafe (Zlib.Gzread.gz_look (gzSt i)) fs h True fun r fs' after =>
      (r = 0 ∨ r = -1) ∧ FdsKept fs fs' ∧ GzPost h i s [] fs' after GzInvUpToSkip ∧
      (∀ s', after.gzstates i = some s' → s'.size = 0 → s'.err ≠ Z_OK ∧ s'.err ≠ Z_BUF_ERROR) ∧
      (ReadsFinite fs s.fd → ReadsFinite fs' s.fd)

/-- `LookFacts` from `gz_look_safe`, `MsgLit` and `GzLookFailEmpty`. -/
theorem lookFacts_of (ml : ∀ (h : Heap) (i : Nat) (s : GzState), GzInv h i s → s.mode = GZ_READ → MsgLit s)
    (lf : GzLookFailEmpty) : LookFacts := by
  intro i h fs s inv hfs hm h0 hlk
  have hu := GzInv.upToOutput inv hm h0
  have L := gz_look_safe i h fs s hu h0 hfs hm hlk (ml h i s inv hm)
  refine ⟨L.1, fun _ => L.2.1 trivial, fun r fs' after he => ?_⟩
  obtain ⟨hr, k, post, -, rf, -, s', hs', keep, -, -, -, hsz, -, -, prog⟩ := L.2.2 r fs' after he
  have hb : s'.x.pos.toInt + s'.x.have.toNat ≤ 9223372036854775807 := by
    by_cases hh : s'.x.have = 0
    · have := s'.x.pos.toInt_lt
      rw [hh]; simp; omega
    · rcases hr with rfl | rfl
      · rcases prog rfl with ⟨_, e, _⟩ | ⟨_, e, _⟩ | ⟨_, _, _, hb⟩
        · exact absurd e hh
        · exact absurd e hh
        · exact hb
      · exact absurd (lf i h fs s fs' after hu h0 hfs hm hlk (ml h i s inv hm) he s' hs') hh
  refine ⟨hr, k, post.mono fun t ht => ?_, fun s'' hs'' => ?_, rf⟩
  · have e : t = s' := Option.some.inj (ht.1.1.symm.trans hs')
    subst e
    exact GzInvOut.upToSkip ht (keep.1.trans hm) hb
  · have e : s'' = s' := Option.some.inj (hs''.symm.trans hs')
    subst e
    exact hsz

/-- `tAgain` over `GzSkipSpecNZ`. -/
theorem tAgain_run' (skip : GzSkipSpecNZ) {i : Nat} {c : Int32}
    {h : Heap} {s : GzState} {fs fs1 : Fs} {hh : Heap} {s2 : GzState} (e : EffI GzInvUpToSkip i h s fs fs1 hh)
    (u2 : GzInvUpToSkip hh i s2) (hm2 : s2.mode = GZ_READ) (hfd2 : s2.fd = s.fd) (hz2 : s2.size ≠ 0)
    (hfin : ReadsFinite fs s.fd → ReadsFinite fs1 s.fd) :
    RunSafe (tAgain c (some (.tab i))) fs1 hh (ReadsFinite fs s.fd) (fun _ fs' after => Eff i h s fs fs' after) := by
  unfold tAgain
  dsimp only
  refine GetcUngetc.RunSafe.bind_lift (ldS_run u2.cur) ?_
  refine GetcUngetc.RunSafe.ite (fun hk => ?_) (fun hk => ?_)
  · have hk' : s2.skip ≠ 0 := by simpa using hk
    refine GetcUngetc.RunSafe.bind (GetcUngetc.RunSafe.fin_mono (skip i hh fs1 s2 u2 e.2.1 hm2 hk')
      (fun hf => by rw [hfd2]; exact hfin hf)) ?_
    rintro r fs3 h3 ⟨hr01, k3, post3, hsk3, hsz3, -⟩
    have e3 : Eff i h s fs fs3 h3 := GetcUngetc.EffI.trans good_skip good_inv e u2.cur post3 k3
    obtain ⟨_, s3, inv3, m3, _, _⟩ := post3
    refine GetcUngetc.RunSafe.ite (fun _ => GetcUngetc.RunSafe.pure' e3) (fun hr => ?_)
    have hr0 : r = 0 := by
      rcases hr01 with h0 | h0
      · exact h0
      · exact absurd (by simp [h0]) hr
    exact tSkip_run GetcUngetc.gzErrorSpec_holds GetcUngetc.gzErrorOwn_holds e3 inv3 (m3.trans hm2)
      (by rw [hsz3 s3 inv3.common.record hz2]; exact hz2) (hsk3 hr0 s3 inv3.common.record)
  · have hsk : s2.skip = 0 := by simpa using hk
    exact tSkip_run GetcUngetc.gzErrorSpec_holds GetcUngetc.gzErrorOwn_holds (e.toEff u2.cur (Or.inr hsk))
      (u2.inv (Or.inr hsk)) hm2 hz2 hsk

/-- `tLook` over `GzSkipSpecNZ`. -/
theorem tLook_run' (skip : GzSkipSpecNZ) {i : Nat} {c : Int32}
    {h : Heap} {s : GzState} {fs fs1 : Fs} {h1 : Heap} {s1 : GzState} (e : EffI GzInvUpToSkip i h s fs fs1 h1)
    (u1 : GzInvUpToSkip h1 i s1) (hm1 : s1.mode = GZ_READ) (hfd1 : s1.fd = s.fd)
    (hsz : s1.size = 0 → s1.err ≠ Z_OK ∧ s1.err ≠ Z_BUF_ERROR)
    (hfin : ReadsFinite fs s.fd → ReadsFinite fs1 s.fd) :
    RunSafe (tLook c (some (.tab i))) fs1 h1 (ReadsFinite fs s.fd) (fun _ fs' after => Eff i h s fs fs' after) := by
  have r1 := u1.reader hm1
  unfold tLook
  refine GetcUngetc.RunSafe.bind_lift (ldS_run u1.cur) ?_
  refine GetcUngetc.RunSafe.ite (fun hr => GetcUngetc.RunSafe.pure' ?_) (fun hr => ?_)
  · have hz : s1.size = 0 := Classical.byContradiction fun hne => by simp [hne] at hr
    exact e.toEff u1.cur (Or.inl (r1.unalloc hz).1)
  have hz1 : s1.size ≠ 0 := by
    intro hz
    have ha : s1.again = 0 := r1.againSize hz
    obtain ⟨n1, n2⟩ := hsz hz
    exact hr (by simp [n1, n2, ha, hz])
  dsimp only
  refine GetcUngetc.RunSafe.ite (fun _ => ?_) (fun _ => tAgain_run' skip e u1 hm1 hfd1 hz1 hfin)
  refine GetcUngetc.RunSafe.bind_lift (again_run u1) ?_
  obtain ⟨u2, post2⟩ := again_step (fs := fs1) u1 hm1 e.2.1
  exact tAgain_run' skip (GetcUngetc.EffI.trans good_skip good_skip e u1.cur post2 (fun _ => Iff.rfl)) u2 hm1
    hfd1 hz1 hfin

/-- **The run of `gzungetc`** over `LookFacts` and `GzSkipSpecNZ`. -/
theorem gzungetc_run' (look : LookFacts) (skip : GzSkipSpecNZ)
    (i : Nat) (c : Int32) (h : Heap) (fs : Fs) (s : GzState) (inv : GzInv h i s) (hfs : FileSystem fs) :
    RunSafe (Zlib.Gzread.gzungetc c (some (.in_gzstate_x i))) fs h (ReadsFinite fs s.fd)
      (fun _ fs' after => Eff i h s fs fs' after) := by
  rw [gzungetc_eq]
  refine GetcUngetc.RunSafe.bind_lift (ldS_run inv.common.record) ?_
  refine GetcUngetc.RunSafe.ite (fun _ => GetcUngetc.RunSafe.pure' (GetcUngetc.Eff.refl inv hfs)) (fun hm => ?_)
  have hm' : s.mode = GZ_READ := by simpa using hm
  dsimp only
  refine GetcUngetc.RunSafe.ite (fun hl => ?_) (fun hl => ?_)
  · have hh : s.x.have = 0 := by simp at hl; exact hl.2
    have hlk : s.how = LOOK := by simp at hl; exact hl.1
    refine GetcUngetc.RunSafe.bind (GetcUngetc.RunSafe.fin_mono (look i h fs s inv hfs hm' hh hlk)
      (fun _ => trivial)) ?_
    rintro r fs1 h1 ⟨_, k1, post1, hsz1, hfin1⟩
    have e1 : EffI GzInvUpToSkip i h s fs fs1 h1 := ⟨k1, post1⟩
    obtain ⟨_, s1, u1, m1, f1, _⟩ := post1
    exact tLook_run' skip e1 u1 (m1.trans hm') f1 (hsz1 s1 u1.cur) hfin1
  · refine tLook_run' skip (GetcUngetc.Eff.refl inv hfs).upToSkip inv.upToSkip hm' rfl ?_ id
    intro hz
    obtain ⟨hh, _, hlook, _⟩ := (inv.reader hm').unalloc hz
    exact absurd (by simp [hlook, hh]) hl

/-- **`gzungetc_step`** (skeleton statement) from `LookFacts` and `GzSkipSpecNZ`. -/
theorem gzungetc_step_of' (look : LookFacts) (skip : GzSkipSpecNZ) (i : Nat) (c : Int32) :
    GzCallSafe i (.gzungetc c (some (.in_gzstate_x i))) := by
  intro h fs s inv hfs _
  have R := gzungetc_run' look skip i c h fs s inv hfs
  exact ⟨R.1, fun hn => R.2.1 (hn trivial), fun v fs' after he => GetcUngetc.Eff.post rfl (R.2.2 v fs' after he)⟩

/-- **`gzungetc_step`** (skeleton statement), from the open fact of `inflate` (`InflateStuckNoOutput`) and the
termination of `gz_skip` from the invariant up to the pending skip (`GzSkipTerminates`). `gzungetc` calls `gz_skip`
after `gz_look`, whose COPY branch may leave output buffered with a skip pending, so batch 3's `gz_skip_safe_fetch`
(entry in `GzInv`) does not apply there; its no-fault and post halves are `gz_skip_post`. -/
theorem gzungetc_step_of (stuck : InflateStuckNoOutput) (term : GzSkipTerminates)
    (i : Nat) (c : Int32) : GzCallSafe i (.gzungetc c (some (.in_gzstate_x i))) :=
  gzungetc_step_of' (lookFacts_of readInvFacts_holds.msgLit gzLookFailEmpty_holds)
    (gzSkipSpecNZ_of (fetchFacts_of readInvFacts_holds stuck (gzFetchRoom_holds stuck)) term) i c

/-- `gz_read`'s statement in the read-side owner's form (`GzReadSafe`) gives batch 3's `GzReadSpec`: its three extra
premises are clauses of `GzReadInv`. -/
theorem gzReadSpec_of (read : GzReadSafe) : GetcUngetc.GzReadSpec := by
  intro i buf len h fs s inv hfs hm hbuf
  have r := inv.reader hm
  exact (read i buf len h fs s inv hfs hm hbuf r.errEnd r.copyIn r.msgLit).mono
    fun _ _ _ ⟨a, b, c, _⟩ => ⟨a, b, c⟩

/-- **`gzgetc_step`** (skeleton statement) from `gz_read`'s statement `GzReadSafe` (`gz_read_safe_of` gives it
from `gz_skip`'s statement `GzSkipRead`). -/
theorem gzgetc_step_of (read : GzReadSafe) (i : Nat) : GzCallSafe i (.gzgetc (some (.in_gzstate_x i))) :=
  gzgetc_step_of' (gzReadSpec_of read) i

/-- **`gzgetc_step`** (skeleton statement), from the one open fact of `inflate` (`InflateStuckNoOutput`), through
`gz_read_safe_stuck`. -/
theorem gzgetc_step_stuck (stuck : InflateStuckNoOutput) (i : Nat) : GzCallSafe i (.gzgetc (some (.in_gzstate_x i))) :=
  gzgetc_step_of (gz_read_safe_stuck stuck) i

/-- **`gzgetc_step`**, the skeleton statement. -/
theorem gzgetc_step (i : Nat) : GzCallSafe i (.gzgetc (some (.in_gzstate_x i))) :=
  gzgetc_step_stuck inflateStuckNoOutput_holds i

/-- **`gzungetc_step`** (skeleton statement) with one open premise, the termination of `gz_skip` from the invariant
up to the pending skip (`GzSkipTerminates`). -/
theorem gzungetc_step_of_term (term : GzSkipTerminates) (i : Nat) (c : Int32) :
    GzCallSafe i (.gzungetc c (some (.in_gzstate_x i))) :=
  gzungetc_step_of inflateStuckNoOutput_holds term i c

end ZlibF.Spec.Public.GzRead
