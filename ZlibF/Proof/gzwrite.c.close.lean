import ZlibF.Proof.«gzwrite.c.write-calls»
import ZlibF.Proof.«gz.read-close»
import ZlibF.Proof.«deflate.c.universal-end»
import ZlibF.Proof.«deflate.c.universal-sequence-safety»

/-!
# gzwrite.c: `gzclose_w` is safe

`gzclose_w_step_of`: the skeleton statement `gzclose_w_step` (`GzCloseSafe`, branch `skeleton/gz`), from the facts of
`gz_error` (`GzErrorSpec`, `GzErrorOwn`). `GzCloseSafe` and `GzReleased` are not on `dev`; as for `gzclose_r`
(`gz.read-close`), the statement is written out with `GzRead.Close.Released`, the copy of `GzReleased`.

`gzclose_w(file)` refuses a reader with no effect. On a writer:
1. the prefix: `gz_zero` when a skip is pending, then `gz_comp(Z_FINISH)` (`zero_any`, `comp_any`), with their
   failures; it ends in `GzInv`;
2. the release (`closeTail_ok`): with buffers and a compressing writer, `deflateEnd` on the embedded stream
   (`deflateEnd_safe` and `end_from_inv`, part 3 of the deflate sequence goal, on the reachable stream of W6) and
   `free(out)`; with buffers `free(in)`; then `gz_error(state, Z_OK, NULL)`, `free(path)`, `close(fd)` (released also
   when it reports -1, M4), `free(state)`;
3. the two steps compose (`released_trans`): the blocks freed are exactly those the handle owned before the call.
-/

namespace ZlibF.Spec.Public.GzSkeleton
open C Zlib.GzFs Zlib.Gzguts ZlibF.Spec.Public
open Zlib.Gzwrite.SafeInit (GzErrorSpec GzErrorOwn)
open ZlibF.Spec.Public.GzRead.Close (Released release_of tailH rest_tail rest_freeStr tail_bytes_keep
  tail_bytes_kill tail_bytes_none tail_istates tail_gz_i tail_gz_ne fs_bytes_ne fs_bytes_kill fs_bytes_none
  fs_gzstates fs_istates ne_blk ptr_of err_run freeGzState_run close_world path_msg owned_not_codec nodup3 nodup4)
set_option autoImplicit false

section close
variable {i : Nat}

/-! ## Composing frames and ledgers -/

theorem chain {A B C : Heap} {P1 P2 R1 R2 : Nat → Prop} (f1 : Frame A B P1)
    (l1 : LiveChange A B (fun _ => False) R1) (f2 : Frame B C P2) (l2 : LiveChange B C (fun _ => False) R2) :
    Frame A C (fun b => P1 b ∨ P2 b) ∧ LiveChange A C (fun _ => False) (fun b => R1 b ∨ R2 b) := by
  refine ⟨⟨f1.1.trans f2.1, f1.2.1.trans f2.2.1, f1.2.2.1.trans f2.2.2.1, Nat.le_trans f1.2.2.2.1 f2.2.2.2.1,
    Nat.le_trans f1.2.2.2.2.1 f2.2.2.2.2.1, fun b hl hn => ?_⟩, fun b => ?_⟩
  · have q1 := f1.2.2.2.2.2 b hl (fun x => hn (Or.inl x))
    have hlB : B.live b := (GetcUngetc.frame_live_iff q1).2 hl
    have q2 := f2.2.2.2.2.2 b hlB (fun x => hn (Or.inr x))
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := q1
    obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩ := q2
    exact ⟨b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4, b5.trans a5, b6.trans a6, b7.trans a7,
      b8.trans a8⟩
  · rw [l2 b, l1 b]
    constructor
    · rintro (⟨(⟨hl, h1⟩ | f), h2⟩ | f)
      · exact Or.inl ⟨hl, fun x => x.elim h1 h2⟩
      · exact (f : False).elim
      · exact (f : False).elim
    · rintro (⟨hl, hn⟩ | f)
      · exact Or.inl ⟨Or.inl ⟨hl, fun x => hn (Or.inl x)⟩, fun x => hn (Or.inr x)⟩
      · exact (f : False).elim

theorem lc_congr {A C : Heap} {R O : Nat → Prop} (l : LiveChange A C (fun _ => False) R)
    (h1 : ∀ b, R b → O b) (h2 : ∀ b, A.live b → O b → R b) : LiveChange A C (fun _ => False) O := by
  intro b
  rw [l b]
  constructor
  · rintro (⟨hl, hn⟩ | f)
    · exact Or.inl ⟨hl, fun x => hn (h2 b hl x)⟩
    · exact Or.inr f
  · rintro (⟨hl, hn⟩ | f)
    · exact Or.inl ⟨hl, fun x => hn (h1 b x)⟩
    · exact Or.inr f

/-- **A release after a step** is a release from the start of the step. -/
theorem released_trans {h H T : Heap} {fs fsA fs' : Fs} {s v : GzState}
    (E : GetcUngetc.Eff i h s fs fsA H) (inv : GzInv H i v) (R : Released H T fsA fs' i v) :
    Released h T fs fs' i s := by
  obtain ⟨k, -, s', inv', -, hfd, ⟨fr, -⟩, lc, ng⟩ := E
  have e := inv.state_eq inv'.common.record
  subst e
  have fr' : Frame h H (GzOwned h i s) := fr
  obtain ⟨g, frT, lcT, hfs', c1, c2⟩ := R
  refine ⟨g, ⟨fr'.1.trans frT.1, fr'.2.1.trans frT.2.1, fr'.2.2.1.trans frT.2.2.1,
    Nat.le_trans fr'.2.2.2.1 frT.2.2.2.1, Nat.le_trans fr'.2.2.2.2.1 frT.2.2.2.2.1, fun b hl hn => ?_⟩,
    fun b => ?_, hfs', fun h0 => by rw [← hfd]; exact c1 (by rw [hfd]; exact h0),
    fun j hj => (c2 j (fun h0 => by rw [hfd]; exact hj (by rw [← hfd]; exact h0))).trans (k j)⟩
  · have q1 := fr'.2.2.2.2.2 b hl hn
    have hlH : H.live b := (GetcUngetc.frame_live_iff q1).2 hl
    have hnH : ¬ GzOwned H i v b := fun x => (ng b x).elim hn (fun y => y hl)
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := q1
    obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩ := frT.2.2.2.2.2 b hlH hnH
    exact ⟨b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4, b5.trans a5, b6.trans a6, b7.trans a7,
      b8.trans a8⟩
  · rw [lcT b]
    have L := lc b
    have N := ng b
    simp only at L
    constructor
    · rintro (⟨hH, hn⟩ | f)
      · rcases L.1 hH with ⟨hl, hr⟩ | ⟨ho, _⟩
        · exact Or.inl ⟨hl, fun x => hr ⟨x, hn⟩⟩
        · exact absurd ho hn
      · exact (f : False).elim
    · rintro (⟨hl, hn⟩ | f)
      · have hnH : ¬ GzOwned H i v b := fun x => (N x).elim hn (fun y => y hl)
        exact Or.inl ⟨L.2 (Or.inl ⟨hl, fun x => hn x.1⟩), hnH⟩
      · exact (f : False).elim

/-! ## The release of the buffers, the message, the path and the record -/

/-- The ledger of the tail of `gzclose_w` from the heap `H1` (after `deflateEnd`, if any): `pout` and `pin` (each
NULL or a block) are freed, then the message, the path and the record. -/
theorem tail_release {H1 : Heap} {t : GzState} (u : Zlib.Gzlib.Spec.Uniq H1) (hs : H1.gzstates i = some t)
    (pin pout : BPtr)
    (blocks : ∀ b, (blkOf t.path = some b ∨ blkOf t.msg = some b ∨ blkOf pin = some b ∨ blkOf pout = some b) →
      ∃ a, H1.bytes b = some a) :
    Frame H1 (tailH (Zlib.Gzlib.Proofs.freeStr (Zlib.Gzlib.Proofs.freeStr H1 pout) pin) i t)
        (fun b => b = i ∨ blkOf t.path = some b ∨ blkOf t.msg = some b ∨ blkOf pin = some b ∨ blkOf pout = some b) ∧
      LiveChange H1 (tailH (Zlib.Gzlib.Proofs.freeStr (Zlib.Gzlib.Proofs.freeStr H1 pout) pin) i t) (fun _ => False)
        (fun b => b = i ∨ blkOf t.path = some b ∨ blkOf t.msg = some b ∨ blkOf pin = some b ∨
          blkOf pout = some b) := by
  refine release_of (DB := fun b => blkOf t.path = some b ∨ blkOf t.msg = some b ∨ blkOf pin = some b ∨
      blkOf pout = some b) (DI := fun _ => False) u hs
    ((rest_tail _ _ _).trans ((rest_freeStr _ _).trans (rest_freeStr _ _))) ?_ ?_ ?_ (fun _ hb => hb.elim) ?_
    (tail_gz_i _ _ _) (fun b hb => Or.inr hb) (fun _ hb => hb.elim) (Or.inl rfl) ?_
  · intro b hb
    simp only [not_or] at hb
    obtain ⟨n1, n2, n3, n4⟩ := hb
    rw [tail_bytes_keep _ _ _ n1 n2, fs_bytes_ne _ n3, fs_bytes_ne _ n4]
  · intro b hb
    rcases hb with hb | hb | hb | hb
    · exact tail_bytes_kill _ _ _ (Or.inl hb)
    · exact tail_bytes_kill _ _ _ (Or.inr hb)
    · exact tail_bytes_none _ _ _ (fs_bytes_kill _ hb)
    · exact tail_bytes_none _ _ _ (fs_bytes_none _ _ (fs_bytes_kill _ hb))
  · intro b _
    rw [tail_istates, fs_istates, fs_istates]
  · intro b hb
    rw [tail_gz_ne _ _ _ hb, fs_gzstates, fs_gzstates]
  · intro b hb
    rcases hb with hb | hb
    · exact Or.inl hb
    · exact Or.inr (Or.inl ⟨hb, blocks b hb⟩)

/-! ## The run of the release -/

/-- `gzclose_w` from the release on (`ret0` is the code of the prefix). -/
def closeTail (i : Nat) (ret0 : Int32) : G Int32 := do
  let mut ret := ret0
  let s ← ldS (gzSt i)
  if s.size != 0 then
    if s.direct == 0 then
      let _ ← Zlib.Deflate.deflateEnd (strmOf (gzSt i))
      freeB s.out
    freeB s.«in»
  Zlib.Gzlib.gz_error (gzSt i) Z_OK .null
  let s ← ldS (gzSt i)
  freeB s.path
  if (← fsClose s.fd) == -1 then ret := Z_ERRNO
  freeGzState (gzSt i)
  return ret

/-- The writer's owned pointers: path, message, and with buffers `in` and (compressing) `out`, distinct blocks. -/
theorem wbufs {h : Heap} {s : GzState} (inv : GzInv h i s) (hm : s.mode = GZ_WRITE) (hsz : s.size ≠ 0) :
    ∃ pb ib ia, s.path = .ref (.blk pb) 0 ∧ s.«in» = .ref (.blk ib) 0 ∧ h.bytes ib = some ia ∧ h.ro ib = false ∧
      pb ≠ ib ∧ (∀ mb, s.msg = .ref (.blk mb) 0 → mb ≠ pb ∧ mb ≠ ib) ∧
      (s.direct = 0 → ∃ ob oa, s.out = .ref (.blk ob) 0 ∧ h.bytes ob = some oa ∧ h.ro ob = false ∧
        pb ≠ ob ∧ ib ≠ ob ∧ ∀ mb, s.msg = .ref (.blk mb) 0 → mb ≠ ob) := by
  have c := inv.common
  have wr := inv.writer hm
  obtain ⟨_, _, pb, pa, hp, -, -, _⟩ := c.path
  obtain ⟨ib, ia, hi, hia, hiro, _⟩ := (wr.bufs hsz).1
  have nd := c.distinct.1
  by_cases hd : s.direct = 0
  · obtain ⟨ob, oa, ho, hoa, horo, _⟩ := (wr.bufs hsz).2 hd
    have e : ownedPtrs s = [s.path, s.msg, s.«in», s.out] := by simp [ownedPtrs, hsz, hd]
    rw [e, hp, hi, ho] at nd
    rcases c.msg with hmn | ⟨_, _, mb, ma, hmg, _⟩
    · rw [hmn] at nd
      have n3 : [pb, ib, ob].Nodup := nd
      obtain ⟨d1, d2, d3⟩ := nodup3 n3
      refine ⟨pb, ib, ia, hp, hi, hia, hiro, d1, (fun mb' e => by rw [hmn] at e; cases e), fun _ =>
        ⟨ob, oa, ho, hoa, horo, d2, d3, (fun mb' e => by rw [hmn] at e; cases e)⟩⟩
    · rw [hmg] at nd
      have n4 : [pb, mb, ib, ob].Nodup := nd
      obtain ⟨d1, d2, d3, d4, d5, d6⟩ := nodup4 n4
      refine ⟨pb, ib, ia, hp, hi, hia, hiro, d2, fun mb' e => ?_, fun _ =>
        ⟨ob, oa, ho, hoa, horo, d3, d6, fun mb' e => ?_⟩⟩
      · rw [hmg] at e; cases e; exact ⟨Ne.symm d1, d4⟩
      · rw [hmg] at e; cases e; exact d5
  · have hne : ¬ GZ_WRITE = GZ_READ := by decide
    have e : ownedPtrs s = [s.path, s.msg, s.«in»] := by simp [ownedPtrs, hsz, hd, hm, hne]
    rw [e, hp, hi] at nd
    rcases c.msg with hmn | ⟨_, _, mb, ma, hmg, _⟩
    · rw [hmn] at nd
      have n2 : [pb, ib].Nodup := nd
      have d1 : pb ≠ ib := fun x => by subst x; simp at n2
      exact ⟨pb, ib, ia, hp, hi, hia, hiro, d1, (fun mb' e => by rw [hmn] at e; cases e), fun x => absurd x hd⟩
    · rw [hmg] at nd
      have n3 : [pb, mb, ib].Nodup := nd
      obtain ⟨d1, d2, d3⟩ := nodup3 n3
      refine ⟨pb, ib, ia, hp, hi, hia, hiro, d2, fun mb' e => ?_, fun x => absurd x hd⟩
      rw [hmg] at e; cases e; exact ⟨Ne.symm d1, d3⟩

/-- `blkOf` of a block pointer. -/
theorem blkOf_eq {p : BPtr} {x b : Nat} (hp : p = .ref (.blk x) 0) : blkOf p = some b ↔ x = b := by
  subst hp
  exact ⟨fun e => Option.some.inj e, fun e => by rw [e]; rfl⟩

set_option maxHeartbeats 1000000 in
/-- **The release of a writer in `GzInv`**: the run returns and releases exactly the owned blocks and the
descriptor. -/
theorem closeTail_ok {H : Heap} {v : GzState} (inv : GzInv H i v) (hw : v.mode = GZ_WRITE) (fs : Fs)
    (hfs : FileSystem fs) (ret0 : Int32) :
    ∃ r fs' after, closeTail i ret0 fs H = .ok ((r, fs'), after) ∧ Released H after fs fs' i v := by
  have c := inv.common
  have hs := c.record
  have u := c.uniq
  have wr := inv.writer hw
  have hS : ldS (gzSt i) H = .ok (v, H) := Zlib.Gzlib.Proofs.ldS_run hs
  obtain ⟨pb, pa, hpath, hpa, hpro, hmsg⟩ := path_msg inv
  have memP : v.path ∈ ownedPtrs v := by simp [ownedPtrs]
  have memM : v.msg ∈ ownedPtrs v := by simp [ownedPtrs]
  -- the tail after the buffers: from a heap `Y` that keeps the record, the path and the message
  have tail : ∀ (Y : Heap) (t : GzState), Y.gzstates i = some t → t.path = v.path → t.msg = v.msg → t.err = v.err →
      t.fd = v.fd → Y.bytes pb = some pa → Y.ro pb = false →
      (∀ mb ma, v.msg = .ref (.blk mb) 0 → H.bytes mb = some ma → H.ro mb = false → Y.bytes mb = some ma ∧
        Y.ro mb = false) →
      ∃ H5, Zlib.Gzlib.gz_error (gzSt i) Z_OK .null Y = .ok ((), Zlib.Gzlib.Spec.setS
          (Zlib.Gzlib.Proofs.freeStr Y t.msg) i (Zlib.Gzlib.Spec.errNull t Z_OK)) ∧
        ldS (gzSt i) (Zlib.Gzlib.Spec.setS (Zlib.Gzlib.Proofs.freeStr Y t.msg) i (Zlib.Gzlib.Spec.errNull t Z_OK)) =
          .ok (Zlib.Gzlib.Spec.errNull t Z_OK, Zlib.Gzlib.Spec.setS (Zlib.Gzlib.Proofs.freeStr Y t.msg) i
            (Zlib.Gzlib.Spec.errNull t Z_OK)) ∧
        freeB (Zlib.Gzlib.Spec.errNull t Z_OK).path (Zlib.Gzlib.Spec.setS (Zlib.Gzlib.Proofs.freeStr Y t.msg) i
          (Zlib.Gzlib.Spec.errNull t Z_OK)) = .ok ((), H5) ∧
        freeGzState (gzSt i) H5 = .ok ((), tailH Y i t) := by
    intro Y t hY hp hm he hfd hYp hYro hYm
    have e4 := err_run (H := Y) (t := t) hY (by
        rcases hmsg with hmn | ⟨mb, ma, hmg, hma, hmro, _⟩
        · exact Or.inl (hm.trans hmn)
        · obtain ⟨y1, y2⟩ := hYm mb ma hmg hma hmro
          exact Or.inr ⟨mb, ma, hm.trans hmg, y1, y2⟩) (fun x => hm.trans (c.memerr (he ▸ x)))
    have e5 : (Zlib.Gzlib.Spec.setS (Zlib.Gzlib.Proofs.freeStr Y t.msg) i (Zlib.Gzlib.Spec.errNull t Z_OK)).gzstates i =
        some (Zlib.Gzlib.Spec.errNull t Z_OK) := Zlib.Gzlib.Proofs.setS_gz_same _ _ _
    have hpb : (Zlib.Gzlib.Spec.setS (Zlib.Gzlib.Proofs.freeStr Y t.msg) i (Zlib.Gzlib.Spec.errNull t Z_OK)).bytes pb =
        some pa := by
      rw [Zlib.Gzlib.Proofs.setS_bytes]
      rcases hmsg with hmn | ⟨mb, ma, hmg, hma, hmro, hne⟩
      · rw [hm, hmn]; exact hYp
      · rw [fs_bytes_ne _ (ne_blk (hm.trans hmg) hne)]; exact hYp
    have e6 := Zlib.Gzlib.Proofs.freeB_run
      (h := Zlib.Gzlib.Spec.setS (Zlib.Gzlib.Proofs.freeStr Y t.msg) i (Zlib.Gzlib.Spec.errNull t Z_OK))
      (p := (Zlib.Gzlib.Spec.errNull t Z_OK).path) (show t.path = _ from hp.trans hpath) hpb
      (by rw [Zlib.Gzlib.Proofs.setS_ro, (rest_freeStr _ _).2.2.2.2.1]; exact hYro)
    refine ⟨_, e4, Zlib.Gzlib.Proofs.ldS_run e5, e6, ?_⟩
    have e7 : (Zlib.Gzlib.Proofs.freeStr (Zlib.Gzlib.Spec.setS (Zlib.Gzlib.Proofs.freeStr Y t.msg) i
        (Zlib.Gzlib.Spec.errNull t Z_OK)) (Zlib.Gzlib.Spec.errNull t Z_OK).path).gzstates i =
        some (Zlib.Gzlib.Spec.errNull t Z_OK) := by rw [fs_gzstates]; exact e5
    exact freeGzState_run e7
  obtain ⟨w1, w2, w3⟩ := close_world v.fd fs hfs
  -- the final ledger from the ledger of the tail
  have fin : ∀ {T : Heap} {P R : Nat → Prop}, T.gzstates i = none → Frame H T P →
      LiveChange H T (fun _ => False) R → (∀ b, P b → GzOwned H i v b) → (∀ b, R b → GzOwned H i v b) →
      (∀ b, H.live b → GzOwned H i v b → R b) → Released H T fs (Zlib.Gzread.Proofs.closeResult v.fd fs).2 i v :=
    fun g fr lc hP hR hO => ⟨g, Zlib.Gzwrite.SafeInit.frame_mono fr hP, lc_congr lc hR hO, w1, w2, w3⟩
  have hpo : ∀ b, blkOf v.path = some b → GzOwned H i v b := fun b e =>
    Or.inr (Or.inl (ptr_of hpath e))
  have hmo : ∀ b, blkOf v.msg = some b → GzOwned H i v b := by
    intro b e
    rcases hmsg with hmn | ⟨mb, ma, hmg, _, _, _⟩
    · rw [hmn] at e; cases e
    · exact Or.inr (Or.inr (Or.inl (ptr_of hmg e)))
  have hmb : ∀ b, blkOf v.msg = some b → ∃ a, H.bytes b = some a := by
    intro b e
    rcases hmsg with hmn | ⟨mb, ma, hmg, hma, _, _⟩
    · rw [hmn] at e; cases e
    · rw [(blkOf_eq hmg).1 e] at hma; exact ⟨ma, hma⟩
  have hpb' : ∀ b, blkOf v.path = some b → ∃ a, H.bytes b = some a := by
    intro b e; rw [← (blkOf_eq hpath).1 e]; exact ⟨pa, hpa⟩
  by_cases hsz : v.size = 0
  · -- no buffers
    have hz : (v.size != 0) = false := by simp [hsz]
    obtain ⟨H5, e4, e5, e6, e7⟩ := tail H v hs rfl rfl rfl rfl hpa hpro (fun mb ma _ h1 h2 => ⟨h1, h2⟩)
    obtain ⟨frT, lcT⟩ := tail_release (t := v) u hs .null .null (by
      intro b hb
      rcases hb with hb | hb | hb | hb
      · exact hpb' b hb
      · exact hmb b hb
      · cases hb
      · cases hb)
    have run : ∃ r, closeTail i ret0 fs H = .ok ((r, (Zlib.Gzread.Proofs.closeResult v.fd fs).2), tailH H i v) :=
      by
        by_cases hc : ((Zlib.Gzread.Proofs.closeResult v.fd fs).1 == -1) = true
        · refine ⟨Z_ERRNO, ?_⟩
          unfold closeTail
          simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app,
            hS, hz, Bool.false_eq_true, ↓reduceIte, e4, e5, e6, Zlib.Gzread.Proofs.fsClose_run]
          simp only [Zlib.Gzlib.Spec.errNull, hc, ↓reduceIte, cbind_app, clift_app, cpure_app, e7]
        · refine ⟨ret0, ?_⟩
          have hc' := Bool.eq_false_iff.mpr hc
          unfold closeTail
          simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app,
            hS, hz, Bool.false_eq_true, ↓reduceIte, e4, e5, e6, Zlib.Gzread.Proofs.fsClose_run]
          simp only [Zlib.Gzlib.Spec.errNull, hc', Bool.false_eq_true, ↓reduceIte, cbind_app, clift_app, cpure_app, e7]
    obtain ⟨r, run⟩ := run
    refine ⟨r, _, tailH H i v, run, fin (tail_gz_i _ _ _) frT lcT ?_ ?_ ?_⟩
    all_goals first
      | (intro b hb
         rcases hb with hb | hb | hb | hb | hb
         · exact Or.inl hb
         · exact hpo b hb
         · exact hmo b hb
         · cases hb
         · cases hb)
      | (intro b _ hb
         rcases hb with hb | hb | hb | ⟨hz', _⟩
         · exact Or.inl hb
         · exact Or.inr (Or.inl (by rw [hb]; rfl))
         · exact Or.inr (Or.inr (Or.inl (by rw [hb]; rfl)))
         · exact absurd hsz hz')
  have hz : (v.size != 0) = true := by simpa using hsz
  obtain ⟨pb', ib, ia, hpath', hin, hia, hiro, dpi, hmi, hout⟩ := wbufs inv hw hsz
  have epb : pb' = pb := by rw [hpath] at hpath'; cases hpath'; rfl
  rw [epb] at dpi hmi hout
  have memI : v.«in» ∈ ownedPtrs v := by simp [ownedPtrs, hsz]
  have hio : ∀ b, blkOf v.«in» = some b → GzOwned H i v b := fun b e =>
    Or.inr (Or.inr (Or.inr ⟨hsz, Or.inl (ptr_of hin e)⟩))
  by_cases hd : v.direct = 0
  · -- a compressing writer: `deflateEnd`, `free(out)`, `free(in)`
    have hd' : (v.direct == 0) = true := by simp [hd]
    obtain ⟨ob, oa, hout', hoa, horo, dpo, dio, hmo'⟩ := hout hd
    have memO : v.out ∈ ownedPtrs v := by simp [ownedPtrs, hsz, hd]
    have hoo : ∀ b, blkOf v.out = some b → GzOwned H i v b := fun b e =>
      Or.inr (Or.inr (Or.inr ⟨hsz, Or.inr ⟨Or.inr hd, Or.inl (ptr_of hout' e)⟩⟩))
    have reach := (wr.codec hd hsz).1
    obtain ⟨ds, z0, d0, dinv, -, -⟩ := Zlib.Deflate.Universal.reachable_inv_of
      (Zlib.Deflate.Universal.Call.sequence_facts_of Zlib.Deflate.Engine.Proofs.tinyOverlay) reach
    have hget : (gzStrm i).get H = some v.strm := by simp [ZStreamRef.get, gzStrm, hs]
    have ez : z0 = v.strm := Option.some.inj (dinv.dgood.live.hz.symm.trans hget)
    subst ez
    obtain ⟨-, -, -, -, -, H1, runE, heq, -, -, -, -, -, -, -, -, -, hroE, -, -, -, -, -, -, uniqE, -, -⟩ :=
      Zlib.Deflate.Proofs.deflateEnd_safe dinv.dgood dinv.defAlloc.2
    obtain ⟨rc', H1', z', runE', -, -, -, frE, lcE⟩ := Zlib.Deflate.Universal.end_from_inv dinv
    have eH : H1' = H1 := by
      rw [runE] at runE'
      simp only [Except.ok.injEq, Prod.mk.injEq] at runE'
      exact runE'.2.symm
    subst eH
    have e1 : (Zlib.Deflate.deflateEnd (strmOf (gzSt i)) H) =
        .ok ((if d0.status = BUSY_STATE then Z_DATA_ERROR else Z_OK), H1') := runE
    have hgz1 : H1'.gzstates i = some { v with strm := { v.strm with state := none } } := by
      rw [heq]
      simp [Zlib.Deflate.Spec.endHeap, gzStrm, ZStreamRef.put, hs]
    have u1 : Zlib.Gzlib.Spec.Uniq H1' := (gz_uniq_iff_deflate H1').2 uniqE
    -- the owned byte blocks keep their bytes across `deflateEnd`
    have keepB : ∀ p, p ∈ ownedPtrs v → ∀ b, blkOf p = some b → H1'.bytes b = H.bytes b := by
      intro p hp b hb
      obtain ⟨hbi, hbs⟩ := c.distinct.2 p hp b hb
      have ho : GzOwned H i v b := by
        rcases (List.mem_append.mp hp) with hp | hp
        · rcases List.mem_cons.mp hp with e | hp
          · subst e; exact hpo b hb
          · rw [List.mem_singleton] at hp; subst hp; exact hmo b hb
        · rw [if_pos hsz] at hp
          rcases List.mem_cons.mp hp with e | hp
          · subst e; exact hio b hb
          · rw [if_pos (Or.inr hd), List.mem_singleton] at hp; subst hp; exact hoo b hb
      exact (frE.2.2.2.2.2 b (c.live b ho) (fun x => x.elim hbi hbs)).1
    have hob1 : H1'.bytes ob = some oa := by rw [keepB _ memO ob (by rw [hout']; rfl)]; exact hoa
    have hro1 : H1'.ro = H.ro := hroE
    have e2 : freeB v.out H1' = .ok ((), Zlib.Gzlib.Proofs.freeStr H1' v.out) :=
      Zlib.Gzlib.Proofs.freeB_run hout' hob1 (by rw [hro1]; exact horo)
    have hib1 : (Zlib.Gzlib.Proofs.freeStr H1' v.out).bytes ib = some ia := by
      rw [fs_bytes_ne _ (ne_blk hout' (Ne.symm dio)), keepB _ memI ib (by rw [hin]; rfl)]; exact hia
    have e3 : freeB v.«in» (Zlib.Gzlib.Proofs.freeStr H1' v.out) =
        .ok ((), Zlib.Gzlib.Proofs.freeStr (Zlib.Gzlib.Proofs.freeStr H1' v.out) v.«in») :=
      Zlib.Gzlib.Proofs.freeB_run hin hib1 (by rw [(rest_freeStr _ _).2.2.2.2.1, hro1]; exact hiro)
    have hgzY : (Zlib.Gzlib.Proofs.freeStr (Zlib.Gzlib.Proofs.freeStr H1' v.out) v.«in»).gzstates i =
        some { v with strm := { v.strm with state := none } } := by rw [fs_gzstates, fs_gzstates]; exact hgz1
    have keepY : ∀ x, x ≠ ib → x ≠ ob →
        (Zlib.Gzlib.Proofs.freeStr (Zlib.Gzlib.Proofs.freeStr H1' v.out) v.«in»).bytes x = H1'.bytes x :=
      fun x h1 h2 => by rw [fs_bytes_ne _ (ne_blk hin (Ne.symm h1)), fs_bytes_ne _ (ne_blk hout' (Ne.symm h2))]
    have roY : (Zlib.Gzlib.Proofs.freeStr (Zlib.Gzlib.Proofs.freeStr H1' v.out) v.«in»).ro = H.ro := by
      rw [(rest_freeStr _ _).2.2.2.2.1, (rest_freeStr _ _).2.2.2.2.1, hro1]
    obtain ⟨H5, e4, e5, e6, e7⟩ := tail (Zlib.Gzlib.Proofs.freeStr (Zlib.Gzlib.Proofs.freeStr H1' v.out) v.«in»)
      { v with strm := { v.strm with state := none } } hgzY rfl rfl rfl rfl
      (by rw [keepY pb (Ne.symm (Ne.symm dpi)) dpo, keepB _ memP pb (by rw [hpath]; rfl)]; exact hpa)
      (by rw [roY]; exact hpro)
      (fun mb ma hmg hma hmro => by
        obtain ⟨n1, n2⟩ := hmi mb hmg
        refine ⟨?_, by rw [roY]; exact hmro⟩
        rw [keepY mb n2 (hmo' mb hmg), keepB _ memM mb (by rw [hmg]; rfl)]
        exact hma)
    obtain ⟨frT, lcT⟩ := tail_release (t := { v with strm := { v.strm with state := none } }) u1 hgz1 v.«in» v.out
      (by
        intro b hb
        rcases hb with hb | hb | hb | hb
        · obtain ⟨a, ha⟩ := hpb' b hb
          exact ⟨a, by rw [keepB _ memP b hb]; exact ha⟩
        · obtain ⟨a, ha⟩ := hmb b hb
          exact ⟨a, by rw [keepB _ memM b hb]; exact ha⟩
        · rw [← (blkOf_eq hin).1 hb]
          exact ⟨ia, by rw [keepB _ memI ib (by rw [hin]; rfl)]; exact hia⟩
        · exact ⟨oa, by rw [← (blkOf_eq hout').1 hb]; exact hob1⟩)
    obtain ⟨frC, lcC⟩ := chain frE lcE frT lcT
    have run : ∃ r, closeTail i ret0 fs H = .ok ((r, (Zlib.Gzread.Proofs.closeResult v.fd fs).2),
        tailH (Zlib.Gzlib.Proofs.freeStr (Zlib.Gzlib.Proofs.freeStr H1' v.out) v.«in») i
          { v with strm := { v.strm with state := none } }) :=
      by
        by_cases hc : ((Zlib.Gzread.Proofs.closeResult v.fd fs).1 == -1) = true
        · refine ⟨Z_ERRNO, ?_⟩
          unfold closeTail
          simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app,
            hS, hz, hd', ↓reduceIte, e1, e2, e3, e4, e5, e6, Zlib.Gzread.Proofs.fsClose_run]
          simp only [Zlib.Gzlib.Spec.errNull, hc, ↓reduceIte, cbind_app, clift_app, cpure_app, e7]
        · refine ⟨ret0, ?_⟩
          have hc' := Bool.eq_false_iff.mpr hc
          unfold closeTail
          simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app,
            hS, hz, hd', ↓reduceIte, e1, e2, e3, e4, e5, e6, Zlib.Gzread.Proofs.fsClose_run]
          simp only [Zlib.Gzlib.Spec.errNull, hc', Bool.false_eq_true, ↓reduceIte, cbind_app, clift_app, cpure_app, e7]
    obtain ⟨r, run⟩ := run
    refine ⟨r, _, _, run, fin (tail_gz_i _ _ _) frC lcC ?_ ?_ ?_⟩
    · intro b hb
      rcases hb with (hb | hb) | hb | hb | hb | hb | hb
      · exact Or.inl hb
      · exact Or.inr (Or.inr (Or.inr ⟨hsz, Or.inr ⟨Or.inr hd, Or.inr hb⟩⟩))
      · exact Or.inl hb
      · exact hpo b hb
      · exact hmo b hb
      · exact hio b hb
      · exact hoo b hb
    · intro b hb
      rcases hb with hb | hb | hb | hb | hb | hb
      · exact Or.inr (Or.inr (Or.inr ⟨hsz, Or.inr ⟨Or.inr hd, Or.inr hb⟩⟩))
      · exact Or.inl hb
      · exact hpo b hb
      · exact hmo b hb
      · exact hio b hb
      · exact hoo b hb
    · intro b _ hb
      rcases hb with hb | hb | hb | ⟨_, hb | ⟨_, hb | hb⟩⟩
      · exact Or.inr (Or.inl hb)
      · exact Or.inr (Or.inr (Or.inl (by rw [hb]; rfl)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (by rw [hb]; rfl))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [hb]; rfl)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by rw [hb]; rfl)))))
      · exact Or.inl hb
  · -- a transparent writer: `free(in)`
    have hd' : (v.direct == 0) = false := by simpa using hd
    have e3 : freeB v.«in» H = .ok ((), Zlib.Gzlib.Proofs.freeStr H v.«in») :=
      Zlib.Gzlib.Proofs.freeB_run hin hia hiro
    have hgzY : (Zlib.Gzlib.Proofs.freeStr (Zlib.Gzlib.Proofs.freeStr H .null) v.«in»).gzstates i = some v := by
      rw [fs_gzstates, fs_gzstates]; exact hs
    have roY : (Zlib.Gzlib.Proofs.freeStr (Zlib.Gzlib.Proofs.freeStr H .null) v.«in»).ro = H.ro := by
      rw [(rest_freeStr _ _).2.2.2.2.1, (rest_freeStr _ _).2.2.2.2.1]
    obtain ⟨H5, e4, e5, e6, e7⟩ := tail (Zlib.Gzlib.Proofs.freeStr (Zlib.Gzlib.Proofs.freeStr H .null) v.«in») v
      hgzY rfl rfl rfl rfl (by rw [fs_bytes_ne _ (ne_blk hin (Ne.symm dpi))]; exact hpa) (by rw [roY]; exact hpro)
      (fun mb ma hmg hma hmro => ⟨by rw [fs_bytes_ne _ (ne_blk hin (Ne.symm (hmi mb hmg).2))]; exact hma,
        by rw [roY]; exact hmro⟩)
    obtain ⟨frT, lcT⟩ := tail_release (t := v) u hs v.«in» .null
      (by
        intro b hb
        rcases hb with hb | hb | hb | hb
        · exact hpb' b hb
        · exact hmb b hb
        · rw [← (blkOf_eq hin).1 hb]; exact ⟨ia, hia⟩
        · cases hb)
    have run : ∃ r, closeTail i ret0 fs H = .ok ((r, (Zlib.Gzread.Proofs.closeResult v.fd fs).2),
        tailH (Zlib.Gzlib.Proofs.freeStr (Zlib.Gzlib.Proofs.freeStr H .null) v.«in») i v) :=
      by
        simp only [Zlib.Gzlib.Proofs.freeStr_null] at e4 e5 e6 e7 ⊢
        by_cases hc : ((Zlib.Gzread.Proofs.closeResult v.fd fs).1 == -1) = true
        · refine ⟨Z_ERRNO, ?_⟩
          unfold closeTail
          simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app,
            hS, hz, hd', Bool.false_eq_true, ↓reduceIte, e3, e4, e5, e6, Zlib.Gzread.Proofs.fsClose_run]
          simp only [Zlib.Gzlib.Spec.errNull, hc, ↓reduceIte, cbind_app, clift_app, cpure_app, e7]
        · refine ⟨ret0, ?_⟩
          have hc' := Bool.eq_false_iff.mpr hc
          unfold closeTail
          simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app,
            hS, hz, hd', Bool.false_eq_true, ↓reduceIte, e3, e4, e5, e6, Zlib.Gzread.Proofs.fsClose_run]
          simp only [Zlib.Gzlib.Spec.errNull, hc', Bool.false_eq_true, ↓reduceIte, cbind_app, clift_app, cpure_app, e7]
    obtain ⟨r, run⟩ := run
    refine ⟨r, _, _, run, fin (tail_gz_i _ _ _) frT lcT ?_ ?_ ?_⟩
    all_goals first
      | (intro b hb
         rcases hb with hb | hb | hb | hb | hb
         · exact Or.inl hb
         · exact hpo b hb
         · exact hmo b hb
         · exact hio b hb
         · cases hb)
      | (intro b _ hb
         rcases hb with hb | hb | hb | ⟨_, hb | ⟨hmo2, _⟩⟩
         · exact Or.inl hb
         · exact Or.inr (Or.inl (by rw [hb]; rfl))
         · exact Or.inr (Or.inr (Or.inl (by rw [hb]; rfl)))
         · exact Or.inr (Or.inr (Or.inr (Or.inl (by rw [hb]; rfl))))
         · exact absurd (hmo2.resolve_left (by rw [hw]; decide)) hd)

/-! ## `gzclose_w` -/

/-- `gzclose_w` from `gz_comp(Z_FINISH)` on. -/
def compClose (i : Nat) (ret : Int32) : G Int32 := do
  let r ← Zlib.Gzwrite.gz_comp (gzSt i) Z_FINISH
  if r == -1 then
    let s ← ldS (gzSt i)
    closeTail i s.err
  else closeTail i ret

theorem gzclose_w_eq :
    Zlib.Gzwrite.gzclose_w (some (.in_gzstate_x i)) = (do
      let s ← ldS (gzSt i)
      if s.mode != GZ_WRITE then return Z_STREAM_ERROR
      if s.skip != 0 then
        let r ← Zlib.Gzwrite.gz_zero (gzSt i)
        if r == -1 then
          let s' ← ldS (gzSt i)
          compClose i s'.err
        else compClose i Z_OK
      else compClose i Z_OK : G Int32) := rfl

theorem compClose_ok (err : GzErrorSpec) (errOwn : GzErrorOwn) {h0 : Heap} {s0 : GzState} {fs0 fs : Fs} {H : Heap}
    {v : GzState} (E : GetcUngetc.Eff i h0 s0 fs0 fs H) (inv : GzInv H i v) (hw : v.mode = GZ_WRITE) (ret : Int32) :
    ∃ r fs' after, compClose i ret fs H = .ok ((r, fs'), after) ∧ Released h0 after fs0 fs' i s0 := by
  obtain ⟨r, fs2, H2, run, k2, post⟩ := comp_any err errOwn inv E.2.1 hw Z_FINISH (by decide)
  have E2 := GetcUngetc.Eff.trans E inv post k2
  obtain ⟨hfs2, s2, inv2, hm2, -⟩ := id post
  have hS2 : ldS (gzSt i) H2 = .ok (s2, H2) := Zlib.Gzlib.Proofs.ldS_run inv2.common.record
  by_cases hr : (r == -1) = true
  · obtain ⟨r', fs', after, run', rel⟩ := closeTail_ok inv2 (hm2.trans hw) fs2 hfs2 s2.err
    refine ⟨r', fs', after, ?_, released_trans E2 inv2 rel⟩
    unfold compClose
    simp only [cbind_app, run, hr, ↓reduceIte, liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift,
      clift_app, hS2]
    exact run'
  · have hr' := Bool.eq_false_iff.mpr hr
    obtain ⟨r', fs', after, run', rel⟩ := closeTail_ok inv2 (hm2.trans hw) fs2 hfs2 ret
    refine ⟨r', fs', after, ?_, released_trans E2 inv2 rel⟩
    unfold compClose
    simp only [cbind_app, run, hr', Bool.false_eq_true, ↓reduceIte]
    exact run'

/-- **`gzclose_w_step`** (skeleton statement `GzCloseSafe i (.gzclose_w (some (.in_gzstate_x i)))`, written out with
`GzRead.Close.Released`, the copy of `GzReleased`), given the facts of `gz_error`: on any handle in `GzInv`, for every
OS world, the call returns, and either refuses a reader with no effect, or releases the writer. -/
theorem gzclose_w_step_of (err : GzErrorSpec) (errOwn : GzErrorOwn) (i : Nat) :
    ∀ h fs s, GzInv h i s → FileSystem fs →
      ∃ value fs' after, (Call.gzclose_w (some (.in_gzstate_x i))).execute fs h = .ok ((value, fs'), after) ∧
        ((s.mode ≠ GZ_WRITE ∧ after = h ∧ fs' = fs) ∨ (¬ s.mode ≠ GZ_WRITE ∧ Released h after fs fs' i s)) := by
  intro h fs s inv hfs
  have hS : ldS (gzSt i) h = .ok (s, h) := Zlib.Gzlib.Proofs.ldS_run inv.common.record
  have run : ∀ v fs' after, Zlib.Gzwrite.gzclose_w (some (.in_gzstate_x i)) fs h = .ok ((v, fs'), after) →
      (Call.gzclose_w (some (.in_gzstate_x i))).execute fs h = .ok ((v, fs'), after) := fun _ _ _ e => e
  by_cases hm : s.mode = GZ_WRITE
  · have hm' : (s.mode != GZ_WRITE) = false := by simp [hm]
    have E0 := GetcUngetc.Eff.refl inv hfs
    by_cases hk : s.skip = 0
    · have hkB : (s.skip != 0) = false := by simp [hk]
      obtain ⟨r, fs', after, run', rel⟩ := compClose_ok err errOwn E0 inv hm Z_OK
      refine ⟨r, fs', after, run _ _ _ ?_, Or.inr ⟨fun x => x hm, rel⟩⟩
      rw [gzclose_w_eq]
      simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hS,
        hm', hkB, Bool.false_eq_true, ↓reduceIte]
      exact run'
    · have hkB : (s.skip != 0) = true := by simpa using hk
      obtain ⟨r, fs2, H2, run2, hr, k2, post2, -⟩ := zero_any err errOwn inv hfs hm
      have E2 := GetcUngetc.Eff.trans E0 inv post2 k2
      obtain ⟨-, -, s2, inv2, hm2, -⟩ := id E2
      have hS2 : ldS (gzSt i) H2 = .ok (s2, H2) := Zlib.Gzlib.Proofs.ldS_run inv2.common.record
      rcases hr with rfl | rfl
      · obtain ⟨r, fs', after, run', rel⟩ := compClose_ok err errOwn E2 inv2 (hm2.trans hm) Z_OK
        refine ⟨r, fs', after, run _ _ _ ?_, Or.inr ⟨fun x => x hm, rel⟩⟩
        rw [gzclose_w_eq]
        simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hS,
          hm', hkB, Bool.false_eq_true, ↓reduceIte, run2, int32_zero_ne_neg_one]
        exact run'
      · obtain ⟨r, fs', after, run', rel⟩ := compClose_ok err errOwn E2 inv2 (hm2.trans hm) s2.err
        refine ⟨r, fs', after, run _ _ _ ?_, Or.inr ⟨fun x => x hm, rel⟩⟩
        rw [gzclose_w_eq]
        simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hS,
          hm', hkB, Bool.false_eq_true, ↓reduceIte, run2, beq_self_eq_true, hS2]
        exact run'
  · have hm' : (s.mode != GZ_WRITE) = true := by simpa using hm
    refine ⟨Z_STREAM_ERROR, fs, h, run _ _ _ ?_, Or.inl ⟨hm, rfl, rfl⟩⟩
    rw [gzclose_w_eq]
    simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hS,
      hm', ↓reduceIte]

end close

end ZlibF.Spec.Public.GzSkeleton
