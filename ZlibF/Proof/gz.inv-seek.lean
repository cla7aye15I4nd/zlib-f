import ZlibF.Proof.«gz.inv-reset»
import ZlibF.Proof.«gz.inv-queries»
import ZlibF.Proof.«gzread.c.skip-have»
import ZlibF.Proof.«gzlib.c.seek»

/-!
# gz safety: `gzseek64` and `gzseek` keep `GzInv`

`gzseek64_step` and `gzseek_step` (skeleton statements, unchanged), for every world of the OS-call oracle.

The run of `gzseek64` comes from the seek proofs (`gzseek64_head_any`, `seekTail_copy`, `seekTail_back`,
`seekTail_fwd`, `gzseek64_write_run`), which need of the handle only `SeekGood` (`GzInv.seekGood`). The paths:

- refusal (serious error, bad `whence`, target outside the range of patch 0002): `-1`, nothing changes;
- a writer: `skip` becomes the distance, or `-1` for a target behind `x.pos`;
- a reader in the raw area (`how == COPY`): one `lseek`; on success the message is freed and the buffer dropped. The
  displacement `pos - x.pos - have` does not overflow by `GzReadInv.posHave` (`x.pos + x.have ≤ GZ_OFF_MAX`); without
  that clause it could (regression `tests/verification/regressions/gz-seek-pos-have.lean`);
- a reader going back: `gzrewind` (`lseek`, then `gz_reset`), then the whole distance becomes `skip`;
- a reader going forward, also from a negative `x.pos` after `gzungetc` at the start: buffered bytes are consumed,
  the rest becomes `skip`.

`GzReadInv.haveSkip` holds after each path: the raw-area seek and `gzrewind` empty the buffer, and a forward seek
sets a nonzero `skip` only when it has consumed the whole buffer.

`lseek` may return anything the oracle chooses; it changes only the call counter, `errno` and, for the regular
file, the position of the one descriptor (`LseekWorld`), so the world stays a `FileSystem` and the set of open
descriptors is kept.
-/

namespace ZlibF.Spec.Public
open C Zlib.GzFs Zlib.Gzguts
open Zlib.Gzlib.Spec (seekT SeekOk SeekOkAt OffMax OffMax_val skipFwd copyRec resetRec setS lseekRes hnd tellPos
  tellSkip fwdN NextOk ptrBlk)
open Zlib.Gzlib.Proofs (freeStr SeekGood i64_toInt_ofInt fwdN_le fwdN_le_off setS_setS)
set_option autoImplicit false

/-! ## The world after `lseek` -/

/-- What `lseek` may do to the world: names, nodes and the size limit are kept, and the descriptor table is kept
or one open descriptor gets a new position that is a `z_off64_t`. -/
def LseekWorld (w w' : Fs) : Prop :=
  w'.names = w.names ∧ w'.nodes = w.nodes ∧ w'.fsizeLimit = w.fsizeLimit ∧
  (w'.fds = w.fds ∨ ∃ (j : Nat) (of : OFile) (p : Nat), w.fds[j]? = some (some of) ∧ p ≤ 2 ^ 63 - 1 ∧
    w'.fds = w.fds.set! j (some { of with pos := p }))

theorem fds_get_some {a : Array (Option OFile)} {j : Nat} {x : OFile} (e : a[j]! = some x) :
    a[j]? = some (some x) := by
  by_cases hj : j < a.size
  · rw [Array.getElem?_eq_some_getElem! _ _ hj, e]
  · have h0 : a[j]? = none := Array.getElem?_eq_none (by omega)
    first
      | (simp [hj] at e)
      | (simp [getElem!_def, h0] at e)

theorem fsLseekReg_world (fd : Int32) (off : Int64) (wh : Int32) (w : Fs) :
    ∃ r w', fsLseekReg fd off wh w = (pure (r, w') : M (Int64 × Fs)) ∧ LseekWorld w w' := by
  unfold fsLseekReg
  dsimp only
  split
  · exact ⟨_, _, rfl, rfl, rfl, rfl, Or.inl rfl⟩
  · cases hof : w.fds[fd.toInt.toNat]! with
    | none => exact ⟨_, _, rfl, rfl, rfl, rfl, Or.inl rfl⟩
    | some of =>
      dsimp only
      repeat' first
        | exact ⟨_, _, rfl, rfl, rfl, rfl, Or.inl rfl⟩
        | exact ⟨_, _, rfl, rfl, rfl, rfl, Or.inr ⟨fd.toInt.toNat, of, _, fds_get_some hof, by omega, rfl⟩⟩
        | split
        | dsimp only

/-- **`lseek` for every oracle value**: the world it leaves is an `LseekWorld` of the one before. -/
theorem lseekRes_world (fd : Int32) (off : Int64) (wh : Int32) (fs : Fs) :
    LseekWorld fs (lseekRes fd off wh fs).2 := by
  unfold lseekRes fsLseek
  dsimp only
  cases hc : fs.lseekChoice fs.nos with
  | regular =>
    obtain ⟨r, w', hy, hw⟩ := fsLseekReg_world fd off wh (tickW fs)
    dsimp only
    rw [hy]
    show LseekWorld fs (if r = -1 then w' else okErrW (fs.okErrno fs.nos) w')
    split
    · exact hw
    · unfold okErrW
      split
      · exact hw
      · exact hw
  | fail e => exact ⟨rfl, rfl, rfl, Or.inl rfl⟩
  | value v =>
    show LseekWorld fs (okErrW (fs.okErrno fs.nos) (tickW fs))
    unfold okErrW
    split
    · exact ⟨rfl, rfl, rfl, Or.inl rfl⟩
    · exact ⟨rfl, rfl, rfl, Or.inl rfl⟩

/-- An `LseekWorld` of a `FileSystem` is a `FileSystem` with the same open descriptors. -/
theorem LseekWorld.fs {w w' : Fs} (hfs : FileSystem w) (hw : LseekWorld w w') : FileSystem w' ∧ FdsKept w w' := by
  obtain ⟨hn, hd, hl, hf⟩ := hw
  obtain ⟨f1, f2, f3, f4⟩ := hfs
  rcases hf with hf | ⟨j, of, p, hj, hp, hf⟩
  · refine ⟨⟨by rw [hl]; exact f1, by rw [hn, hd]; exact f2, by rw [hf, hd]; exact f3, by rw [hd]; exact f4⟩, ?_⟩
    intro k
    unfold GzOracle.FdOpen
    rw [hf]
  · have hjs : j < w.fds.size := by
      by_cases hc : j < w.fds.size
      · exact hc
      · rw [Array.getElem?_eq_none (by omega)] at hj
        cases hj
    refine ⟨⟨by rw [hl]; exact f1, by rw [hn, hd]; exact f2, ?_, by rw [hd]; exact f4⟩, ?_⟩
    · intro k file hk
      rw [hd]
      by_cases he : j = k
      · subst he
        simp only [hf, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, ite_true, hjs,
          Option.some.injEq] at hk
        subst hk
        obtain ⟨a, _, c⟩ := f3 j of hj
        exact ⟨a, hp, c⟩
      · have hold : w.fds[k]? = some (some file) := by
          simpa [hf, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, he] using hk
        exact f3 k file hold
    · intro k
      unfold GzOracle.FdOpen
      by_cases he : j = k
      · subst he
        constructor
        · intro _
          exact ⟨of, hj⟩
        · intro _
          exact ⟨{ of with pos := p }, by
            rw [hf]; simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, ite_true, hjs]⟩
      · rw [hf]
        simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, he]

/-- `lseek` keeps a `FileSystem` and its open descriptors, for every oracle value. -/
theorem lseekRes_fs {fs : Fs} (hfs : FileSystem fs) (fd : Int32) (off : Int64) (wh : Int32) :
    FileSystem (lseekRes fd off wh fs).2 ∧ FdsKept fs (lseekRes fd off wh fs).2 :=
  (lseekRes_world fd off wh fs).fs hfs

/-! ## From `GzInv` to the hypotheses of the seek proofs -/

theorem ptrBlk_eq_blkOf (p : BPtr) : ptrBlk p = blkOf p := by
  cases p with
  | null => rfl
  | ref r o => cases r <;> rfl

section facts
variable {h : Heap} {i : Nat} {s : GzState}

theorem GzInv.seekGood (inv : GzInv h i s) : SeekGood h i s := by
  refine ⟨inv.common.record, inv.common.mode, ?_, inv.common.memerr⟩
  rcases inv.common.msg with hn | ⟨_, _, mb, a, hp, ha, hro, _⟩
  · exact Or.inl hn
  · exact Or.inr ⟨mb, hp, a, ha, hro⟩

theorem GzInv.nextOk (inv : GzInv h i s) : NextOk h s := by
  have c := inv.common
  rcases c.next with hn | ⟨b, off, a, hx, _, _, hmb, hb, hle⟩
  · refine ⟨Or.inl ⟨hn, c.nullHave hn⟩, fun b hb => ?_⟩
    rw [hn] at hb
    simp [ptrBlk] at hb
  · refine ⟨Or.inr ⟨.blk b, a, off, hx, hb, hle⟩, ?_⟩
    intro b' hb' e
    rw [hx] at hb'
    have hbb : b = b' := by simpa [ptrBlk] using hb'
    subst hbb
    rw [ptrBlk_eq_blkOf] at e
    exact hmb e

/-- `gztell64` is never `-2^63` (it is at least `x.pos ≥ -x.have`). -/
theorem GzInv.tell_lo (inv : GzInv h i s) : -9223372036854775808 < tellPos s := by
  obtain ⟨hsk, _, hph⟩ := inv.common.pos
  have hht := s.x.have.toNat_lt
  by_cases hp0 : s.past != 0 <;> simp [tellPos, tellSkip, hp0] <;> omega

/-- The message block, if any, is owned. -/
theorem GzInv.msg_owned (inv : GzInv h i s) (b : Nat) (hb : blkOf s.msg = some b) : GzOwned h i s b := by
  rcases inv.common.msg with hn | ⟨_, _, mb, _, hp, _⟩
  · rw [hn] at hb
    simp [blkOf] at hb
  · rw [hp] at hb
    simp only [blkOf, Option.some.injEq] at hb
    subst hb
    exact Or.inr (Or.inr (Or.inl hp))

end facts

/-! ## Record updates that keep `GzInv` -/

/-- The record `gz_reset` leaves for a reader (`resetRec` with the mode test taken). -/
def resetRd (s : GzState) : GzState :=
  { { s with eof := 0, how := LOOK, junk := -1, x := { s.x with «have» := 0, pos := 0 }, past := 0, again := 0 } with
    skip := 0, msg := .null, err := Z_OK, strm := { s.strm with avail_in := 0 } }

theorem gz_frame_refl (h : Heap) (P : Nat → Prop) : Frame h h P :=
  ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, fun _ _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

theorem frame_setS {h H : Heap} {P : Nat → Prop} {i : Nat} (fr : Frame h H P) (hi : P i) (x : GzState) :
    Frame h (setS H i x) P := by
  refine ⟨fr.1, fr.2.1, fr.2.2.1, fr.2.2.2.1, fr.2.2.2.2.1, ?_⟩
  intro b hl hb
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := fr.2.2.2.2.2 b hl hb
  have hbi : b ≠ i := fun e => hb (e ▸ hi)
  refine ⟨e1, e2, e3, e4, e5, e6, ?_, e8⟩
  show upd H.gzstates i (some x) b = h.gzstates b
  rw [upd_ne _ _ _ _ hbi]
  exact e7

/-- Stream ownership through the record depends on `strm.state` only. -/
theorem putGz_streamOwned_state {h : Heap} {i : Nat} {s s' : GzState} (hs : h.gzstates i = some s)
    (hz : s'.strm.state = s.strm.state) (b : Nat) :
    StreamOwned (putGz h i s') (.in_gzstate_strm i) b ↔ StreamOwned h (.in_gzstate_strm i) b := by
  have g1 : ZStreamRef.get (putGz h i s') (.in_gzstate_strm i) = some s'.strm := by
    simp [ZStreamRef.get, putGz]
  have g2 : ZStreamRef.get h (.in_gzstate_strm i) = some s.strm := by
    simp [ZStreamRef.get, hs]
  unfold StreamOwned
  rw [g1, g2]
  simp only [Option.some.injEq, exists_eq_left']
  rw [hz]
  exact Iff.rfl

theorem rec_strm_eq (s' : GzState) (z : ZStream) (hz : s'.strm = z) : ({ s' with strm := z } : GzState) = s' := by
  cases s'
  simp only at hz
  subst hz
  rfl

theorem putGz3 (F : Heap) (i : Nat) (a b c : GzState) :
    putGz (putGz (putGz F i a) i b) i c = setS F i c := by
  simp [putGz, Zlib.Gzlib.Spec.setS, upd_upd]

/-- **Free the message, write scalars, drop the input** (the shape of `gz_reset` and of the raw-area seek): a reader
record `s'` with the message cleared, the error `Z_OK`, no codec input and scalars that keep the clauses. The handle
owns its old blocks but the message; only the record and the message block change. -/
theorem GzInv.clear_put_drop {h : Heap} {i : Nat} {s : GzState} (inv : GzInv h i s) (hm : s.mode = GZ_READ)
    (s' : GzState)
    (same : s'.path = s.path ∧ s'.msg = .null ∧ s'.«in» = s.«in» ∧ s'.out = s.out ∧ s'.size = s.size ∧
      s'.mode = s.mode ∧ s'.direct = s.direct ∧ s'.strm = { s.strm with avail_in := 0 } ∧
      s'.x.next = s.x.next ∧ s'.err = Z_OK)
    (want : 8 ≤ s'.want.toNat ∧ s'.want.toNat < 2 ^ 31 ∧ (s.size = 0 ∨ s'.want = s.want))
    (pos : 0 ≤ s'.skip.toInt ∧ s'.x.pos.toInt + s'.skip.toInt ≤ 9223372036854775807 ∧
      0 ≤ s'.x.pos.toInt + s'.x.have.toNat)
    (have_le : s'.x.have.toNat ≤ s.x.have.toNat)
    (rd : (s'.how = LOOK ∨ s'.how = GZ_COPY ∨ s'.how = GZIP) ∧ (s'.how = GZ_COPY → s'.direct = 0 ∨ s'.direct = 1) ∧
      (s'.how = GZIP → s'.direct = 0) ∧ (s'.junk = -1 ∨ s'.junk = 0 ∨ s'.junk = 1) ∧
      (s'.eof = 0 ∨ s'.eof = 1) ∧ (s'.past = 0 ∨ s'.past = 1) ∧ (s'.again = 0 ∨ s'.again = 1) ∧
      (s.size = 0 → s'.how = LOOK) ∧ (s.size = 0 → s'.again = 0) ∧
      s'.x.pos.toInt + s'.x.have.toNat ≤ 9223372036854775807 ∧ (s'.x.have ≠ 0 → s'.skip = 0)) :
    GzInv (setS (freeStr h s.msg) i s') i s' ∧
    (∀ b, GzOwned (setS (freeStr h s.msg) i s') i s' b ↔ GzOwned h i s b ∧ blkOf s.msg ≠ some b) ∧
    (∀ b, (setS (freeStr h s.msg) i s').live b ↔ h.live b ∧ blkOf s.msg ≠ some b) ∧
    Frame h (setS (freeStr h s.msg) i s') (fun b => b = i ∨ blkOf s.msg = some b) := by
  obtain ⟨hpath, hmsg, hin, hout, hsize, hmode, hdirect, hstrm, hnext, herr⟩ := same
  obtain ⟨inv1, own1, live1, frame1⟩ :=
    inv.clear_message s'.eof s'.past Z_OK (fun _ => ⟨rd.2.2.2.2.1, rd.2.2.2.2.2.1⟩)
  have hs1 := inv1.common.record
  have inv2 := inv1.put_scalars (s' := { s' with strm := s.strm })
    ⟨hpath, hmsg, hin, hout, hsize, hmode, hdirect, rfl, hnext, herr⟩ want pos have_le
    (fun _ => rd) (fun hw => absurd (hm.symm.trans hw) (by decide))
  have inv3 := inv2.drop_input
  have key : ∀ (H : Heap) (Z : GzState), H = setS (freeStr h s.msg) i Z → Z = s' → GzInv H i Z →
      GzInv (setS (freeStr h s.msg) i s') i s' := by
    intro H Z e1 e2 g
    subst e1 e2
    exact g
  have hH : setS (freeStr h s.msg) i s' =
      putGz (putGz (freeStr h s.msg) i { s with eof := s'.eof, past := s'.past, msg := .null, err := Z_OK }) i s' := by
    simp [putGz, Zlib.Gzlib.Spec.setS, upd_upd]
  have hstate : s'.strm.state =
      ({ s with eof := s'.eof, past := s'.past, msg := .null, err := Z_OK } : GzState).strm.state := by
    rw [hstrm]
  refine ⟨key _ _ (putGz3 _ _ _ _ _) (rec_strm_eq s' _ hstrm) inv3, ?_, ?_, ?_⟩
  · intro b
    rw [← own1 b, hH]
    unfold GzOwned
    simp only [hpath, hmsg, hin, hout, hsize, hmode, hdirect, putGz_streamOwned_state hs1 hstate]
  · intro b
    rw [← live1 b, hH]
    exact putGz_live hs1 b
  · rw [hH]
    exact frame_setS frame1 (Or.inl rfl) s'

/-- **A forward seek of a reader keeps `GzInv`**: consume up to `x.have` buffered bytes, the rest of the distance
becomes `skip`. The handle owns the same blocks. Holds from a negative `x.pos` too. -/
theorem GzInv.seek_fwd {h : Heap} {i : Nat} {s : GzState} (inv : GzInv h i s) (hm : s.mode = GZ_READ) {t : Int}
    (ht : SeekOk t) (hfw : s.x.pos.toInt ≤ t) (hd : t - s.x.pos.toInt ≤ OffMax) :
    GzInv (setS h i (skipFwd s t)) i (skipFwd s t) ∧
    ∀ b, GzOwned (setS h i (skipFwd s t)) i (skipFwd s t) b ↔ GzOwned h i s b := by
  have r := inv.reader hm
  have c := inv.common
  have hOM := OffMax_val
  have ht1 := ht.1
  have ht2 := ht.2
  have hht := s.x.have.toNat_lt
  have hlt := s.x.pos.toInt_lt
  have hge := s.x.pos.le_toInt
  have hle := fwdN_le (s := s) (t - s.x.pos.toInt)
  have hle2 := fwdN_le_off (s := s) (off := t - s.x.pos.toInt) (by omega)
  have hn32 : (UInt32.ofNat (fwdN s (t - s.x.pos.toInt))).toNat = fwdN s (t - s.x.pos.toInt) :=
    UInt32.toNat_ofNat_of_lt' (by have hsz : UInt32.size = 4294967296 := rfl; omega)
  have hhave : (skipFwd s t).x.have.toNat = s.x.have.toNat - fwdN s (t - s.x.pos.toInt) := by
    show (s.x.have - UInt32.ofNat _).toNat = _
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le, hn32]; omega), hn32]
  have hpos : (skipFwd s t).x.pos.toInt = s.x.pos.toInt + fwdN s (t - s.x.pos.toInt) := by
    show (Int64.ofInt _).toInt = _
    exact i64_toInt_ofInt (by omega) (by omega)
  have hskip : (skipFwd s t).skip.toInt = t - s.x.pos.toInt - fwdN s (t - s.x.pos.toInt) := by
    show (Int64.ofInt _).toInt = _
    exact i64_toInt_ofInt (by omega) (by omega)
  have hph := r.posHave
  have hpl := c.pos.2.2
  have hhs : (skipFwd s t).x.have ≠ 0 → (skipFwd s t).skip = 0 := by
    intro hne
    have hn0 : (skipFwd s t).x.have.toNat ≠ 0 := fun e => hne (UInt32.toNat_inj.1 (by rw [e]; rfl))
    rw [hhave] at hn0
    have hz : (skipFwd s t).skip.toInt = (0 : Int64).toInt := by
      rw [hskip, show (0 : Int64).toInt = 0 from rfl]
      by_cases hc : t - s.x.pos.toInt < (s.x.have.toNat : Int)
      · rw [fwdN, ite_eq_left hc]; omega
      · rw [fwdN, ite_eq_right hc] at hn0; omega
    exact Int64.toInt_inj.1 hz
  refine ⟨inv.put_consume ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (fwdN s (t - s.x.pos.toInt)) rfl
    (by rw [hhave]; omega) ⟨c.want.1, c.want.2, Or.inr rfl⟩
    ⟨by rw [hskip]; omega, by rw [hpos, hskip]; omega, by rw [hpos, hhave]; omega⟩
    (fun _ => ⟨r.how, r.copyDirect, r.gzipDirect, r.junk, r.flags.1, r.flags.2.1, r.flags.2.2,
      fun hz => (r.unalloc hz).2.2.1, r.againSize, by rw [hpos, hhave]; omega, hhs⟩)
    (fun hw => absurd (hm.symm.trans hw) (by decide)), ?_⟩
  intro b
  exact putGz_owned (s' := skipFwd s t) c.record ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ b

end ZlibF.Spec.Public

namespace ZlibF.Spec.Public.GzSkeleton
open C Zlib.GzFs Zlib.Gzguts ZlibF.Spec.Public
open Zlib.Gzlib.Spec (seekT SeekOk SeekOkAt OffMax OffMax_val skipFwd copyRec resetRec setS lseekRes hnd)
open Zlib.Gzlib.Proofs (freeStr i64_toInt_ofInt setS_setS gzseek64_refuse gzseek64_head_any gzseek64_write_run
  seekTail_copy seekTail_back seekTail_fwd)
set_option autoImplicit false

/-- The post-condition from a record change, for a call that writes no caller region: the handle owns its old
blocks but those of `D` (all owned before), and only the record and `D` change. -/
theorem post_gen {h after : Heap} {i : Nat} {s s' : GzState} {fs fs' : Fs} {call : Call} (inv : GzInv h i s)
    (hfs' : FileSystem fs') (hk : FdsKept fs fs') (hr : GzWriteRegions call = []) (inv' : GzInv after i s')
    (hm : s'.mode = s.mode) (hfd : s'.fd = s.fd) (D : Nat → Prop) (hD : ∀ b, D b → GzOwned h i s b)
    (hown : ∀ b, GzOwned after i s' b ↔ GzOwned h i s b ∧ ¬ D b) (hlive : ∀ b, after.live b ↔ h.live b ∧ ¬ D b)
    (fr : Frame h after (fun b => b = i ∨ D b)) :
    FdsKept fs fs' ∧ GzStepPost h i s call fs' after := by
  refine ⟨hk, hfs', s', inv', hm, hfd, ?_, ?_⟩
  · rw [hr]
    refine ⟨?_, fun region hmem => by cases hmem⟩
    show Frame h after (GzOwned h i s)
    refine ⟨fr.1, fr.2.1, fr.2.2.1, fr.2.2.2.1, fr.2.2.2.2.1, fun b hl ho => fr.2.2.2.2.2 b hl ?_⟩
    rintro (hb | hb)
    · exact ho (Or.inl hb)
    · exact ho (hD b hb)
  · unfold LiveChange
    intro b
    dsimp only
    rw [hlive b, hown b]
    constructor
    · rintro ⟨hl, hn⟩
      exact Or.inl ⟨hl, fun hx => hx.2 ⟨hx.1, hn⟩⟩
    · rintro (⟨hl, hx⟩ | ⟨⟨ho, _⟩, hnl⟩)
      · exact ⟨hl, fun hd => hx ⟨hD b hd, fun hy => hy.2 hd⟩⟩
      · exact absurd (inv.common.live b ho) hnl

/-- Heap unchanged, world changed within a `FileSystem` with the same descriptors. -/
theorem post_same {h : Heap} {i : Nat} {s : GzState} {fs fs' : Fs} {call : Call} (inv : GzInv h i s)
    (hfs' : FileSystem fs') (hk : FdsKept fs fs') (hr : GzWriteRegions call = []) :
    FdsKept fs fs' ∧ GzStepPost h i s call fs' h :=
  post_gen inv hfs' hk hr inv rfl rfl (fun _ => False) (fun _ e => e.elim)
    (fun _ => ⟨fun hh => ⟨hh, id⟩, fun hh => hh.1⟩) (fun _ => ⟨fun hh => ⟨hh, id⟩, fun hh => hh.1⟩)
    (gz_frame_refl h _)

/-- **`gzseek64` on a handle in `GzInv`, every world:** it returns, and the post-condition holds. -/
theorem gzseek64_inv {h : Heap} {i : Nat} {s : GzState} (inv : GzInv h i s) {fs : Fs} (hfs : FileSystem fs)
    (offset : Int64) (whence : Int32) :
    ∃ r fs' after, Zlib.Gzlib.gzseek64 (hnd i) offset whence fs h = .ok ((r, fs'), after) ∧
      FdsKept fs fs' ∧ GzStepPost h i s (.gzseek64 (some (.in_gzstate_x i)) offset whence) fs' after := by
  have c := inv.common
  have hs := c.record
  have hG := inv.seekGood
  have hP := inv.posInv
  have hOM := OffMax_val
  have hht := s.x.have.toNat_lt
  have hxl := s.x.pos.toInt_lt
  have hxg := s.x.pos.le_toInt
  obtain ⟨hsk, hps, hph⟩ := c.pos
  have hr : GzWriteRegions (.gzseek64 (some (.in_gzstate_x i)) offset whence) = [] := rfl
  have hW0 : FdsKept fs fs := fun _ => Iff.rfl
  by_cases hbad : (s.err ≠ Z_OK ∧ s.err ≠ Z_BUF_ERROR) ∨ (whence ≠ SEEK_SET ∧ whence ≠ SEEK_CUR)
  · exact ⟨_, _, _, gzseek64_refuse hG offset fs hbad, post_same inv hfs hW0 hr⟩
  have he : s.err = Z_OK ∨ s.err = Z_BUF_ERROR := by
    by_cases h1 : s.err = Z_OK
    · exact Or.inl h1
    · by_cases h2 : s.err = Z_BUF_ERROR
      · exact Or.inr h2
      · exact absurd (Or.inl ⟨h1, h2⟩) hbad
  have hw : whence = SEEK_SET ∨ whence = SEEK_CUR := by
    by_cases h1 : whence = SEEK_SET
    · exact Or.inl h1
    · by_cases h2 : whence = SEEK_CUR
      · exact Or.inr h2
      · exact absurd (Or.inr ⟨h1, h2⟩) hbad
  have hhead := gzseek64_head_any hG hP he hw (fun _ => inv.tell_lo) offset fs
  obtain ⟨t, htd⟩ : ∃ t, t = seekT s offset whence := ⟨_, rfl⟩
  rw [← htd] at hhead
  by_cases hnok : ¬ SeekOkAt s t
  · rw [ite_eq_right hnok] at hhead
    exact ⟨_, _, _, hhead, post_same inv hfs hW0 hr⟩
  have hok : SeekOkAt s t := Decidable.of_not_not hnok
  rw [ite_eq_left hok] at hhead
  have ht0 := hok.1.1
  have htM := hok.1.2
  have hd : t - s.x.pos.toInt ≤ OffMax := by
    by_cases hn : s.x.pos.toInt < 0
    · have := hok.2 hn
      omega
    · omega
  have hq : (Int64.ofInt t).toInt = t := i64_toInt_ofInt (by omega) (by omega)
  have z0 : (0 : Int64).toInt = 0 := rfl
  have u0 : ((0 : UInt32).toNat : Int) = 0 := rfl
  rcases c.mode with hm | hm
  · -- a reader
    have r := inv.reader hm
    have hN := inv.nextOk
    by_cases hc : s.how = GZ_COPY
    · -- the raw area: one `lseek`
      have hraw : -9223372036854775808 ≤ t - s.x.pos.toInt - s.x.have.toNat := by
        have := r.posHave
        omega
      rw [seekTail_copy hG hm hc hok.1 hd hraw fs] at hhead
      obtain ⟨hfs', hk⟩ := lseekRes_fs hfs s.fd (Int64.ofInt (t - s.x.pos.toInt - s.x.have.toNat)) SEEK_CUR
      generalize lseekRes s.fd (Int64.ofInt (t - s.x.pos.toInt - s.x.have.toNat)) SEEK_CUR fs = L at hhead hfs' hk
      by_cases hl : L.1 = -1
      · rw [ite_eq_left hl] at hhead
        exact ⟨_, _, _, hhead, post_same inv hfs' hk hr⟩
      · rw [ite_eq_right hl] at hhead
        refine ⟨_, _, _, hhead, ?_⟩
        obtain ⟨inv', own', live', fr'⟩ := inv.clear_put_drop hm (copyRec s t)
          ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ ⟨c.want.1, c.want.2, Or.inr rfl⟩
          ⟨by show (0 : Int) ≤ (0 : Int64).toInt; decide,
            by show (Int64.ofInt t).toInt + (0 : Int64).toInt ≤ 9223372036854775807; rw [hq, z0]; omega,
            by show (0 : Int) ≤ (Int64.ofInt t).toInt + ((0 : UInt32).toNat : Int); rw [hq, u0]; omega⟩
          (by show (0 : UInt32).toNat ≤ _; exact Nat.zero_le _)
          ⟨r.how, r.copyDirect, r.gzipDirect, r.junk, Or.inl rfl, Or.inl rfl, r.flags.2.2,
            fun hz => (r.unalloc hz).2.2.1, r.againSize,
            by show (Int64.ofInt t).toInt + ((0 : UInt32).toNat : Int) ≤ 9223372036854775807; rw [hq, u0]; omega,
            fun hz => absurd rfl hz⟩
        exact post_gen inv hfs' hk hr inv' rfl rfl _ inv.msg_owned own' live' fr'
    · by_cases hb : t < s.x.pos.toInt
      · -- back: `gzrewind`, then forward from 0
        have hnn : 0 ≤ s.x.pos.toInt := by omega
        rw [seekTail_back hG hm hc he hnn hok.1 hb hN fs] at hhead
        obtain ⟨hfs', hk⟩ := lseekRes_fs hfs s.fd s.start SEEK_SET
        generalize lseekRes s.fd s.start SEEK_SET fs = L at hhead hfs' hk
        by_cases hl : L.1 = -1
        · rw [ite_eq_left hl] at hhead
          exact ⟨_, _, _, hhead, post_same inv hfs' hk hr⟩
        · rw [ite_eq_right hl] at hhead
          have hmo' : (s.mode == GZ_READ) = true := by simpa using hm
          have hR : resetRec s = (resetRd s) := by
            unfold resetRec resetRd
            rw [hmo']
            rfl
          rw [hR] at hhead
          refine ⟨_, _, _, hhead, ?_⟩
          obtain ⟨inv1, own1, live1, fr1⟩ := inv.clear_put_drop hm (resetRd s)
            ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ ⟨c.want.1, c.want.2, Or.inr rfl⟩
            ⟨by show (0 : Int) ≤ (0 : Int64).toInt; decide,
              by show (0 : Int64).toInt + (0 : Int64).toInt ≤ 9223372036854775807; decide,
              by show (0 : Int) ≤ (0 : Int64).toInt + ((0 : UInt32).toNat : Int); decide⟩
            (by show (0 : UInt32).toNat ≤ _; exact Nat.zero_le _)
            ⟨Or.inl rfl, fun e => absurd e (by show ¬ (LOOK = GZ_COPY); decide),
              fun e => absurd e (by show ¬ (LOOK = GZIP); decide), Or.inl rfl,
              Or.inl rfl, Or.inl rfl, Or.inl rfl, fun _ => rfl, fun _ => rfl,
              by show (0 : Int64).toInt + ((0 : UInt32).toNat : Int) ≤ 9223372036854775807; decide,
              fun hz => absurd rfl hz⟩
          obtain ⟨inv2, own2⟩ := inv1.seek_fwd hm (t := t) hok.1 (by show (0 : Int64).toInt ≤ t; rw [z0]; omega)
            (by show t - (0 : Int64).toInt ≤ OffMax; rw [z0]; omega)
          have hs1 := inv1.common.record
          rw [setS_setS] at inv2 own2
          refine post_gen inv hfs' hk hr inv2 rfl rfl _ inv.msg_owned (fun b => (own2 b).trans (own1 b))
            (fun b => ?_) ?_
          · rw [← setS_setS _ _ (resetRd s)]
            exact (putGz_live hs1 b).trans (live1 b)
          · rw [← setS_setS _ _ (resetRd s)]
            exact frame_setS fr1 (Or.inl rfl) _
      · -- forward
        have hfw : s.x.pos.toInt ≤ t := by omega
        rw [seekTail_fwd hG hm hc hok.1 hd hfw hN fs] at hhead
        refine ⟨_, _, _, hhead, ?_⟩
        obtain ⟨inv2, own2⟩ := inv.seek_fwd hm hok.1 hfw hd
        exact post_gen inv hfs hW0 hr inv2 rfl rfl (fun _ => False) (fun _ e => e.elim)
          (fun b => ⟨fun hh => ⟨(own2 b).1 hh, id⟩, fun hh => (own2 b).2 hh.1⟩)
          (fun b => ⟨fun hh => ⟨(putGz_live hs b).1 hh, id⟩, fun hh => (putGz_live hs b).2 hh.1⟩)
          (frame_setS (gz_frame_refl h _) (Or.inl rfl) _)
  · -- a writer
    have w := inv.writer hm
    have h0 : s.x.have.toNat = 0 := by rw [w.have0]; rfl
    have hnn : 0 ≤ s.x.pos.toInt := by omega
    have hrun := gzseek64_write_run hG hP hnn he hw hm offset fs
    rw [← htd] at hrun
    by_cases hc : SeekOk t ∧ s.x.pos.toInt ≤ t
    · rw [ite_eq_left hc] at hrun
      refine ⟨_, _, _, hrun, ?_⟩
      have hK : (Int64.ofInt (t - s.x.pos.toInt)).toInt = t - s.x.pos.toInt := i64_toInt_ofInt (by omega) (by omega)
      have inv2 := inv.put_scalars (s' := { s with skip := Int64.ofInt (t - s.x.pos.toInt) })
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ ⟨c.want.1, c.want.2, Or.inr rfl⟩
        ⟨by show 0 ≤ (Int64.ofInt (t - s.x.pos.toInt)).toInt; rw [hK]; omega,
          by show s.x.pos.toInt + (Int64.ofInt (t - s.x.pos.toInt)).toInt ≤ 9223372036854775807; rw [hK]; omega,
          hph⟩
        (Nat.le_refl _) (fun hr' => absurd (hr'.symm.trans hm) (by decide)) (fun _ => w.reset)
      exact post_gen inv hfs hW0 hr inv2 rfl rfl (fun _ => False) (fun _ e => e.elim)
        (fun b => ⟨fun hh => ⟨(putGz_owned (s' := { s with skip := Int64.ofInt (t - s.x.pos.toInt) }) hs ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ b).1 hh, id⟩,
          fun hh => (putGz_owned (s' := { s with skip := Int64.ofInt (t - s.x.pos.toInt) }) hs ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ b).2 hh.1⟩)
        (fun b => ⟨fun hh => ⟨(putGz_live hs b).1 hh, id⟩, fun hh => (putGz_live hs b).2 hh.1⟩)
        (frame_setS (gz_frame_refl h _) (Or.inl rfl) _)
    · rw [ite_eq_right hc] at hrun
      exact ⟨_, _, _, hrun, post_same inv hfs hW0 hr⟩

/-- `gzseek64`: from `gzseek64_safe` restated to `GzInv`: result -1 or the target, positions bounded, the COPY
path's `lseek` (M3: any result, unrelated to reads), the rewind path. Relies on patch 0002 (R-1) and the local
patches for R-3, R-4 (`x.next += 0`) and F-1. -/
theorem gzseek64_step (i : Nat) (offset : Int64) (whence : Int32) :
    GzCallSafe i (.gzseek64 (some (.in_gzstate_x i)) offset whence) := by
  intro h fs s inv hfs _
  obtain ⟨r, fs', after, e, post⟩ := gzseek64_inv inv hfs offset whence
  have e' : Call.execute (.gzseek64 (some (.in_gzstate_x i)) offset whence) fs h = .ok ((r, fs'), after) := e
  refine ⟨fun err he => ?_, fun _ => ⟨r, fs', after, e'⟩, fun v fs2 a2 he => ?_⟩
  · rw [e'] at he
    cases he
  · rw [e'] at he
    cases he
    exact post

/-- `gzseek` is `gzseek64` (`gzseek_eq`). -/
theorem gzseek_step (i : Nat) (offset : Int64) (whence : Int32) :
    GzCallSafe i (.gzseek (some (.in_gzstate_x i)) offset whence) := by
  intro h fs s inv hfs ha
  have e : Call.execute (.gzseek (some (.in_gzstate_x i)) offset whence) fs h =
      Call.execute (.gzseek64 (some (.in_gzstate_x i)) offset whence) fs h :=
    Zlib.Gzlib.Proofs.gzseek_eq _ offset whence fs h
  rw [e]
  exact gzseek64_step i offset whence h fs s inv hfs ha

end ZlibF.Spec.Public.GzSkeleton
