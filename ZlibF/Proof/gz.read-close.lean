import ZlibF.Proof.«gz.read-look»
import ZlibF.Proof.«gzread.c.close»

/-!
# gz read side: `gzclose_r` is safe

`gzclose_r(file)` on a reader: with buffers (`size != 0`) it calls `inflateEnd` on the embedded stream and frees
`out` and `in`; then `gz_error(state, Z_OK, NULL)` frees the message, `free(path)`, `close(fd)`, `free(state)`.

The statement is the close step of the gz skeleton (`gzclose_r_step`, with `GzCloseSafe` and `GzReleased` of
`gz.skeleton-model.lean` on the branch `skeleton/gz`). Those two definitions are not on `dev`; `Close.Released`
below is a copy of `GzReleased`, and `gzclose_r_step_safe` is `GzCloseSafe i (.gzclose_r (some (.in_gzstate_x i)))`
written out.

1. The OS world: `close(fd)` releases the descriptor in every world, also when the oracle reports `-1` (M4), and
   changes no other descriptor (`close_world`).
2. The heap: a generic ledger lemma (`release_of`): if the final heap is the old one with exactly the owned objects
   removed, the frame and the exact ledger hold.
3. The two runs (`run_buf`, `run_unbuf`) as compositions of the primitive runs.
4. `gzclose_r_safe` (reader) and `gzclose_r_step_safe` (any handle in `GzInv`).

No callee contract is assumed: `inflateEnd` is `inflateEnd_safe` on the codec, which `GzReadInv.codec` gives as a
reachable inflate stream.
-/

namespace ZlibF.Spec.Public.GzRead
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib.Spec Zlib.Gzlib.Proofs ZlibF.Spec.Public
set_option autoImplicit false

namespace Close

/-- The handle is gone: the record and every owned block freed, nothing else changed, and the descriptor
released also when `close` reports -1 (M4); no other descriptor changes. A copy of `GzReleased` of the gz
skeleton (`gz.skeleton-model.lean`, branch `skeleton/gz`). -/
def Released (h after : Heap) (fs fs' : Fs) (i : Nat) (s : GzState) : Prop :=
  after.gzstates i = none ∧ Frame h after (GzOwned h i s) ∧
  LiveChange h after (fun _ => False) (GzOwned h i s) ∧ FileSystem fs' ∧
  (0 ≤ s.fd.toInt → ¬ GzOracle.FdOpen fs' s.fd.toInt.toNat) ∧
  (∀ j, (0 ≤ s.fd.toInt → j ≠ s.fd.toInt.toNat) → (GzOracle.FdOpen fs' j ↔ GzOracle.FdOpen fs j))

/-! ## 1. The OS world after `close(fd)` -/

/-- The result of the regular-file `close` (`fsCloseReg`), as a pure function. -/
def regOut (fd : Int32) (w : Fs) : Int32 × Fs :=
  if fd < 0 || fd.toInt ≥ w.fds.size then (-1, { w with errno := EBADF })
  else match w.fds[fd.toInt.toNat]! with
    | none => (-1, { w with errno := EBADF })
    | some _ => (0, { w with fds := w.fds.set! fd.toInt.toNat none })

theorem fsCloseReg_eq (fd : Int32) (w : Fs) : fsCloseReg fd w = (pure (regOut fd w) : M (Int32 × Fs)) := by
  unfold fsCloseReg regOut
  split
  · first | rfl | simp_all
  · split
    · first | rfl | simp_all
    · first | rfl | simp_all

theorem regOut_props (fd : Int32) (w : Fs) :
    (regOut fd w).2.fsizeLimit = w.fsizeLimit ∧ (regOut fd w).2.names = w.names ∧
    (regOut fd w).2.nodes = w.nodes ∧
    (∀ j, (0 ≤ fd.toInt → j ≠ fd.toInt.toNat) → (regOut fd w).2.fds[j]? = w.fds[j]?) ∧
    (0 ≤ fd.toInt → ∀ f, (regOut fd w).2.fds[fd.toInt.toNat]? ≠ some (some f)) := by
  unfold regOut
  split
  · next hc =>
    refine ⟨rfl, rfl, rfl, fun _ _ => rfl, ?_⟩
    intro h0 f hf
    dsimp only at hf
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hc
    rcases hc with hc | hc
    · rw [Int32.lt_iff_toInt_lt, Int32.toInt_zero] at hc
      omega
    · have hle : w.fds.size ≤ fd.toInt.toNat := by omega
      rw [Array.getElem?_eq_none hle] at hf
      cases hf
  · next hc =>
    have h0 : 0 ≤ fd.toInt ∧ fd.toInt < w.fds.size := by
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hc
      rw [Int32.lt_iff_toInt_lt, Int32.toInt_zero] at hc
      omega
    split
    · next hx =>
      refine ⟨rfl, rfl, rfl, fun _ _ => rfl, ?_⟩
      intro _ f hf
      dsimp only at hf
      rw [getElem!_def, hf] at hx
      cases hx
    · refine ⟨rfl, rfl, rfl, ?_, ?_⟩
      · intro j hj
        have hne : fd.toInt.toNat ≠ j := fun e => hj h0.1 e.symm
        show (w.fds.set! fd.toInt.toNat none)[j]? = w.fds[j]?
        rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, if_neg hne]
      · intro _ f hf
        have hlt : fd.toInt.toNat < w.fds.size := by omega
        dsimp only at hf
        rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, if_pos rfl, if_pos hlt] at hf
        cases hf

theorem closeResult_eq (fd : Int32) (fs : Fs) :
    Zlib.Gzread.Proofs.closeResult fd fs = (match fs.closeFail fs.nos with
      | some e => (-1, { (regOut fd (tickW fs)).2 with errno := failErrno e EIO })
      | none => ((regOut fd (tickW fs)).1, if (regOut fd (tickW fs)).1 = -1 then (regOut fd (tickW fs)).2
          else okErrW (fs.okErrno fs.nos) (regOut fd (tickW fs)).2)) := by
  unfold Zlib.Gzread.Proofs.closeResult fsClose
  simp only [fsCloseReg_eq]
  rfl

theorem fs_of_sub {w w' : Fs} (hfs : FileSystem w) (e1 : w'.fsizeLimit = w.fsizeLimit) (e2 : w'.names = w.names)
    (e3 : w'.nodes = w.nodes)
    (hf : ∀ (j : Nat) (f : OFile), w'.fds[j]? = some (some f) → w.fds[j]? = some (some f)) : FileSystem w' := by
  obtain ⟨a, b, c, d⟩ := hfs
  refine ⟨by rw [e1]; exact a, ?_, ?_, ?_⟩
  · intro p n hp
    rw [e2] at hp
    rw [e3]
    exact b p n hp
  · intro j f hj
    rw [e3]
    exact c j f (hf j f hj)
  · intro j n hj
    rw [e3] at hj
    exact d j n hj

/-- **`close(fd)` in every world**: the world stays well formed, the descriptor is no longer open (also when the
oracle reports a failure, M4), and every other descriptor is as it was. -/
theorem close_world (fd : Int32) (fs : Fs) (hfs : FileSystem fs) :
    FileSystem (Zlib.Gzread.Proofs.closeResult fd fs).2 ∧
    (0 ≤ fd.toInt → ¬ GzOracle.FdOpen (Zlib.Gzread.Proofs.closeResult fd fs).2 fd.toInt.toNat) ∧
    (∀ j, (0 ≤ fd.toInt → j ≠ fd.toInt.toNat) →
      (GzOracle.FdOpen (Zlib.Gzread.Proofs.closeResult fd fs).2 j ↔ GzOracle.FdOpen fs j)) := by
  obtain ⟨e1, e2, e3, p1, p2⟩ := regOut_props fd (tickW fs)
  have key : ∀ y : Fs, y.fsizeLimit = (regOut fd (tickW fs)).2.fsizeLimit → y.names = (regOut fd (tickW fs)).2.names →
      y.nodes = (regOut fd (tickW fs)).2.nodes → y.fds = (regOut fd (tickW fs)).2.fds →
      FileSystem y ∧ (0 ≤ fd.toInt → ¬ GzOracle.FdOpen y fd.toInt.toNat) ∧
      (∀ j, (0 ≤ fd.toInt → j ≠ fd.toInt.toNat) → (GzOracle.FdOpen y j ↔ GzOracle.FdOpen fs j)) := by
    intro y f1 f2 f3 f4
    refine ⟨fs_of_sub hfs (f1.trans e1) (f2.trans e2) (f3.trans e3) ?_, ?_, ?_⟩
    · intro j f hj
      rw [f4] at hj
      by_cases hc : (0 ≤ fd.toInt → j ≠ fd.toInt.toNat)
      · rw [p1 j hc] at hj
        exact hj
      · exfalso
        by_cases h0 : 0 ≤ fd.toInt
        · by_cases hjn : j = fd.toInt.toNat
          · subst hjn
            exact p2 h0 f hj
          · exact hc (fun _ => hjn)
        · exact hc (fun h' => absurd h' h0)
    · rintro h0 ⟨f, hf⟩
      rw [f4] at hf
      exact p2 h0 f hf
    · intro j hj
      unfold GzOracle.FdOpen
      rw [f4, p1 j hj]
      exact Iff.rfl
  rw [closeResult_eq]
  cases fs.closeFail fs.nos with
  | some e => exact key _ rfl rfl rfl rfl
  | none =>
    dsimp only
    split
    · exact key _ rfl rfl rfl rfl
    · cases fs.okErrno fs.nos with
      | none => exact key _ rfl rfl rfl rfl
      | some e => exact key _ rfl rfl rfl rfl

/-! ## 2. The heap: removing exactly the owned objects -/

/-- The fields other than `bytes`, `istates` and `gzstates` agree. -/
def SameRest (A B : Heap) : Prop :=
  A.words = B.words ∧ A.streams = B.streams ∧ A.gzheaders = B.gzheaders ∧ A.dstates = B.dstates ∧ A.ro = B.ro ∧
  A.static = B.static ∧ A.allocOk = B.allocOk ∧ A.garbage = B.garbage ∧ A.nextBlk = B.nextBlk ∧ A.nalloc = B.nalloc

theorem SameRest.trans {A B C : Heap} (x : SameRest A B) (y : SameRest B C) : SameRest A C := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := x
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := y
  exact ⟨a1.trans b1, a2.trans b2, a3.trans b3, a4.trans b4, a5.trans b5, a6.trans b6, a7.trans b7, a8.trans b8,
    a9.trans b9, a10.trans b10⟩

theorem rest_freeStr (H : Heap) (p : BPtr) : SameRest (freeStr H p) H := by
  cases p with
  | null => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | ref r o => cases r <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem rest_setS (H : Heap) (i : Nat) (t : GzState) : SameRest (setS H i t) H :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem rest_freeIst (H : Heap) (k : Nat) : SameRest (Zlib.Inflate.Spec.freeIst H k) H :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem fs_istates (H : Heap) (p : BPtr) : (freeStr H p).istates = H.istates := by
  cases p with
  | null => rfl
  | ref r o => cases r <;> rfl

theorem fs_gzstates (H : Heap) (p : BPtr) : (freeStr H p).gzstates = H.gzstates := by
  cases p with
  | null => rfl
  | ref r o => cases r <;> rfl

theorem fs_bytes_ne (H : Heap) {p : BPtr} {b : Nat} (hb : blkOf p ≠ some b) : (freeStr H p).bytes b = H.bytes b := by
  cases p with
  | null => rfl
  | ref r o =>
    cases r with
    | blk x =>
      have hx : b ≠ x := fun e => hb (by rw [e]; rfl)
      exact upd_ne _ _ _ _ hx
    | _ => rfl

theorem fs_bytes_kill (H : Heap) {p : BPtr} {b : Nat} (hb : blkOf p = some b) : (freeStr H p).bytes b = none := by
  cases p with
  | null => cases hb
  | ref r o =>
    cases r with
    | blk x =>
      have hx : x = b := Option.some.inj hb
      subst hx
      exact upd_same _ _ _
    | _ => cases hb

theorem fs_bytes_none (H : Heap) (p : BPtr) {b : Nat} (hn : H.bytes b = none) : (freeStr H p).bytes b = none := by
  by_cases hb : blkOf p = some b
  · exact fs_bytes_kill H hb
  · rw [fs_bytes_ne H hb]
    exact hn

theorem ne_blk {p : BPtr} {x b : Nat} (hp : p = .ref (.blk x) 0) (hne : x ≠ b) : blkOf p ≠ some b := by
  subst hp
  intro e
  exact hne (Option.some.inj e)

theorem ptr_of {p : BPtr} {x b : Nat} (hp : p = .ref (.blk x) 0) (hb : blkOf p = some b) : p = .ref (.blk b) 0 := by
  subst hp
  have e : x = b := Option.some.inj hb
  rw [e]

/-- **The ledger of a removal.** If the final heap `T` is `h` with the objects of the blocks `DB` removed from the
byte table, those of `DI` from the inflate-state table and the record `i`, the other tables and fields unchanged, and
every block of `O` is one of these objects, then `T` frames `h` over `O` and its live blocks are those of `h` minus
`O`. -/
theorem release_of {h T : Heap} {i : Nat} {s : GzState} {O DB DI : Nat → Prop}
    (u : Zlib.Gzlib.Spec.Uniq h) (hs : h.gzstates i = some s) (rest : SameRest T h)
    (bk : ∀ b, ¬ DB b → T.bytes b = h.bytes b) (bd : ∀ b, DB b → T.bytes b = none)
    (ik : ∀ b, ¬ DI b → T.istates b = h.istates b) (idd : ∀ b, DI b → T.istates b = none)
    (gk : ∀ b, b ≠ i → T.gzstates b = h.gzstates b) (gd : T.gzstates i = none)
    (hDB : ∀ b, DB b → O b) (hDI : ∀ b, DI b → O b) (hOi : O i)
    (cover : ∀ b, O b → b = i ∨ (DB b ∧ ∃ a, h.bytes b = some a) ∨ (DI b ∧ ∃ x, h.istates b = some x)) :
    Frame h T O ∧ LiveChange h T (fun _ => False) O := by
  obtain ⟨ew, es, eh, ed, er, est, ea, eg, en, ena⟩ := rest
  have keep : ∀ b, ¬ O b → T.bytes b = h.bytes b ∧ T.words b = h.words b ∧ T.streams b = h.streams b ∧
      T.gzheaders b = h.gzheaders b ∧ T.dstates b = h.dstates b ∧ T.istates b = h.istates b ∧
      T.gzstates b = h.gzstates b ∧ T.ro b = h.ro b := by
    intro b hb
    refine ⟨bk b (fun d => hb (hDB b d)), by rw [ew], by rw [es], by rw [eh], by rw [ed],
      ik b (fun d => hb (hDI b d)), gk b (fun e => hb (by rw [e]; exact hOi)), by rw [er]⟩
  have dead : ∀ b, O b → ¬ T.live b := by
    intro b hb hl
    unfold Heap.live at hl
    rcases cover b hb with e | ⟨d, a, ha⟩ | ⟨d, x, hx⟩
    · subst e
      obtain ⟨n1, n2, n3, n4, n5, n6⟩ := Zlib.Gzwrite.SafeInit.uniq_gz_only u hs
      have t1 : T.bytes b = none := by
        by_cases d : DB b
        · exact bd b d
        · rw [bk b d, n1]
      have t6 : T.istates b = none := by
        by_cases d : DI b
        · exact idd b d
        · rw [ik b d, n6]
      rw [t1, ew, n2, es, n3, eh, n4, ed, n5, t6, gd] at hl
      simp at hl
    · obtain ⟨n2, n3, n4, n5, n6, n7⟩ := Look.uniq_bytes_all u ha
      have t6 : T.istates b = none := by
        by_cases d : DI b
        · exact idd b d
        · rw [ik b d, n6]
      have t7 : T.gzstates b = none := by
        by_cases e : b = i
        · subst e
          exact gd
        · rw [gk b e, n7]
      rw [bd b d, ew, n2, es, n3, eh, n4, ed, n5, t6, t7] at hl
      simp at hl
    · obtain ⟨n2, n3, n4, n5, n1, n7⟩ := Zlib.Inflate.Proofs.Uniq.istates_only u hx
      have t1 : T.bytes b = none := by
        by_cases d : DB b
        · exact bd b d
        · rw [bk b d, n1]
      have t7 : T.gzstates b = none := by
        by_cases e : b = i
        · subst e
          exact gd
        · rw [gk b e, n7]
      rw [t1, ew, n2, es, n3, eh, n4, ed, n5, idd b d, t7] at hl
      simp at hl
  refine ⟨⟨est.symm, ea.symm, eg.symm, Nat.le_of_eq en.symm, Nat.le_of_eq ena.symm, fun b _ hb => keep b hb⟩, ?_⟩
  intro b
  by_cases hb : O b
  · constructor
    · intro hl
      exact absurd hl (dead b hb)
    · rintro (⟨_, h2⟩ | h3)
      · exact absurd hb h2
      · exact (h3 : False).elim
  · obtain ⟨k1, k2, k3, k4, k5, k6, k7, -⟩ := keep b hb
    unfold Heap.live
    rw [k1, k2, k3, k4, k5, k6, k7]
    constructor
    · intro hl
      exact Or.inl ⟨hl, hb⟩
    · rintro (⟨hl, _⟩ | f)
      · exact hl
      · exact (f : False).elim

/-! ## 3. The heaps of the run -/

/-- `free(state)`: the record is gone. -/
def finH (X : Heap) (i : Nat) : Heap := { X with gzstates := upd X.gzstates i none }

/-- The heap after `gz_error(state, Z_OK, NULL)`, `free(path)` and `free(state)`. -/
def tailH (H : Heap) (i : Nat) (t : GzState) : Heap :=
  finH (freeStr (setS (freeStr H t.msg) i (errNull t Z_OK)) t.path) i

/-- The record after `inflateEnd`: the embedded stream has no state. -/
def strip (s : GzState) : GzState := { s with strm := { s.strm with state := none } }

/-- The heap after `inflateEnd(&state->strm); free(state->out); free(state->in);`. -/
def codecH (h : Heap) (i k : Nat) (s : GzState) (st : InflateState) : Heap :=
  freeStr (freeStr (setS (Zlib.Inflate.Spec.endHeap h k st) i (strip s)) s.out) s.«in»

theorem rest_tail (H : Heap) (i : Nat) (t : GzState) : SameRest (tailH H i t) H :=
  ((rest_freeStr _ _).trans (rest_setS _ _ _)).trans (rest_freeStr _ _)

theorem tail_bytes_keep (H : Heap) (i : Nat) (t : GzState) {b : Nat} (h1 : blkOf t.path ≠ some b)
    (h2 : blkOf t.msg ≠ some b) : (tailH H i t).bytes b = H.bytes b := by
  show (freeStr (setS (freeStr H t.msg) i (errNull t Z_OK)) t.path).bytes b = H.bytes b
  rw [fs_bytes_ne _ h1, setS_bytes, fs_bytes_ne _ h2]

theorem tail_bytes_kill (H : Heap) (i : Nat) (t : GzState) {b : Nat}
    (h : blkOf t.path = some b ∨ blkOf t.msg = some b) : (tailH H i t).bytes b = none := by
  show (freeStr (setS (freeStr H t.msg) i (errNull t Z_OK)) t.path).bytes b = none
  rcases h with h | h
  · exact fs_bytes_kill _ h
  · exact fs_bytes_none _ _ (by rw [setS_bytes]; exact fs_bytes_kill _ h)

theorem tail_bytes_none (H : Heap) (i : Nat) (t : GzState) {b : Nat} (h : H.bytes b = none) :
    (tailH H i t).bytes b = none := by
  show (freeStr (setS (freeStr H t.msg) i (errNull t Z_OK)) t.path).bytes b = none
  exact fs_bytes_none _ _ (by rw [setS_bytes]; exact fs_bytes_none _ _ h)

theorem tail_istates (H : Heap) (i : Nat) (t : GzState) : (tailH H i t).istates = H.istates := by
  show (freeStr (setS (freeStr H t.msg) i (errNull t Z_OK)) t.path).istates = H.istates
  rw [fs_istates, setS_istates, fs_istates]

theorem tail_gz_i (H : Heap) (i : Nat) (t : GzState) : (tailH H i t).gzstates i = none :=
  upd_same _ _ _

theorem tail_gz_ne (H : Heap) (i : Nat) (t : GzState) {b : Nat} (hb : b ≠ i) :
    (tailH H i t).gzstates b = H.gzstates b := by
  show (upd (freeStr (setS (freeStr H t.msg) i (errNull t Z_OK)) t.path).gzstates i none) b = H.gzstates b
  rw [upd_ne _ _ _ _ hb, fs_gzstates, setS_gz_ne _ _ _ _ hb, fs_gzstates]

section codec
variable {h : Heap} {i k : Nat} {s : GzState} {st : InflateState}

theorem freeWin_eq (H : Heap) {p : BPtr} (hw : p = .null ∨ ∃ w, p = .ref (.blk w) 0) :
    Zlib.Inflate.Spec.freeWin H p = freeStr H p := by
  rcases hw with hn | ⟨w, hw⟩
  · subst hn; rfl
  · subst hw; rfl

theorem endHeap_eq (hw : st.window = .null ∨ ∃ w, st.window = .ref (.blk w) 0) :
    Zlib.Inflate.Spec.endHeap h k st = Zlib.Inflate.Spec.freeIst (freeStr h st.window) k := by
  unfold Zlib.Inflate.Spec.endHeap
  rw [freeWin_eq h hw]

theorem rest_codec (hw : st.window = .null ∨ ∃ w, st.window = .ref (.blk w) 0) : SameRest (codecH h i k s st) h := by
  unfold codecH
  rw [endHeap_eq hw]
  exact (rest_freeStr _ _).trans ((rest_freeStr _ _).trans ((rest_setS _ _ _).trans
    ((rest_freeIst _ _).trans (rest_freeStr _ _))))

theorem codec_bytes_keep (hw : st.window = .null ∨ ∃ w, st.window = .ref (.blk w) 0) {b : Nat}
    (h1 : blkOf s.«in» ≠ some b) (h2 : blkOf s.out ≠ some b) (h3 : blkOf st.window ≠ some b) :
    (codecH h i k s st).bytes b = h.bytes b := by
  unfold codecH
  rw [endHeap_eq hw, fs_bytes_ne _ h1, fs_bytes_ne _ h2, setS_bytes]
  exact fs_bytes_ne _ h3

theorem codec_bytes_kill (hw : st.window = .null ∨ ∃ w, st.window = .ref (.blk w) 0) {b : Nat}
    (d : blkOf s.«in» = some b ∨ blkOf s.out = some b ∨ blkOf st.window = some b) :
    (codecH h i k s st).bytes b = none := by
  unfold codecH
  rw [endHeap_eq hw]
  rcases d with d | d | d
  · exact fs_bytes_kill _ d
  · exact fs_bytes_none _ _ (fs_bytes_kill _ d)
  · exact fs_bytes_none _ _ (fs_bytes_none _ _ (by rw [setS_bytes]; exact fs_bytes_kill _ d))

theorem codec_istates : (codecH h i k s st).istates = upd h.istates k none := by
  unfold codecH
  rw [fs_istates, fs_istates, setS_istates]
  show upd (Zlib.Inflate.Spec.freeWin h st.window).istates k none = upd h.istates k none
  simp

theorem codec_gz : (codecH h i k s st).gzstates = upd h.gzstates i (some (strip s)) := by
  unfold codecH
  rw [fs_gzstates, fs_gzstates]
  show upd (Zlib.Inflate.Spec.endHeap h k st).gzstates i (some (strip s)) = upd h.gzstates i (some (strip s))
  rw [show (Zlib.Inflate.Spec.endHeap h k st).gzstates = h.gzstates by
    simp [Zlib.Inflate.Spec.endHeap]]

end codec

/-! ## 4. The runs -/

theorem put_gz {H : Heap} {i : Nat} {t : GzState} (e : H.gzstates i = some t) (z : ZStream) :
    (ZStreamRef.in_gzstate_strm i).put H z = setS H i { t with strm := z } := by
  simp [ZStreamRef.put, e, setS]

theorem freeGzState_run {H : Heap} {i : Nat} {u : GzState} (e : H.gzstates i = some u) :
    freeGzState (some (.tab i)) H = .ok ((), finH H i) := by
  simp [freeGzState, e, finH]

/-- `gz_error(state, Z_OK, NULL)`: the old message is freed, the code is `Z_OK`, there is no message. -/
theorem err_run {H : Heap} {i : Nat} {t : GzState} (hs : H.gzstates i = some t)
    (hmsg : t.msg = .null ∨ ∃ mb a, t.msg = .ref (.blk mb) 0 ∧ H.bytes mb = some a ∧ H.ro mb = false)
    (hmem : t.err = Z_MEM_ERROR → t.msg = .null) :
    Zlib.Gzlib.gz_error (some (.tab i)) Z_OK .null H = .ok ((), setS (freeStr H t.msg) i (errNull t Z_OK)) := by
  unfold Zlib.Gzlib.gz_error
  rcases hmsg with hn | ⟨mb, a, hm, ha, hro⟩
  · gsimp [hs, hn, errNull]
  · have hne : t.err ≠ Z_MEM_ERROR := fun h' => by have := hmem h'; rw [hm] at this; cases this
    gsimp [hs, hm, hne, freeB_blk_run ha hro, freeB_blk_setS ha hro, errNull]

/-- The run of a reader with buffers, given the runs of its pieces. -/
theorem run_buf {h H1 H2 H3 H4 H5 : Heap} {i : Nat} {s t : GzState} (fs : Fs) (hs : h.gzstates i = some s)
    (hm : s.mode = GZ_READ) (hsz : s.size ≠ 0)
    (e1 : Zlib.Inflate.inflateEnd (some (.in_gzstate_strm i)) h = .ok (Z_OK, H1))
    (e2 : freeB s.out H1 = .ok ((), H2)) (e3 : freeB s.«in» H2 = .ok ((), H3))
    (e4 : Zlib.Gzlib.gz_error (some (.tab i)) Z_OK .null H3 = .ok ((), H4))
    (e5 : H4.gzstates i = some t) (e6 : freeB t.path H4 = .ok ((), H5)) {u : GzState}
    (e7 : H5.gzstates i = some u) :
    Zlib.Gzread.gzclose_r (hnd i) fs h =
      .ok (((if (Zlib.Gzread.Proofs.closeResult t.fd fs).1 ≠ 0 then Z_ERRNO
        else if s.err = Z_BUF_ERROR then Z_BUF_ERROR else Z_OK),
        (Zlib.Gzread.Proofs.closeResult t.fd fs).2), finH H5 i) := by
  have hm' : (s.mode != GZ_READ) = false := by simp [hm]
  have hz' : (s.size != 0) = true := by simp [hsz]
  unfold Zlib.Gzread.gzclose_r
  simp only [hnd_isNone, Bool.false_eq_true, ↓reduceIte, castState_hnd]
  simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, g_bind_app, g_lift_app,
    ldS_run hs, hm', hz', Bool.false_eq_true, eq_self_iff_true, ↓reduceIte, strmOf_tab, e1, e2, e3, e4,
    ldS_run e5, e6]
  simp [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, g_bind_app, g_lift_app,
    g_pure_app, Zlib.Gzread.Proofs.fsClose_run, freeGzState_run e7]

/-- The run of a reader without buffers, given the runs of its pieces. -/
theorem run_unbuf {h H4 H5 : Heap} {i : Nat} {s t : GzState} (fs : Fs) (hs : h.gzstates i = some s)
    (hm : s.mode = GZ_READ) (hsz : s.size = 0)
    (e4 : Zlib.Gzlib.gz_error (some (.tab i)) Z_OK .null h = .ok ((), H4))
    (e5 : H4.gzstates i = some t) (e6 : freeB t.path H4 = .ok ((), H5)) {u : GzState}
    (e7 : H5.gzstates i = some u) :
    Zlib.Gzread.gzclose_r (hnd i) fs h =
      .ok (((if (Zlib.Gzread.Proofs.closeResult t.fd fs).1 ≠ 0 then Z_ERRNO
        else if s.err = Z_BUF_ERROR then Z_BUF_ERROR else Z_OK),
        (Zlib.Gzread.Proofs.closeResult t.fd fs).2), finH H5 i) := by
  have hm' : (s.mode != GZ_READ) = false := by simp [hm]
  have hz' : (s.size != 0) = false := by simp [hsz]
  unfold Zlib.Gzread.gzclose_r
  simp only [hnd_isNone, Bool.false_eq_true, ↓reduceIte, castState_hnd]
  simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, g_bind_app, g_lift_app,
    ldS_run hs, hm', hz', Bool.false_eq_true, ↓reduceIte, e4, ldS_run e5, e6]
  simp [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, g_bind_app, g_lift_app,
    g_pure_app, Zlib.Gzread.Proofs.fsClose_run, freeGzState_run e7]

theorem rc_cases (c : Int32) (e : Int32) :
    (if c ≠ 0 then Z_ERRNO else if e = Z_BUF_ERROR then Z_BUF_ERROR else Z_OK) = Z_OK ∨
    (if c ≠ 0 then Z_ERRNO else if e = Z_BUF_ERROR then Z_BUF_ERROR else Z_OK) = Z_BUF_ERROR ∨
    (if c ≠ 0 then Z_ERRNO else if e = Z_BUF_ERROR then Z_BUF_ERROR else Z_OK) = Z_ERRNO := by
  by_cases h1 : c ≠ 0
  · rw [if_pos h1]
    exact Or.inr (Or.inr rfl)
  · rw [if_neg h1]
    by_cases h2 : e = Z_BUF_ERROR
    · rw [if_pos h2]
      exact Or.inr (Or.inl rfl)
    · rw [if_neg h2]
      exact Or.inl rfl

/-! ## 5. The pointer facts of a reader -/

section blocks
variable {h : Heap} {i : Nat} {s : GzState}

theorem nodup3 {a b c : Nat} (hn : [a, b, c].Nodup) : a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩ <;> subst e <;> simp at hn

theorem nodup4 {a b c d : Nat} (hn : [a, b, c, d].Nodup) :
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  refine ⟨fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_⟩ <;> subst e <;> simp at hn

/-- The path and the message: live writable blocks, distinct. -/
theorem path_msg (inv : GzInv h i s) :
    ∃ pb pa, s.path = .ref (.blk pb) 0 ∧ h.bytes pb = some pa ∧ h.ro pb = false ∧
      (s.msg = .null ∨ ∃ mb ma, s.msg = .ref (.blk mb) 0 ∧ h.bytes mb = some ma ∧ h.ro mb = false ∧ mb ≠ pb) := by
  have c := GzInv.common inv
  obtain ⟨_, _, pb, pa, hp, hpa, hpro, _⟩ := c.path
  refine ⟨pb, pa, hp, hpa, hpro, ?_⟩
  rcases c.msg with hmn | ⟨_, _, mb, ma, hmg, hma, hmro, _⟩
  · exact Or.inl hmn
  · refine Or.inr ⟨mb, ma, hmg, hma, hmro, ?_⟩
    have nd := c.distinct.1
    have e : ownedPtrs s = [s.path, s.msg] ++
        (if s.size ≠ 0 then s.«in» :: (if s.mode = GZ_READ ∨ s.direct = 0 then [s.out] else []) else []) := rfl
    rw [e, List.filterMap_append, hp, hmg] at nd
    have nd2 := (List.nodup_append.mp nd).1
    simp [blkOf] at nd2
    omega

/-- With buffers: `in` and `out` are live writable blocks, distinct from each other and from the path and the
message. -/
theorem bufs_distinct (inv : GzInv h i s) (hm : s.mode = GZ_READ) (hsz : s.size ≠ 0) :
    ∃ pb pa ib ia ob oa, s.path = .ref (.blk pb) 0 ∧ h.bytes pb = some pa ∧ h.ro pb = false ∧
      s.«in» = .ref (.blk ib) 0 ∧ h.bytes ib = some ia ∧ h.ro ib = false ∧
      s.out = .ref (.blk ob) 0 ∧ h.bytes ob = some oa ∧ h.ro ob = false ∧
      pb ≠ ib ∧ pb ≠ ob ∧ ib ≠ ob ∧
      (s.msg = .null ∨ ∃ mb ma, s.msg = .ref (.blk mb) 0 ∧ h.bytes mb = some ma ∧ h.ro mb = false ∧
        mb ≠ pb ∧ mb ≠ ib ∧ mb ≠ ob) := by
  have c := GzInv.common inv
  have rd := GzInv.reader inv hm
  obtain ⟨_, _, pb, pa, hp, hpa, hpro, _⟩ := c.path
  obtain ⟨⟨ib, ia, hi, hia, hiro, _⟩, ⟨ob, oa, ho, hoa, horo, _⟩⟩ := rd.bufs hsz
  have nd := c.distinct.1
  have e : ownedPtrs s = [s.path, s.msg, s.«in», s.out] := by simp [ownedPtrs, hsz, hm]
  rw [e, hp, hi, ho] at nd
  rcases c.msg with hmn | ⟨_, _, mb, ma, hmg, hma, hmro, _⟩
  · rw [hmn] at nd
    have n3 : [pb, ib, ob].Nodup := nd
    obtain ⟨d1, d2, d3⟩ := nodup3 n3
    exact ⟨pb, pa, ib, ia, ob, oa, hp, hpa, hpro, hi, hia, hiro, ho, hoa, horo, d1, d2, d3, Or.inl hmn⟩
  · rw [hmg] at nd
    have n4 : [pb, mb, ib, ob].Nodup := nd
    obtain ⟨d1, d2, d3, d4, d5, d6⟩ := nodup4 n4
    exact ⟨pb, pa, ib, ia, ob, oa, hp, hpa, hpro, hi, hia, hiro, ho, hoa, horo, d2, d3, d6,
      Or.inr ⟨mb, ma, hmg, hma, hmro, Ne.symm d1, d4, d5⟩⟩

/-- An owned pointer's block is not the codec's. -/
theorem owned_not_codec (inv : GzInv h i s) {p : BPtr} (hp : p ∈ ownedPtrs s) {b : Nat} (hb : blkOf p = some b) :
    ¬ StreamOwned h (gzStrm i) b :=
  ((GzInv.common inv).distinct.2 p hp b hb).2

end blocks

/-! ## 6. `gzclose_r` -/

/-- **`gzclose_r` on a reader is safe.** On a handle in `GzInv` with `mode = GZ_READ`, for every OS world: the call
returns (no fault), with `Z_OK`, `Z_BUF_ERROR` or `Z_ERRNO`; the record and every block the handle owned (path,
message, `in`, `out`, the inflate state and its window) are freed and nothing else changes (`Frame`, exact
`LiveChange`); the descriptor is released, also when `close` reports a failure, and no other descriptor changes. -/
theorem gzclose_r_safe {h : Heap} {i : Nat} {s : GzState} (inv : GzInv h i s) (hm : s.mode = GZ_READ)
    (fs : Fs) (hfs : FileSystem fs) :
    ∃ rc fs' after, Zlib.Gzread.gzclose_r (some (.in_gzstate_x i)) fs h = .ok ((rc, fs'), after) ∧
      (rc = Z_OK ∨ rc = Z_BUF_ERROR ∨ rc = Z_ERRNO) ∧ Released h after fs fs' i s := by
  have c := GzInv.common inv
  have hs := c.record
  have u := c.uniq
  obtain ⟨w1, w2, w3⟩ := close_world s.fd fs hfs
  by_cases hsz : s.size = 0
  · -- no buffers, no codec
    obtain ⟨pb, pa, hpath, hpa, hpro, hmsg⟩ := path_msg inv
    have e4 := err_run hs (by
        rcases hmsg with hmn | ⟨mb, ma, hmg, hma, hmro, _⟩
        · exact Or.inl hmn
        · exact Or.inr ⟨mb, ma, hmg, hma, hmro⟩) c.memerr
    have e5 : (setS (freeStr h s.msg) i (errNull s Z_OK)).gzstates i = some (errNull s Z_OK) := setS_gz_same _ _ _
    have hpb : (setS (freeStr h s.msg) i (errNull s Z_OK)).bytes pb = some pa := by
      rw [setS_bytes]
      rcases hmsg with hmn | ⟨mb, ma, hmg, hma, hmro, hne⟩
      · rw [hmn]; exact hpa
      · rw [fs_bytes_ne _ (ne_blk hmg hne)]; exact hpa
    have e6 : freeB (errNull s Z_OK).path (setS (freeStr h s.msg) i (errNull s Z_OK)) =
        .ok ((), freeStr (setS (freeStr h s.msg) i (errNull s Z_OK)) s.path) :=
      freeB_run (h := setS (freeStr h s.msg) i (errNull s Z_OK)) (p := (errNull s Z_OK).path) hpath hpb
        (by rw [(rest_setS _ _ _).2.2.2.2.1, (rest_freeStr _ _).2.2.2.2.1]; exact hpro)
    have e7 : (freeStr (setS (freeStr h s.msg) i (errNull s Z_OK)) s.path).gzstates i = some (errNull s Z_OK) := by
      rw [fs_gzstates]; exact e5
    have run := run_unbuf fs hs hm hsz e4 e5 e6 e7
    refine ⟨_, _, tailH h i s, run, rc_cases _ _, tail_gz_i _ _ _, ?_⟩
    have rel := release_of (T := tailH h i s) (O := GzOwned h i s)
      (DB := fun b => blkOf s.path = some b ∨ blkOf s.msg = some b) (DI := fun _ => False) u hs
      (rest_tail _ _ _)
      (fun b hb => tail_bytes_keep _ _ _ (fun e => hb (Or.inl e)) (fun e => hb (Or.inr e)))
      (fun b hb => tail_bytes_kill _ _ _ hb)
      (fun b _ => by rw [tail_istates])
      (fun _ hb => False.elim hb)
      (fun b hb => tail_gz_ne _ _ _ hb)
      (tail_gz_i _ _ _)
      (by
        intro b hb
        rcases hb with hb | hb
        · exact Or.inr (Or.inl (ptr_of hpath hb))
        · rcases hmsg with hmn | ⟨mb, ma, hmg, _, _, _⟩
          · rw [hmn] at hb; cases hb
          · exact Or.inr (Or.inr (Or.inl (ptr_of hmg hb))))
      (fun _ hb => False.elim hb)
      (Or.inl rfl)
      (by
        intro b hb
        rcases hb with hb | hb | hb | ⟨hz, _⟩
        · exact Or.inl hb
        · right; left
          rw [hpath] at hb
          have e : pb = b := by cases hb; rfl
          subst e
          exact ⟨Or.inl (by rw [hpath]; rfl), pa, hpa⟩
        · right; left
          rcases hmsg with hmn | ⟨mb, ma, hmg, hma, _, _⟩
          · rw [hmn] at hb; cases hb
          · rw [hmg] at hb
            have e : mb = b := by cases hb; rfl
            subst e
            exact ⟨Or.inr (by rw [hmg]; rfl), ma, hma⟩
        · exact absurd hsz hz)
    exact ⟨rel.1, rel.2, w1, w2, w3⟩
  · -- buffers and an inflate codec
    have rd := GzInv.reader inv hm
    obtain ⟨k, st, hzst, hk, -, -, I⟩ := Look.codec_facts inv hm hsz
    have hfree : s.strm.zfree = .fn "zcfree" := I.alloc.2
    obtain ⟨h', hr, he, -⟩ := Zlib.Inflate.Proofs.inflateEnd_safe I.good hfree
    have hwin := Zlib.Inflate.Proofs.windowBlock I.good.inv.win
    have hw : st.window = .null ∨ ∃ w, st.window = .ref (.blk w) 0 := by
      rcases hwin with hn | ⟨w, _, hw, _, _⟩
      · exact Or.inl hn
      · exact Or.inr ⟨w, hw⟩
    have hget : (ZStreamRef.in_gzstate_strm i).get h = some s.strm := by simp [ZStreamRef.get, hs]
    have notW : ∀ x, ¬ StreamOwned h (gzStrm i) x → blkOf st.window ≠ some x := by
      intro x hx hb
      apply hx
      rcases hw with hn | ⟨w, hw'⟩
      · rw [hn] at hb; cases hb
      · exact ⟨s.strm, hget, Or.inl ⟨k, st, hzst, hk, Or.inr (ptr_of hw' hb)⟩⟩
    obtain ⟨pb, pa, ib, ia, ob, oa, hpath, hpa, hpro, hin, hia, hiro, hout, hoa, horo, dpi, dpo, dio, hmsg⟩ :=
      bufs_distinct inv hm hsz
    have memP : s.path ∈ ownedPtrs s := by simp [ownedPtrs]
    have memM : s.msg ∈ ownedPtrs s := by simp [ownedPtrs]
    have memI : s.«in» ∈ ownedPtrs s := by simp [ownedPtrs, hsz]
    have memO : s.out ∈ ownedPtrs s := by simp [ownedPtrs, hsz, hm]
    have nP := owned_not_codec inv memP (b := pb) (by rw [hpath]; rfl)
    have nI := owned_not_codec inv memI (b := ib) (by rw [hin]; rfl)
    have nO := owned_not_codec inv memO (b := ob) (by rw [hout]; rfl)
    -- the steps
    have hgz0 : (Zlib.Inflate.Spec.endHeap h k st).gzstates i = some s := by
      simp [Zlib.Inflate.Spec.endHeap, hs]
    have e1 : Zlib.Inflate.inflateEnd (some (.in_gzstate_strm i)) h =
        .ok (Z_OK, setS (Zlib.Inflate.Spec.endHeap h k st) i (strip s)) := by
      subst he
      exact hr.trans (congrArg (fun H => (Except.ok (Z_OK, H) : Except Fault (Int32 × Heap))) (put_gz hgz0 _))
    have rest1 : SameRest (setS (Zlib.Inflate.Spec.endHeap h k st) i (strip s)) h := by
      rw [endHeap_eq hw]
      exact (rest_setS _ _ _).trans ((rest_freeIst _ _).trans (rest_freeStr _ _))
    have b1 : ∀ x, blkOf st.window ≠ some x →
        (setS (Zlib.Inflate.Spec.endHeap h k st) i (strip s)).bytes x = h.bytes x := by
      intro x hx
      rw [setS_bytes, endHeap_eq hw]
      exact fs_bytes_ne _ hx
    have e2 : freeB s.out (setS (Zlib.Inflate.Spec.endHeap h k st) i (strip s)) =
        .ok ((), freeStr (setS (Zlib.Inflate.Spec.endHeap h k st) i (strip s)) s.out) :=
      freeB_run hout (by rw [b1 ob (notW ob nO)]; exact hoa) (by rw [rest1.2.2.2.2.1]; exact horo)
    have e3 : freeB s.«in» (freeStr (setS (Zlib.Inflate.Spec.endHeap h k st) i (strip s)) s.out) =
        .ok ((), codecH h i k s st) :=
      freeB_run hin (by rw [fs_bytes_ne _ (ne_blk hout (Ne.symm dio)), b1 ib (notW ib nI)]; exact hia)
        (by rw [(rest_freeStr _ _).2.2.2.2.1, rest1.2.2.2.2.1]; exact hiro)
    have restC := rest_codec (h := h) (i := i) (k := k) (s := s) hw
    have hgzC : (codecH h i k s st).gzstates i = some (strip s) := by rw [codec_gz]; exact upd_same _ _ _
    have e4 := err_run (H := codecH h i k s st) (t := strip s) hgzC (by
        rcases hmsg with hmn | ⟨mb, ma, hmg, hma, hmro, d1, d2, d3⟩
        · exact Or.inl hmn
        · have nM := owned_not_codec inv memM (b := mb) (by rw [hmg]; rfl)
          refine Or.inr ⟨mb, ma, hmg, ?_, ?_⟩
          · rw [codec_bytes_keep hw (ne_blk hin (Ne.symm d2)) (ne_blk hout (Ne.symm d3)) (notW mb nM)]
            exact hma
          · rw [restC.2.2.2.2.1]; exact hmro) c.memerr
    have e5 : (setS (freeStr (codecH h i k s st) (strip s).msg) i (errNull (strip s) Z_OK)).gzstates i =
        some (errNull (strip s) Z_OK) := setS_gz_same _ _ _
    have hpb : (setS (freeStr (codecH h i k s st) (strip s).msg) i (errNull (strip s) Z_OK)).bytes pb = some pa := by
      rw [setS_bytes]
      have hk' : (codecH h i k s st).bytes pb = some pa := by
        rw [codec_bytes_keep hw (ne_blk hin (fun e => dpi e.symm)) (ne_blk hout (fun e => dpo e.symm)) (notW pb nP)]
        exact hpa
      rcases hmsg with hmn | ⟨mb, ma, hmg, hma, hmro, d1, d2, d3⟩
      · show (freeStr (codecH h i k s st) s.msg).bytes pb = some pa
        rw [hmn]; exact hk'
      · show (freeStr (codecH h i k s st) s.msg).bytes pb = some pa
        rw [fs_bytes_ne _ (ne_blk hmg d1)]; exact hk'
    have e6 : freeB (errNull (strip s) Z_OK).path
        (setS (freeStr (codecH h i k s st) (strip s).msg) i (errNull (strip s) Z_OK)) =
        .ok ((), freeStr (setS (freeStr (codecH h i k s st) (strip s).msg) i (errNull (strip s) Z_OK)) s.path) :=
      freeB_run (h := setS (freeStr (codecH h i k s st) (strip s).msg) i (errNull (strip s) Z_OK))
        (p := (errNull (strip s) Z_OK).path) hpath hpb
        (by rw [(rest_setS _ _ _).2.2.2.2.1, (rest_freeStr _ _).2.2.2.2.1, restC.2.2.2.2.1]; exact hpro)
    have e7 : (freeStr (setS (freeStr (codecH h i k s st) (strip s).msg) i (errNull (strip s) Z_OK)) s.path).gzstates i =
        some (errNull (strip s) Z_OK) := by
      rw [fs_gzstates]; exact e5
    have run := run_buf fs hs hm hsz e1 e2 e3 e4 e5 e6 e7
    refine ⟨_, _, tailH (codecH h i k s st) i (strip s), run, rc_cases _ _, tail_gz_i _ _ _, ?_⟩
    have rel := release_of (T := tailH (codecH h i k s st) i (strip s)) (O := GzOwned h i s)
      (DB := fun b => blkOf s.path = some b ∨ blkOf s.msg = some b ∨ blkOf s.«in» = some b ∨
        blkOf s.out = some b ∨ blkOf st.window = some b)
      (DI := fun b => b = k) u hs
      ((rest_tail _ _ _).trans restC)
      (by
        intro b hb
        simp only [not_or] at hb
        obtain ⟨n1, n2, n3, n4, n5⟩ := hb
        rw [tail_bytes_keep (codecH h i k s st) i (strip s) n1 n2]
        exact codec_bytes_keep hw n3 n4 n5)
      (by
        intro b hb
        rcases hb with hb | hb | hb
        · exact tail_bytes_kill (codecH h i k s st) i (strip s) (Or.inl hb)
        · exact tail_bytes_kill (codecH h i k s st) i (strip s) (Or.inr hb)
        · exact tail_bytes_none (codecH h i k s st) i (strip s) (codec_bytes_kill hw hb))
      (by
        intro b hb
        rw [tail_istates, codec_istates]
        exact upd_ne _ _ _ _ hb)
      (by
        intro b hb
        rw [hb, tail_istates, codec_istates]
        exact upd_same _ _ _)
      (by
        intro b hb
        rw [tail_gz_ne (codecH h i k s st) i (strip s) hb, codec_gz]
        exact upd_ne _ _ _ _ hb)
      (tail_gz_i _ _ _)
      (by
        intro b hb
        rcases hb with hb | hb | hb | hb | hb
        · exact Or.inr (Or.inl (ptr_of hpath hb))
        · rcases hmsg with hmn | ⟨mb, ma, hmg, _, _, _⟩
          · rw [hmn] at hb; cases hb
          · exact Or.inr (Or.inr (Or.inl (ptr_of hmg hb)))
        · exact Or.inr (Or.inr (Or.inr ⟨hsz, Or.inl (ptr_of hin hb)⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨hsz, Or.inr ⟨Or.inl hm, Or.inl (ptr_of hout hb)⟩⟩))
        · rcases hw with hn | ⟨w, hw'⟩
          · rw [hn] at hb; cases hb
          · exact Or.inr (Or.inr (Or.inr ⟨hsz, Or.inr ⟨Or.inl hm, Or.inr
              ⟨s.strm, hget, Or.inl ⟨k, st, hzst, hk, Or.inr (ptr_of hw' hb)⟩⟩⟩⟩)))
      (by
        intro b hb
        rw [hb]
        exact Or.inr (Or.inr (Or.inr ⟨hsz, Or.inr ⟨Or.inl hm, Or.inr
          ⟨s.strm, hget, Or.inl ⟨k, st, hzst, hk, Or.inl rfl⟩⟩⟩⟩)))
      (Or.inl rfl)
      (by
        intro b hb
        rcases hb with hb | hb | hb | ⟨_, hb | ⟨_, hb | hb⟩⟩
        · exact Or.inl hb
        · right; left
          rw [hpath] at hb
          have e : pb = b := by cases hb; rfl
          subst e
          exact ⟨Or.inl (by rw [hpath]; rfl), pa, hpa⟩
        · right; left
          rcases hmsg with hmn | ⟨mb, ma, hmg, hma, _, _⟩
          · rw [hmn] at hb; cases hb
          · rw [hmg] at hb
            have e : mb = b := by cases hb; rfl
            subst e
            exact ⟨Or.inr (Or.inl (by rw [hmg]; rfl)), ma, hma⟩
        · right; left
          rw [hin] at hb
          have e : ib = b := by cases hb; rfl
          subst e
          exact ⟨Or.inr (Or.inr (Or.inl (by rw [hin]; rfl))), ia, hia⟩
        · right; left
          rw [hout] at hb
          have e : ob = b := by cases hb; rfl
          subst e
          exact ⟨Or.inr (Or.inr (Or.inr (Or.inl (by rw [hout]; rfl)))), oa, hoa⟩
        · rcases hb with ⟨z, hz, ⟨k0, s0, hk0, hs0, ho⟩ | ⟨k0, d0, hk0, -, -⟩⟩
          · rw [hget] at hz
            cases hz
            rw [hzst] at hk0
            cases hk0
            rw [hk] at hs0
            cases hs0
            rcases ho with ho | ho
            · exact Or.inr (Or.inr ⟨ho, st, by rw [ho]; exact hk⟩)
            · rcases hwin with hn | ⟨w, a, hw', ha, _⟩
              · rw [hn] at ho; cases ho
              · rw [hw'] at ho
                have e : w = b := by cases ho; rfl
                subst e
                exact Or.inr (Or.inl ⟨Or.inr (Or.inr (Or.inr (Or.inr (by rw [hw']; rfl)))), a, ha⟩)
          · rw [hget] at hz
            cases hz
            rw [hzst] at hk0
            cases hk0)
    exact ⟨rel.1, rel.2, w1, w2, w3⟩

end Close

/-- **`gzclose_r`, the close step of the skeleton** (`gzclose_r_step`, `GzCloseSafe` of `gz.skeleton-model.lean`
written out): on any handle in `GzInv`, for every OS world, the call returns, and either refuses a writer with no
effect, or releases a reader (`Close.Released`). -/
theorem gzclose_r_step_safe (i : Nat) :
    ∀ h fs s, GzInv h i s → FileSystem fs →
      ∃ value fs' after, (Call.gzclose_r (some (.in_gzstate_x i))).execute fs h = .ok ((value, fs'), after) ∧
        ((s.mode ≠ GZ_READ ∧ after = h ∧ fs' = fs) ∨ (¬ s.mode ≠ GZ_READ ∧ Close.Released h after fs fs' i s)) := by
  intro h fs s inv hfs
  by_cases hm : s.mode = GZ_READ
  · obtain ⟨rc, fs', after, run, -, rel⟩ := Close.gzclose_r_safe inv hm fs hfs
    exact ⟨rc, fs', after, run, Or.inr ⟨fun hn => hn hm, rel⟩⟩
  · exact ⟨Z_STREAM_ERROR, fs, h,
      Zlib.Gzread.Proofs.gzclose_r_wrong_mode (GzInv.common inv).record hm fs, Or.inl ⟨hm, rfl, rfl⟩⟩

#print axioms Close.gzclose_r_safe
#print axioms gzclose_r_step_safe

end ZlibF.Spec.Public.GzRead
