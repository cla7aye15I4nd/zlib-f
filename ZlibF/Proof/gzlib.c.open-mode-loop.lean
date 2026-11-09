import ZlibF.Proof.«gzlib.c.open-mode-step»

/-!
# gzlib.c: arbitrary mode-loop prefixes

An arbitrary caller prefix runs through the actual loop. The continuation is
kept as the same remaining loop, so early '+' and final NUL use the same run.
-/

namespace Zlib.Gzlib.Proofs
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib.Spec ZlibF.Spec.Public.OffsetProof
open ZlibF.Math.GzModeParser

structure ModeAccum where
  state : GzState
  flags : Int32
  exclusive : Int32

/-- Exact pure accumulator of the actual nonfreeing source actions. -/
def modeAccumStep (q : ModeAccum) (b : UInt8) : ModeAccum :=
  { state := modeActionState q.state (sourceAction b)
    flags := modeActionFlags q.flags (sourceAction b)
    exclusive := modeActionExclusive q.exclusive (sourceAction b) }

def modeFold (bs : List UInt8) (q : ModeAccum) : ModeAccum := bs.foldl modeAccumStep q

/-- Every normal actual prefix preserves its connection to the original API
fold, including arbitrary level/strategy updates and last-setting wins. -/
theorem modeFold_rep (bs : List UInt8) (q : ModeAccum) (acc : Acc)
    (hr : ModeRep q.state acc) (hn : (43 : UInt8) ∉ bs) :
    ModeRep (modeFold bs q).state
      (bs.foldl (fun acc b => semanticStep acc (semanticAction (sourceAction b))) acc) := by
  induction bs generalizing q acc with
  | nil => exact hr
  | cons b bs ih =>
    have hhead : sourceAction b ≠ .bad := by
      intro he
      have hb := (sourceAction_bad b).mp he
      exact hn (by simp [hb])
    exact ih (modeAccumStep q b) _ (modeRep_action q.state acc b hr hhead)
      (fun he => hn (by simp [he]))

/-- An arbitrary normal caller prefix executes on the actual heap, then
continues with the same source loop, remaining fuel and updated pointer.
No input byte, callee contract or intermediate invariant is guessed. -/
theorem modeWhile_prefix (h : Heap) (fs : Fs) (i : Nat) (r : BRef) (off : Nat)
    (a : Array UInt8) (q : ModeAccum) (pre : List UInt8) (k : Nat)
    (hs : h.gzstates i = some q.state) (ha : Space.get h r = some a)
    (hbound : off + pre.length ≤ a.size)
    (hchars : ∀ j, j < pre.length → a[off + j]? = pre[j]?)
    (hzero : (0 : UInt8) ∉ pre) (hplus : (43 : UInt8) ∉ pre) (hk : pre.length ≤ k) :
    gwhile.go modeCondition (modeBody (some (.tab i))) k
      { mode := .ref r off, oflag := q.flags, exclusive := q.exclusive, done := false } fs h =
    gwhile.go modeCondition (modeBody (some (.tab i))) (k - pre.length)
      { mode := .ref r (off + pre.length), oflag := (modeFold pre q).flags, exclusive := (modeFold pre q).exclusive, done := false }
      fs (setS h i (modeFold pre q).state) := by
  induction pre generalizing h off q k with
  | nil =>
    simp [modeFold, setS, upd_self _ _ _ hs]
  | cons b pre ih =>
    cases k with
    | zero => simp at hk
    | succ k =>
      have hoff : off < a.size := by simp at hbound; omega
      have hnext : off + 1 ≤ a.size := by omega
      have hbyte : a[off] = b := by
        have hc := hchars 0 (by simp)
        simpa [Array.getElem?_eq_getElem hoff] using hc
      have hnonzero : b ≠ 0 := by
        intro he
        exact hzero (by simp [he])
      have hnormal : sourceAction b ≠ .bad := by
        intro he
        exact hplus (by simp [(sourceAction_bad b).mp he])
      have hload : load8 (.ref r off) h = .ok (b, h) := by
        simp [load8, Ptr.load, ha, hoff, hbyte]
      have hbody := modeBody_normal h fs i q.state r off a b q.flags q.exclusive
        hs ha hoff hnext hbyte hnormal
      have hnextstate : (setS h i (modeAccumStep q b).state).gzstates i =
          some (modeAccumStep q b).state := by simp [setS]
      have hnextview : Space.get (setS h i (modeAccumStep q b).state) r = some a := by
        rw [modeBytes_setS]
        exact ha
      have htailchars : ∀ j, j < pre.length → a[(off + 1) + j]? = pre[j]? := by
        intro j hj
        have hc := hchars (j + 1) (by simp; omega)
        simpa only [List.getElem?_cons_succ,
          show off + (j + 1) = (off + 1) + j by omega] using hc
      have htail := ih (setS h i (modeAccumStep q b).state) (off + 1) (modeAccumStep q b) k
        hnextstate hnextview (by simp at hbound; omega) htailchars
        (fun he => hzero (by simp [he])) (fun he => hplus (by simp [he])) (by simp at hk; omega)
      rw [gwhile.go]
      simp only [G_bind_app, modeCondition_byte h fs
        { mode := .ref r off, oflag := q.flags, exclusive := q.exclusive, done := false } b hload]
      simp only [Bool.not_false, Bool.and_true, show (b != 0) = true by simpa using hnonzero, ite_true]
      simp only [G_bind_app, hbody]
      change gwhile.go modeCondition (modeBody (some (.tab i))) k
        { mode := .ref r (off + 1), oflag := (modeAccumStep q b).flags, exclusive := (modeAccumStep q b).exclusive, done := false }
        fs (setS h i (modeAccumStep q b).state) = _
      rw [htail]
      simp [modeFold, List.foldl_cons, setS, upd_upd, Nat.add_left_comm, Nat.add_comm]

/-- A complete normal string runs its actual prefix and then reads its real
NUL, terminating on the exact accumulated record and locals. -/
theorem modeWhile_normal (h : Heap) (fs : Fs) (i : Nat) (r : BRef) (off : Nat)
    (a : Array UInt8) (q : ModeAccum) (bs : List UInt8) (k : Nat)
    (hs : h.gzstates i = some q.state) (ha : Space.get h r = some a)
    (hbound : off + bs.length < a.size)
    (hchars : ∀ j, j ≤ bs.length → a[off + j]? = (bs ++ [0])[j]?)
    (hzero : (0 : UInt8) ∉ bs) (hplus : (43 : UInt8) ∉ bs) (hk : bs.length < k) :
    gwhile.go modeCondition (modeBody (some (.tab i))) k
      { mode := .ref r off, oflag := q.flags, exclusive := q.exclusive, done := false } fs h =
      .ok (({ mode := .ref r (off + bs.length), oflag := (modeFold bs q).flags, exclusive := (modeFold bs q).exclusive, done := false }, fs),
        setS h i (modeFold bs q).state) := by
  have hpre := modeWhile_prefix h fs i r off a q bs k hs ha (by omega)
    (fun j hj => by simpa only [List.getElem?_append_left hj] using hchars j (by omega)) hzero hplus (by omega)
  have hz : a[off + bs.length] = 0 := by
    have hc := hchars bs.length (Nat.le_refl _)
    simpa [Array.getElem?_eq_getElem hbound] using hc
  have hload : load8 (.ref r (off + bs.length)) (setS h i (modeFold bs q).state) =
      .ok (0, setS h i (modeFold bs q).state) := by
    simp [load8, Ptr.load, modeBytes_setS, ha, hbound, hz]
  have hremain : k - bs.length = (k - bs.length - 1) + 1 := by omega
  rw [hpre, hremain, gwhile.go]
  simp only [G_bind_app, modeCondition_byte _ fs
    { mode := .ref r (off + bs.length), oflag := (modeFold bs q).flags, exclusive := (modeFold bs q).exclusive, done := false } 0 hload]
  simp [G_pure_app]

/-- Every actual public CString without '+' has a complete mode-loop execution
on arbitrary original byte storage, with the exact full source accumulator. -/
theorem openModeLoop_normal_public (h : Heap) (fs : Fs) (i : Nat) (s : GzState)
    (mode : BPtr) (bs : List UInt8) (hs : h.gzstates i = some s)
    (hc : ZlibF.Spec.Public.CString h mode bs) (hp : (43 : UInt8) ∉ bs) :
    ∃ ml, ml.done = false ∧ ml.oflag = (modeFold bs { state := s, flags := 0, exclusive := 0 }).flags ∧
      ml.exclusive = (modeFold bs { state := s, flags := 0, exclusive := 0 }).exclusive ∧
      openModeLoop (some (.tab i)) mode fs h =
        .ok ((ml, fs), setS h i (modeFold bs { state := s, flags := 0, exclusive := 0 }).state) := by
  obtain ⟨r, off, a, rfl, ha, hbound, hchars⟩ := writerCString_view h mode bs hc
  let q : ModeAccum := { state := s, flags := 0, exclusive := 0 }
  refine ⟨{ mode := .ref r (off + bs.length), oflag := (modeFold bs q).flags, exclusive := (modeFold bs q).exclusive, done := false }, rfl, rfl, rfl, ?_⟩
  rw [openModeLoop_step_cut]
  unfold gwhile
  exact modeWhile_normal h fs i r off a q bs fuel hs ha hbound hchars hc.2.1 hp hc.2.2

/-- A '+' at any position follows the real preceding prefix, frees the same
handle, and terminates; no arbitrary suffix is executed after the error. -/
theorem openModeLoop_plus_public (h : Heap) (fs : Fs) (i : Nat) (s : GzState)
    (mode : BPtr) (bs : List UInt8) (hs : h.gzstates i = some s)
    (hc : ZlibF.Spec.Public.CString h mode bs) (hp : (43 : UInt8) ∈ bs) :
    ∃ ml, ml.done = true ∧ openModeLoop (some (.tab i)) mode fs h =
      .ok ((ml, fs), { h with gzstates := upd h.gzstates i none }) := by
  have hsplit : ∃ pre post, bs = pre ++ 43 :: post ∧ (43 : UInt8) ∉ pre := by
    clear hc
    induction bs with
    | nil => simp at hp
    | cons b bs ih =>
      by_cases he : b = 43
      · subst b
        exact ⟨[], bs, rfl, by simp⟩
      · have hrest : (43 : UInt8) ∈ bs := by simpa [List.mem_cons, Ne.symm he] using hp
        obtain ⟨pre, post, hpre, hno⟩ := ih hrest
        exact ⟨b :: pre, post, by simp [hpre], by simp [Ne.symm he, hno]⟩
  obtain ⟨pre, post, hbs, hno⟩ := hsplit
  obtain ⟨r, off, a, rfl, ha, hbound, hchars⟩ := writerCString_view h mode bs hc
  let q : ModeAccum := { state := s, flags := 0, exclusive := 0 }
  have hlen : bs.length = pre.length + 1 + post.length := by simp [hbs]; omega
  have hpreBound : off + pre.length ≤ a.size := by omega
  have hpreChars : ∀ j, j < pre.length → a[off + j]? = pre[j]? := by
    intro j hj
    have he := hchars j (by omega)
    simpa [hbs, List.getElem?_append_left hj] using he
  have hpreZero : (0 : UInt8) ∉ pre := by
    intro he
    exact hc.2.1 (by simp [hbs, he])
  have hpreRun := modeWhile_prefix h fs i r off a q pre fuel hs ha hpreBound hpreChars
    hpreZero hno (by have hz := hc.2.2; change bs.length < fuel at hz; omega)
  have hplusBound : off + pre.length < a.size := by omega
  have hbyte : a[off + pre.length] = 43 := by
    have he := hchars pre.length (by omega)
    simpa [hbs, Array.getElem?_eq_getElem hplusBound, List.getElem?_append] using he
  have hstate : (setS h i (modeFold pre q).state).gzstates i = some (modeFold pre q).state := by simp [setS]
  have hview : Space.get (setS h i (modeFold pre q).state) r = some a := by rw [modeBytes_setS]; exact ha
  have hremain : fuel - pre.length = (fuel - pre.length - 2) + 2 := by
    have hz := hc.2.2
    change bs.length < fuel at hz
    omega
  have hbad := modeWhile_bad (setS h i (modeFold pre q).state) fs i (modeFold pre q).state
    r (off + pre.length) a (modeFold pre q).flags (modeFold pre q).exclusive
    (fuel - pre.length - 2) hstate hview hplusBound hbyte
  refine ⟨{ mode := .ref r (off + pre.length), oflag := (modeFold pre q).flags, exclusive := (modeFold pre q).exclusive, done := true }, rfl, ?_⟩
  rw [openModeLoop_step_cut]
  unfold gwhile
  rw [hpreRun, hremain, hbad]
  simp [setS, upd_upd]

/-- The real initial handle writes preserve any public caller mode CString. -/
theorem openFront_cstring (h : Heap) (mode : BPtr) (bs : List UInt8)
    (hc : ZlibF.Spec.Public.CString h mode bs) :
    ZlibF.Spec.Public.CString (openFrontHeap h) mode bs := by
  rcases hc with ⟨hb, hn, hl⟩
  refine ⟨?_, hn, hl⟩
  rcases hb with hn | ⟨r, off, a, hp, hg, hbound, he⟩
  · exact Or.inl hn
  · exact Or.inr ⟨r, off, a, hp, by rw [modeBytes_openFrontHeap]; exact hg, hbound, he⟩

/-- Exact initialized record after the complete actual normal-mode loop. -/
def modePreparedRecord (h : Heap) (bs : List UInt8) : GzState :=
  (modeFold bs { state := openFrontRecord h, flags := 0, exclusive := 0 }).state

def modePreparedHeap (h : Heap) (bs : List UInt8) : Heap :=
  setS (openFrontHeap h) h.nextBlk (modePreparedRecord h bs)

/-- Actual first allocation, initialization and any normal caller mode string
reach the real source continuation with the full public parser relation. -/
theorem gz_open_mode_normal_front (h : Heap) (fs : Fs) (path mode : BPtr) (fd : Int32)
    (bs : List UInt8) (hf : Fresh h) (hp : path ≠ .null)
    (hc : ZlibF.Spec.Public.CString h mode bs) (hn : (43 : UInt8) ∉ bs)
    (ha : h.allocOk h.nalloc = true) :
    ∃ ml, ml.done = false ∧
      ModeRep (modePreparedRecord h bs)
        (bs.foldl (fun acc b => semanticStep acc (semanticAction (sourceAction b))) initial) ∧
      gz_open path fd mode fs h = openAfterMode (some (.tab h.nextBlk)) path fd ml fs (modePreparedHeap h bs) := by
  have hs : (openFrontHeap h).gzstates h.nextBlk = some (openFrontRecord h) := by simp [openFrontHeap]
  obtain ⟨ml, hdone, _, _, hloop⟩ := openModeLoop_normal_public (openFrontHeap h) fs h.nextBlk
    (openFrontRecord h) mode bs hs (openFront_cstring h mode bs hc) hn
  refine ⟨ml, hdone, modeFold_rep bs _ initial (modeRep_initial h) hn, ?_⟩
  obtain ⟨r, off, a, hm, _, _, _⟩ := writerCString_view h mode bs hc
  have hmn : mode ≠ .null := by simp [hm]
  rw [gz_open_mode_cut]
  offsetsimp [hp, hmn, allocGzState, ha, Fresh.slotUsed_next hf, setS, upd_upd]
  dsimp only [openFrontHeap, openFrontRecord] at hloop
  rw [hloop]
  rfl

/-- An error mode containing '+' goes through the same real first allocation
and initial writes, then frees its actual handle before any path allocation. -/
theorem gz_open_mode_plus (h : Heap) (fs : Fs) (path mode : BPtr) (fd : Int32)
    (bs : List UInt8) (hf : Fresh h) (hp : path ≠ .null)
    (hc : ZlibF.Spec.Public.CString h mode bs) (hn : (43 : UInt8) ∈ bs)
    (ha : h.allocOk h.nalloc = true) :
    gz_open path fd mode fs h = .ok ((none, fs), openReleased h) := by
  have hs : (openFrontHeap h).gzstates h.nextBlk = some (openFrontRecord h) := by simp [openFrontHeap]
  obtain ⟨ml, hdone, hloop⟩ := openModeLoop_plus_public (openFrontHeap h) fs h.nextBlk
    (openFrontRecord h) mode bs hs (openFront_cstring h mode bs hc) hn
  obtain ⟨r, off, a, hm, _, _, _⟩ := writerCString_view h mode bs hc
  have hmn : mode ≠ .null := by simp [hm]
  rw [gz_open_mode_cut]
  offsetsimp [hp, hmn, allocGzState, ha, Fresh.slotUsed_next hf, setS, upd_upd]
  dsimp only [openFrontHeap, openFrontRecord] at hloop
  rw [hloop]
  unfold openAfterMode
  offsetsimp [hdone]
  simp [openReleased, upd_upd]

/-- Source mode actions leave initialization's buffer and message fields alone. -/
theorem modeActionState_fields (s : GzState) (action : Action) :
    (modeActionState s action).size = s.size ∧
    (modeActionState s action).want = s.want ∧
    (modeActionState s action).msg = s.msg := by
  cases action with
  | mode m => cases m <;> exact ⟨rfl, rfl, rfl⟩
  | level _ | strategy _ | bad | binary | cloexec | exclusive | gzipOnly | nonblock | transparent | ignore =>
    exact ⟨rfl, rfl, rfl⟩

/-- Arbitrary mode prefixes retain the fields actually initialized before the loop. -/
theorem modeFold_fields (bs : List UInt8) (q : ModeAccum) :
    (modeFold bs q).state.size = q.state.size ∧
    (modeFold bs q).state.want = q.state.want ∧
    (modeFold bs q).state.msg = q.state.msg := by
  induction bs generalizing q with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons b bs ih =>
    have htail := ih (modeAccumStep q b)
    have hstep := modeActionState_fields q.state (sourceAction b)
    exact ⟨htail.1.trans hstep.1, htail.2.1.trans hstep.2.1, htail.2.2.trans hstep.2.2⟩

/-- Prepared normal modes retain actual size/want/message initialization. -/
theorem modePrepared_fields (h : Heap) (bs : List UInt8) :
    (modePreparedRecord h bs).size = 0 ∧ (modePreparedRecord h bs).want = 8192 ∧
      (modePreparedRecord h bs).msg = .null := by
  have he := modeFold_fields bs { state := openFrontRecord h, flags := 0, exclusive := 0 }
  exact ⟨he.1, he.2.1.trans (by rfl), he.2.2⟩

/-- The real first allocation and all normal mode updates have the same live
object kinds as ordinary writer initialization, so no new invariant is assumed. -/
theorem modePrepared_invariants (h : Heap) (bs : List UInt8) (hf : Fresh h) (hu : Uniq h) :
    Fresh (modePreparedHeap h bs) ∧ Uniq (modePreparedHeap h bs) := by
  have hs : Shape (writerEntryHeap h false) (modePreparedHeap h bs) := by
    intro b
    by_cases hb : b = h.nextBlk <;>
      simp [writerEntryHeap, modePreparedHeap, setS, hb]
  exact ⟨Shape.fresh hs rfl (writerEntry_fresh h false hf),
    Shape.uniq hs (writerEntry_uniq h false hf hu)⟩

/-- Mode parsing preserves every original caller string on the actual prepared heap. -/
theorem modePrepared_cstring (h : Heap) (bs : List UInt8) (path : BPtr) (name : List UInt8)
    (hc : ZlibF.Spec.Public.CString h path name) :
    ZlibF.Spec.Public.CString (modePreparedHeap h bs) path name :=
  openCString_setS _ h.nextBlk (modePreparedRecord h bs) path name (openFront_cstring h path name hc)

/-- Exact frame and allocation ledger for the actual allocation/mode prefix. -/
theorem modePrepared_ledger (h : Heap) (bs : List UInt8) (hf : Fresh h) :
    ZlibF.Spec.Public.Frame h (modePreparedHeap h bs) (fun _ => False) ∧
    ZlibF.Spec.Public.LiveChange h (modePreparedHeap h bs) (fun b => b = h.nextBlk) (fun _ => False) :=
  openFrontHeap_ledger h (modePreparedRecord h bs) (Fresh.slotUsed_next hf)

/-- The full mode loop consumes no further allocation-oracle call. -/
theorem modePrepared_counts (h : Heap) (bs : List UInt8) :
    (modePreparedHeap h bs).nextBlk = h.nextBlk + 1 ∧
    (modePreparedHeap h bs).nalloc = h.nalloc + 1 ∧
    (modePreparedHeap h bs).allocOk = h.allocOk := ⟨rfl, rfl, rfl⟩

#print axioms modePrepared_fields
#print axioms modePrepared_invariants
#print axioms modePrepared_cstring
#print axioms modePrepared_ledger
#print axioms gz_open_mode_normal_front
#print axioms gz_open_mode_plus
#print axioms modeWhile_normal
#print axioms openModeLoop_normal_public
#print axioms openModeLoop_plus_public
#print axioms modeFold_rep
#print axioms modeWhile_prefix
end Zlib.Gzlib.Proofs
