import ZlibF.Proof.«deflate.c.quiet-strat-def»

/-!
# deflate.c: a strategy run with no input lowers the work term (`StratQuiet`)

`strat_quiet` proves `StratQuiet` for every strategy that `deflate` dispatches to, from the
invariant, the strategy entry and an empty input. The strategy loops of batch B are run again with
a stronger loop state: besides batch B's loop head, the work term of the potential has not risen
since the call, and if it is unchanged, no output byte was written and nothing is pending
(`QDown`). Every iteration that consumes lookahead lowers the work term; `fill_window` with no
input keeps it. At level 0 (`deflate_stored`) the work term is the window data not yet in a
block: each stored block lowers it by its length, and an empty block is only the last one. A loop
that stops short of the last block under `Z_FINISH` leaves less output room than the final block
needs (`FinRoom`), so `finish_started` leaves the output full.
-/

namespace Zlib.Deflate.Universal
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Engine.Proofs
open Zlib.Deflate.Proofs
open ZlibF.Math.DeflateSymbols
open Zlib.Trees.Proofs.Out (TreesInvAt)
set_option autoImplicit false

/-! ## The work term between two states -/

/-- From the state `z`, `d` to `z'`, `d'`: no input was added, the work term did not rise, an
unchanged work term means no output and nothing pending, and `gzindex` is kept. -/
structure QDown (z : ZStream) (d : DeflateState) (z' : ZStream) (d' : DeflateState) : Prop where
  avail : z'.avail_in.toNat ≤ z.avail_in.toNat
  le : Quiet.work d' ≤ Quiet.work d
  eq : Quiet.work d' = Quiet.work d → z'.avail_out = z.avail_out ∧ d'.pending = 0
  gz : d'.gzindex = d.gzindex

theorem QDown.refl {z : ZStream} {d : DeflateState} (pending : d.pending = 0) : QDown z d z d :=
  ⟨Nat.le_refl _, Nat.le_refl _, fun _ => ⟨rfl, pending⟩, rfl⟩

theorem QDown.trans {z1 z2 z3 : ZStream} {d1 d2 d3 : DeflateState} (one : QDown z1 d1 z2 d2)
    (two : QDown z2 d2 z3 d3) : QDown z1 d1 z3 d3 := by
  refine ⟨Nat.le_trans two.avail one.avail, Nat.le_trans two.le one.le, fun e => ?_, two.gz.trans one.gz⟩
  have e1 : Quiet.work d2 = Quiet.work d1 := by have := two.le; have := one.le; omega
  have e2 : Quiet.work d3 = Quiet.work d2 := by have := two.le; omega
  exact ⟨(two.eq e2).1.trans (one.eq e1).1, (two.eq e2).2⟩

theorem fr_avail {h0 h : Heap} {r : ZStreamRef} {ds : Nat} {d0 d : DeflateState} {z0 z : ZStream}
    (fr : Fr h0 r ds d0 z0 h z d) : z.avail_in.toNat ≤ z0.avail_in.toNat := by
  obtain ⟨u, p, acc, _⟩ := fr.acc
  have := acc.2.2.1
  omega

theorem QDown.of_lt {h h' : Heap} {r : ZStreamRef} {ds : Nat} {z z' : ZStream} {d d' : DeflateState}
    (fr : Fr h r ds d z h' z' d') (lt : Quiet.work d' < Quiet.work d) (gz : d'.gzindex = d.gzindex) :
    QDown z d z' d' :=
  ⟨fr_avail fr, Nat.le_of_lt lt, fun e => absurd e (Nat.ne_of_lt lt), gz⟩

theorem work_nz {d : DeflateState} (lv : d.level ≠ 0) :
    Quiet.work d = 3 * d.lookahead.toNat + (if d.match_available = 0 then 0 else 2) +
      (if d.sym_next = 0 then 0 else 1) := by
  unfold Quiet.work
  simp [lv]

theorem sym_ind_le (d : DeflateState) : (if d.sym_next = 0 then 0 else 1) ≤ 1 := by
  split <;> omega

theorem ma_ind_le (d : DeflateState) : (if d.match_available = 0 then 0 else 2) ≤ 2 := by
  split <;> omega

/-- A step without a lazy literal that consumes lookahead lowers the work term. -/
theorem work_lt_noLazy {d d' : DeflateState} (lv : d.level ≠ 0) (lv' : d'.level ≠ 0)
    (ma' : d'.match_available = 0) (la : d'.lookahead.toNat < d.lookahead.toNat) :
    Quiet.work d' < Quiet.work d := by
  rw [work_nz lv, work_nz lv']
  have := sym_ind_le d'
  simp only [ma', if_pos]
  omega

/-- `fill_window` with no input keeps the work term, the counts and `gzindex`. -/
theorem fill_down {roll : Prop} {h after : Heap} {r : ZStreamRef} {ds : Nat} {z z' : ZStream}
    {d d' : DeflateState} (post : FillPost roll h after r ds z z' d d') (empty : z.avail_in = 0)
    (pending : d.pending = 0) (lv : d.level ≠ 0) :
    QDown z d z' d' ∧ Quiet.work d' = Quiet.work d ∧ z'.avail_in = 0 ∧ d'.lookahead = d.lookahead ∧
      d'.pending = 0 := by
  obtain ⟨used, account, _⟩ := post.account
  obtain ⟨sLevel, _, _, _, _, sAvail, _, sSym, _, _, _, _, _, _, _, sPending, _⟩ := post.same
  have consumed := post.consumed
  have i0 : z.avail_in.toNat = 0 := by rw [empty]; rfl
  have a1 := account.2.2.1
  have o1 := account.2.2.2.1
  have in0 : z'.avail_in.toNat = 0 := by omega
  have la : d'.lookahead = d.lookahead := UInt32.toNat_inj.mp (by omega)
  have lv' : d'.level ≠ 0 := by rw [sLevel]; exact lv
  have w : Quiet.work d' = Quiet.work d := by
    rw [work_nz lv, work_nz lv', la, sAvail, sSym]
  have gz : d'.gzindex = d.gzindex := by
    obtain ⟨base, choice, eq⟩ := post.fields
    rcases choice with same | ⟨_, same⟩ <;> subst same <;> exact (congrArg DeflateState.gzindex eq).trans rfl
  have out : z'.avail_out = z.avail_out := UInt32.toNat_inj.mp (by omega)
  refine ⟨⟨by omega, by omega, fun _ => ⟨out, sPending.trans pending⟩, gz⟩, w,
    UInt32.toNat_inj.mp (by rw [in0]; rfl), la, sPending.trans pending⟩

/-! ## `gzindex` across a block flush -/

set_option maxHeartbeats 1600000 in
/-- `FLUSH_BLOCK` keeps `gzindex`: `_tr_flush_block` and `flush_pending` change only the block and
pending fields (`FlushFrame`), and the rest of the macro only reads. -/
theorem flush_block_gz {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream}
    {d : DeflateState} {buf : Array UInt8} {xs : List Symbol}
    (ready : BlockReady h r ds z d pb buf xs) (safe : FlushSafeAt d.lit_bufsize.toNat) (last : Bool)
    {opt : Option block_state} {after : Heap} {res : DeflateState}
    (run : FLUSH_BLOCK (some (.tab ds)) (if last then 1 else 0) h = .ok (opt, after))
    (hs : after.dstates ds = some res) : res.gzindex = d.gzindex := by
  have good := ready.good
  obtain ⟨ob, pointer⟩ := output_reference good.live.hz ready.buffers ready.out
  obtain ⟨w, wa, win, get, _⟩ := window_block good
  have levelPos : 0 < d.level.toInt := by
    have lo := good.inv.level_lo
    have ne : d.level.toInt ≠ 0 := by
      intro zero; exact ready.level (Int32.toInt_inj.mp (by rw [zero]; rfl))
    omega
  have shape := ready.shape
  have range : d.strstart.toNat ≤ d.window_size.toNat := by
    have := shape.room
    change d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat at this
    omega
  obtain ⟨_, after1, z1, result, run1, goodA, _, _, _, _, _, _, _, _, _, frame, _⟩ :=
    safe rfl good ready.trees ready.buffers levelPos pointer (shape.cursor ready.pending) ready.pending
      shape.biValid ready.ledger ready.clear win get ready.blockLow ready.blockHigh range last
  have gz : result.gzindex = d.gzindex := (congrArg DeflateState.gzindex frame).trans rfl
  have back : result.strm = some r :=
    ((congrArg DeflateState.strm frame).trans rfl).trans good.live.back
  have keep : after = after1 := by
    unfold FLUSH_BLOCK at run
    simp only [bind_app, run1, ldDeflateState_tab goodA.live.hs, back, zrd_eq, goodA.live.hz] at run
    revert run
    intro e
    repeat' (first | (simp only [M_ite_app] at e) | (split at e))
    all_goals (simp only [pure_app, Except.ok.injEq, Prod.mk.injEq] at e; exact e.2.symm)
  subst keep
  have : res = result := Option.some.inj (hs.symm.trans goodA.live.hs)
  rw [this]; exact gz

/-! ## The end of a strategy run -/

/-- What `StratQuiet` asks of a strategy run, without `started` (which `StratMeaning` gives). -/
structure QEnd (flush : Int32) (z : ZStream) (d : DeflateState) (z' : ZStream) (d' : DeflateState)
    (b : block_state) : Prop where
  le : Quiet.work d' ≤ Quiet.work d
  eq : Quiet.work d' = Quiet.work d → b = finish_started ∨ b = finish_done ∨
    (z'.avail_out = z.avail_out ∧ d'.pending = 0)
  more : b = need_more → z'.avail_out ≠ 0 → d'.pending = 0 ∧ flush ≠ Z_FINISH
  gz : d'.gzindex = d.gzindex

theorem QEnd.after {flush : Int32} {z0 z z' : ZStream} {d0 d d' : DeflateState} {b : block_state}
    (down : QDown z0 d0 z d) (fin : QEnd flush z d z' d' b) : QEnd flush z0 d0 z' d' b := by
  refine ⟨Nat.le_trans fin.le down.le, fun e => ?_, fin.more, fin.gz.trans down.gz⟩
  have e1 : Quiet.work d = Quiet.work d0 := by have := fin.le; have := down.le; omega
  have e2 : Quiet.work d' = Quiet.work d := by have := fin.le; omega
  rcases fin.eq e2 with s | s | ⟨o, p⟩
  · exact Or.inl s
  · exact Or.inr (Or.inl s)
  · exact Or.inr (Or.inr ⟨o.trans (down.eq e1).1, p⟩)

/-- A `need_more` return from a strategy loop. -/
theorem QEnd.more_of {flush : Int32} {z0 z : ZStream} {d0 d : DeflateState} (down : QDown z0 d0 z d)
    (why : z.avail_out = 0 ∨ (d.pending = 0 ∧ flush = Z_NO_FLUSH)) : QEnd flush z0 d0 z d need_more := by
  refine ⟨down.le, fun e => Or.inr (Or.inr (down.eq e)), fun _ room => ?_, down.gz⟩
  rcases why with full | ⟨p, f⟩
  · exact absurd full room
  · exact ⟨p, by rw [f]; decide⟩

/-! ## Strategy loops with the work term -/

/-- The measure of a strategy loop with no input: one more than the work term. -/
def qMeasure (ds : Nat) (st : LoopS) (h : Heap) : Nat :=
  if st.brk || st.ret.isSome then 0 else
    match h.dstates ds with
    | some d => 1 + Quiet.work d
    | none => 0

theorem qMeasure_bound (ds : Nat) (st : LoopS) (h : Heap) : qMeasure ds st h < fuel := by
  unfold qMeasure fuel
  split
  · decide
  · split
    · rename_i d _
      have := Quiet.work_lt d
      omega
    · decide

theorem qMeasure_head {ds : Nat} {st : LoopS} {h : Heap} {d : DeflateState} (state : h.dstates ds = some d)
    (brk : st.brk = false) (ret : st.ret = none) : qMeasure ds st h = 1 + Quiet.work d := by
  simp [qMeasure, brk, ret, state]

theorem qMeasure_exit {ds : Nat} {st : LoopS} {h : Heap} (exit : st.brk = true ∨ st.ret.isSome = true) :
    qMeasure ds st h = 0 := by
  rcases exit with e | e <;> simp [qMeasure, e]

/-- The states of a strategy loop with no input: a loop head, a `need_more` return, or the `break`
with no lookahead, each with the work term not above the start. -/
def QLoop (K : DeflateState → Prop) (r : ZStreamRef) (ds : Nat) (z0 : ZStream) (d0 : DeflateState)
    (flush : Int32) (st : LoopS) (h : Heap) : Prop :=
  ∃ z d, Head K h r ds z d ∧ QDown z0 d0 z d ∧
    ((st.brk = false ∧ st.ret = none ∧ d.pending = 0) ∨
     (st.ret = some need_more ∧ (z.avail_out = 0 ∨ (d.pending = 0 ∧ flush = Z_NO_FLUSH))) ∨
     (st.brk = true ∧ st.ret = none ∧ d.pending = 0 ∧ d.lookahead = 0))

/-- The outcome of one iteration from the head `z`, `d`: a continuing iteration lowers the work term. -/
def QStep (K : DeflateState → Prop) (r : ZStreamRef) (ds : Nat) (flush : Int32) (z : ZStream)
    (d : DeflateState) (st st' : LoopS) (h' : Heap) : Prop :=
  ∃ z' d', Head K h' r ds z' d' ∧ QDown z d z' d' ∧
    ((st'.brk = false ∧ st'.ret = none ∧ d'.pending = 0 ∧ Quiet.work d' < Quiet.work d) ∨
     (st'.ret = some need_more ∧ (z'.avail_out = 0 ∨ (d'.pending = 0 ∧ flush = Z_NO_FLUSH))) ∨
     (st'.brk = true ∧ st'.ret = none ∧ d'.pending = 0 ∧ d'.lookahead = 0))

/-- The loop rule: iterations that lower the work term end in an exit state of `QLoop`. -/
theorem q_loop {K : DeflateState → Prop} {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream}
    {d : DeflateState} (body : LoopS → M LoopS) (flush : Int32)
    (head : Head K h r ds z d) (pending : d.pending = 0) (empty : z.avail_in = 0)
    (step : ∀ (st : LoopS) (h1 : Heap) (z1 : ZStream) (d1 : DeflateState), Head K h1 r ds z1 d1 →
      d1.pending = 0 → z1.avail_in = 0 → st.brk = false → st.ret = none →
      ∃ st' h', body st h1 = .ok (st', h') ∧ QStep K r ds flush z1 d1 st st' h') :
    ∃ st h', cwhile forever body {} h = .ok (st, h') ∧ QLoop K r ds z d flush st h' ∧
      (st.brk = true ∨ st.ret.isSome = true) := by
  have start : QLoop K r ds z d flush {} h :=
    ⟨z, d, head, QDown.refl pending, Or.inl ⟨rfl, rfl, pending⟩⟩
  obtain ⟨st, h', run, loop, exit⟩ := cwhile_measure (cond := forever) (body := body)
    (QLoop K r ds z d flush)
    (fun st h' => QLoop K r ds z d flush st h' ∧ (st.brk = true ∨ st.ret.isSome = true)) (qMeasure ds)
    (fun st h1 ⟨z1, d1, head1, down1, cases⟩ => by
      rcases cases with ⟨brk, ret, pend1⟩ | ⟨ret, why⟩ | ⟨brk, ret, pend1, la1⟩
      · refine ⟨true, st, h1, (by simp [forever, brk, ret]), (fun _ => ?_), (fun e => by cases e)⟩
        have empty1 : z1.avail_in = 0 := by
          have := down1.avail
          rw [empty] at this
          exact UInt32.toNat_inj.mp (by change _ ≤ 0 at this; change _ = 0; omega)
        obtain ⟨st', h', run', z', d', head', down', cases'⟩ := step st h1 z1 d1 head1 pend1 empty1 brk ret
        have m0 := qMeasure_head (st := st) head1.inv.good.live.hs brk ret
        refine ⟨st', h', run', ⟨z', d', head', down1.trans down', ?_⟩, ?_⟩
        · rcases cases' with ⟨b, r', p, _⟩ | m | e
          · exact Or.inl ⟨b, r', p⟩
          · exact Or.inr (Or.inl m)
          · exact Or.inr (Or.inr e)
        · rcases cases' with ⟨b, r', _, lt⟩ | ⟨m, _⟩ | ⟨b, _⟩
          · rw [qMeasure_head head'.inv.good.live.hs b r', m0]; omega
          · rw [qMeasure_exit (Or.inr (by rw [m]; rfl)), m0]; omega
          · rw [qMeasure_exit (Or.inl b), m0]; omega
      · refine ⟨false, st, h1, (by simp [forever, ret]), (fun e => by cases e), (fun _ => ?_)⟩
        exact ⟨⟨z1, d1, head1, down1, Or.inr (Or.inl ⟨ret, why⟩)⟩, Or.inr (by rw [ret]; rfl)⟩
      · refine ⟨false, st, h1, (by simp [forever, brk]), (fun e => by cases e), (fun _ => ?_)⟩
        exact ⟨⟨z1, d1, head1, down1, Or.inr (Or.inr ⟨brk, ret, pend1, la1⟩)⟩, Or.inl brk⟩)
    start (qMeasure_bound ds {} h)
  exact ⟨st, h', run, loop, exit⟩

/-- An iteration that consumed lookahead, after a part that kept the work term. -/
theorem qstep_of_iter {K : DeflateState → Prop} {h1 h' : Heap} {r : ZStreamRef} {ds : Nat}
    {z z1 z' : ZStream} {d d1 d' : DeflateState} {flush : Int32} {st st' : LoopS}
    (down1 : QDown z d z1 d1) (fr : Fr h1 r ds d1 z1 h' z' d') (head' : Head K h' r ds z' d')
    (lt : Quiet.work d' < Quiet.work d1) (gz : d'.gzindex = d1.gzindex) (brk' : st'.brk = st.brk)
    (brk : st.brk = false) (ret : st.ret = none)
    (cases : (st'.ret = st.ret ∧ d'.pending = 0) ∨ (st'.ret = some need_more ∧ z'.avail_out = 0)) :
    QStep K r ds flush z d st st' h' := by
  refine ⟨z', d', head', down1.trans (QDown.of_lt fr lt gz), ?_⟩
  rcases cases with ⟨e, p⟩ | ⟨e, o⟩
  · exact Or.inl ⟨brk'.trans brk, e.trans ret, p, Nat.lt_of_lt_of_le lt down1.le⟩
  · exact Or.inr (Or.inl ⟨e, Or.inl o⟩)

set_option maxHeartbeats 1600000 in
/-- The end of the compression functions (`finish_tail`) with the work term. -/
theorem finish_tail_q {kind : DeflateState → Prop} {h : Heap} {r : ZStreamRef}
    {ds : Nat} {z : ZStream} {d : DeflateState} (head : Head kind h r ds z d) (pending : d.pending = 0)
    (flush : Int32) (quiet : d.match_available = 0) (look0 : d.lookahead = 0) :
    ∃ bstate after z' d', finish_tail (some (.tab ds)) flush h = .ok (bstate, after) ∧
      r.get after = some z' ∧ after.dstates ds = some d' ∧ QEnd flush z d z' d' bstate := by
  obtain ⟨pb, buf, xs, ready⟩ := head.inv.ready pending head.level head.buffers head.out quiet
  have w0 : Quiet.work d = (if d.sym_next = 0 then 0 else 1) := by
    rw [work_nz head.level, look0, quiet]; simp
  by_cases finish : flush = Z_FINISH
  · obtain ⟨opt, produced, after, z', result, run, invA, buffersA, account, keeps, _, idle, _, choiceT, bits,
      fullOut, totalOutF, bufferF, totalInF, shapeF, keysF, lastF⟩ := flush_block_macro ready head.safe true
    have run' : FLUSH_BLOCK (some (.tab ds)) 1 h = .ok (opt, after) := run
    have gz := flush_block_gz ready head.safe true run invA.good.live.hs
    have lvA : result.level ≠ 0 := by rw [keeps.level]; exact head.level
    have wA : Quiet.work result = 0 := by
      rw [work_nz lvA, keeps.lookahead, keeps.matchAvailable, keeps.symNext, look0, quiet]; simp
    have le : Quiet.work result ≤ Quiet.work d := by rw [wA]; exact Nat.zero_le _
    rcases choiceT rfl with none' | started
    · subst none'
      refine ⟨finish_done, after, z', result, ?_, invA.good.live.hz, invA.good.live.hs,
        ⟨le, fun _ => Or.inr (Or.inl rfl), fun e => absurd e (by decide), gz⟩⟩
      simp [finish_tail, finish, bind_app, run']
    · subst started
      refine ⟨finish_started, after, z', result, ?_, invA.good.live.hz, invA.good.live.hs,
        ⟨le, fun _ => Or.inl rfl, fun e => absurd e (by decide), gz⟩⟩
      simp [finish_tail, finish, bind_app, run']
  · have finishB : (flush == Z_FINISH) = false := by simpa using finish
    have rdSym : rd (some (.tab ds)) (·.sym_next) h = .ok (d.sym_next, h) := by
      simp [rdD_eq, head.inv.good.live.hs]
    by_cases symbols : d.sym_next = 0
    · refine ⟨block_done, h, z, d, ?_, head.inv.good.live.hz, head.inv.good.live.hs,
        ⟨Nat.le_refl _, fun _ => Or.inr (Or.inr ⟨rfl, pending⟩), fun e => absurd e (by decide), rfl⟩⟩
      simp [finish_tail, finishB, bind_app, rdSym, symbols]
    · have symbolsB : (d.sym_next != 0) = true := by simpa using symbols
      obtain ⟨opt, produced, after, z', result, run, invA, buffersA, account, keeps, _, idleF, choiceF, _, _,
        fullOut, totalOutF, bufferF, totalInF, shapeF, keysF, lastF⟩ := flush_block_macro ready head.safe false
      have run' : FLUSH_BLOCK (some (.tab ds)) 0 h = .ok (opt, after) := run
      have gz := flush_block_gz ready head.safe false run invA.good.live.hs
      have lvA : result.level ≠ 0 := by rw [keeps.level]; exact head.level
      have lt : Quiet.work result < Quiet.work d := by
        rw [work_nz lvA, keeps.lookahead, keeps.matchAvailable, keeps.symNext, look0, quiet, w0]; simp [symbols]
      rcases choiceF rfl with none' | more
      · subst none'
        refine ⟨block_done, after, z', result, ?_, invA.good.live.hz, invA.good.live.hs,
          ⟨Nat.le_of_lt lt, fun e => absurd e (Nat.ne_of_lt lt), fun e => absurd e (by decide), gz⟩⟩
        simp [finish_tail, finishB, bind_app, rdSym, symbolsB, symbols, run']
      · subst more
        refine ⟨need_more, after, z', result, ?_, invA.good.live.hz, invA.good.live.hs,
          ⟨Nat.le_of_lt lt, fun e => absurd e (Nat.ne_of_lt lt),
            fun _ room => absurd (fullOut (Option.some_ne_none _)) room, gz⟩⟩
        simp [finish_tail, finishB, bind_app, rdSym, symbolsB, symbols, run']

/-- `s->insert = 0` keeps the work term. -/
theorem insert_down {z : ZStream} {d : DeflateState} (pending : d.pending = 0) (v : UInt32) :
    QDown z d z { d with insert := v } :=
  ⟨Nat.le_refl _, Nat.le_of_eq rfl, fun _ => ⟨rfl, pending⟩, rfl⟩

/-! ## `deflate_huff` -/

set_option maxHeartbeats 1600000 in
/-- One literal iteration of `deflate_huff` (`huff_literal_iter`), with the lookahead, `gzindex`
and the `need_more` state. -/
theorem huff_literal_iterQ {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream}
    {d : DeflateState} (head : Head HuffKind h r ds z d) (look : 1 ≤ d.lookahead.toNat)
    (pending : d.pending = 0) (st : LoopS) :
    ∃ st' h',
      (do
        wr (some (.tab ds)) (fun d => { d with match_length := 0 })
        let d ← ldDeflateState (some (.tab ds))
        let c ← index8 d.window d.strstart.toNat
        let bflush ← tally_lit (some (.tab ds)) c
        wr (some (.tab ds)) (fun d => { d with lookahead := d.lookahead - 1, strstart := d.strstart + 1 })
        huffTail (some (.tab ds)) st bflush) h = .ok (st', h') ∧ st'.brk = st.brk ∧
      ∃ z' d', Head HuffKind h' r ds z' d' ∧ Fr h r ds d z h' z' d' ∧
        d'.lookahead.toNat + 1 = d.lookahead.toNat ∧ d'.gzindex = d.gzindex ∧
        ((st'.ret = st.ret ∧ d'.pending = 0) ∨ (st'.ret = some need_more ∧ z'.avail_out = 0)) := by
  obtain ⟨wrRun, inv1⟩ := clear_match_inv head.inv (Or.inl head.kind)
  have buffers1 := state_write_buffers (d' := { d with match_length := 0 }) head.inv.good head.buffers
    ⟨rfl, rfl, rfl, rfl⟩ inv1.good
  obtain ⟨b, buf', c, h3, run, h3def, pbuf, good3, laEq, ssEq, buffers3, fullCase, notFullCase⟩ :=
    literal_step_inv inv1 head.level look (Or.inl head.kind) rfl pending buffers1 head.out
      (huffTail (some (.tab ds)) st)
  have priv3 : Fr h r ds d z h3 z (literalStep { d with match_length := 0 } c) := by
    refine Fr.priv head.inv.good head.buffers ?_ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rw [h3def]
    exact (priv_setD h r ds d _ head.inv.good.live.hs).trans
      ((priv_tally inv1.good pbuf buf' _).keys ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)
  have start : (do
        wr (some (.tab ds)) (fun d => { d with match_length := 0 })
        let d ← ldDeflateState (some (.tab ds))
        let c ← index8 d.window d.strstart.toNat
        let bflush ← tally_lit (some (.tab ds)) c
        wr (some (.tab ds)) (fun d => { d with lookahead := d.lookahead - 1, strstart := d.strstart + 1 })
        huffTail (some (.tab ds)) st bflush) h =
      huffTail (some (.tab ds)) st ({ d with match_length := 0 }.sym_next + 3 ==
        { d with match_length := 0 }.sym_end) h3 := by
    rw [bind_app, wrRun]
    exact run
  have la3 : (literalStep { d with match_length := 0 } c).lookahead.toNat + 1 = d.lookahead.toNat := by
    rw [laEq]
    change (d.lookahead.toNat - 1) + 1 = _
    omega
  by_cases flag : ({ d with match_length := 0 }.sym_next + 3 == { d with match_length := 0 }.sym_end) = true
  · obtain ⟨xs', ready⟩ := fullCase flag
    obtain ⟨opt, produced, after, z', result, flushRun, invA, buffersA, account, keeps, outA, idle, choice, _, _, fullOut, totalOutF, bufferF, totalInF, shapeF, keysF, lastF⟩ :=
      flush_block_macro ready head.safe false
    have flushRun' : FLUSH_BLOCK (some (.tab ds)) 0 h3 = .ok (opt, after) := flushRun
    have gzA := flush_block_gz ready head.safe false flushRun invA.good.live.hs
    have inputA : z'.avail_in ≠ 0 → z'.next_in ≠ .null := by
      rw [keeps.availIn, keeps.nextIn]; exact head.input
    have headA : Head HuffKind after r ds z' result :=
      ⟨invA, buffersA, outA, inputA, by rw [keeps.level]; exact head.level,
        by unfold HuffKind; rw [keeps.strategy]; exact head.kind, keysF.safe head.safe⟩
    have frA : Fr h r ds d z after z' result := Fr.trans head.inv.good head.buffers priv3
      (Fr.flush account totalInF totalOutF bufferF shapeF keysF)
    have laA : result.lookahead.toNat + 1 = d.lookahead.toNat := by rw [keeps.lookahead]; exact la3
    rcases choice rfl with none' | more
    · subst none'
      refine ⟨{ st with bflush := true }, after, ?_, rfl, z', result, headA, frA, laA, gzA,
        Or.inl ⟨rfl, (idle rfl).1⟩⟩
      rw [start, flag]
      simp [huffTail, bind_app, flushRun']
    · subst more
      refine ⟨{ st with bflush := true, ret := some need_more }, after, ?_, rfl, z', result, headA, frA, laA, gzA,
        Or.inr ⟨rfl, fullOut (Option.some_ne_none _)⟩⟩
      rw [start, flag]
      simp [huffTail, bind_app, flushRun']
  · have notFull : ({ d with match_length := 0 }.sym_next + 3 == { d with match_length := 0 }.sym_end) = false := by
      simpa using flag
    have inv3 := notFullCase notFull
    refine ⟨{ st with bflush := false }, h3, ?_, rfl, z, literalStep { d with match_length := 0 } c,
      ⟨inv3, buffers3, head.out, head.input, head.level, head.kind, head.safe⟩, priv3, la3, rfl,
      Or.inl ⟨rfl, pending⟩⟩
    rw [start, notFull]
    simp [huffTail]

set_option maxHeartbeats 2400000 in
/-- **One iteration of `deflate_huff`** with no input. -/
theorem huff_body_q {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (head : Head HuffKind h r ds z d) (pending : d.pending = 0) (empty : z.avail_in = 0)
    (flush : Int32) (st : LoopS) (brk : st.brk = false) (ret : st.ret = none) :
    ∃ st' h', deflate_huff_body (some (.tab ds)) flush st h = .ok (st', h') ∧
      QStep HuffKind r ds flush z d st st' h' := by
  have rdLook : rd (some (.tab ds)) (·.lookahead) h = .ok (d.lookahead, h) := by
    simp [rdD_eq, head.inv.good.live.hs]
  rw [huff_body_source]
  by_cases emptyL : d.lookahead = 0
  · have emptyB : (d.lookahead == 0) = true := by simp [emptyL]
    have short : d.lookahead.toNat < 262 := by rw [emptyL]; decide
    obtain ⟨after1, z1, d1, fillRun, inv1, buffers1, post⟩ :=
      fill_window_inv head.inv head.level head.buffers head.input short
    obtain ⟨_, sStrategy, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := post.same
    have head1 : Head HuffKind after1 r ds z1 d1 :=
      head_after_fill head inv1 buffers1 post (fun k => by unfold HuffKind; rw [sStrategy]; exact k)
    obtain ⟨down1, _, _, la1, pending1⟩ := fill_down post empty pending head.level
    have empty1 : d1.lookahead = 0 := la1.trans emptyL
    have rdLook1 : rd (some (.tab ds)) (·.lookahead) after1 = .ok (d1.lookahead, after1) := by
      simp [rdD_eq, inv1.good.live.hs]
    have empty1B : (d1.lookahead == 0) = true := by simp [empty1]
    by_cases noFlush : flush = Z_NO_FLUSH
    · refine ⟨{ st with ret := some need_more }, after1, ?_, z1, d1, head1, down1,
        Or.inr (Or.inl ⟨rfl, Or.inr ⟨pending1, noFlush⟩⟩)⟩
      simp only [bind_app, rdLook, emptyB, ite_true]
      rw [show fill_window (some (.tab ds)) h = .ok ((), after1) from fillRun]
      simp only [bind_app, rdLook1, empty1B, ite_true, noFlush, beq_self_eq_true]
      rfl
    · have noFlushB : (flush == Z_NO_FLUSH) = false := by simpa using noFlush
      refine ⟨{ st with brk := true }, after1, ?_, z1, d1, head1, down1,
        Or.inr (Or.inr ⟨rfl, ret, pending1, empty1⟩)⟩
      simp only [bind_app, rdLook, emptyB, ite_true]
      rw [show fill_window (some (.tab ds)) h = .ok ((), after1) from fillRun]
      simp only [bind_app, rdLook1, empty1B, ite_true, noFlushB, Bool.false_eq_true, ite_false]
      rfl
  · have emptyB : (d.lookahead == 0) = false := by simpa using emptyL
    have look : 1 ≤ d.lookahead.toNat := by
      have : d.lookahead.toNat ≠ 0 := fun e => emptyL (UInt32.toNat_inj.mp e)
      omega
    obtain ⟨st', h', iterRun, brk', z', d', head', fr', la', gz', cases⟩ := huff_literal_iterQ head look pending st
    refine ⟨st', h', ?_, qstep_of_iter (QDown.refl pending) fr' head'
      (work_lt_noLazy head.level head'.level (idle_of_roll head'.inv.shape (Or.inl head'.kind)) (by omega))
      gz' brk' brk ret cases⟩
    simp only [bind_app, rdLook, emptyB, Bool.false_eq_true, ite_false]
    exact iterRun

/-- **`deflate_huff` with no input** lowers the work term. -/
theorem huff_q {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream}
    {d : DeflateState} (safe : FlushSafeAt d.lit_bufsize.toNat) (inv : DInv h r ds z d) (entry : StratIn h r z d)
    (flush : Int32) (level : d.level ≠ 0) (huff : d.strategy.toInt = 2) (empty : z.avail_in = 0) :
    ∃ bstate after z' d', C.run (Zlib.Deflate.deflate_huff (some (.tab ds)) flush) h = .ok (bstate, after) ∧
      r.get after = some z' ∧ after.dstates ds = some d' ∧ QEnd flush z d z' d' bstate := by
  have head : Head HuffKind h r ds z d := ⟨inv, entry.buffers, entry.out, entry.input, level, huff, safe⟩
  obtain ⟨st, h1, loopRun, ⟨z1, d1, head1, down1, cases⟩, exit⟩ :=
    q_loop (deflate_huff_body (some (.tab ds)) flush) flush head entry.pending empty
      (fun st _ _ _ hd p e b r => huff_body_q hd p e flush st b r)
  rcases cases with ⟨brk, ret0, _⟩ | ⟨ret, why⟩ | ⟨brk, ret, pending1, empty1⟩
  · rcases exit with e | e
    · rw [brk] at e; cases e
    · rw [ret0] at e; cases e
  · refine ⟨need_more, h1, z1, d1, ?_, head1.inv.good.live.hz, head1.inv.good.live.hs, QEnd.more_of down1 why⟩
    simp [C.run, deflate_huff, bind_app, loopRun, ret]
  · obtain ⟨wrRun, head2⟩ := clear_insert_head head1 id
    obtain ⟨bstate, after, z', d', tailRun, hz', hs', fin⟩ := finish_tail_q head2 pending1 flush
      (idle_of_roll head1.inv.shape (Or.inl head1.kind) : d1.match_available = 0) empty1
    refine ⟨bstate, after, z', d', ?_, hz', hs', QEnd.after down1 (QEnd.after (insert_down pending1 0) fin)⟩
    simp only [C.run, deflate_huff, bind_app, loopRun, ret, wrRun]
    exact tailRun

/-! ## `deflate_rle` -/

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **One emission of `deflate_rle`** from a loop head with lookahead and room for a run: the run
detection, then a run or a literal with the block flush on a full symbol buffer. -/
theorem rle_emit_iterQ {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream}
    {d : DeflateState} (head : Head RleKind h r ds z d) (look : 1 ≤ d.lookahead.toNat)
    (room : d.strstart.toNat + 258 < d.window_size.toNat) (pending : d.pending = 0) (st : LoopS) :
    ∃ st' h',
      (do
        wr (some (.tab ds)) (fun d => { d with match_length := 0 })
        rleScan (some (.tab ds))
        rleEmit (some (.tab ds)) st) h = .ok (st', h') ∧ st'.brk = st.brk ∧
      ∃ z' d', Head RleKind h' r ds z' d' ∧ Fr h r ds d z h' z' d' ∧
        d'.lookahead.toNat < d.lookahead.toNat ∧ d'.gzindex = d.gzindex ∧
        ((st'.ret = st.ret ∧ d'.pending = 0) ∨ (st'.ret = some need_more ∧ z'.avail_out = 0)) := by
  obtain ⟨wrRun, inv1⟩ := clear_match_inv head.inv (Or.inr head.kind)
  have buffers1 := state_write_buffers (d' := { d with match_length := 0 }) head.inv.good head.buffers
    ⟨rfl, rfl, rfl, rfl⟩ inv1.good
  let d1 : DeflateState := { d with match_length := 0 }
  have kind1 : RleKind d1 := head.kind
  obtain ⟨ml, scanRun, mlCases⟩ := rle_scan_run (d := d1) inv1.good rfl inv1.shape.room room
  have state2 : (setD (setD h ds d1) ds { d1 with match_length := ml }).dstates ds = some { d1 with match_length := ml } := by
    simp
  have heap2 : setD (setD h ds d1) ds { d1 with match_length := ml } = setD h ds { d1 with match_length := ml } := by
    rw [setD_setD]
  -- the tail after the emission, for both flag values
  have tail : ∀ (h3 : Heap) (z3 : ZStream) (d3 : DeflateState) (bflush : Bool)
      (count : d3.lookahead.toNat < d.lookahead.toNat) (gz3 : d3.gzindex = d.gzindex)
      (good3 : DGood h3 r ds z d3) (buffers3 : StreamBuffers h3 r) (z3eq : z3 = z)
      (kind3 : RleKind d3) (safe3 : FlushSafeAt d3.lit_bufsize.toNat) (level3 : d3.level ≠ 0) (pending3 : d3.pending = 0)
      (full : bflush = true → ∃ pb buf xs, BlockReady h3 r ds z d3 pb buf xs)
      (notFull : bflush = false → DInv h3 r ds z d3),
      ∃ st' h', huffTail (some (.tab ds)) st bflush h3 = .ok (st', h') ∧ st'.brk = st.brk ∧
        ∃ z' d', Head RleKind h' r ds z' d' ∧ Fr h3 r ds d3 z h' z' d' ∧
          d'.lookahead.toNat < d.lookahead.toNat ∧ d'.gzindex = d.gzindex ∧
          ((st'.ret = st.ret ∧ d'.pending = 0) ∨ (st'.ret = some need_more ∧ z'.avail_out = 0)) := by
    intro h3 z3 d3 bflush count gz3 good3 buffers3 _ kind3 safe3 level3 pending3 full notFull
    cases bflush with
    | false =>
      refine ⟨{ st with bflush := false }, h3, by simp [huffTail], rfl,
        z, d3, ⟨notFull rfl, buffers3, head.out, head.input, level3, kind3, safe3⟩, Fr.refl good3 buffers3, count, gz3,
        Or.inl ⟨rfl, pending3⟩⟩
    | true =>
      obtain ⟨pb, buf, xs, ready⟩ := full rfl
      obtain ⟨opt, produced, after, z', result, flushRun, invA, buffersA, account, keeps, outA, idle, choice, _, _, fullOut, totalOutF, bufferF, totalInF, shapeF, keysF, lastF⟩ :=
        flush_block_macro ready safe3 false
      have flushRun' : FLUSH_BLOCK (some (.tab ds)) 0 h3 = .ok (opt, after) := flushRun
      have gzA := (flush_block_gz ready safe3 false flushRun invA.good.live.hs).trans gz3
      have inputA : z'.avail_in ≠ 0 → z'.next_in ≠ .null := by
        rw [keeps.availIn, keeps.nextIn]; exact head.input
      have headA : Head RleKind after r ds z' result :=
        ⟨invA, buffersA, outA, inputA, by rw [keeps.level]; exact level3,
          by unfold RleKind; rw [keeps.strategy]; exact kind3, keysF.safe safe3⟩
      rcases choice rfl with none' | more
      · subst none'
        refine ⟨{ st with bflush := true }, after, by simp [huffTail, bind_app, flushRun'], rfl,
          z', result, headA, (Fr.flush account totalInF totalOutF bufferF shapeF keysF), ?_, gzA, Or.inl ⟨rfl, (idle rfl).1⟩⟩
        rw [keeps.lookahead]; exact count
      · subst more
        exact ⟨{ st with bflush := true, ret := some need_more }, after, by simp [huffTail, bind_app, flushRun'], rfl,
          z', result, headA, (Fr.flush account totalInF totalOutF bufferF shapeF keysF), by rw [keeps.lookahead]; exact count,
          gzA, Or.inr ⟨rfl, fullOut (Option.some_ne_none _)⟩⟩
  have lift : ∀ {h3 h' : Heap} {d3 : DeflateState} {st' : LoopS}, Fr h r ds d z h3 z d3 →
      (∃ z' d', Head RleKind h' r ds z' d' ∧ Fr h3 r ds d3 z h' z' d' ∧
        d'.lookahead.toNat < d.lookahead.toNat ∧ d'.gzindex = d.gzindex ∧
        ((st'.ret = st.ret ∧ d'.pending = 0) ∨ (st'.ret = some need_more ∧ z'.avail_out = 0))) →
      (∃ z' d', Head RleKind h' r ds z' d' ∧ Fr h r ds d z h' z' d' ∧
        d'.lookahead.toNat < d.lookahead.toNat ∧ d'.gzindex = d.gzindex ∧
        ((st'.ret = st.ret ∧ d'.pending = 0) ∨ (st'.ret = some need_more ∧ z'.avail_out = 0))) := by
    intro h3 h' d3 st' pre cases
    obtain ⟨z', d', hd, f, rest⟩ := cases
    exact ⟨z', d', hd, Fr.trans head.inv.good head.buffers pre f, rest⟩
  rcases mlCases with zero | ⟨lo, hi, within⟩
  · -- a literal
    subst zero
    have self2 : setD h ds { d1 with match_length := 0 } = setD h ds d1 := rfl
    obtain ⟨b, buf', c, h3, run, h3def, pbuf, good3, laEq, ssEq, buffers3, fullCase, notFullCase⟩ :=
      literal_step_inv inv1 head.level look (Or.inr head.kind) rfl pending buffers1 head.out
        (huffTail (some (.tab ds)) st)
    have ld1 : ldDeflateState (some (.tab ds)) (setD h ds d1) = .ok (d1, setD h ds d1) :=
      ldDeflateState_tab (setD_dstates_same h ds d1)
    have notBig : ¬ (d1.match_length ≥ MIN_MATCH_u) := by
      change ¬ ((0 : UInt32) ≥ 3); decide
    obtain ⟨st', h', tailRun, brk', cases⟩ := tail h3 z (literalStep d1 c) _
      (by rw [laEq]; change (d.lookahead.toNat - 1) < _; omega) rfl good3 buffers3 rfl head.kind head.safe head.level pending
      (fun flag => let ⟨xs, ready⟩ := fullCase flag; ⟨b, buf', xs, ready⟩) notFullCase
    have heapL : setD (setD h ds d1) ds { d1 with match_length := 0 } = setD h ds d1 := by
      rw [setD_setD]
    have emit : rleEmit (some (.tab ds)) st (setD h ds d1) =
        (do
          let d ← ldDeflateState (some (.tab ds))
          let c ← index8 d.window d.strstart.toNat
          let bflush ← tally_lit (some (.tab ds)) c
          wr (some (.tab ds)) (fun d => { d with lookahead := d.lookahead - 1, strstart := d.strstart + 1 })
          huffTail (some (.tab ds)) st bflush) (setD h ds d1) := by
      unfold rleEmit
      simp only [bind_app, ld1, if_neg notBig]
    refine ⟨st', h', ?_, brk', lift ?_ cases⟩
    · rw [bind_app, wrRun]
      simp only [bind_app, scanRun]
      have all := emit.trans (run.trans tailRun)
      rw [← heapL] at all
      exact all
    · refine Fr.priv head.inv.good head.buffers ?_ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rw [h3def]
      exact (priv_setD h r ds d _ head.inv.good.live.hs).trans
        ((priv_tally inv1.good pbuf buf' _).keys ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)
  · -- a run
    have noRoll : d1.strategy.toInt = 2 ∨ d1.strategy.toInt = 3 := Or.inr head.kind
    obtain ⟨b, buf', h3, run, good3, laEq, ssEq, buffers3, fullCase, notFullCase, priv3⟩ :=
      run_step_inv inv1 head.level noRoll rfl pending buffers1 head.out ml lo hi within
        (huffTail (some (.tab ds)) st)
    obtain ⟨st', h', tailRun, brk', cases⟩ := tail h3 z (runStep d1 ml) _
      (by rw [laEq]; change (d.lookahead.toNat - ml.toNat) < _; omega) rfl good3 buffers3 rfl head.kind head.safe
      head.level pending (fun flag => let ⟨xs, ready⟩ := fullCase flag; ⟨b, buf', xs, ready⟩) notFullCase
    refine ⟨st', h', ?_, brk', lift (Fr.priv (d' := runStep d1 ml) head.inv.good head.buffers
      ((priv_setD h r ds d _ head.inv.good.live.hs).trans (priv3.keys ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩) cases⟩
    rw [bind_app, wrRun]
    simp only [bind_app, scanRun]
    have ld2 : ldDeflateState (some (.tab ds)) (setD (setD h ds d1) ds { d1 with match_length := ml }) =
        .ok ({ d1 with match_length := ml }, setD (setD h ds d1) ds { d1 with match_length := ml }) :=
      ldDeflateState_tab (setD_dstates_same _ ds _)
    have big : ({ d1 with match_length := ml } : DeflateState).match_length ≥ MIN_MATCH_u := by
      change MIN_MATCH_u ≤ ml
      rw [UInt32.le_iff_toNat_le]; exact lo
    have emit : rleEmit (some (.tab ds)) st (setD (setD h ds d1) ds { d1 with match_length := ml }) =
        (do
          let bflush ← tally_dist (some (.tab ds)) 1 (ml - MIN_MATCH_u)
          wr (some (.tab ds)) (fun d =>
            { d with lookahead := d.lookahead - d.match_length, strstart := d.strstart + d.match_length, match_length := 0 })
          huffTail (some (.tab ds)) st bflush) (setD (setD h ds d1) ds { d1 with match_length := ml }) := by
      unfold rleEmit
      simp only [bind_app, ld2, if_pos big]
    exact emit.trans (run.trans tailRun)

set_option maxHeartbeats 2400000 in
/-- **One iteration of `deflate_rle`** with no input. -/
theorem rle_body_q {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (head : Head RleKind h r ds z d) (pending : d.pending = 0) (empty : z.avail_in = 0)
    (flush : Int32) (st : LoopS) (brk : st.brk = false) (ret : st.ret = none) :
    ∃ st' h', deflate_rle_body (some (.tab ds)) flush st h = .ok (st', h') ∧
      QStep RleKind r ds flush z d st st' h' := by
  have rdLook : rd (some (.tab ds)) (·.lookahead) h = .ok (d.lookahead, h) := by
    simp [rdD_eq, head.inv.good.live.hs]
  have finishIter : ∀ {h1 : Heap} {z1 : ZStream} {d1 : DeflateState}, Head RleKind h1 r ds z1 d1 →
      QDown z d z1 d1 → d1.pending = 0 → 1 ≤ d1.lookahead.toNat →
      d1.strstart.toNat + 258 < d1.window_size.toNat →
      ∃ st' h', (do
          wr (some (.tab ds)) (fun d => { d with match_length := 0 })
          rleScan (some (.tab ds))
          rleEmit (some (.tab ds)) st) h1 = .ok (st', h') ∧ QStep RleKind r ds flush z d st st' h' := by
    intro h1 z1 d1 head1 down1 pending1 look1 room1
    obtain ⟨st', h', iterRun, brk', z', d', head', fr', la', gz', cases⟩ := rle_emit_iterQ head1 look1 room1 pending1 st
    exact ⟨st', h', iterRun, qstep_of_iter down1 fr' head'
      (work_lt_noLazy head1.level head'.level (idle_of_roll head'.inv.shape (Or.inr head'.kind)) la')
      gz' brk' brk ret cases⟩
  rw [rle_body_source]
  by_cases small : d.lookahead ≤ MAX_MATCH_u
  · have short : d.lookahead.toNat < 262 := by
      have := UInt32.le_iff_toNat_le.mp small; change _ ≤ 258 at this; omega
    obtain ⟨after1, z1, d1, fillRun, inv1, buffers1, post⟩ :=
      fill_window_inv head.inv head.level head.buffers head.input short
    obtain ⟨_, sStrategy, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := post.same
    have head1 : Head RleKind after1 r ds z1 d1 :=
      head_after_fill head inv1 buffers1 post (fun k => by unfold RleKind; rw [sStrategy]; exact k)
    obtain ⟨down1, _, _, la1, pending1⟩ := fill_down post empty pending head.level
    have rdLook1 : rd (some (.tab ds)) (·.lookahead) after1 = .ok (d1.lookahead, after1) := by
      simp [rdD_eq, inv1.good.live.hs]
    have room1 := fill_room post
    have fillRun' : fill_window (some (.tab ds)) h = .ok ((), after1) := fillRun
    by_cases stop1 : (d1.lookahead ≤ MAX_MATCH_u && flush == Z_NO_FLUSH) = true
    · have noFlush : flush = Z_NO_FLUSH := by
        simp only [Bool.and_eq_true, beq_iff_eq] at stop1; exact stop1.2
      refine ⟨{ st with ret := some need_more }, after1, ?_, z1, d1, head1, down1,
        Or.inr (Or.inl ⟨rfl, Or.inr ⟨pending1, noFlush⟩⟩)⟩
      simp only [bind_app, rdLook, M_ite_app, small, ite_true, fillRun', rdLook1, stop1]
      rfl
    · have stop1F : (d1.lookahead ≤ MAX_MATCH_u && flush == Z_NO_FLUSH) = false := by simpa using stop1
      by_cases empty1 : d1.lookahead = 0
      · have empty1B : (d1.lookahead == 0) = true := by simp [empty1]
        refine ⟨{ st with brk := true }, after1, ?_, z1, d1, head1, down1,
          Or.inr (Or.inr ⟨rfl, ret, pending1, empty1⟩)⟩
        simp only [bind_app, rdLook, M_ite_app, small, ite_true, fillRun', rdLook1, stop1F,
          Bool.false_eq_true, ite_false, empty1B]
        rfl
      · have empty1B : (d1.lookahead == 0) = false := by simpa using empty1
        have look1 : 1 ≤ d1.lookahead.toNat := by
          have : d1.lookahead.toNat ≠ 0 := fun e => empty1 (UInt32.toNat_inj.mp e)
          omega
        obtain ⟨st', h', iterRun, step⟩ := finishIter head1 down1 pending1 look1 (by omega)
        refine ⟨st', h', ?_, step⟩
        simp only [bind_app, rdLook, M_ite_app, small, ite_true, fillRun', rdLook1, stop1F,
          Bool.false_eq_true, ite_false, empty1B]
        exact iterRun
  · have big : 258 < d.lookahead.toNat := by
      have := small; rw [UInt32.le_iff_toNat_le] at this; change ¬ _ ≤ 258 at this; omega
    have room := head.inv.shape.room
    obtain ⟨st', h', iterRun, step⟩ := finishIter head (QDown.refl pending) pending (by omega) (by omega)
    refine ⟨st', h', ?_, step⟩
    simp only [bind_app, rdLook, M_ite_app, small, ite_false]
    exact iterRun

/-- **`deflate_rle` with no input** lowers the work term. -/
theorem rle_q {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream}
    {d : DeflateState} (safe : FlushSafeAt d.lit_bufsize.toNat) (inv : DInv h r ds z d) (entry : StratIn h r z d)
    (flush : Int32) (level : d.level ≠ 0) (rle : d.strategy.toInt = 3) (empty : z.avail_in = 0) :
    ∃ bstate after z' d', C.run (Zlib.Deflate.deflate_rle (some (.tab ds)) flush) h = .ok (bstate, after) ∧
      r.get after = some z' ∧ after.dstates ds = some d' ∧ QEnd flush z d z' d' bstate := by
  have head : Head RleKind h r ds z d := ⟨inv, entry.buffers, entry.out, entry.input, level, rle, safe⟩
  obtain ⟨st, h1, loopRun, ⟨z1, d1, head1, down1, cases⟩, exit⟩ :=
    q_loop (deflate_rle_body (some (.tab ds)) flush) flush head entry.pending empty
      (fun st _ _ _ hd p e b r => rle_body_q hd p e flush st b r)
  rcases cases with ⟨brk, ret0, _⟩ | ⟨ret, why⟩ | ⟨brk, ret, pending1, empty1⟩
  · rcases exit with e | e
    · rw [brk] at e; cases e
    · rw [ret0] at e; cases e
  · refine ⟨need_more, h1, z1, d1, ?_, head1.inv.good.live.hz, head1.inv.good.live.hs, QEnd.more_of down1 why⟩
    simp [C.run, deflate_rle, bind_app, loopRun, ret]
  · obtain ⟨wrRun, head2⟩ := clear_insert_head head1 id
    obtain ⟨bstate, after, z', d', tailRun, hz', hs', fin⟩ := finish_tail_q head2 pending1 flush
      (idle_of_roll head1.inv.shape (Or.inr head1.kind) : d1.match_available = 0) empty1
    refine ⟨bstate, after, z', d', ?_, hz', hs', QEnd.after down1 (QEnd.after (insert_down pending1 0) fin)⟩
    simp only [C.run, deflate_rle, bind_app, loopRun, ret, wrRun]
    exact tailRun

/-! ## `deflate_fast` -/

/-- The tail of an iteration of `deflate_fast` and `deflate_slow` (`lazy_tail_step`), with the
lookahead, the lazy literal and `gzindex` of the `need_more` state. -/
theorem lazy_tail_stepQ {kind : DeflateState → Prop}
    (kindKeep : ∀ d d' : DeflateState, d'.strategy = d.strategy → d'.level = d.level → kind d → kind d')
    {h3 : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d3 : DeflateState} (st : LoopS) (hh : UInt32)
    (bflush : Bool) (buffers3 : StreamBuffers h3 r) (out : z.next_out ≠ .null)
    (input : z.avail_in ≠ 0 → z.next_in ≠ .null) (level3 : d3.level ≠ 0) (kind3 : kind d3)
    (safe3 : FlushSafeAt d3.lit_bufsize.toNat) (pending3 : d3.pending = 0)
    (full : bflush = true → ∃ pb buf xs, BlockReady h3 r ds z d3 pb buf xs)
    (notFull : bflush = false → DInv h3 r ds z d3) :
    ∃ st' h', lazyTail (some (.tab ds)) st hh bflush h3 = .ok (st', h') ∧ st'.brk = st.brk ∧
      ∃ z' d', Head kind h' r ds z' d' ∧ Fr h3 r ds d3 z h' z' d' ∧ d'.lookahead = d3.lookahead ∧
        d'.match_available = d3.match_available ∧ d'.gzindex = d3.gzindex ∧
        ((st'.ret = st.ret ∧ d'.pending = 0) ∨ (st'.ret = some need_more ∧ z'.avail_out = 0)) := by
  cases bflush with
  | false =>
    exact ⟨{ st with hash_head := hh, bflush := false }, h3, by simp [lazyTail], rfl,
      z, d3, ⟨notFull rfl, buffers3, out, input, level3, kind3, safe3⟩, Fr.refl (notFull rfl).good buffers3,
      rfl, rfl, rfl, Or.inl ⟨rfl, pending3⟩⟩
  | true =>
    obtain ⟨pb, buf, xs, ready⟩ := full rfl
    obtain ⟨opt, produced, after, z', result, flushRun, invA, buffersA, account, keeps, outA, idle, choice, _, _, fullOut, totalOutF, bufferF, totalInF, shapeF, keysF, lastF⟩ :=
      flush_block_macro ready safe3 false
    have flushRun' : FLUSH_BLOCK (some (.tab ds)) 0 h3 = .ok (opt, after) := flushRun
    have gzA := flush_block_gz ready safe3 false flushRun invA.good.live.hs
    have inputA : z'.avail_in ≠ 0 → z'.next_in ≠ .null := by
      rw [keeps.availIn, keeps.nextIn]; exact input
    have headA : Head kind after r ds z' result :=
      ⟨invA, buffersA, outA, inputA, by rw [keeps.level]; exact level3,
        kindKeep d3 result keeps.strategy keeps.level kind3, keysF.safe safe3⟩
    rcases choice rfl with none' | more
    · subst none'
      exact ⟨{ st with hash_head := hh, bflush := true }, after, by simp [lazyTail, bind_app, flushRun'], rfl,
        z', result, headA, (Fr.flush account totalInF totalOutF bufferF shapeF keysF), keeps.lookahead,
        keeps.matchAvailable, gzA, Or.inl ⟨rfl, (idle rfl).1⟩⟩
    · subst more
      exact ⟨{ st with hash_head := hh, bflush := true, ret := some need_more }, after,
        by simp [lazyTail, bind_app, flushRun'], rfl, z', result, headA,
        (Fr.flush account totalInF totalOutF bufferF shapeF keysF), keeps.lookahead, keeps.matchAvailable, gzA,
        Or.inr ⟨rfl, fullOut (Option.some_ne_none _)⟩⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- **The literal emission of `deflate_fast`** after a search that found no match of 3. -/
theorem fast_literal_emitQ {h h2 : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream}
    {d d2 : DeflateState} (head : Head FastKind h r ds z d) (pending : d.pending = 0)
    (look : 1 ≤ d.lookahead.toNat) (search : SearchOut h h2 r ds z d d2)
    (small : d2.match_length.toNat < 3) (st : LoopS) (hh : UInt32) :
    ∃ st' h', fastEmit (some (.tab ds)) st hh h2 = .ok (st', h') ∧ st'.brk = st.brk ∧
      ∃ z' d', Head FastKind h' r ds z' d' ∧ Fr h r ds d z h' z' d' ∧
        d'.lookahead.toNat < d.lookahead.toNat ∧ d'.gzindex = d.gzindex ∧
        ((st'.ret = st.ret ∧ d'.pending = 0) ∨ (st'.ret = some need_more ∧ z'.avail_out = 0)) := by
  have inv := head.inv
  have shape := inv.shape
  have upd := search.update
  -- the fields of d2 that the literal reads
  have eWin : d2.window = d.window := by rw [upd]
  have eSym : d2.sym_next = d.sym_next := by rw [upd]
  have eEnd : d2.sym_end = d.sym_end := by rw [upd]
  have eWs : d2.window_size = d.window_size := by rw [upd]
  have eW : d2.w_size = d.w_size := by rw [upd]
  have eSs := search.strstart
  have eLa := search.lookahead
  have eIns := search.insert
  have buffers2 : StreamBuffers h2 r := by
    obtain ⟨win, prev, hd, pb⟩ : d2.window = d.window ∧ d2.prev = d.prev ∧ d2.head = d.head ∧
        d2.pending_buf = d.pending_buf := by rw [upd]; exact ⟨rfl, rfl, rfl, rfl⟩
    exact stream_buffers_private_read inv.good.live.hz search.good.live.hz head.buffers search.frame
      (fun i mine => (stream_owned_deflate inv.good i).mpr (Or.inl mine))
      (stream_owned_keys inv.good search.good win prev hd pb) (stream_accounting_self z) search.borrow
  have recorded2 : ∃ xs, Recorded h2 d2 xs ∧ ∀ s ∈ xs, s.distance ≤ d2.w_size.toNat - 262 := by
    obtain ⟨xs, ⟨b, a, pbuf, get, ledger⟩, dist⟩ := inv.symbols.recorded
    refine ⟨xs, ⟨b, a, by rw [upd]; exact pbuf, by rw [search.bytes]; exact get, ?_⟩, by rw [eW]; exact dist⟩
    rw [upd]; exact ledger.keep rfl rfl rfl rfl
  have room2 : d2.strstart.toNat + d2.lookahead.toNat ≤ d2.window_size.toNat := by
    rw [eSs, eLa, eWs]; exact shape.room
  have strict2 : d2.sym_next.toNat < d2.sym_end.toNat := by rw [eSym, eEnd]; exact shape.symRoom
  have look2 : 1 ≤ d2.lookahead.toNat := by rw [eLa]; exact look
  obtain ⟨b, buf, buf', xs, c, h3, run, h3def, trees, ledger, dist, bufEq, good3, trees3, ledger3, chains3,
    count, ssEq, laEq, notFull⟩ := literal_step_core search.good recorded2 room2 strict2 search.chains look2
      (lazyTail (some (.tab ds)) st hh)
  have keys2 : Keys d d2 := by rw [upd]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have pre : Fr h r ds d z h3 z (literalStep d2 c) := by
    refine Fr.priv head.inv.good head.buffers (search.priv.trans ?_) (keys2.trans ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)
    rw [h3def]
    exact (priv_tally search.good trees.base.pbuf buf' _).keys keys2
  have ld2 : ldDeflateState (some (.tab ds)) h2 = .ok (d2, h2) := ldDeflateState_tab search.good.live.hs
  have notBig : ¬ (d2.match_length ≥ MIN_MATCH_u) := by
    rw [GE.ge, UInt32.le_iff_toNat_le]; change ¬ 3 ≤ _; omega
  have emit : fastEmit (some (.tab ds)) st hh h2 = lazyTail (some (.tab ds)) st hh (d2.sym_next + 3 == d2.sym_end) h3 := by
    have := run
    simp only [bind_app, ld2] at this
    unfold fastEmit
    simp only [bind_app, ld2, if_neg notBig]
    exact this
  let d3 := literalStep d2 c
  have staticEq : h3.static = h.static := by rw [h3def]; exact search.static
  obtain ⟨w, wa, win, getW, _⟩ := window_block inv.good
  have pbuf := trees.base.pbuf
  have wb : w ≠ b := by
    obtain ⟨w0, p0, q0, b0, blocks⟩ := inv.good.inv.blocks
    have we : w0 = w := by simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.win.symm
    have be : b0 = b := by
      rw [show d2.pending_buf = d.pending_buf by rw [upd]] at pbuf
      simpa only [pbuf, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.pbuf.symm
    subst w0 b0; exact blocks.wb
  have getW3 : h3.bytes w = some wa := by
    rw [h3def]; simp [Zlib.Trees.Proofs.Out.setB, upd_ne _ _ _ _ wb, search.bytes, getW]
  have ss3 : d3.strstart.toNat = d.strstart.toNat + 1 := by rw [ssEq, eSs]
  have la3 : d3.lookahead.toNat = d.lookahead.toNat - 1 := by rw [laEq, eLa]
  have chainsA : Chains h3 d3 := by
    unfold Chains
    apply chains_up chains3
    unfold chainTop
    change _ ≤ min (d3.strstart.toNat - d2.insert.toNat) (d3.strstart.toNat + d3.lookahead.toNat - 2)
    rw [ss3, la3, eIns]
    by_cases ready : 3 ≤ d.lookahead.toNat
    · rw [if_pos ready]
      have zero : d.insert = 0 := shape.insertDone ready
      have z0 : d.insert.toNat = 0 := by rw [zero]; rfl
      omega
    · rw [if_neg ready]
      omega
  have kind := head.kind
  have hashingA : Hashing h3 d3 := by
    refine ⟨fun _ => chainsA, fun one => ?_, fun _ _ large => ?_⟩
    · have zero := shape.slides.2 head.level
      change d2.«matches» = 1 at one
      rw [show d2.«matches» = d.«matches» by rw [upd], zero] at one; cases one
    · change 3 ≤ d3.lookahead.toNat at large
      rw [la3] at large
      obtain ⟨w0, wa0, win0, get0, form⟩ := search.form (by omega)
      have wid : w0 = w := by simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using win0.symm
      subst w0
      have aid : wa0 = wa := Option.some.inj (get0.symm.trans getW)
      subst aid
      refine ⟨w, wa0, by change d2.window = _; rw [eWin]; exact win, getW3, ?_⟩
      change InsHForm d2.hash_shift d2.hash_mask (bfn wa0) d3.strstart.toNat d2.ins_h
      rw [ss3, show d2.hash_shift = d.hash_shift by rw [upd], show d2.hash_mask = d.hash_mask by rw [upd]]
      exact form
  have span := shape.blockSpan head.level
  have ml2 : d2.match_length.toNat ≤ 2 := by omega
  have mlEq : d3.match_length = d2.match_length := rfl
  have shapeCore : ∀ (sr : d3.sym_next.toNat < d3.sym_end.toNat ∨ True),
      d3.strstart.toNat + d3.lookahead.toNat ≤ d3.window_size.toNat ∧
      d3.insert.toNat ≤ d3.strstart.toNat ∧ (3 ≤ d3.lookahead.toNat → d3.insert = 0) ∧
      d3.block_start.toInt ≤ d3.strstart.toNat ∧
      (d3.match_available ≠ 0 → 1 ≤ d3.strstart.toNat) := by
    intro _
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [ss3, la3]; change _ ≤ d2.window_size.toNat; rw [eWs]; have := shape.room; omega
    · rw [ss3]; change d2.insert.toNat ≤ _; rw [eIns]; have := shape.insert; omega
    · intro large; rw [la3] at large; change d2.insert = 0; rw [eIns]; exact shape.insertDone (by omega)
    · rw [ss3]; change d2.block_start.toInt ≤ _; rw [show d2.block_start = d.block_start by rw [upd]]
      have := shape.blockStart; omega
    · intro _; rw [ss3]; omega
  have ePl : d2.prev_length = d.prev_length := search.prevLength
  have eMa : d2.match_available = d.match_available := search.available
  have eBs : d2.block_start = d.block_start := by rw [upd]
  have eLv : d2.level = d.level := by rw [upd]
  have eSt : d2.strategy = d.strategy := by rw [upd]
  have eHw : d2.high_water = d.high_water := by rw [upd]
  have eLf : d2.last_flush = d.last_flush := by rw [upd]
  have eWr : d2.wrap = d.wrap := by rw [upd]
  have eStat : d2.status = d.status := by rw [upd]
  have eBv : d2.bi_valid = d.bi_valid := by rw [upd]
  have ePd : d2.pending = d.pending := by rw [upd]
  have ePo : d2.pending_out = d.pending_out := by rw [upd]
  have ePb : d2.pending_buf = d.pending_buf := by rw [upd]
  have eMt : d2.«matches» = d.«matches» := by rw [upd]
  have eLit : d2.lit_bufsize = d.lit_bufsize := by rw [upd]
  have eBl : d2.bl_tree = d.bl_tree := by rw [upd]
  have eOpt : d2.opt_len = d.opt_len := by rw [upd]
  have eStc : d2.static_len = d.static_len := by rw [upd]
  have lazyB := shape.fastLazy kind.1 kind.2.1 kind.2.2.1 kind.2.2.2
  obtain ⟨cRoom, cIns, cDone, cStart, cAvail⟩ := shapeCore (Or.inr trivial)
  have pendingMatch3 : 3 ≤ d3.match_length.toNat →
      1 ≤ (d3.strstart - 1 - d3.match_start).toNat ∧
      (d3.strstart - 1 - d3.match_start).toNat ≤ d3.w_size.toNat - 262 ∧
      d3.match_length.toNat ≤ d3.lookahead.toNat + 1 ∧ d3.insert = 0 ∧ 1 ≤ d3.strstart.toNat := by
    intro large; change 3 ≤ d2.match_length.toNat at large; omega
  have fast3 : 1 ≤ d3.level.toInt → d3.level.toInt ≤ 3 → d3.strategy.toInt ≠ 2 → d3.strategy.toInt ≠ 3 →
      d3.match_length.toNat ≤ 2 ∧ d3.prev_length.toNat ≤ 2 := by
    intro _ _ _ _
    exact ⟨ml2, by change d2.prev_length.toNat ≤ 2; rw [ePl]; exact lazyB.2⟩
  have biValid3 : d3.bi_valid.toInt ≤ 7 := by change d2.bi_valid.toInt ≤ 7; rw [eBv]; exact shape.biValid
  have cursor3 : d3.pending = 0 → d3.pending_out = d3.pending_buf := by
    change d2.pending = 0 → d2.pending_out = d2.pending_buf; rw [ePd, ePo, ePb]; exact shape.cursor
  have slides3 : d3.«matches».toNat ≤ 2 ∧ (d3.level ≠ 0 → d3.«matches» = 0) := by
    change d2.«matches».toNat ≤ 2 ∧ (d2.level ≠ 0 → d2.«matches» = 0); rw [eMt, eLv]; exact shape.slides
  have hw3 : d3.high_water.toNat ≤ d3.window_size.toNat := by
    change d2.high_water.toNat ≤ d2.window_size.toNat; rw [eHw, eWs]; exact shape.highWater
  have wi3 : d3.strstart.toNat + d3.lookahead.toNat ≤ d3.high_water.toNat := by
    rw [ss3, la3]; change _ ≤ d2.high_water.toNat; rw [eHw]; have := shape.windowInit; omega
  have lf3 : -2 ≤ d3.last_flush.toInt ∧ d3.last_flush.toInt ≤ 5 := by
    change -2 ≤ d2.last_flush.toInt ∧ d2.last_flush.toInt ≤ 5; rw [eLf]; exact shape.lastFlush
  have hf3 : d3.status = INIT_STATE ∨ d3.status = GZIP_STATE → d3.last_flush = -2 ∨ d3.last_flush = -1 := by
    change d2.status = INIT_STATE ∨ d2.status = GZIP_STATE → d2.last_flush = -2 ∨ d2.last_flush = -1
    rw [eStat, eLf]; exact shape.headerFlush
  have tr3 : d3.wrap.toInt < 0 → d3.status = FINISH_STATE := by
    change d2.wrap.toInt < 0 → d2.status = FINISH_STATE; rw [eWr, eStat]; exact shape.trailer
  have ma3 : d3.match_available = 0 ∨ d3.match_available = 1 := by
    change d2.match_available = 0 ∨ d2.match_available = 1; rw [eMa]; exact shape.matchAvailable
  have pl3 : d3.prev_length.toNat ≤ 258 := by change d2.prev_length.toNat ≤ 258; rw [ePl]; exact shape.prevLength
  have level3 : d3.level ≠ 0 := by change d2.level ≠ 0; rw [eLv]; exact head.level
  have kind3 : FastKind d3 := by
    unfold FastKind; change 1 ≤ d2.level.toInt ∧ d2.level.toInt ≤ 3 ∧ d2.strategy.toInt ≠ 2 ∧ d2.strategy.toInt ≠ 3
    rw [eLv, eSt]; exact kind
  have pending3 : d3.pending = 0 := by change d2.pending = 0; rw [ePd]; exact pending
  have globals3 : LibraryGlobals h3 := by unfold LibraryGlobals; rw [staticEq]; exact inv.globals
  have clear3 : BlockInit.BlockClear d3 := by
    have c := inv.symbols.clear
    refine ⟨fun k hk => ?_, ?_, ?_⟩
    · change d2.bl_tree[k]!.fc = 0; rw [eBl]; exact c.bl k hk
    · change d2.opt_len = 0; rw [eOpt]; exact c.opt
    · change d2.static_len = 0; rw [eStc]; exact c.fixed
  have distA : ∀ s ∈ xs ++ [⟨0, c.toNat⟩], s.distance ≤ d3.w_size.toNat - 262 := by
    intro s mem
    rcases List.mem_append.mp mem with old | new
    · exact dist s old
    · simp only [List.mem_singleton] at new; subst new; exact Nat.zero_le _
  have getB3 : h3.bytes b = some buf' := by rw [h3def]; simp
  have blockLow : -(2 : Int) ^ 62 ≤ d3.block_start.toInt := by
    change -(2 : Int) ^ 62 ≤ d2.block_start.toInt; rw [eBs]; exact block_start_low inv head.level
  have out := head.out
  have input := head.input
  have idle3 : d3.match_available = 0 := by change d2.match_available = 0; rw [eMa]; exact idle_of_low shape head.kind.2.1
  have lz3 : 3 ≤ d3.prev_length.toNat → 4 ≤ d3.level.toInt ∧ d3.strategy.toInt ≠ 2 ∧ d3.strategy.toInt ≠ 3 ∧
      d3.prev_length.toNat < d3.match_length.toNat := fun large =>
    absurd large (by have := (fast3 kind3.1 kind3.2.1 kind3.2.2.1 kind3.2.2.2).2; omega)
  have sb3 : d3.sym_next ≠ 0 → d3.block_start.toInt < d3.strstart.toNat := fun _ => by
    change d2.block_start.toInt < (d3.strstart.toNat : Int); rw [eBs, ss3]; have := shape.blockStart; omega
  obtain ⟨st', h', tailRun, brk', z', d', head', acc', laEq', _, gzEq', cases⟩ := lazy_tail_stepQ fast_kind_keep st hh (d2.sym_next + 3 == d2.sym_end)
    (by rw [h3def]; rw [h3def] at good3
        exact private_write_buffers search.good buffers2 pbuf ⟨rfl, rfl, rfl, rfl⟩ good3)
    out input level3 kind3 (by rw [show d3.lit_bufsize = d.lit_bufsize by change d2.lit_bufsize = d.lit_bufsize; rw [upd]]; exact head.safe) pending3
    (fun full => ⟨b, buf', xs ++ [⟨0, c.toNat⟩], ⟨good3, inv.alloc, globals3, trees3, ledger3, clear3,
      flushed_shape cRoom cIns cDone pl3 search.matchShape ma3 (fun zero => absurd zero level3) cAvail
        pendingMatch3 fast3 hw3 wi3 lf3 hf3 tr3 biValid3 cursor3
        (by change 0 < d2.sym_end.toNat; rw [eEnd]; have := shape.symRoom; omega) slides3 lz3
        (fun nz => absurd idle3 nz) idle3,
      hashingA, pending3, blockLow, cStart, level3,
      (by rw [h3def]; rw [h3def] at good3
          exact private_write_buffers search.good buffers2 pbuf ⟨rfl, rfl, rfl, rfl⟩ good3), out⟩⟩)
    (fun flag => by
      have strictA := notFull flag
      refine ⟨good3, inv.alloc, globals3, ⟨cRoom, cIns, cDone, pl3, search.matchShape, ma3, cStart, ?_,
        (fun zero => absurd zero level3), cAvail, pendingMatch3, fast3, hw3, wi3, lf3, hf3, tr3, biValid3, cursor3, strictA,
        slides3, lz3, sb3, fun nz => absurd idle3 nz, fun nz => absurd idle3 nz⟩, hashingA, ⟨⟨_, ⟨b, buf', pbuf, getB3, ledger3⟩, distA⟩, clear3, ?_⟩⟩
      · intro _
        change ((d3.strstart.toNat : Int)) - d2.block_start.toInt ≤
          258 * (d3.sym_next.toNat / 3 : Nat) + d2.match_available.toInt
        rw [ss3, count, eBs, eMa, eSym]
        have div : (d.sym_next.toNat + 3) / 3 = d.sym_next.toNat / 3 + 1 := by omega
        rw [div]
        push_cast
        omega
      · intro b0 off pout _
        change d2.pending_out = _ at pout
        rw [ePo, shape.cursor pending, ← ePb, pbuf] at pout
        simp only [Ptr.ref.injEq, BRef.blk.injEq] at pout
        change off + d2.pending.toNat ≤ d2.lit_bufsize.toNat
        rw [← pout.2, ePd, pending]
        exact Nat.zero_le _)
  refine ⟨st', h', emit.trans tailRun, brk', z', d', head', Fr.trans head.inv.good head.buffers pre acc',
    by rw [laEq', la3]; omega, by rw [gzEq']; show d2.gzindex = d.gzindex; rw [upd], cases⟩


set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **The match emission of `deflate_fast`** after a search that found a match of 3 or more. -/
theorem fast_match_emitQ {h h2 : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream}
    {d d2 : DeflateState} (head : Head FastKind h r ds z d) (pending : d.pending = 0)
    (room : d.strstart.toNat + 262 ≤ d.window_size.toNat) (search : SearchOut h h2 r ds z d d2)
    (big : 3 ≤ d2.match_length.toNat) (st : LoopS) (hh : UInt32) :
    ∃ st' h', fastEmit (some (.tab ds)) st hh h2 = .ok (st', h') ∧ st'.brk = st.brk ∧
      ∃ z' d', Head FastKind h' r ds z' d' ∧ Fr h r ds d z h' z' d' ∧
        d'.lookahead.toNat < d.lookahead.toNat ∧ d'.gzindex = d.gzindex ∧
        ((st'.ret = st.ret ∧ d'.pending = 0) ∨ (st'.ret = some need_more ∧ z'.avail_out = 0)) := by
  have inv := head.inv
  have shape := inv.shape
  have upd := search.update
  have kind := head.kind
  have lazyB := shape.fastLazy kind.1 kind.2.1 kind.2.2.1 kind.2.2.2
  obtain ⟨within, dlo, dhi⟩ := search.matched big
  have ready : 3 ≤ d.lookahead.toNat := by omega
  have insertZero : d.insert = 0 := shape.insertDone ready
  have mlHi := search.matchShape
  obtain ⟨w, wa, win, getW, wsize⟩ := window_block inv.good
  have wsz := inv.good.inv.wsz
  have wsHi := (slide_window_sizes inv.good).2
  have ld2 : ldDeflateState (some (.tab ds)) h2 = .ok (d2, h2) := ldDeflateState_tab search.good.live.hs
  have bigU : d2.match_length ≥ MIN_MATCH_u := by rw [GE.ge, UInt32.le_iff_toNat_le]; exact big
  -- the continuation after the record
  let K : Bool → M LoopS := fun bflush => do
    let d ← ldDeflateState (some (.tab ds))
    if d.match_length ≤ d.max_lazy_match && d.lookahead ≥ MIN_MATCH_u then
      wr (some (.tab ds)) (fun d => { d with match_length := d.match_length - 1 })
      let hh ← cdoWhile (fastMatchBody (some (.tab ds))) (fastMatchCond (some (.tab ds))) hh
      wr (some (.tab ds)) (fun d => { d with strstart := d.strstart + 1 })
      lazyTail (some (.tab ds)) st hh bflush
    else
      wr (some (.tab ds)) (fun d => { d with strstart := d.strstart + d.match_length, match_length := 0 })
      let d ← ldDeflateState (some (.tab ds))
      let c ← index8 d.window d.strstart.toNat
      wr (some (.tab ds)) (fun d => { d with ins_h := c.toUInt32 })
      UPDATE_HASH (some (.tab ds)) (← index8 d.window (d.strstart + 1).toNat)
      lazyTail (some (.tab ds)) st hh bflush
  obtain ⟨b, buf, buf', xs, h4, recRun, h4def, pbuf2, get2, good4, trees4, ledger4, dist4, chainsAt4, buffers4,
    count4, la4, notFull4, static4, borrow4⟩ := fast_match_record head search big K
  have emit : fastEmit (some (.tab ds)) st hh h2 = K (d2.sym_next + 3 == d2.sym_end) h4 := by
    have := recRun
    unfold fastEmit
    simp only [bind_app, ld2, if_pos bigU]
    exact this
  let d4 := matchRecorded d2
  have upd4 : d4.strstart = d.strstart := by change d2.strstart = _; exact search.strstart
  have ss4 : d4.strstart.toNat = d.strstart.toNat := by rw [upd4]
  have ld4 : ldDeflateState (some (.tab ds)) h4 = .ok (d4, h4) := ldDeflateState_tab good4.live.hs
  have keys2 : Keys d d2 := by rw [upd]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have keys4 : Keys d d4 := keys2.trans ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have priv4 : PrivStep h h4 r ds d := by
    refine search.priv.trans ?_
    rw [h4def]
    exact (priv_tally search.good pbuf2 buf' _).keys keys2
  have wb : w ≠ b := by
    obtain ⟨w0, p0, q0, b0, blocks⟩ := inv.good.inv.blocks
    have we : w0 = w := by simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.win.symm
    have be : b0 = b := by
      rw [show d2.pending_buf = d.pending_buf by rw [upd]] at pbuf2
      simpa only [pbuf2, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.pbuf.symm
    subst w0 b0; exact blocks.wb
  have getW4 : h4.bytes w = some wa := by
    rw [h4def]; simp [Zlib.Trees.Proofs.Out.setB, upd_ne _ _ _ _ wb, search.bytes, getW]
  have win4 : d4.window = .ref (.blk w) 0 := by change d2.window = _; rw [upd]; exact win
  have getB4 : h4.bytes b = some buf' := by rw [h4def]; simp
  have ml4 : d4.match_length = d2.match_length := rfl
  have hsh : HashParams d.hash_size d.hash_shift d.hash_mask := hash_parameters inv.good.inv
  have upd5 : ∀ {β : Type} (g : DeflateState → β), (∀ x : DeflateState, g (matchRecorded x) = g x) →
      g d4 = g d2 := fun g hg => hg d2
  have eHs4 : d4.hash_shift = d.hash_shift := by change d2.hash_shift = _; rw [upd]
  have eHm4 : d4.hash_mask = d.hash_mask := by change d2.hash_mask = _; rw [upd]
  have eWs4 : d4.window_size = d.window_size := by change d2.window_size = _; rw [upd]
  have eIns4 : d4.ins_h = d2.ins_h := rfl
  -- the rolling hash of the search, on the window of h4
  obtain ⟨w0, wa0, win0, get0, form2⟩ := search.form ready
  have wid : w0 = w := by simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using win0.symm
  subst w0
  have aid : wa0 = wa := Option.some.inj (get0.symm.trans getW)
  subst aid
  -- the chains of the record, at the window arrays
  obtain ⟨w1, p1, q1, wa1, pa1, qa1, win1, prev1, head1, hw1, hp1, hq1, H1⟩ := chainsAt4
  have wid1 : w1 = w := by have e := win1.symm.trans win4; simpa using e
  subst wid1
  have aid1 : wa1 = wa0 := Option.some.inj (hw1.symm.trans getW4)
  subst aid1
  have runK := emit
  by_cases cond : (d4.match_length ≤ d4.max_lazy_match && d4.lookahead ≥ MIN_MATCH_u) = true
  · -- insert the rest of a short match
    have cond' := cond
    simp only [Bool.and_eq_true, decide_eq_true_eq] at cond'
    have la4' : 3 ≤ d4.lookahead.toNat := by
      have := UInt32.le_iff_toNat_le.mp cond'.2; change 3 ≤ _ at this; exact this
    let d5 : DeflateState := { d4 with match_length := d4.match_length - 1 }
    let h5 := setD h4 ds d5
    have wrA : wr (some (.tab ds)) (fun d => { d with match_length := d.match_length - 1 }) h4 = .ok ((), h5) := by
      rw [wrD_eq, good4.live.hs]
    have good5 : DGood h5 r ds z d5 := engine_update_good good4 rfl
    have la4n : d4.lookahead.toNat = d.lookahead.toNat - d2.match_length.toNat := la4
    have chains5 : HeapChains h5 d5 (d5.strstart.toNat + 1) := by
      rw [show d5.strstart.toNat = d.strstart.toNat from ss4]
      refine ⟨w1, p1, q1, wa1, pa1, qa1, win1, prev1, head1, by simpa [h5] using hw1, by simpa [h5] using hp1,
        by simpa [h5] using hq1, ?_⟩
      change HashChains _ _ _ d4.hash_size d4.hash_shift d4.hash_mask d4.w_size.toNat _
        (d4.strstart.toNat + d4.lookahead.toNat)
      exact chains_lower_lim H1 (by rw [ss4]; omega)
    have form5 : InsHForm d5.hash_shift d5.hash_mask (bfn wa1) (d5.strstart.toNat + 1) d5.ins_h := by
      change InsHForm d4.hash_shift d4.hash_mask (bfn wa1) (d4.strstart.toNat + 1) d2.ins_h
      rw [eHs4, eHm4, ss4]; exact form2
    have getW5 : h5.bytes w1 = some wa1 := by simpa [h5] using getW4
    have pos5 : 1 ≤ d5.match_length.toNat := by
      change 1 ≤ (d2.match_length - 1).toNat; rw [u32_sub_one (by omega)]; omega
    have ml5 : d5.match_length.toNat = d2.match_length.toNat - 1 := by
      change (d2.match_length - 1).toNat = _; exact u32_sub_one (by omega)
    obtain ⟨cand, h6, d6, loopRun, good6, chains6, win6, bytesW6, ml6, ss6, la6, form6, frame6, bytes6, bframe6,
      borrow6, priv6⟩ := fast_match_insert_loop good5 chains5 win4 getW5 pos5 (by omega) la4'
        (by change d4.strstart.toNat + d5.match_length.toNat + 1 + d4.lookahead.toNat ≤ d4.window_size.toNat
            rw [ml5, ss4, la4n, eWs4]; have := shape.room; omega) form5 hh
    let d7 : DeflateState := { d6 with strstart := d6.strstart + 1 }
    let h7 := setD h6 ds d7
    have wr7 : wr (some (.tab ds)) (fun d => { d with strstart := d.strstart + 1 }) h6 = .ok ((), h7) := by
      rw [wrD_eq, good6.live.hs]
    have good7 : DGood h7 r ds z d7 := engine_update_good good6 rfl
    have ss6n : d6.strstart.toNat = d.strstart.toNat + d2.match_length.toNat - 1 := by
      rw [ss6]; change d4.strstart.toNat + d5.match_length.toNat = _; rw [ss4, ml5]; omega
    have ss7 : d7.strstart.toNat = d.strstart.toNat + d2.match_length.toNat := by
      change (d6.strstart + 1).toNat = _
      rw [UInt32.toNat_add]; simp only [show (1 : UInt32).toNat = 1 from rfl]
      rw [Nat.mod_eq_of_lt (by have := shape.room; omega)]; omega
    have fields7 : d7 = { matchRecorded d2 with strstart := d7.strstart, match_length := 0, ins_h := d7.ins_h } := by
      have fr := frame6
      unfold FastInsertFrame at fr
      calc d7 = { d6 with strstart := d6.strstart + 1 } := rfl
        _ = { ({ d5 with strstart := d6.strstart, ins_h := d6.ins_h, match_length := d6.match_length } : DeflateState)
              with strstart := d6.strstart + 1 } := by rw [← fr]
        _ = { matchRecorded d2 with strstart := d7.strstart, match_length := 0, ins_h := d7.ins_h } := by
              rw [ml6]
    have runA : K (d2.sym_next + 3 == d2.sym_end) h4 =
        lazyTail (some (.tab ds)) st cand (d2.sym_next + 3 == d2.sym_end) h7 := by
      simp only [K, bind_app, ld4, cond, ite_true, wrA, loopRun, wr7]
    have bytes7 : h7.bytes = h4.bytes := by change h6.bytes = _; rw [bytes6]; rfl
    obtain ⟨buffers7, fullCase, notFullCase, level7, kind7, pending7, la7⟩ :=
      fast_match_final (h7 := h7) (d7 := d7) (t7 := d.strstart.toNat + d2.match_length.toNat)
        (t7le := Nat.le_refl _) (t7lo := by have := la4n; omega)
        head pending search big good4 ledger4 dist4 pbuf2 getB4 buffers4
        static4 borrow4 count4 la4 good7 fields7 ss7 bytes7
        (by change h6.static = _; rw [bframe6.static]; rfl)
        (by change h6.libcErrorBorrow = _; rw [borrow6]; rfl)
        (fun i ne => by
          change (setD h6 ds d7).dstates i = _
          rw [setD_dstates_ne _ _ _ _ ne, bframe6.dstates i ne]; simp [h5, setD_dstates_ne _ _ _ _ ne])
        (fun i ne => by change h6.ro i = _; rw [bframe6.ro i ne]; rfl)
        (by
          obtain ⟨w', p', q', wa', pa', qa', win', prev', head', hw', hp', hq', H'⟩ := chains6
          refine ⟨w', p', q', wa', pa', qa', win', prev', head', by simpa [h7] using hw', by simpa [h7] using hp',
            by simpa [h7] using hq', ?_⟩
          change HashChains _ _ _ d6.hash_size d6.hash_shift d6.hash_mask d6.w_size.toNat _
            (d7.strstart.toNat + d6.lookahead.toNat)
          rw [← ss7]
          have e : d6.strstart.toNat + 1 = d7.strstart.toNat := by rw [ss7, ss6n]; omega
          rw [← e]
          exact chains_mono H' (Nat.le_refl _) (by omega))
        (fun large => ⟨w1, wa1, win, by simpa [h7] using bytesW6, by
          change InsHForm d.hash_shift d.hash_mask (bfn wa1) d7.strstart.toNat d6.ins_h
          have e : d6.strstart.toNat + 1 = d7.strstart.toNat := by rw [ss7, ss6n]; omega
          rw [← e]
          have hs : d6.hash_shift = d.hash_shift := by
            unfold FastInsertFrame at frame6; rw [frame6]; exact eHs4
          have hm : d6.hash_mask = d.hash_mask := by
            unfold FastInsertFrame at frame6; rw [frame6]; exact eHm4
          rw [← hs, ← hm]; exact form6⟩)
        (d2.sym_next + 3 == d2.sym_end) rfl notFull4
    obtain ⟨st', h', tailRun, brk', z', d', head', acc', laEq', _, gzEq', cases⟩ := lazy_tail_stepQ fast_kind_keep st cand
      (d2.sym_next + 3 == d2.sym_end) buffers7 head.out head.input level7 kind7 ((by rw [fields7]; exact keys4.trans ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ : Keys d d7).safe head.safe) pending7 fullCase notFullCase
    have keys7 : Keys d d7 := by rw [fields7]; exact keys4.trans ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    have pre : Fr h r ds d z h7 z d7 := by
      refine Fr.priv head.inv.good head.buffers ?_ keys7
      have keys5 : Keys d d5 := keys4.trans ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      exact ((priv4.trans (priv_setD h4 r ds d d5 good4.live.hs)).trans (priv6.keys keys5)).trans
        (priv_setD h6 r ds d d7 good6.live.hs)
    refine ⟨st', h', (emit.trans runA).trans tailRun, brk', z', d', head', Fr.trans head.inv.good head.buffers pre acc',
      by rw [laEq', la7]; omega, by rw [gzEq', fields7]; show d2.gzindex = d.gzindex; rw [upd], cases⟩
  · -- skip the rest of a long match and prime the hash at the new position
    have condF : (d4.match_length ≤ d4.max_lazy_match && d4.lookahead ≥ MIN_MATCH_u) = false := by
      simpa using cond
    have la4n : d4.lookahead.toNat = d.lookahead.toNat - d2.match_length.toNat := la4
    let d5 : DeflateState := { d4 with strstart := d4.strstart + d4.match_length, match_length := 0 }
    let h5 := setD h4 ds d5
    have wrB : wr (some (.tab ds)) (fun d => { d with strstart := d.strstart + d.match_length, match_length := 0 }) h4 =
        .ok ((), h5) := by rw [wrD_eq, good4.live.hs]
    have good5 : DGood h5 r ds z d5 := engine_update_good good4 rfl
    have ss5 : d5.strstart.toNat = d.strstart.toNat + d2.match_length.toNat := by
      change (d4.strstart + d2.match_length).toNat = _
      rw [UInt32.toNat_add, ss4, Nat.mod_eq_of_lt (by have := shape.room; omega)]
    have ld5 : ldDeflateState (some (.tab ds)) h5 = .ok (d5, h5) := ldDeflateState_tab good5.live.hs
    have getW5 : h5.bytes w1 = some wa1 := by simpa [h5] using getW4
    have win5 : d5.window = .ref (.blk w1) 0 := win4
    have read1 : index8 d5.window d5.strstart.toNat h5 = .ok (bfn wa1 (d.strstart.toNat + d2.match_length.toNat), h5) := by
      rw [win5, ss5]; exact index8_bfn getW5 (by simp) (by omega)
    obtain ⟨c1, c1def⟩ : ∃ x, x = bfn wa1 (d.strstart.toNat + d2.match_length.toNat) := ⟨_, rfl⟩
    rw [← c1def] at read1
    let d6 : DeflateState := { d5 with ins_h := c1.toUInt32 }
    let h6 := setD h5 ds d6
    have wr6 : wr (some (.tab ds)) (fun d => { d with ins_h := c1.toUInt32 }) h5 = .ok ((), h6) := by
      rw [wrD_eq, good5.live.hs]
    have good6 : DGood h6 r ds z d6 := engine_update_good good5 rfl
    have getW6 : h6.bytes w1 = some wa1 := by simpa [h6] using getW5
    have ss5' : (d5.strstart + 1).toNat = d.strstart.toNat + d2.match_length.toNat + 1 := by
      rw [UInt32.toNat_add, ss5]; simp only [show (1 : UInt32).toNat = 1 from rfl]
      rw [Nat.mod_eq_of_lt (by have := shape.room; omega)]
    have read2 : index8 d5.window (d5.strstart + 1).toNat h6 =
        .ok (bfn wa1 (d.strstart.toNat + d2.match_length.toNat + 1), h6) := by
      rw [win5, ss5']; exact index8_bfn getW6 (by simp) (by omega)
    obtain ⟨c2, c2def⟩ : ∃ x, x = bfn wa1 (d.strstart.toNat + d2.match_length.toNat + 1) := ⟨_, rfl⟩
    rw [← c2def] at read2
    have shift6 : d6.hash_shift < 32 := by
      change d4.hash_shift < 32; rw [eHs4, UInt32.lt_iff_toNat_lt]; exact hsh.hsh_lt
    have upd7 := UPDATE_HASH_ok (h := h6) (sr := ds) (d := d6) c2 good6.live.hs shift6
    let d7 : DeflateState := { d6 with ins_h := updHash d6.hash_shift d6.hash_mask d6.ins_h c2 }
    let h7 := setD h6 ds d7
    have upd7' : UPDATE_HASH (some (.tab ds)) c2 h6 = .ok ((), h7) := upd7
    have good7 : DGood h7 r ds z d7 := engine_update_good good6 rfl
    have runB : K (d2.sym_next + 3 == d2.sym_end) h4 =
        lazyTail (some (.tab ds)) st hh (d2.sym_next + 3 == d2.sym_end) h7 := by
      simp only [K, bind_app, ld4, condF, Bool.false_eq_true, ite_false, wrB, ld5, read1, wr6, read2, upd7']
    have fields7 : d7 = { matchRecorded d2 with strstart := d7.strstart, match_length := 0, ins_h := d7.ins_h } := rfl
    have ss7 : d7.strstart.toNat = d.strstart.toNat + d2.match_length.toNat := ss5
    obtain ⟨buffers7, fullCase, notFullCase, level7, kind7, pending7, la7⟩ :=
      fast_match_final (h7 := h7) (d7 := d7) (t7 := d.strstart.toNat + 1)
        (t7le := by omega) (t7lo := by omega)
        head pending search big good4 ledger4 dist4 pbuf2 getB4 buffers4
        static4 borrow4 count4 la4 good7 fields7 ss7 rfl rfl rfl
        (fun i ne => by simp [h7, h6, h5, setD_dstates_ne _ _ _ _ ne]) (fun _ _ => rfl)
        (by
          refine ⟨w1, p1, q1, wa1, pa1, qa1, win1, prev1, head1, by simpa [h7, h6, h5] using hw1,
            by simpa [h7, h6, h5] using hp1, by simpa [h7, h6, h5] using hq1, ?_⟩
          change HashChains _ _ _ d4.hash_size d4.hash_shift d4.hash_mask d4.w_size.toNat _
            (d7.strstart.toNat + d4.lookahead.toNat)
          rw [ss7, la4n]
          have lim : d.strstart.toNat + d2.match_length.toNat + (d.lookahead.toNat - d2.match_length.toNat) =
              d.strstart.toNat + d.lookahead.toNat := by omega
          rw [lim]
          exact chains_mono H1 (Nat.le_refl _) (Nat.le_refl _))
        (fun _ => ⟨w1, wa1, win, by simpa [h7, h6, h5] using getW4, by
          change InsHForm d.hash_shift d.hash_mask (bfn wa1) d7.strstart.toNat
            (updHash d4.hash_shift d4.hash_mask c1.toUInt32 c2)
          rw [ss7, eHs4, eHm4, c1def, c2def]
          exact form_init hsh (bfn wa1) (d.strstart.toNat + d2.match_length.toNat)⟩)
        (d2.sym_next + 3 == d2.sym_end) rfl notFull4
    obtain ⟨st', h', tailRun, brk', z', d', head', acc', laEq', _, gzEq', cases⟩ := lazy_tail_stepQ fast_kind_keep st hh
      (d2.sym_next + 3 == d2.sym_end) buffers7 head.out head.input level7 kind7 ((keys4.trans ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ : Keys d d7).safe head.safe) pending7 fullCase notFullCase
    have pre : Fr h r ds d z h7 z d7 := by
      refine Fr.priv head.inv.good head.buffers ?_ (keys4.trans ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)
      exact ((priv4.trans (priv_setD h4 r ds d d5 good4.live.hs)).trans (priv_setD h5 r ds d d6 good5.live.hs)).trans
        (priv_setD h6 r ds d d7 good6.live.hs)
    refine ⟨st', h', (emit.trans runB).trans tailRun, brk', z', d', head', Fr.trans head.inv.good head.buffers pre acc',
      by rw [laEq', la7]; omega, by rw [gzEq', fields7]; show d2.gzindex = d.gzindex; rw [upd], cases⟩


/-- One search and emission of `deflate_fast` (`fast_iter`), with the lookahead and `gzindex`. -/
theorem fast_iterQ {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream}
    {d : DeflateState} (head : Head FastKind h r ds z d) (pending : d.pending = 0)
    (look : 1 ≤ d.lookahead.toNat) (room : d.strstart.toNat + 262 ≤ d.window_size.toNat) (st : LoopS) :
    ∃ st' h', (do
        let hash_head ← fastSearch (some (.tab ds))
        fastEmit (some (.tab ds)) st hash_head) h = .ok (st', h') ∧ st'.brk = st.brk ∧
      ∃ z' d', Head FastKind h' r ds z' d' ∧ Fr h r ds d z h' z' d' ∧
        d'.lookahead.toNat < d.lookahead.toNat ∧ d'.gzindex = d.gzindex ∧
        ((st'.ret = st.ret ∧ d'.pending = 0) ∨ (st'.ret = some need_more ∧ z'.avail_out = 0)) := by
  obtain ⟨hh, h2, d2, searchRun, search⟩ := fast_search_run head look room
  by_cases big : 3 ≤ d2.match_length.toNat
  · obtain ⟨st', h', emitRun, rest⟩ := fast_match_emitQ head pending room search big st hh
    exact ⟨st', h', by simp only [bind_app, searchRun]; exact emitRun, rest⟩
  · obtain ⟨st', h', emitRun, rest⟩ := fast_literal_emitQ head pending look search (by omega) st hh
    exact ⟨st', h', by simp only [bind_app, searchRun]; exact emitRun, rest⟩

set_option maxHeartbeats 2400000 in
/-- **One iteration of `deflate_fast`** with no input. -/
theorem fast_body_q {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (head : Head FastKind h r ds z d) (pending : d.pending = 0) (empty : z.avail_in = 0)
    (flush : Int32) (st : LoopS) (brk : st.brk = false) (ret : st.ret = none) :
    ∃ st' h', deflate_fast_body (some (.tab ds)) flush st h = .ok (st', h') ∧
      QStep FastKind r ds flush z d st st' h' := by
  have rdLook : rd (some (.tab ds)) (·.lookahead) h = .ok (d.lookahead, h) := by
    simp [rdD_eq, head.inv.good.live.hs]
  have finishIter : ∀ {h1 : Heap} {z1 : ZStream} {d1 : DeflateState}, Head FastKind h1 r ds z1 d1 →
      QDown z d z1 d1 → d1.pending = 0 → 1 ≤ d1.lookahead.toNat →
      d1.strstart.toNat + 262 ≤ d1.window_size.toNat →
      ∃ st' h', (do
          let hash_head ← fastSearch (some (.tab ds))
          fastEmit (some (.tab ds)) st hash_head) h1 = .ok (st', h') ∧ QStep FastKind r ds flush z d st st' h' := by
    intro h1 z1 d1 head1 down1 pending1 look1 room1
    obtain ⟨st', h', iterRun, brk', z', d', head', fr', la', gz', cases⟩ := fast_iterQ head1 pending1 look1 room1 st
    exact ⟨st', h', iterRun, qstep_of_iter down1 fr' head'
      (work_lt_noLazy head1.level head'.level (idle_of_low head'.inv.shape head'.kind.2.1) la')
      gz' brk' brk ret cases⟩
  rw [fast_body_source]
  by_cases small : d.lookahead < MIN_LOOKAHEAD_u
  · have short : d.lookahead.toNat < 262 := UInt32.lt_iff_toNat_lt.mp small
    obtain ⟨after1, z1, d1, fillRun, inv1, buffers1, post⟩ :=
      fill_window_inv head.inv head.level head.buffers head.input short
    obtain ⟨sLevel, sStrategy, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := post.same
    have head1 : Head FastKind after1 r ds z1 d1 :=
      head_after_fill head inv1 buffers1 post (fun k => by unfold FastKind; rw [sStrategy, sLevel]; exact k)
    obtain ⟨down1, _, _, la1, pending1⟩ := fill_down post empty pending head.level
    have rdLook1 : rd (some (.tab ds)) (·.lookahead) after1 = .ok (d1.lookahead, after1) := by
      simp [rdD_eq, inv1.good.live.hs]
    have room1 := fill_room post
    have fillRun' : fill_window (some (.tab ds)) h = .ok ((), after1) := fillRun
    by_cases stop1 : (d1.lookahead < MIN_LOOKAHEAD_u && flush == Z_NO_FLUSH) = true
    · have noFlush : flush = Z_NO_FLUSH := by
        simp only [Bool.and_eq_true, beq_iff_eq] at stop1; exact stop1.2
      refine ⟨{ st with ret := some need_more }, after1, ?_, z1, d1, head1, down1,
        Or.inr (Or.inl ⟨rfl, Or.inr ⟨pending1, noFlush⟩⟩)⟩
      simp only [bind_app, rdLook, M_ite_app, small, ite_true, fillRun', rdLook1, stop1]
      rfl
    · have stop1F : (d1.lookahead < MIN_LOOKAHEAD_u && flush == Z_NO_FLUSH) = false := by simpa using stop1
      by_cases empty1 : d1.lookahead = 0
      · have empty1B : (d1.lookahead == 0) = true := by simp [empty1]
        refine ⟨{ st with brk := true }, after1, ?_, z1, d1, head1, down1,
          Or.inr (Or.inr ⟨rfl, ret, pending1, empty1⟩)⟩
        simp only [bind_app, rdLook, M_ite_app, small, ite_true, fillRun', rdLook1, stop1F,
          Bool.false_eq_true, ite_false, empty1B]
        rfl
      · have empty1B : (d1.lookahead == 0) = false := by simpa using empty1
        have look1 : 1 ≤ d1.lookahead.toNat := by
          have : d1.lookahead.toNat ≠ 0 := fun e => empty1 (UInt32.toNat_inj.mp e)
          omega
        obtain ⟨st', h', iterRun, step⟩ := finishIter head1 down1 pending1 look1 room1
        refine ⟨st', h', ?_, step⟩
        simp only [bind_app, rdLook, M_ite_app, small, ite_true, fillRun', rdLook1, stop1F,
          Bool.false_eq_true, ite_false, empty1B]
        simp only [bind_app] at iterRun
        exact iterRun
  · have big : 262 ≤ d.lookahead.toNat := by
      have := small; rw [UInt32.lt_iff_toNat_lt] at this; change ¬ _ < 262 at this; omega
    have room := head.inv.shape.room
    obtain ⟨st', h', iterRun, step⟩ := finishIter head (QDown.refl pending) pending (by omega) (by omega)
    refine ⟨st', h', ?_, step⟩
    simp only [bind_app, rdLook, M_ite_app, small, ite_false]
    simp only [bind_app] at iterRun
    exact iterRun

/-- **`deflate_fast` with no input** lowers the work term. -/
theorem fast_q {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream}
    {d : DeflateState} (safe : FlushSafeAt d.lit_bufsize.toNat) (inv : DInv h r ds z d) (entry : StratIn h r z d)
    (flush : Int32) (fast : 1 ≤ d.level.toInt ∧ d.level.toInt ≤ 3 ∧ d.strategy.toInt ≠ 2 ∧ d.strategy.toInt ≠ 3)
    (empty : z.avail_in = 0) :
    ∃ bstate after z' d', C.run (Zlib.Deflate.deflate_fast (some (.tab ds)) flush) h = .ok (bstate, after) ∧
      r.get after = some z' ∧ after.dstates ds = some d' ∧ QEnd flush z d z' d' bstate := by
  have level : d.level ≠ 0 := by
    intro zero; have := fast.1; rw [zero] at this; exact absurd this (by decide)
  have head : Head FastKind h r ds z d := ⟨inv, entry.buffers, entry.out, entry.input, level, fast, safe⟩
  obtain ⟨st, h1, loopRun, ⟨z1, d1, head1, down1, cases⟩, exit⟩ :=
    q_loop (deflate_fast_body (some (.tab ds)) flush) flush head entry.pending empty
      (fun st _ _ _ hd p e b r => fast_body_q hd p e flush st b r)
  rcases cases with ⟨brk, ret0, _⟩ | ⟨ret, why⟩ | ⟨brk, ret, pending1, empty1⟩
  · rcases exit with e | e
    · rw [brk] at e; cases e
    · rw [ret0] at e; cases e
  · refine ⟨need_more, h1, z1, d1, ?_, head1.inv.good.live.hz, head1.inv.good.live.hs, QEnd.more_of down1 why⟩
    simp [C.run, deflate_fast, bind_app, loopRun, ret]
  · obtain ⟨wrRun, head2⟩ := set_insert_head head1 empty1 (fun _ k => k)
    obtain ⟨bstate, after, z', d', tailRun, hz', hs', fin⟩ := finish_tail_q head2 pending1 flush
      (idle_of_low head1.inv.shape head1.kind.2.1 : d1.match_available = 0) empty1
    refine ⟨bstate, after, z', d', ?_, hz', hs', QEnd.after down1 (QEnd.after (insert_down pending1 _) fin)⟩
    simp only [C.run, deflate_fast, bind_app, loopRun, ret, wrRun]
    exact tailRun

/-! ## `deflate_slow` -/

/-- A step that keeps the lazy literal and consumes lookahead lowers the work term. -/
theorem work_lt_keepLazy {d d' : DeflateState} (lv : d.level ≠ 0) (lv' : d'.level ≠ 0)
    (ma : d'.match_available = d.match_available) (la : d'.lookahead.toNat < d.lookahead.toNat) :
    Quiet.work d' < Quiet.work d := by
  rw [work_nz lv, work_nz lv', ma]
  have := sym_ind_le d'
  omega

/-- A step that marks a lazy literal, consumes lookahead and records no symbol lowers the work term. -/
theorem work_lt_mark {d d' : DeflateState} (lv : d.level ≠ 0) (lv' : d'.level ≠ 0)
    (sym : d'.sym_next = d.sym_next) (la : d'.lookahead.toNat < d.lookahead.toNat) :
    Quiet.work d' < Quiet.work d := by
  rw [work_nz lv, work_nz lv', sym]
  have := ma_ind_le d'
  omega

/-- Recording the last lazy literal lowers the work term. -/
theorem work_lt_end {d d' : DeflateState} (lv : d.level ≠ 0) (lv' : d'.level ≠ 0)
    (la : d'.lookahead = d.lookahead) (ma' : d'.match_available = 0) (ma : d.match_available ≠ 0) :
    Quiet.work d' < Quiet.work d := by
  rw [work_nz lv, work_nz lv', la, ma', if_neg ma]
  have := sym_ind_le d'
  simp only [if_pos]
  omega

set_option maxHeartbeats 16000000 in
/-- **A literal is pending and no match is emitted**: the byte at `strstart - 1` is tallied, the
block flushed when the symbol buffer is full, and the step moves past `strstart`. -/
theorem slow_pendingQ {h h2 : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream}
    {d d2 : DeflateState} (head : Head SlowKind h r ds z d) (pending : d.pending = 0)
    (look : 1 ≤ d.lookahead.toNat) (out : SlowOut h h2 r ds z d d2)
    (noMatch : ¬ (3 ≤ d2.prev_length.toNat ∧ d2.match_length.toNat ≤ d2.prev_length.toNat))
    (avail : d2.match_available ≠ 0) (st : LoopS) (hh : UInt32) :
    ∃ st' h', slowPending (some (.tab ds)) st hh d2 h2 = .ok (st', h') ∧ st'.brk = st.brk ∧
      ∃ z' d', Head SlowKind h' r ds z' d' ∧ Fr h r ds d z h' z' d' ∧
        Quiet.work d' < Quiet.work d ∧ d'.gzindex = d.gzindex ∧
        ((st'.ret = st.ret ∧ d'.pending = 0) ∨ (st'.ret = some need_more ∧ z'.avail_out = 0)) := by
  have inv := head.inv
  have shape := inv.shape
  have upd := out.update
  have level := head.level
  have kind := head.kind
  have wsHi := (slide_window_sizes inv.good).2
  have wsz := inv.good.inv.wsz
  have ssLt := d.strstart.toNat_lt
  have room := shape.room
  have eMa : d2.match_available = d.match_available := out.available
  have one : d.match_available = 1 := by
    rcases shape.matchAvailable with e | e
    · rw [← eMa] at e; exact absurd e avail
    · exact e
  have s1 : 1 ≤ d.strstart.toNat := shape.available (by rw [one]; decide)
  have eSs := out.strstart
  have eLa := out.lookahead
  have eIns := out.insert
  obtain ⟨w, wa, win, getW, sizeW⟩ := window_block inv.good
  have getW2 : h2.bytes w = some wa := by rw [out.bytes]; exact getW
  have win2 : d2.window = .ref (.blk w) 0 := by rw [upd]; exact win
  have back : (d2.strstart - 1).toNat = d.strstart.toNat - 1 := by
    rw [eSs]; exact UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by simpa using s1))
  have readC : index8 d2.window (d2.strstart - 1).toNat h2 = .ok (bfn wa (d.strstart.toNat - 1), h2) := by
    rw [win2, back]; exact index8_bfn getW2 (by simp) (by omega)
  obtain ⟨c, cdef⟩ : ∃ x, x = bfn wa (d.strstart.toNat - 1) := ⟨_, rfl⟩
  rw [← cdef] at readC
  -- the symbols of the block, on the heap after the search
  obtain ⟨⟨xs, ⟨b, buf, pbuf, getB, ledger⟩, dist⟩, clear, below⟩ := inv.symbols
  have pbuf2 : d2.pending_buf = .ref (.blk b) 0 := by rw [upd]; exact pbuf
  have getB2 : h2.bytes b = some buf := by rw [out.bytes]; exact getB
  have trees2 : TreesInvAt h2 ds d2 b buf := trees_at_of_good out.good pbuf2 getB2
  have ledger2 : SymbolLedger buf d2 xs := by rw [upd]; exact ledger.keep rfl rfl rfl rfl
  have strict2 : d2.sym_next.toNat < d2.sym_end.toNat := by
    rw [show d2.sym_next = d.sym_next by rw [upd], show d2.sym_end = d.sym_end by rw [upd]]; exact shape.symRoom
  have roomT := literal_room out.good.inv strict2
  have tallyRun := tally_literal_run trees2.base c roomT
  let X := literalState d2 c
  obtain ⟨h3, h3def⟩ : ∃ x, x = setD (Zlib.Trees.Proofs.Out.setB h2 b (literalBytes buf d2 c)) ds X := ⟨_, rfl⟩
  rw [← h3def] at tallyRun
  have good3 : DGood h3 r ds z X := by rw [h3def]; exact literal_good_after out.good trees2 c roomT
  have getB3 : h3.bytes b = some (literalBytes buf d2 c) := by rw [h3def]; simp [Zlib.Trees.Proofs.Out.setB]
  have trees3 : TreesInvAt h3 ds X b (literalBytes buf d2 c) := trees_at_of_good good3 pbuf2 getB3
  have ledger3 := ledger_literal trees2.base ledger2 roomT c
  have count3 := literal_count trees2.base roomT c
  have buffers2 : StreamBuffers h2 r := by
    obtain ⟨wn, pv, hd, pb⟩ : d2.window = d.window ∧ d2.prev = d.prev ∧ d2.head = d.head ∧
        d2.pending_buf = d.pending_buf := by rw [upd]; exact ⟨rfl, rfl, rfl, rfl⟩
    exact stream_buffers_private_read inv.good.live.hz out.good.live.hz head.buffers out.frame
      (fun i mine => (stream_owned_deflate inv.good i).mpr (Or.inl mine))
      (stream_owned_keys inv.good out.good wn pv hd pb) (stream_accounting_self z) out.borrow
  have buffers3 : StreamBuffers h3 r := by
    rw [h3def]; rw [h3def] at good3
    exact private_write_buffers out.good buffers2 pbuf2 ⟨rfl, rfl, rfl, rfl⟩ good3
  have wb : w ≠ b := by
    obtain ⟨w0, p0, q0, b0, blocks⟩ := inv.good.inv.blocks
    have we : w0 = w := by simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.win.symm
    have be : b0 = b := by simpa only [pbuf, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.pbuf.symm
    subst w0 b0; exact blocks.wb
  have getW3 : h3.bytes w = some wa := by
    rw [h3def]; simp [Zlib.Trees.Proofs.Out.setB, upd_ne _ _ _ _ wb, getW2]
  have chains3 : HeapChains h3 X (if 3 ≤ d.lookahead.toNat then d.strstart.toNat + 1 else chainTop d) := by
    rw [h3def]; exact pending_write_chains out.good out.chains pbuf2 _ c
  have static3 : h3.static = h.static := by rw [h3def]; exact out.frame.static
  have ld2 : ldDeflateState (some (.tab ds)) h2 = .ok (d2, h2) := ldDeflateState_tab out.good.live.hs
  have keys2 : Keys d d2 := by rw [upd]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have priv3 : PrivStep h h3 r ds d := by
    refine out.priv.trans ?_
    rw [h3def]
    exact (priv_tally out.good pbuf2 _ X).keys keys2
  have back2 : d2.strm = some r := by rw [upd]; exact inv.good.live.back
  -- the frontier after the step
  have topOk : ∀ (F : DeflateState), F.strstart.toNat = d.strstart.toNat + 1 → F.lookahead.toNat = d.lookahead.toNat - 1 →
      F.insert = d.insert → (if 3 ≤ d.lookahead.toNat then d.strstart.toNat + 1 else chainTop d) ≤ chainTop F := by
    intro F fs fl fi
    unfold chainTop
    rw [fs, fl, fi]
    by_cases ready : 3 ≤ d.lookahead.toNat
    · rw [if_pos ready]
      have z0 : d.insert.toNat = 0 := by rw [shape.insertDone ready]; rfl
      omega
    · rw [if_neg ready]; omega
  have formOk : ∀ (F : DeflateState) (hF : Heap), F.window = d.window → hF.bytes w = some wa →
      F.strstart.toNat = d.strstart.toNat + 1 → F.lookahead.toNat = d.lookahead.toNat - 1 →
      F.hash_shift = d.hash_shift → F.hash_mask = d.hash_mask → F.ins_h = d2.ins_h →
      F.strategy.toInt ≠ 2 → F.strategy.toInt ≠ 3 → 3 ≤ F.lookahead.toNat → RollingHash hF F := by
    intro F hF fw get fs fl fsh fm fih _ _ large
    rw [fl] at large
    obtain ⟨w0, wa0, win0, get0, form⟩ := out.form (by omega)
    have wid : w0 = w := by simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using win0.symm
    subst w0
    have aid : wa0 = wa := Option.some.inj (get0.symm.trans getW)
    subst aid
    refine ⟨w, wa0, by rw [fw]; exact win, get, ?_⟩
    rw [fs, fsh, fm, fih]; exact form
  have zero : d.«matches» = 0 := shape.slides.2 level
  have flagEnd : ∀ (flag : Bool) (hF : Heap) (zF : ZStream) (F : DeflateState), Head SlowKind hF r ds zF F → Fr h r ds d z hF zF F →
      zF.avail_in = z.avail_in → F.lookahead.toNat = d.lookahead.toNat - 1 → r.get hF = some zF →
      (zF.avail_out ≠ 0 → F.pending = 0) → F.match_available = d.match_available → F.gzindex = d.gzindex →
      ∃ st' h', (do
          if (← zrd d2.strm (·.avail_out)) == 0 then return { st with hash_head := hh, bflush := flag, ret := some need_more }
          return { st with hash_head := hh, bflush := flag } : M LoopS) hF = .ok (st', h') ∧ st'.brk = st.brk ∧
        ∃ z' d', Head SlowKind h' r ds z' d' ∧ Fr h r ds d z h' z' d' ∧
          Quiet.work d' < Quiet.work d ∧ d'.gzindex = d.gzindex ∧
          ((st'.ret = st.ret ∧ d'.pending = 0) ∨ (st'.ret = some need_more ∧ z'.avail_out = 0)) := by
    intro flag hF zF F headF accF inF laF getF drainF maF gzF
    have wlt : Quiet.work F < Quiet.work d := work_lt_keepLazy level headF.level maF (by omega)
    have readOut : zrd d2.strm (·.avail_out) hF = .ok (zF.avail_out, hF) := by rw [back2]; simp [zrd_eq, getF]
    by_cases full : zF.avail_out = 0
    · exact ⟨{ st with hash_head := hh, bflush := flag, ret := some need_more }, hF,
        by simp [bind_app, readOut, full], rfl, zF, F, headF, accF, wlt, gzF, Or.inr ⟨rfl, full⟩⟩
    · have fullB : (zF.avail_out == 0) = false := by simpa using full
      refine ⟨{ st with hash_head := hh, bflush := flag }, hF,
        by simp only [bind_app, readOut, fullB, Bool.false_eq_true, ite_false]; rfl, rfl,
        zF, F, headF, accF, wlt, gzF, Or.inl ⟨rfl, drainF full⟩⟩
  have la3 : (advanceState X).lookahead.toNat = d.lookahead.toNat - 1 := by
    show (d2.lookahead - 1).toNat = _; rw [eLa]
    exact UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by simpa using look))
  have ss3 : (advanceState X).strstart.toNat = d.strstart.toNat + 1 := by
    show (d2.strstart + 1).toNat = _; rw [eSs, UInt32.toNat_add]; simp; omega
  cases flagE : (d2.sym_next + 3 == d2.sym_end)
  · -- no flush
    let F := advanceState X
    have state3 : h3.dstates ds = some X := good3.live.hs
    have wrRun : wr (some (.tab ds)) (fun d => { d with strstart := d.strstart + 1, lookahead := d.lookahead - 1 }) h3 =
        .ok ((), setD h3 ds F) := by rw [wrD_eq, state3]; rfl
    have good5 : DGood (setD h3 ds F) r ds z F := engine_update_good good3 rfl
    have shapeF : Shape F := by
      refine slow_shape shape kind level out look noMatch rfl rfl eIns rfl rfl rfl
        (by show d2.match_available = 1; rw [eMa, one])
        (by show d2.level = d.level; rw [upd]) (by show d2.strategy = d.strategy; rw [upd])
        (by show d2.high_water = d.high_water; rw [upd]) (by show d2.window_size = d.window_size; rw [upd])
        (by show d2.w_size = d.w_size; rw [upd]) (by show d2.last_flush = d.last_flush; rw [upd])
        (by show d2.status = d.status; rw [upd]) (by show d2.wrap = d.wrap; rw [upd]) ?_ ?_
        (by show d2.bi_valid.toInt ≤ 7; rw [show d2.bi_valid = d.bi_valid by rw [upd]]; exact shape.biValid)
        (by show d2.pending = 0 → d2.pending_out = d2.pending_buf
            rw [show d2.pending = d.pending by rw [upd], show d2.pending_out = d.pending_out by rw [upd],
              show d2.pending_buf = d.pending_buf by rw [upd]]; exact shape.cursor)
        (literal_not_full trees2 c roomT flagE)
        (by show d2.«matches» = 0; rw [show d2.«matches» = d.«matches» by rw [upd]]; exact zero) (by omega)
      · show d2.block_start.toInt < _
        rw [show d2.block_start = d.block_start by rw [upd], ss3]; have := shape.blockStart; omega
      · show ((advanceState X).strstart.toNat : Int) - d2.block_start.toInt ≤
          258 * (X.sym_next.toNat / 3 : Nat) + d2.match_available.toInt
        rw [ss3, count3, show d2.block_start = d.block_start by rw [upd],
          show d2.sym_next = d.sym_next by rw [upd], eMa, one]
        have span := shape.blockSpan level
        rw [one] at span
        have o1 : (1 : Int32).toInt = 1 := rfl
        rw [o1] at span ⊢
        have div : (d.sym_next.toNat + 3) / 3 = d.sym_next.toNat / 3 + 1 := by omega
        rw [div]; push_cast; omega
    have hashingF : Hashing (setD h3 ds F) F := by
      refine ⟨fun _ => ?_, fun one' => ?_, fun s2 s3 large => ?_⟩
      · obtain ⟨w0, p0, q0, wa0, pa0, qa0, wn0, pv0, hd0, hw0, hp0, hq0, H⟩ := chains3
        refine ⟨w0, p0, q0, wa0, pa0, qa0, wn0, pv0, hd0, hw0, hp0, hq0, ?_⟩
        exact chains_mono H (topOk F ss3 la3 eIns) (by
          change X.strstart.toNat + X.lookahead.toNat ≤ (advanceState X).strstart.toNat + (advanceState X).lookahead.toNat
          rw [ss3, la3]; change d2.strstart.toNat + d2.lookahead.toNat ≤ _; rw [eSs, eLa]; omega)
      · change d2.«matches» = 1 at one'
        rw [show d2.«matches» = d.«matches» by rw [upd], zero] at one'; cases one'
      · exact formOk F (setD h3 ds F) (by show d2.window = d.window; rw [upd]) getW3 ss3 la3
          (by show d2.hash_shift = d.hash_shift; rw [upd]) (by show d2.hash_mask = d.hash_mask; rw [upd]) rfl
          s2 s3 large
    have symbolsF : Symbols (setD h3 ds F) F := by
      refine ⟨⟨xs ++ [({ distance := 0, value := c.toNat } : Symbol)],
          ⟨b, _, pbuf2, getB3, ledger3.keep (result := F) rfl rfl rfl rfl⟩, ?_⟩,
        ⟨fun k hk => by show (X.bl_tree[k]!).fc = 0; rw [show X.bl_tree = d.bl_tree by show d2.bl_tree = d.bl_tree; rw [upd]]; exact clear.bl k hk,
          by show d2.opt_len = 0; rw [show d2.opt_len = d.opt_len by rw [upd]]; exact clear.opt,
          by show d2.static_len = 0; rw [show d2.static_len = d.static_len by rw [upd]]; exact clear.fixed⟩, ?_⟩
      · intro s mem
        rcases List.mem_append.mp mem with old | new
        · show s.distance ≤ d2.w_size.toNat - 262; rw [show d2.w_size = d.w_size by rw [upd]]; exact dist s old
        · simp only [List.mem_singleton] at new; subst new; exact Nat.zero_le _
      · intro b0 off pout _
        change d2.pending_out = _ at pout
        rw [show d2.pending_out = d.pending_out by rw [upd], shape.cursor pending, pbuf] at pout
        simp only [Ptr.ref.injEq, BRef.blk.injEq] at pout
        change off + d2.pending.toNat ≤ d2.lit_bufsize.toNat
        rw [← pout.2, show d2.pending = d.pending by rw [upd], pending]
        exact Nat.zero_le _
    have invF : DInv (setD h3 ds F) r ds z F :=
      ⟨good5, inv.alloc, by unfold LibraryGlobals; show h3.static = _; rw [static3]; exact inv.globals,
        shapeF, hashingF, symbolsF⟩
    have buffersF : StreamBuffers (setD h3 ds F) r :=
      state_write_buffers good3 buffers3 ⟨rfl, rfl, rfl, rfl⟩ good5
    have headF : Head SlowKind (setD h3 ds F) r ds z F :=
      ⟨invF, buffersF, head.out, head.input, by show d2.level ≠ 0; rw [show d2.level = d.level by rw [upd]]; exact level,
        slow_kind_keep d F (by show d2.strategy = d.strategy; rw [upd]) (by show d2.level = d.level; rw [upd]) kind,
        FlushSafeAt.of_lit (by show d2.lit_bufsize = d.lit_bufsize; rw [upd]) head.safe⟩
    obtain ⟨st', h', endRun, brk', cases⟩ := flagEnd false (setD h3 ds F) z F headF
      (Fr.priv head.inv.good head.buffers (priv3.trans (priv_setD h3 r ds d F good3.live.hs))
        (keys2.trans ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)) rfl la3
      good5.live.hz (fun _ => by show d2.pending = 0; rw [show d2.pending = d.pending by rw [upd]]; exact pending)
      (by show d2.match_available = d.match_available; exact eMa) (by show d2.gzindex = d.gzindex; rw [upd])
    refine ⟨st', h', ?_, brk', cases⟩
    unfold slowPending
    simp only [bind_app, readC, tallyRun, flagE, Bool.false_eq_true, ite_false, wrRun]
    simp only [bind_app] at endRun
    exact endRun
  · -- the symbol buffer is full: the block is flushed before the step
    have lax : BlockLax h3 r ds z X b (literalBytes buf d2 c) (xs ++ [({ distance := 0, value := c.toNat } : Symbol)]) := by
      refine ⟨good3, inv.alloc, by unfold LibraryGlobals; rw [static3]; exact inv.globals, trees3, ledger3,
        ⟨fun k hk => by show (X.bl_tree[k]!).fc = 0; rw [show X.bl_tree = d.bl_tree by show d2.bl_tree = d.bl_tree; rw [upd]]; exact clear.bl k hk,
          by show d2.opt_len = 0; rw [show d2.opt_len = d.opt_len by rw [upd]]; exact clear.opt,
          by show d2.static_len = 0; rw [show d2.static_len = d.static_len by rw [upd]]; exact clear.fixed⟩,
        by show d2.pending = 0; rw [show d2.pending = d.pending by rw [upd]]; exact pending,
        by show -(2 : Int) ^ 62 ≤ d2.block_start.toInt; rw [show d2.block_start = d.block_start by rw [upd]]
           exact block_start_low inv level,
        by show d2.block_start.toInt ≤ d2.strstart.toNat; rw [show d2.block_start = d.block_start by rw [upd], eSs]
           exact shape.blockStart,
        by show d2.level ≠ 0; rw [show d2.level = d.level by rw [upd]]; exact level,
        buffers3, head.out, ?_, ?_, ?_⟩
      · show d2.strstart.toNat + d2.lookahead.toNat ≤ d2.window_size.toNat
        rw [eSs, eLa, show d2.window_size = d.window_size by rw [upd]]; exact room
      · show d2.pending = 0 → d2.pending_out = d2.pending_buf
        rw [show d2.pending = d.pending by rw [upd], show d2.pending_out = d.pending_out by rw [upd],
          show d2.pending_buf = d.pending_buf by rw [upd]]; exact shape.cursor
      · show d2.bi_valid.toInt ≤ 7; rw [show d2.bi_valid = d.bi_valid by rw [upd]]; exact shape.biValid
    obtain ⟨produced, h4, z4, R, run4, good4, buffers4, acc4, drained, cursor4, bits4, frame4, matches4,
      clear4, ⟨b4, a4, pb4, get4, ledger4⟩, static4, chainsT4, win4, totalO4, totalI4, buffer4, shape4, keys4⟩ :=
      flush_block_lax lax (FlushSafeAt.of_lit (by show d2.lit_bufsize = d.lit_bufsize; rw [upd]) head.safe) false
    have e := frame4
    unfold Block.FlushFrame at e
    have fS : R.strstart = d2.strstart := (congrArg DeflateState.strstart e).trans rfl
    have fL : R.lookahead = d2.lookahead := (congrArg DeflateState.lookahead e).trans rfl
    have fI : R.insert = d2.insert := (congrArg DeflateState.insert e).trans rfl
    have fH : R.ins_h = d2.ins_h := (congrArg DeflateState.ins_h e).trans rfl
    have fMl : R.match_length = d2.match_length := (congrArg DeflateState.match_length e).trans rfl
    have fMs : R.match_start = d2.match_start := (congrArg DeflateState.match_start e).trans rfl
    have fMa : R.match_available = d2.match_available := (congrArg DeflateState.match_available e).trans rfl
    have fPl : R.prev_length = d2.prev_length := (congrArg DeflateState.prev_length e).trans rfl
    have fLv : R.level = d2.level := (congrArg DeflateState.level e).trans rfl
    have fSt : R.strategy = d2.strategy := (congrArg DeflateState.strategy e).trans rfl
    have fLit : R.lit_bufsize = d2.lit_bufsize := (congrArg DeflateState.lit_bufsize e).trans rfl
    have fHw : R.high_water = d2.high_water := (congrArg DeflateState.high_water e).trans rfl
    have fWs : R.window_size = d2.window_size := (congrArg DeflateState.window_size e).trans rfl
    have fW : R.w_size = d2.w_size := (congrArg DeflateState.w_size e).trans rfl
    have fLf : R.last_flush = d2.last_flush := (congrArg DeflateState.last_flush e).trans rfl
    have fStat : R.status = d2.status := (congrArg DeflateState.status e).trans rfl
    have fWr : R.wrap = d2.wrap := (congrArg DeflateState.wrap e).trans rfl
    have fBs : R.block_start = d2.strstart.toUInt64.toInt64 := (congrArg DeflateState.block_start e).trans rfl
    have fEnd : R.sym_end = d2.sym_end := (congrArg DeflateState.sym_end e).trans rfl
    have fGz : R.gzindex = d2.gzindex := (congrArg DeflateState.gzindex e).trans rfl
    have fWin : R.window = d2.window := (congrArg DeflateState.window e).trans rfl
    have fHs : R.hash_shift = d2.hash_shift := (congrArg DeflateState.hash_shift e).trans rfl
    have fHm : R.hash_mask = d2.hash_mask := (congrArg DeflateState.hash_mask e).trans rfl
    have fPb : R.pending_buf = d2.pending_buf := (congrArg DeflateState.pending_buf e).trans rfl
    have fWb : R.w_bits = d2.w_bits := (congrArg DeflateState.w_bits e).trans rfl
    have symZero : R.sym_next = 0 := by
      have := ledger4.count; simp at this; exact UInt32.toNat_inj.mp (by rw [this]; rfl)
    let F := advanceState R
    have state4 : h4.dstates ds = some R := good4.live.hs
    have wrRun : wr (some (.tab ds)) (fun d => { d with strstart := d.strstart + 1, lookahead := d.lookahead - 1 }) h4 =
        .ok ((), setD h4 ds F) := by rw [wrD_eq, state4]; rfl
    have good5 : DGood (setD h4 ds F) r ds z4 F := engine_update_good good4 rfl
    have ssF : F.strstart.toNat = d.strstart.toNat + 1 := by
      show (R.strstart + 1).toNat = _; rw [fS, eSs, UInt32.toNat_add]; simp; omega
    have laF : F.lookahead.toNat = d.lookahead.toNat - 1 := by
      show (R.lookahead - 1).toNat = _; rw [fL, eLa]
      exact UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by simpa using look))
    have bsF : F.block_start.toInt = d.strstart.toNat := by
      show R.block_start.toInt = _; rw [fBs, eSs]; exact u32_toInt64_toInt _
    have shapeF : Shape F := by
      refine slow_shape shape kind level out look noMatch (by show R.strstart + 1 = _; rw [fS])
        (by show R.lookahead - 1 = _; rw [fL]) (by show R.insert = _; rw [fI, eIns])
        (by show R.prev_length = _; rw [fPl]) (by show R.match_length = _; rw [fMl])
        (by show R.match_start = _; rw [fMs]) (by show R.match_available = 1; rw [fMa, eMa, one])
        (by show R.level = d.level; rw [fLv, upd]) (by show R.strategy = d.strategy; rw [fSt, upd])
        (by show R.high_water = d.high_water; rw [fHw, upd]) (by show R.window_size = d.window_size; rw [fWs, upd])
        (by show R.w_size = d.w_size; rw [fW, upd]) (by show R.last_flush = d.last_flush; rw [fLf, upd])
        (by show R.status = d.status; rw [fStat, upd]) (by show R.wrap = d.wrap; rw [fWr, upd])
        (by rw [bsF, ssF]; omega) ?_ (by show R.bi_valid.toInt ≤ 7; omega) cursor4
        (by show R.sym_next.toNat < R.sym_end.toNat
            rw [symZero, fEnd, show d2.sym_end = d.sym_end by rw [upd]]; have := shape.symRoom; simp; omega)
        matches4 (by omega)
      rw [bsF, ssF]
      show _ ≤ 258 * (R.sym_next.toNat / 3 : Nat) + R.match_available.toInt
      rw [symZero, fMa, eMa, one]
      have o1 : (1 : Int32).toInt = 1 := rfl
      rw [o1]; simp; omega
    have getW4 : h4.bytes w = some wa := by rw [win4 w (by show d2.window = _; rw [upd]; exact win)]; exact getW3
    have hashingF : Hashing (setD h4 ds F) F := by
      refine ⟨fun _ => ?_, fun one' => ?_, fun s2 s3 large => ?_⟩
      · obtain ⟨w0, p0, q0, wa0, pa0, qa0, wn0, pv0, hd0, hw0, hp0, hq0, H⟩ := chainsT4 _ chains3
        refine ⟨w0, p0, q0, wa0, pa0, qa0, wn0, pv0, hd0, hw0, hp0, hq0, ?_⟩
        refine chains_mono H (topOk F ssF laF (by show R.insert = _; rw [fI, eIns])) (by
          change R.strstart.toNat + R.lookahead.toNat ≤ F.strstart.toNat + F.lookahead.toNat
          rw [ssF, laF, fS, fL, eSs, eLa]; omega)
      · change R.«matches» = 1 at one'
        rw [matches4] at one'; cases one'
      · exact formOk F (setD h4 ds F) (by show R.window = d.window; rw [fWin, upd]) getW4 ssF laF
          (by show R.hash_shift = d.hash_shift; rw [fHs, upd]) (by show R.hash_mask = d.hash_mask; rw [fHm, upd])
          (by show R.ins_h = d2.ins_h; rw [fH]) s2 s3 large
    have symbolsF : Symbols (setD h4 ds F) F := by
      refine ⟨⟨[], ⟨b4, a4, pb4, get4, ledger4.keep (result := F) rfl rfl rfl rfl⟩, by simp⟩,
        ⟨clear4.bl, clear4.opt, clear4.fixed⟩, ?_⟩
      intro _ _ _ nonzero
      exact absurd (show F.sym_next = 0 from symZero) nonzero
    have invF : DInv (setD h4 ds F) r ds z4 F :=
      ⟨good5, ⟨acc4.2.2.2.2.2.2.2.1.trans inv.alloc.1, acc4.2.2.2.2.2.2.2.2.1.trans inv.alloc.2⟩,
        by unfold LibraryGlobals; show h4.static = _; rw [static4, static3]; exact inv.globals,
        shapeF, hashingF, symbolsF⟩
    have buffersF : StreamBuffers (setD h4 ds F) r :=
      state_write_buffers good4 buffers4 ⟨rfl, rfl, rfl, rfl⟩ good5
    have inZ : z4.avail_in = z.avail_in := by
      have := acc4.2.2.1; exact UInt32.toNat_inj.mp (by omega)
    have outZ : z4.next_out ≠ .null := by rw [acc4.2.2.2.2.2.1]; exact advance_ne_null _ head.out
    have inputZ : z4.avail_in ≠ 0 → z4.next_in ≠ .null := fun nz => by
      rw [acc4.2.2.2.2.1, advance_zero]; exact head.input (by rw [← inZ]; exact nz)
    have headF : Head SlowKind (setD h4 ds F) r ds z4 F :=
      ⟨invF, buffersF, outZ, inputZ, by show R.level ≠ 0; rw [fLv, show d2.level = d.level by rw [upd]]; exact level,
        slow_kind_keep d F (by show R.strategy = d.strategy; rw [fSt, upd]) (by show R.level = d.level; rw [fLv, upd]) kind,
        FlushSafeAt.of_lit (by show R.lit_bufsize = d.lit_bufsize; rw [fLit, upd]) head.safe⟩
    obtain ⟨st', h', endRun, brk', cases⟩ := flagEnd true (setD h4 ds F) z4 F headF
      (Fr.trans head.inv.good head.buffers
        (Fr.priv head.inv.good head.buffers priv3 (keys2.trans ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ : Keys d X))
        (Fr.trans good3 buffers3 (Fr.flush acc4 totalI4 totalO4 buffer4 shape4 keys4)
          (Fr.priv good4 buffers4 (priv_setD h4 r ds R F state4) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩))) inZ laF
      good5.live.hz (fun full => by
        rcases drained with p0 | a0
        · exact p0
        · exact absurd a0 full)
      (by show R.match_available = d.match_available; rw [fMa, eMa]) (by show R.gzindex = d.gzindex; rw [fGz, upd])
    refine ⟨st', h', ?_, brk', cases⟩
    have run4' : FLUSH_BLOCK_ONLY (some (.tab ds)) 0 h3 = .ok ((), h4) := run4
    unfold slowPending
    simp only [bind_app, readC, tallyRun, flagE, ite_true, run4', wrRun]
    simp only [bind_app] at endRun
    exact endRun

open Zlib.Deflate.BorrowProofs in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **The pending match is emitted**: `_tr_tally_dist` of the match found at `strstart - 1`, the
insertions of its remaining positions, the reset of the lazy state, and the block flush when the
symbol buffer is full. -/
theorem slow_matchQ {h h2 : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream}
    {d d2 : DeflateState} (head : Head SlowKind h r ds z d) (pending : d.pending = 0)
    (out : SlowOut h h2 r ds z d d2)
    (isMatch : 3 ≤ d2.prev_length.toNat ∧ d2.match_length.toNat ≤ d2.prev_length.toNat)
    (st : LoopS) (hh : UInt32) :
    ∃ st' h', (do
        let bflush ← tally_dist (some (.tab ds)) (d2.strstart - 1 - d2.prev_match) (d2.prev_length - MIN_MATCH_u)
        let hh ← slowMatchAdvance (some (.tab ds)) (d2.strstart + d2.lookahead - MIN_MATCH_u) hh
        lazyTail (some (.tab ds)) st hh bflush) h2 = .ok (st', h') ∧ st'.brk = st.brk ∧
      ∃ z' d', Head SlowKind h' r ds z' d' ∧ Fr h r ds d z h' z' d' ∧
        Quiet.work d' < Quiet.work d ∧ d'.gzindex = d.gzindex ∧
        ((st'.ret = st.ret ∧ d'.pending = 0) ∨ (st'.ret = some need_more ∧ z'.avail_out = 0)) := by
  have inv := head.inv
  have shape := inv.shape
  have upd := out.update
  have level := head.level
  have kind := head.kind
  have wsHi := (slide_window_sizes inv.good).2
  have room := shape.room
  have ssLt := d.strstart.toNat_lt
  have big : 3 ≤ d.match_length.toNat := by rw [← out.prevLength]; exact isMatch.1
  obtain ⟨dlo, dhi, mlLa, insZero, s1⟩ := shape.pendingMatch big
  have mlHi : d.match_length.toNat ≤ 258 := shape.matchLength
  have eSs := out.strstart
  have eLa := out.lookahead
  have ePl := out.prevLength
  have ePm := out.prevMatch
  obtain ⟨w, wa, win, getW, _⟩ := window_block inv.good
  have getW2 : h2.bytes w = some wa := by rw [out.bytes]; exact getW
  -- the record of the match
  obtain ⟨⟨xs, ⟨b, buf, pbuf, getB, ledger⟩, dist⟩, clear, _⟩ := inv.symbols
  have pbuf2 : d2.pending_buf = .ref (.blk b) 0 := by rw [upd]; exact pbuf
  have getB2 : h2.bytes b = some buf := by rw [out.bytes]; exact getB
  have trees2 : TreesInvAt h2 ds d2 b buf := trees_at_of_good out.good pbuf2 getB2
  have ledger2 : SymbolLedger buf d2 xs := by rw [upd]; exact ledger.keep rfl rfl rfl rfl
  have strict2 : d2.sym_next.toNat < d2.sym_end.toNat := by
    rw [show d2.sym_next = d.sym_next by rw [upd], show d2.sym_end = d.sym_end by rw [upd]]; exact shape.symRoom
  have roomT := literal_room out.good.inv strict2
  obtain ⟨dist0, dist0def⟩ : ∃ x, x = d2.strstart - 1 - d2.prev_match := ⟨_, rfl⟩
  obtain ⟨len0, len0def⟩ : ∃ x, x = d2.prev_length - MIN_MATCH_u := ⟨_, rfl⟩
  have distEq : dist0 = d.strstart - 1 - d.match_start := by rw [dist0def, eSs, ePm]
  have dlo0 : 1 ≤ dist0.toNat := by rw [distEq]; exact dlo
  have dhi0 : dist0.toNat ≤ d.w_size.toNat - 262 := by rw [distEq]; exact dhi
  have lenNat : len0.toNat = d.match_length.toNat - 3 := by
    rw [len0def, ePl]
    exact UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by change 3 ≤ _; exact big))
  have tallyRun := tally_match_run trees2.base dist0 len0 dlo0 (by omega) roomT
  have ledger3 := ledger_match trees2.base ledger2 roomT dist0 len0 dlo0 (by omega) (by omega)
  let buf' := matchBytes buf d2 dist0.toUInt16 len0.toUInt8
  let d3 := matchSymbolState d2 dist0 len0
  obtain ⟨h3, h3def⟩ : ∃ x, x = setD (Zlib.Trees.Proofs.Out.setB h2 b buf') ds d3 := ⟨_, rfl⟩
  have tallyRun' : tally_dist (some (.tab ds)) dist0 len0 h2 = .ok (d2.sym_next + 3 == d2.sym_end, h3) := by
    rw [h3def]; exact tallyRun
  have good3 : DGood h3 r ds z d3 := by rw [h3def]; exact match_good_after out.good trees2 dist0 len0 roomT
  have getB3 : h3.bytes b = some buf' := by rw [h3def]; simp [Zlib.Trees.Proofs.Out.setB]
  have wb : w ≠ b := by
    obtain ⟨w0, p0, q0, b0, blocks⟩ := inv.good.inv.blocks
    have we : w0 = w := by simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.win.symm
    have be : b0 = b := by simpa only [pbuf, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.pbuf.symm
    subst w0 b0; exact blocks.wb
  have getW3 : h3.bytes w = some wa := by
    rw [h3def]; simp [Zlib.Trees.Proofs.Out.setB, upd_ne _ _ _ _ wb, getW2]
  have count3 : d3.sym_next.toNat = d.sym_next.toNat + 3 := by
    rw [show d.sym_next = d2.sym_next by rw [upd]]; exact literal_count trees2.base roomT 0
  have buffers2 : StreamBuffers h2 r := by
    obtain ⟨wn, pv, hd, pb⟩ : d2.window = d.window ∧ d2.prev = d.prev ∧ d2.head = d.head ∧
        d2.pending_buf = d.pending_buf := by rw [upd]; exact ⟨rfl, rfl, rfl, rfl⟩
    exact stream_buffers_private_read inv.good.live.hz out.good.live.hz head.buffers out.frame
      (fun i mine => (stream_owned_deflate inv.good i).mpr (Or.inl mine))
      (stream_owned_keys inv.good out.good wn pv hd pb) (stream_accounting_self z) out.borrow
  have buffers3 : StreamBuffers h3 r := by
    rw [h3def]; rw [h3def] at good3
    exact private_write_buffers out.good buffers2 pbuf2 ⟨rfl, rfl, rfl, rfl⟩ good3
  have static3 : h3.static = h.static := by rw [h3def]; exact out.frame.static
  have borrow3 : h3.libcErrorBorrow = h.libcErrorBorrow := by rw [h3def]; exact out.borrow
  -- the chains and the rolling hash before the insertions
  have T3 : HeapChains h3 d3 (if 3 ≤ d.lookahead.toNat then d.strstart.toNat + 1 else chainTop d) := by
    rw [h3def]
    obtain ⟨w', p', q', wa', pa', qa', win', prev', hd', hw', hp', hq', H⟩ :=
      pending_write_chains out.good out.chains pbuf2 buf' 0
    exact ⟨w', p', q', wa', pa', qa', win', prev', hd', hw', hp', hq', H⟩
  have chains3 : HeapChains h3 d3 (min (d3.strstart.toNat + 1) (d3.strstart.toNat + d3.lookahead.toNat - 2)) := by
    apply chains_up T3
    change _ ≤ min (d2.strstart.toNat + 1) (d2.strstart.toNat + d2.lookahead.toNat - 2)
    rw [eSs, eLa]
    by_cases ready : 3 ≤ d.lookahead.toNat
    · rw [if_pos ready]; omega
    · rw [if_neg ready]; unfold chainTop; rw [insZero]
      have z0 : (0 : UInt32).toNat = 0 := rfl
      rw [z0]; omega
  have form3 : d3.strstart.toNat + 1 ≤ d3.strstart.toNat + d3.lookahead.toNat - 3 →
      InsHForm d3.hash_shift d3.hash_mask (bfn wa) (d3.strstart.toNat + 1) d3.ins_h := by
    intro le
    change d2.strstart.toNat + 1 ≤ d2.strstart.toNat + d2.lookahead.toNat - 3 at le
    rw [eSs, eLa] at le
    obtain ⟨w0, wa0, win0, get0, form⟩ := out.form (by omega)
    have wid : w0 = w := by simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using win0.symm
    rw [wid] at get0
    have aid : wa0 = wa := Option.some.inj (get0.symm.trans getW)
    rw [aid] at form
    change InsHForm d2.hash_shift d2.hash_mask (bfn wa) (d2.strstart.toNat + 1) d2.ins_h
    rw [show d2.hash_shift = d.hash_shift by rw [upd], show d2.hash_mask = d.hash_mask by rw [upd], eSs]
    exact form
  -- the insertions and the reset
  obtain ⟨cand, h6, R, advRun, goodR, _, chainsR, winR, getWR, maR, mlR, plR, ssR, laR, endR, roomR, formR,
      keepR, hwR, bytesR, bsR, ltR, dtR, fieldsR, frameR⟩ :=
    slow_match_advance_frontier good3 chains3
      (show d3.window = .ref (.blk w) 0 by change d2.window = _; rw [upd]; exact win) getW3
      (show 3 ≤ d3.prev_length.toNat from isMatch.1)
      (show d3.prev_length.toNat ≤ 258 by change d2.prev_length.toNat ≤ 258; rw [ePl]; exact mlHi)
      (show d3.prev_length.toNat - 1 ≤ d3.lookahead.toNat by
        change d2.prev_length.toNat - 1 ≤ d2.lookahead.toNat; rw [ePl, eLa]; omega)
      (show 3 ≤ d3.strstart.toNat + d3.lookahead.toNat by
        change 3 ≤ d2.strstart.toNat + d2.lookahead.toNat; rw [eSs, eLa]; omega)
      (show d3.strstart.toNat + d3.lookahead.toNat ≤ d3.window_size.toNat by
        change d2.strstart.toNat + d2.lookahead.toNat ≤ d2.window_size.toNat
        rw [eSs, eLa, show d2.window_size = d.window_size by rw [upd]]; exact room)
      form3 hh
  have advRun' : slowMatchAdvance (some (.tab ds)) (d2.strstart + d2.lookahead - MIN_MATCH_u) hh h3 =
      .ok (cand, h6) := advRun
  have keys2 : Keys d d2 := by rw [upd]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have keys3 : Keys d d3 := keys2.trans ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨wP, pP, qP, bP, blocksP⟩ := inv.good.inv.blocks
  obtain ⟨privAdv, eR, getR, keysR⟩ := PrivM.slow_match_advance (r := r) blocksP.prev blocksP.head _ hh h3 cand h6
    ⟨d3, good3.live.hs, keys3⟩ advRun'
  have keysRR : Keys d R := by
    have := goodR.live.hs; rw [getR] at this; cases this; exact keysR
  have pre : Fr h r ds d z h6 z R := by
    refine Fr.priv head.inv.good head.buffers (out.priv.trans ?_) keysRR
    refine PrivStep.trans ?_ privAdv
    rw [h3def]
    exact (priv_tally out.good pbuf2 buf' d3).keys keys2
  have borrowR : h6.libcErrorBorrow = h3.libcErrorBorrow := Zlib.Deflate.BorrowProofs.Private.stable_slowMatchAdvance _ _ _ h3 _ h6 advRun'
  have f : ∀ {β : Type} (g : DeflateState → β),
      (∀ x : DeflateState, g { x with strstart := R.strstart, lookahead := R.lookahead, ins_h := R.ins_h, prev_length := R.prev_length, match_available := 0, match_length := 2 } = g x) → g R = g d3 :=
    fun g hg => (congrArg g fieldsR).trans (hg d3)
  have eLv : R.level = d.level := by rw [f DeflateState.level (fun _ => rfl)]; change d2.level = _; rw [upd]
  have eSt : R.strategy = d.strategy := by rw [f DeflateState.strategy (fun _ => rfl)]; change d2.strategy = _; rw [upd]
  have ePd : R.pending = d.pending := by rw [f DeflateState.pending (fun _ => rfl)]; change d2.pending = _; rw [upd]
  have ePo : R.pending_out = d.pending_out := by
    rw [f DeflateState.pending_out (fun _ => rfl)]; change d2.pending_out = _; rw [upd]
  have ePb : R.pending_buf = d.pending_buf := by
    rw [f DeflateState.pending_buf (fun _ => rfl)]; change d2.pending_buf = _; rw [upd]
  have eEnd : R.sym_end = d.sym_end := by rw [f DeflateState.sym_end (fun _ => rfl)]; change d2.sym_end = _; rw [upd]
  have eSym : R.sym_next = d3.sym_next := f DeflateState.sym_next (fun _ => rfl)
  have eIns : R.insert = d.insert := by
    rw [f DeflateState.insert (fun _ => rfl)]; change d2.insert = _; exact out.insert
  have eBs : R.block_start = d.block_start := by
    rw [f DeflateState.block_start (fun _ => rfl)]; change d2.block_start = _; rw [upd]
  have eWs : R.window_size = d.window_size := by
    rw [f DeflateState.window_size (fun _ => rfl)]; change d2.window_size = _; rw [upd]
  have eW : R.w_size = d.w_size := by rw [f DeflateState.w_size (fun _ => rfl)]; change d2.w_size = _; rw [upd]
  have eWin : R.window = d.window := by rw [f DeflateState.window (fun _ => rfl)]; change d2.window = _; rw [upd]
  have ePv : R.prev = d.prev := by rw [f DeflateState.prev (fun _ => rfl)]; change d2.prev = _; rw [upd]
  have eHd : R.head = d.head := by rw [f DeflateState.head (fun _ => rfl)]; change d2.head = _; rw [upd]
  have eHw : R.high_water = d.high_water := by
    rw [f DeflateState.high_water (fun _ => rfl)]; change d2.high_water = _; rw [upd]
  have eLf : R.last_flush = d.last_flush := by
    rw [f DeflateState.last_flush (fun _ => rfl)]; change d2.last_flush = _; rw [upd]
  have eWr : R.wrap = d.wrap := by rw [f DeflateState.wrap (fun _ => rfl)]; change d2.wrap = _; rw [upd]
  have eStat : R.status = d.status := by rw [f DeflateState.status (fun _ => rfl)]; change d2.status = _; rw [upd]
  have eBv : R.bi_valid = d.bi_valid := by rw [f DeflateState.bi_valid (fun _ => rfl)]; change d2.bi_valid = _; rw [upd]
  have eMt : R.«matches» = d.«matches» := by rw [f DeflateState.«matches» (fun _ => rfl)]; change d2.«matches» = _; rw [upd]
  have eLit : R.lit_bufsize = d3.lit_bufsize := f DeflateState.lit_bufsize (fun _ => rfl)
  have eLt : R.dyn_ltree = d3.dyn_ltree := f DeflateState.dyn_ltree (fun _ => rfl)
  have eDt : R.dyn_dtree = d3.dyn_dtree := f DeflateState.dyn_dtree (fun _ => rfl)
  have eBl : R.bl_tree = d.bl_tree := by rw [f DeflateState.bl_tree (fun _ => rfl)]; change d2.bl_tree = _; rw [upd]
  have eOpt : R.opt_len = d.opt_len := by rw [f DeflateState.opt_len (fun _ => rfl)]; change d2.opt_len = _; rw [upd]
  have eStc : R.static_len = d.static_len := by
    rw [f DeflateState.static_len (fun _ => rfl)]; change d2.static_len = _; rw [upd]
  have eHs : R.hash_shift = d.hash_shift := by
    rw [f DeflateState.hash_shift (fun _ => rfl)]; change d2.hash_shift = _; rw [upd]
  have eHm : R.hash_mask = d.hash_mask := by
    rw [f DeflateState.hash_mask (fun _ => rfl)]; change d2.hash_mask = _; rw [upd]
  have ssR' : R.strstart.toNat = d.strstart.toNat + d.match_length.toNat - 1 := by
    rw [ssR]; change d2.strstart.toNat + (d2.prev_length.toNat - 1) = _; rw [eSs, ePl]; omega
  have laR' : R.lookahead.toNat = d.lookahead.toNat - (d.match_length.toNat - 1) := by
    rw [laR]; change d2.lookahead.toNat - (d2.prev_length.toNat - 1) = _; rw [eLa, ePl]
  have symR : R.sym_next.toNat = d.sym_next.toNat + 3 := by rw [eSym]; exact count3
  have levelR : R.level ≠ 0 := by rw [eLv]; exact level
  have kindR : SlowKind R := slow_kind_keep d R eSt eLv kind
  have pendingR : R.pending = 0 := by rw [ePd]; exact pending
  have buffersR : StreamBuffers h6 r := by
    exact stream_buffers_private_read good3.live.hz goodR.live.hz buffers3 frameR
      (fun i mine => (stream_owned_deflate good3 i).mpr (Or.inl mine))
      (stream_owned_keys good3 goodR (by rw [eWin]; change d.window = d2.window; rw [upd])
        (by rw [ePv]; change d.prev = d2.prev; rw [upd]) (by rw [eHd]; change d.head = d2.head; rw [upd])
        (by rw [ePb]; change d.pending_buf = d2.pending_buf; rw [upd]))
      (stream_accounting_self z) borrowR
  have pbufR : R.pending_buf = .ref (.blk b) 0 := by rw [ePb]; exact pbuf
  have getBR : h6.bytes b = some buf' := by rw [bytesR]; exact getB3
  have ledgerR : SymbolLedger buf' R (xs ++ [⟨dist0.toNat, len0.toNat⟩]) := ledger3.keep eSym eLit eLt eDt
  have treesR : TreesInvAt h6 ds R b buf' := trees_at_of_good goodR pbufR getBR
  have globalsR : LibraryGlobals h6 := by
    unfold LibraryGlobals; rw [frameR.static, static3]; exact inv.globals
  have clearR : BlockInit.BlockClear R := by
    exact ⟨fun k hk => by rw [eBl]; exact clear.bl k hk, by rw [eOpt]; exact clear.opt, by rw [eStc]; exact clear.fixed⟩
  have chainsC : Chains h6 R := by
    unfold Chains chainTop
    rw [eIns, insZero]
    have z0 : (0 : UInt32).toNat = 0 := rfl
    rw [z0, Nat.sub_zero]
    exact chainsR
  have hashingR : Hashing h6 R := by
    refine ⟨fun _ => chainsC, fun one => ?_, fun _ _ large => ⟨w, wa, winR, getWR, formR large⟩⟩
    rw [eMt, shape.slides.2 level] at one; cases one
  have endR' : R.strstart.toNat + R.lookahead.toNat = d.strstart.toNat + d.lookahead.toNat := by
    rw [endR]; change d2.strstart.toNat + d2.lookahead.toNat = _; rw [eSs, eLa]
  have room7 : R.strstart.toNat + R.lookahead.toNat ≤ R.window_size.toNat := by rw [endR', eWs]; exact room
  have ins7 : R.insert.toNat ≤ R.strstart.toNat := by
    rw [eIns, insZero]; exact Nat.zero_le _
  have done7 : 3 ≤ R.lookahead.toNat → R.insert = 0 := fun _ => by rw [eIns]; exact insZero
  have pl7 : R.prev_length.toNat ≤ 258 := by rw [plR]; decide
  have ml7 : R.match_length.toNat ≤ 258 := by rw [mlR]; decide
  have ma7 : R.match_available = 0 ∨ R.match_available = 1 := Or.inl maR
  have bs7 : R.block_start.toInt ≤ R.strstart.toNat := by rw [eBs, ssR']; have := shape.blockStart; omega
  have sb7 : R.sym_next ≠ 0 → R.block_start.toInt < R.strstart.toNat := fun _ => by
    rw [eBs, ssR']; have := shape.blockStart; omega
  have lz7 : 3 ≤ R.prev_length.toNat → 4 ≤ R.level.toInt ∧ R.strategy.toInt ≠ 2 ∧ R.strategy.toInt ≠ 3 ∧
      R.prev_length.toNat < R.match_length.toNat := fun large => absurd large (by rw [plR]; decide)
  have av7 : R.match_available ≠ 0 → 1 ≤ R.strstart.toNat := fun ne => absurd maR ne
  have pm7 : 3 ≤ R.match_length.toNat → 1 ≤ (R.strstart - 1 - R.match_start).toNat ∧
      (R.strstart - 1 - R.match_start).toNat ≤ R.w_size.toNat - 262 ∧
      R.match_length.toNat ≤ R.lookahead.toNat + 1 ∧ R.insert = 0 ∧ 1 ≤ R.strstart.toNat := by
    intro large; rw [mlR] at large; exact absurd large (by decide)
  have fl7 : 1 ≤ R.level.toInt → R.level.toInt ≤ 3 → R.strategy.toInt ≠ 2 → R.strategy.toInt ≠ 3 →
      R.match_length.toNat ≤ 2 ∧ R.prev_length.toNat ≤ 2 :=
    fun _ hi => absurd (show 4 ≤ R.level.toInt by rw [eLv]; exact kind.1) (by omega)
  have hw7 : R.high_water.toNat ≤ R.window_size.toNat := by rw [eHw, eWs]; exact shape.highWater
  have wi7 : R.strstart.toNat + R.lookahead.toNat ≤ R.high_water.toNat := by
    rw [endR', eHw]; exact shape.windowInit
  have lf7 : -2 ≤ R.last_flush.toInt ∧ R.last_flush.toInt ≤ 5 := by rw [eLf]; exact shape.lastFlush
  have hf7 : R.status = INIT_STATE ∨ R.status = GZIP_STATE → R.last_flush = -2 ∨ R.last_flush = -1 := by
    rw [eStat, eLf]; exact shape.headerFlush
  have tr7 : R.wrap.toInt < 0 → R.status = FINISH_STATE := by rw [eWr, eStat]; exact shape.trailer
  have bv7 : R.bi_valid.toInt ≤ 7 := by rw [eBv]; exact shape.biValid
  have cu7 : R.pending = 0 → R.pending_out = R.pending_buf := by rw [ePd, ePo, ePb]; exact shape.cursor
  have sl7 : R.«matches».toNat ≤ 2 ∧ (R.level ≠ 0 → R.«matches» = 0) := by rw [eMt, eLv]; exact shape.slides
  have blockLow : -(2 : Int) ^ 62 ≤ R.block_start.toInt := by rw [eBs]; exact block_start_low inv level
  have distOk : ∀ s ∈ xs ++ [⟨dist0.toNat, len0.toNat⟩], s.distance ≤ R.w_size.toNat - 262 := by
    intro s mem
    rw [eW]
    rcases List.mem_append.mp mem with old | new
    · exact dist s old
    · simp only [List.mem_singleton] at new; subst new; exact dhi0
  have fullCase : (d2.sym_next + 3 == d2.sym_end) = true → ∃ pb buf xs, BlockReady h6 r ds z R pb buf xs :=
    fun _ => ⟨b, buf', _, ⟨goodR, inv.alloc, globalsR, treesR, ledgerR, clearR,
      flushed_shape room7 ins7 done7 pl7 ml7 ma7 (fun zero => absurd zero levelR) av7 pm7 fl7 hw7 wi7 lf7 hf7 tr7
        bv7 cu7 (by rw [eEnd]; have := shape.symRoom; omega) sl7 lz7 (fun nz => absurd maR nz) maR,
      hashingR, pendingR, blockLow, bs7, levelR, buffersR, head.out⟩⟩
  have notFullCase : (d2.sym_next + 3 == d2.sym_end) = false → DInv h6 r ds z R := by
    intro flag
    have strict : R.sym_next.toNat < R.sym_end.toNat := by
      rw [eSym, f DeflateState.sym_end (fun _ => rfl)]; exact literal_not_full trees2 0 roomT flag
    refine ⟨goodR, inv.alloc, globalsR, ⟨room7, ins7, done7, pl7, ml7, ma7, bs7, ?_,
      (fun zero => absurd zero levelR), av7, pm7, fl7, hw7, wi7, lf7, hf7, tr7, bv7, cu7, strict, sl7,
      lz7, sb7, fun nz => absurd maR nz, fun nz => absurd maR nz⟩, hashingR,
      ⟨⟨_, ⟨b, buf', pbufR, getBR, ledgerR⟩, distOk⟩, clearR, ?_⟩⟩
    · intro _
      rw [ssR', symR, eBs, maR]
      have span := shape.blockSpan level
      have avail : d.match_available.toInt ≤ 1 := by
        rcases shape.matchAvailable with e | e <;> rw [e] <;> decide
      have z0 : (0 : Int32).toInt = 0 := rfl
      rw [z0]
      have div : (d.sym_next.toNat + 3) / 3 = d.sym_next.toNat / 3 + 1 := by omega
      rw [div]
      push_cast
      omega
    · intro b0 off pout _
      rw [ePo, shape.cursor pending, ← ePb, pbufR] at pout
      simp only [Ptr.ref.injEq, BRef.blk.injEq] at pout
      rw [← pout.2, pendingR]
      exact Nat.zero_le _
  obtain ⟨st', h', tailRun, brk', z', d', head', acc', laEq', maEq', gzEq', cases⟩ := lazy_tail_stepQ slow_kind_keep st cand
    (d2.sym_next + 3 == d2.sym_end) buffersR head.out head.input levelR kindR (FlushSafeAt.of_lit (by have := goodR.live.hs; rw [getR] at this; cases this; exact keysR.lit) head.safe) pendingR fullCase notFullCase
  refine ⟨st', h', ?_, brk', z', d', head', Fr.trans head.inv.good head.buffers pre acc', ?_, ?_, cases⟩
  · rw [← dist0def, ← len0def]
    simp only [bind_app, tallyRun', advRun']
    exact tailRun
  · exact work_lt_noLazy level head'.level (maEq'.trans maR) (by rw [laEq', laR']; omega)
  · rw [gzEq', f DeflateState.gzindex (fun _ => rfl)]; change d2.gzindex = _; rw [upd]

set_option maxHeartbeats 4000000 in
/-- One search and decision of `deflate_slow` from a loop head with lookahead and matcher room. -/
theorem slow_iterQ {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream}
    {d : DeflateState} (head : Head SlowKind h r ds z d) (pending : d.pending = 0)
    (look : 1 ≤ d.lookahead.toNat) (room : d.strstart.toNat + 262 ≤ d.window_size.toNat)
    (flush : Int32) (st : LoopS) :
    ∃ st' h', (do
        let hash_head ← slowSearch (some (.tab ds))
        slowDecision (some (.tab ds)) flush st hash_head) h = .ok (st', h') ∧ st'.brk = st.brk ∧
      ∃ z' d', Head SlowKind h' r ds z' d' ∧ Fr h r ds d z h' z' d' ∧
        Quiet.work d' < Quiet.work d ∧ d'.gzindex = d.gzindex ∧
        ((st'.ret = st.ret ∧ d'.pending = 0) ∨ (st'.ret = some need_more ∧ z'.avail_out = 0)) := by
  obtain ⟨hh, h2, d2, searchRun, out⟩ := slow_search_run head room
  have ld2 : ldDeflateState (some (.tab ds)) h2 = .ok (d2, h2) := ldDeflateState_tab out.good.live.hs
  have start : ∀ (k : M LoopS) st' h', k h2 = .ok (st', h') →
      (do
        let d ← ldDeflateState (some (.tab ds))
        k) h2 = .ok (st', h') := by
    intro k st' h' run; rw [bind_app, ld2]; exact run
  by_cases sel : 3 ≤ d2.prev_length.toNat ∧ d2.match_length.toNat ≤ d2.prev_length.toNat
  · have selB : (decide (d2.prev_length ≥ MIN_MATCH_u) && decide (d2.match_length ≤ d2.prev_length)) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq, GE.ge, UInt32.le_iff_toNat_le]; exact ⟨sel.1, sel.2⟩
    obtain ⟨st', h', run, rest⟩ := slow_matchQ head pending out sel st hh
    refine ⟨st', h', ?_, rest⟩
    rw [bind_app, searchRun]
    simp only []
    rw [slow_decision_source, bind_app, ld2]
    simp only [selB, ite_true]
    exact run
  · have selB : (decide (d2.prev_length ≥ MIN_MATCH_u) && decide (d2.match_length ≤ d2.prev_length)) = false := by
      cases e : (decide (d2.prev_length ≥ MIN_MATCH_u) && decide (d2.match_length ≤ d2.prev_length))
      · rfl
      · exfalso; apply sel
        simp only [Bool.and_eq_true, decide_eq_true_eq, GE.ge, UInt32.le_iff_toNat_le] at e
        exact ⟨e.1, e.2⟩
    by_cases avail : d2.match_available ≠ 0
    · have availB : (d2.match_available != 0) = true := by simpa using avail
      obtain ⟨st', h', run, rest⟩ := slow_pendingQ head pending look out sel avail st hh
      refine ⟨st', h', ?_, rest⟩
      rw [bind_app, searchRun]
      simp only []
      rw [slow_decision_source, bind_app, ld2]
      simp only [selB, Bool.false_eq_true, ite_false, availB, ite_true]
      exact run
    · have idle : d2.match_available = 0 := by simpa using avail
      have availB : (d2.match_available != 0) = false := by simp [idle]
      obtain ⟨wrRun, invM, buffersM⟩ := slow_mark head look out sel idle
      have upd := out.update
      have headM : Head SlowKind (setD h2 ds (markState d2)) r ds z (markState d2) :=
        ⟨invM, buffersM, head.out, head.input, by show d2.level ≠ 0; rw [upd]; exact head.level,
          slow_kind_keep d (markState d2) (by show d2.strategy = _; rw [upd]) (by show d2.level = _; rw [upd]) head.kind,
          FlushSafeAt.of_lit (by show d2.lit_bufsize = d.lit_bufsize; rw [upd]) head.safe⟩
      refine ⟨{ st with hash_head := hh, bflush := false }, setD h2 ds (markState d2), ?_, rfl,
        z, markState d2, headM,
          Fr.priv head.inv.good head.buffers (out.priv.trans (priv_setD h2 r ds d _ out.good.live.hs))
            (by show Keys d (markState d2); rw [show markState d2 = { d2 with match_available := 1, strstart := d2.strstart + 1, lookahead := d2.lookahead - 1 } from rfl, upd]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩),
          ?_, ?_, Or.inl ⟨rfl, ?_⟩⟩
      · rw [bind_app, searchRun]
        simp only []
        rw [slow_decision_source, bind_app, ld2]
        simp only [selB, Bool.false_eq_true, ite_false, availB, bind_app, wrRun]
        rfl
      · refine work_lt_mark head.level headM.level (by show d2.sym_next = d.sym_next; rw [upd]) ?_
        show (d2.lookahead - 1).toNat < _
        rw [out.lookahead, UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by simpa using look))]
        have one1 : (1 : UInt32).toNat = 1 := rfl
        omega
      · show d2.gzindex = d.gzindex; rw [upd]
      · show d2.pending = 0; rw [upd]; exact pending

set_option maxHeartbeats 2400000 in
/-- **One iteration of `deflate_slow`** with no input. -/
theorem slow_body_q {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (head : Head SlowKind h r ds z d) (pending : d.pending = 0) (empty : z.avail_in = 0)
    (flush : Int32) (st : LoopS) (brk : st.brk = false) (ret : st.ret = none) :
    ∃ st' h', deflate_slow_body (some (.tab ds)) flush st h = .ok (st', h') ∧
      QStep SlowKind r ds flush z d st st' h' := by
  have rdLook : rd (some (.tab ds)) (·.lookahead) h = .ok (d.lookahead, h) := by
    simp [rdD_eq, head.inv.good.live.hs]
  have finishIter : ∀ {h1 : Heap} {z1 : ZStream} {d1 : DeflateState}, Head SlowKind h1 r ds z1 d1 →
      QDown z d z1 d1 → d1.pending = 0 → 1 ≤ d1.lookahead.toNat →
      d1.strstart.toNat + 262 ≤ d1.window_size.toNat →
      ∃ st' h', (do
          let hash_head ← slowSearch (some (.tab ds))
          slowDecision (some (.tab ds)) flush st hash_head) h1 = .ok (st', h') ∧
        QStep SlowKind r ds flush z d st st' h' := by
    intro h1 z1 d1 head1 down1 pending1 look1 room1
    obtain ⟨st', h', iterRun, brk', z', d', head', fr', wlt, gz', cases⟩ := slow_iterQ head1 pending1 look1 room1 flush st
    exact ⟨st', h', iterRun, qstep_of_iter down1 fr' head' wlt gz' brk' brk ret cases⟩
  rw [slow_body_source]
  by_cases small : d.lookahead < MIN_LOOKAHEAD_u
  · have short : d.lookahead.toNat < 262 := UInt32.lt_iff_toNat_lt.mp small
    obtain ⟨after1, z1, d1, fillRun, inv1, buffers1, post⟩ :=
      fill_window_inv head.inv head.level head.buffers head.input short
    obtain ⟨sLevel, sStrategy, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := post.same
    have head1 : Head SlowKind after1 r ds z1 d1 :=
      head_after_fill head inv1 buffers1 post (fun k => by unfold SlowKind; rw [sStrategy, sLevel]; exact k)
    obtain ⟨down1, _, _, la1, pending1⟩ := fill_down post empty pending head.level
    have rdLook1 : rd (some (.tab ds)) (·.lookahead) after1 = .ok (d1.lookahead, after1) := by
      simp [rdD_eq, inv1.good.live.hs]
    have room1 := fill_room post
    have fillRun' : fill_window (some (.tab ds)) h = .ok ((), after1) := fillRun
    by_cases stop1 : (d1.lookahead < MIN_LOOKAHEAD_u && flush == Z_NO_FLUSH) = true
    · have noFlush : flush = Z_NO_FLUSH := by
        simp only [Bool.and_eq_true, beq_iff_eq] at stop1; exact stop1.2
      refine ⟨{ st with ret := some need_more }, after1, ?_, z1, d1, head1, down1,
        Or.inr (Or.inl ⟨rfl, Or.inr ⟨pending1, noFlush⟩⟩)⟩
      simp only [bind_app, rdLook, M_ite_app, small, ite_true, fillRun', rdLook1, stop1]
      rfl
    · have stop1F : (d1.lookahead < MIN_LOOKAHEAD_u && flush == Z_NO_FLUSH) = false := by simpa using stop1
      by_cases empty1 : d1.lookahead = 0
      · have empty1B : (d1.lookahead == 0) = true := by simp [empty1]
        refine ⟨{ st with brk := true }, after1, ?_, z1, d1, head1, down1,
          Or.inr (Or.inr ⟨rfl, ret, pending1, empty1⟩)⟩
        simp only [bind_app, rdLook, M_ite_app, small, ite_true, fillRun', rdLook1, stop1F,
          Bool.false_eq_true, ite_false, empty1B]
        rfl
      · have empty1B : (d1.lookahead == 0) = false := by simpa using empty1
        have look1 : 1 ≤ d1.lookahead.toNat := by
          have : d1.lookahead.toNat ≠ 0 := fun e => empty1 (UInt32.toNat_inj.mp e)
          omega
        obtain ⟨st', h', iterRun, step⟩ := finishIter head1 down1 pending1 look1 room1
        refine ⟨st', h', ?_, step⟩
        simp only [bind_app, rdLook, M_ite_app, small, ite_true, fillRun', rdLook1, stop1F,
          Bool.false_eq_true, ite_false, empty1B]
        simp only [bind_app] at iterRun
        exact iterRun
  · have big : 262 ≤ d.lookahead.toNat := by
      have := small; rw [UInt32.lt_iff_toNat_lt] at this; change ¬ _ < 262 at this; omega
    have room := head.inv.shape.room
    obtain ⟨st', h', iterRun, step⟩ := finishIter head (QDown.refl pending) pending (by omega) (by omega)
    refine ⟨st', h', ?_, step⟩
    simp only [bind_app, rdLook, M_ite_app, small, ite_false]
    simp only [bind_app] at iterRun
    exact iterRun

set_option maxHeartbeats 1600000 in
/-- `finish_tail` from a state ready for a block flush that holds symbols, with the work term. -/
theorem finish_tail_readyQ {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream}
    {d : DeflateState} {buf : Array UInt8} {xs : List Symbol} (ready : BlockReady h r ds z d pb buf xs)
    (safe : FlushSafeAt d.lit_bufsize.toNat) (symbols : d.sym_next ≠ 0) (flush : Int32)
    (quiet : d.match_available = 0) (look0 : d.lookahead = 0) :
    ∃ bstate after z' d', finish_tail (some (.tab ds)) flush h = .ok (bstate, after) ∧
      r.get after = some z' ∧ after.dstates ds = some d' ∧ QEnd flush z d z' d' bstate := by
  have w0 : Quiet.work d = 1 := by
    rw [work_nz ready.level, look0, quiet]; simp [symbols]
  by_cases finish : flush = Z_FINISH
  · obtain ⟨opt, produced, after, z', result, run, invA, buffersA, account, keeps, _, idle, _, choiceT, bits,
      fullOut, totalOutF, bufferF, totalInF, shapeF, keysF, lastF⟩ := flush_block_macro ready safe true
    have run' : FLUSH_BLOCK (some (.tab ds)) 1 h = .ok (opt, after) := run
    have gz := flush_block_gz ready safe true run invA.good.live.hs
    have lvA : result.level ≠ 0 := by rw [keeps.level]; exact ready.level
    have wA : Quiet.work result = 0 := by
      rw [work_nz lvA, keeps.lookahead, keeps.matchAvailable, keeps.symNext, look0, quiet]; simp
    have le : Quiet.work result ≤ Quiet.work d := by rw [wA]; exact Nat.zero_le _
    rcases choiceT rfl with none' | started
    · subst none'
      refine ⟨finish_done, after, z', result, ?_, invA.good.live.hz, invA.good.live.hs,
        ⟨le, fun _ => Or.inr (Or.inl rfl), fun e => absurd e (by decide), gz⟩⟩
      simp [finish_tail, finish, bind_app, run']
    · subst started
      refine ⟨finish_started, after, z', result, ?_, invA.good.live.hz, invA.good.live.hs,
        ⟨le, fun _ => Or.inl rfl, fun e => absurd e (by decide), gz⟩⟩
      simp [finish_tail, finish, bind_app, run']
  · have finishB : (flush == Z_FINISH) = false := by simpa using finish
    have rdSym : rd (some (.tab ds)) (·.sym_next) h = .ok (d.sym_next, h) := by
      simp [rdD_eq, ready.good.live.hs]
    obtain ⟨opt, produced, after, z', result, run, invA, buffersA, account, keeps, _, idleF, choiceF, _, _,
      fullOut, totalOutF, bufferF, totalInF, shapeF, keysF, lastF⟩ := flush_block_macro ready safe false
    have run' : FLUSH_BLOCK (some (.tab ds)) 0 h = .ok (opt, after) := run
    have gz := flush_block_gz ready safe false run invA.good.live.hs
    have lvA : result.level ≠ 0 := by rw [keeps.level]; exact ready.level
    have lt : Quiet.work result < Quiet.work d := by
      rw [work_nz lvA, keeps.lookahead, keeps.matchAvailable, keeps.symNext, look0, quiet, w0]; simp
    rcases choiceF rfl with none' | more
    · subst none'
      refine ⟨block_done, after, z', result, ?_, invA.good.live.hz, invA.good.live.hs,
        ⟨Nat.le_of_lt lt, fun e => absurd e (Nat.ne_of_lt lt), fun e => absurd e (by decide), gz⟩⟩
      simp [finish_tail, finishB, bind_app, rdSym, symbols, run']
    · subst more
      refine ⟨need_more, after, z', result, ?_, invA.good.live.hz, invA.good.live.hs,
        ⟨Nat.le_of_lt lt, fun e => absurd e (Nat.ne_of_lt lt),
          fun _ room => absurd (fullOut (Option.some_ne_none _)) room, gz⟩⟩
      simp [finish_tail, finishB, bind_app, rdSym, symbols, run']

/-- **`deflate_slow` with no input** lowers the work term. -/
theorem slow_q {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream}
    {d : DeflateState} (safe : FlushSafeAt d.lit_bufsize.toNat) (inv : DInv h r ds z d) (entry : StratIn h r z d)
    (flush : Int32) (slow : 4 ≤ d.level.toInt ∧ d.strategy.toInt ≠ 2 ∧ d.strategy.toInt ≠ 3)
    (empty : z.avail_in = 0) :
    ∃ bstate after z' d', C.run (Zlib.Deflate.deflate_slow (some (.tab ds)) flush) h = .ok (bstate, after) ∧
      r.get after = some z' ∧ after.dstates ds = some d' ∧ QEnd flush z d z' d' bstate := by
  have level : d.level ≠ 0 := by
    intro zero; have := slow.1; rw [zero] at this; exact absurd this (by decide)
  have head : Head SlowKind h r ds z d := ⟨inv, entry.buffers, entry.out, entry.input, level, slow, safe⟩
  obtain ⟨st, h1, loopRun, ⟨z1, d1, head1, down1, cases⟩, exit⟩ :=
    q_loop (deflate_slow_body (some (.tab ds)) flush) flush head entry.pending empty
      (fun st _ _ _ hd p e b r => slow_body_q hd p e flush st b r)
  rcases cases with ⟨brk, ret0, _⟩ | ⟨ret, why⟩ | ⟨brk, ret, pending1, empty1⟩
  · rcases exit with e | e
    · rw [brk] at e; cases e
    · rw [ret0] at e; cases e
  · refine ⟨need_more, h1, z1, d1, ?_, head1.inv.good.live.hz, head1.inv.good.live.hs, QEnd.more_of down1 why⟩
    simp [C.run, deflate_slow, bind_app, loopRun, ret]
  · have ld1 : ldDeflateState (some (.tab ds)) h1 = .ok (d1, h1) := ldDeflateState_tab head1.inv.good.live.hs
    by_cases avail : d1.match_available ≠ 0
    · have availB : (d1.match_available != 0) = true := by simpa using avail
      obtain ⟨c, b, buf, xs, h3, readC, tallyRun, state3, ready, symbols, priv3⟩ :=
        slow_end_literal head1 pending1 empty1 avail
      obtain ⟨bstate, after, z', d', tailRun, hz', hs', fin⟩ :=
        finish_tail_readyQ ready head1.safe symbols flush rfl empty1
      have lt : Quiet.work (endState (literalState d1 c)) < Quiet.work d1 :=
        work_lt_end head1.level head1.level rfl rfl avail
      have downE : QDown z1 d1 z1 (endState (literalState d1 c)) :=
        ⟨Nat.le_refl _, Nat.le_of_lt lt, fun e => absurd e (Nat.ne_of_lt lt), rfl⟩
      refine ⟨bstate, after, z', d', ?_, hz', hs', QEnd.after down1 (QEnd.after downE fin)⟩
      have wr1 : wr (some (.tab ds)) (fun d => { d with match_available := 0 }) h3 =
          .ok ((), setD h3 ds { literalState d1 c with match_available := 0 }) := by rw [wrD_eq, state3]
      have wr2 : wr (some (.tab ds)) (fun d => { d with insert := if d.strstart < MIN_MATCH_u - 1 then d.strstart else MIN_MATCH_u - 1 })
          (setD h3 ds { literalState d1 c with match_available := 0 }) =
          .ok ((), setD (setD h3 ds { literalState d1 c with match_available := 0 }) ds (endState (literalState d1 c))) := by
        rw [wrD_eq]; simp; rfl
      simp only [C.run, deflate_slow, bind_app, loopRun, ret, ld1, availB, ite_true, readC, tallyRun, wr1, wr2]
      exact tailRun
    · have idle : d1.match_available = 0 := by simpa using avail
      have availB : (d1.match_available != 0) = false := by simp [idle]
      obtain ⟨wrRun, head2⟩ := set_insert_head head1 empty1 (fun _ k => k)
      obtain ⟨bstate, after, z', d', tailRun, hz', hs', fin⟩ := finish_tail_q head2 pending1 flush idle empty1
      refine ⟨bstate, after, z', d', ?_, hz', hs', QEnd.after down1 (QEnd.after (insert_down pending1 _) fin)⟩
      simp only [C.run, deflate_slow, bind_app, loopRun, ret, ld1, availB, Bool.false_eq_true, ite_false, wrRun]
      exact tailRun

end Zlib.Deflate.Universal

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Universal
set_option autoImplicit false

/-! ## `deflate_stored` -/

/-- The sizes `deflate_stored` computes with. -/
theorem stored_geom {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) :
    512 ≤ d.pending_buf_size.toNat ∧ d.pending_buf_size.toNat ≤ 2 ^ 17 ∧ 512 ≤ d.w_size.toNat ∧
      d.w_size.toNat ≤ 32768 := by
  obtain ⟨w, p, q, b, blocks⟩ := good.inv.blocks
  have psize := blocks.psize
  have lit := good.inv.lit
  have hsize := good.inv.hsize
  have hlo := good.inv.hbits_lo
  have hhi := good.inv.hbits_hi
  have a : 2 ^ 8 ≤ 2 ^ d.hash_bits.toNat := Nat.pow_le_pow_right (by omega) hlo
  have b' : 2 ^ d.hash_bits.toNat ≤ 2 ^ 16 := Nat.pow_le_pow_right (by omega) hhi
  have ws := slide_window_sizes good
  omega

open Zlib.Deflate.Universal in
/-- The work term at level 0: the stored data not yet in a block. -/
theorem work_l0 {d : DeflateState} (l0 : d.level = 0) (shape : Shape d) :
    Zlib.Deflate.Universal.Quiet.work d = d.strstart.toNat - d.block_start.toInt.toNat := by
  have zero := shape.levelZero l0
  have ma : d.match_available = 0 := by
    by_cases e : d.match_available = 0
    · exact e
    · have := (shape.lazyAvail e).1; rw [l0] at this; exact absurd this (by decide)
  unfold Zlib.Deflate.Universal.Quiet.work
  simp [l0, zero.2.1, zero.2.2, ma]

/-- After a loop that stopped short of a last block under `Z_FINISH`, the final block of
`deflate_stored` fills the output: the output room is at most the header and the block. -/
def FinRoom (z : ZStream) (d : DeflateState) : Prop :=
  (z.avail_out.toNat : Int) ≤ (((d.bi_valid.toInt.toNat + 42) / 8 : Nat) : Int) +
    min ((d.strstart.toNat : Int) - d.block_start.toInt)
      (min ((d.pending_buf_size.toNat : Int) - (((d.bi_valid.toInt.toNat + 42) / 8 : Nat) : Int)) 65535)

set_option maxHeartbeats 4000000 in
open Zlib.Deflate.Universal in
/-- **The rest of an iteration.** With the header room (`have = avail_out - hv`), a length within
it whose input part is available, and `left = strstart - block_start`, the break test, the
emission and the direct copies keep the loop invariant; a completed iteration consumes output. -/
theorem stored_restQ {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (buffers : StreamBuffers h r) (pend0 : d.pending = 0)
    (out : z.next_out ≠ .null) (input : z.avail_in ≠ 0 → z.next_in ≠ .null) (level0 : d.level = 0)
    (flush : Int32) (min_block : UInt32) (st : StoredS) (have_ left len : UInt32)
    (haveEq : have_.toNat + (d.bi_valid.toInt.toNat + 42) / 8 = z.avail_out.toNat)
    (leftEq : (left.toNat : Int) = d.strstart.toNat - d.block_start.toInt)
    (lenHave : len.toNat ≤ have_.toNat)
    (lenIn : (len - directLeft left len).toNat ≤ z.avail_in.toNat)
    (empty : z.avail_in = 0) (lenLeft : len.toNat ≤ left.toNat) (mbPos : 0 < min_block.toNat)
    (lenCase : len.toNat = left.toNat ∨ len.toNat = have_.toNat ∨ len.toNat = 65535)
    (mbLe : min_block.toNat + 5 ≤ d.pending_buf_size.toNat) (mbW : min_block.toNat ≤ d.w_size.toNat) :
    ∃ st' g z' d', storedRest (some (.tab ds)) flush (some r) min_block st have_ left len z h = .ok (st', g) ∧
      StoredStep h g r ds z z' d d' ∧ (st'.brk = false → z'.avail_out.toNat < z.avail_out.toNat) ∧
      (st.last = 0 → st'.last ≠ 0 → flush = Z_FINISH ∧ z'.avail_in = 0 ∧ d'.bi_valid.toInt = 0) ∧
      (st'.brk = true → g = h ∧ z' = z ∧ d' = d ∧
        (flush = Z_FINISH → FinRoom z d)) ∧
      (st'.brk = false → Zlib.Deflate.Universal.Quiet.work d' ≤ Zlib.Deflate.Universal.Quiet.work d ∧ (Zlib.Deflate.Universal.Quiet.work d' < Zlib.Deflate.Universal.Quiet.work d ∨ st'.last ≠ 0)) := by
  have good := inv.good
  have shape := inv.shape
  have zero := shape.levelZero level0
  unfold storedRest
  by_cases stop : (len < min_block && ((len == 0 && flush != Z_FINISH) || flush == Z_NO_FLUSH ||
      !(len ≥ left && len - left == z.avail_in))) = true
  · refine ⟨_, h, z, d, by simp only [stop, ite_true]; rfl, ⟨inv, buffers, pend0, out, input, StoredFields.refl d,
      Zlib.Deflate.Universal.Fr.refl inv.good buffers, ⟨fun _ a g => ⟨a, g, rfl⟩, fun _ => rfl⟩⟩,
      fun no => by simp at no, fun zero nz => by exact absurd zero nz, fun _ => ⟨rfl, rfl, rfl, fun fin => ?_⟩,
      fun no => by simp at no⟩
    obtain ⟨s1, s2⟩ := Bool.and_eq_true_iff.mp stop
    have lt1 : len.toNat < min_block.toNat := UInt32.lt_iff_toNat_lt.mp (of_decide_eq_true s1)
    have nlt : len.toNat < left.toNat := by
      rcases Nat.lt_or_ge len.toNat left.toNat with lt | hc
      · exact lt
      · exfalso
        have eqL : len = left := UInt32.toNat_inj.mp (by omega)
        rw [eqL, empty, fin] at s2
        simp [show (Z_FINISH == Z_NO_FLUSH) = false by decide] at s2
    unfold FinRoom
    have bits := inv.bi_valid_le
    have hv6 : (d.bi_valid.toInt.toNat + 42) / 8 ≤ 6 := by omega
    have geo := stored_geom good
    rcases lenCase with c | c | c <;> omega
  · have stopF : (len < min_block && ((len == 0 && flush != Z_FINISH) || flush == Z_NO_FLUSH ||
        !(len ≥ left && len - left == z.avail_in))) = false := by simpa using stop
    have bits := inv.bi_valid_le
    obtain ⟨after, z1, e, runE, goodE, buffersE, accE, fieldsE, pendE, cursorE, bitsE, staticE, _, sizesE,
        winE, prevE, headE, totE, frE⟩ :=
      stored_emit good buffers out pend0 (shape.cursor pend0) bits.2 good.live.back (by omega) len
        (flush == Z_FINISH && (len ≥ left && len - left == z.avail_in))
    have avail1 : z1.avail_out.toNat + (d.bi_valid.toInt.toNat + 42) / 8 = z.avail_out.toNat := accE.2.2.2.1
    have in1 : z1.avail_in.toNat = z.avail_in.toNat := by have := accE.2.2.1; omega
    have globalsE : LibraryGlobals after := by unfold LibraryGlobals; rw [staticE]; exact inv.globals
    have bsE : e.block_start = d.block_start := by rw [fieldsE]
    have ssE : e.strstart = d.strstart := by rw [fieldsE]
    have wsE : e.window_size = d.window_size := by rw [fieldsE]
    have room := shape.room
    obtain ⟨g, z2, runD, stepD, accD, totD, frD⟩ := stored_direct goodE buffersE globalsE (output_valid_after accE out)
      (input_valid_after accE input) (by rw [bsE]; exact zero.1) left len
      (by rw [bsE, ssE]; omega) (by rw [ssE, wsE]; omega) (by omega) (by omega)
    let e2 := { e with block_start := Int64.ofInt (e.block_start.toInt + (directLeft left len).toNat) }
    have dl := directLeft_le left len
    have fields2 : StoredFields d e2 := by
      show e2 = _
      have f1 : StoredFields d e := by unfold StoredFields; rw [fieldsE]
      exact f1.trans rfl
    have bs2 : e2.block_start.toInt = d.block_start.toInt + (directLeft left len).toNat := by
      show (Int64.ofInt (e.block_start.toInt + (directLeft left len).toNat)).toInt = _
      rw [bsE]
      have := d.strstart.toNat_lt
      exact int64_ofInt_toInt _ (by omega) (by omega)
    have shape2 : Shape e2 := shape_stored shape fields2 level0 (by rw [bs2]; omega) (by rw [bs2]; omega)
      (by show e.bi_valid.toInt ≤ 7; omega) (fun _ => cursorE)
    have account := stream_accounting_trans accE accD
    have invG : DInv g r ds z2 e2 := dinv_stored_keep inv stepD.good fields2 shape2 zero.2.2
      (stepD.static.trans staticE)
      (fun w win => by
        rw [stepD.private_ w (Or.inr (Or.inr (Or.inl (by show e.window = _; rw [fieldsE]; exact win))))]
        exact winE w win)
      (fun p prv => by rw [stepD.words]; exact prevE p prv)
      (fun q hd => by rw [stepD.words]; exact headE q hd)
      account.2.2.2.2.2.2.2.1 account.2.2.2.2.2.2.2.2.1
    let all := decide (len ≥ left) && len - left == z.avail_in
    let last : Int32 := if (flush == Z_FINISH && all) = true then 1 else 0
    have run : (if (decide (len < min_block) && (len == 0 && flush != Z_FINISH || flush == Z_NO_FLUSH || !all)) = true
        then (pure { st with len, left, have_, all, brk := true } : M StoredS)
        else (do
          storedEmit (some (.tab ds)) (some r) len last
          let moved ← storedDirect (some (.tab ds)) (some r) left len
          pure { st with last, len := moved.2, left := moved.1, have_, all, brk := false })) h =
        .ok ({ st with last, len := len - directLeft left len, left := directLeft left len, have_, all, brk := false }, g) := by
      dsimp only [all, last]
      simp only [stopF, Bool.false_eq_true, ite_false, bind_app, runE, runD]
      rfl
    refine ⟨_, g, z2, e2, run, ⟨invG, stepD.buffers, by show e.pending = 0; exact pendE,
      output_valid_after account out, input_valid_after account input, fields2, Zlib.Deflate.Universal.Fr.trans good buffers frE frD,
      sizesE.chain stepD.sizes⟩, fun (_ : false = false) => ?_, fun _ nz => ?_, fun no => by simp at no,
      fun _ => ?_⟩
    · have := account.2.2.2.1
      omega
    · change (if (flush == Z_FINISH && all) = true then (1 : Int32) else 0) ≠ 0 at nz
      have yes : (flush == Z_FINISH && all) = true := by
        cases c : (flush == Z_FINISH && all)
        · rw [c] at nz; exact absurd rfl nz
        · rfl
      simp only [all, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at yes
      obtain ⟨fin, ge, eqIn⟩ := yes
      have dlEq : directLeft left len = left := by
        unfold directLeft; rw [if_neg (by rw [GT.gt, UInt32.lt_iff_toNat_lt]; have := UInt32.le_iff_toNat_le.mp ge; omega)]
      refine ⟨fin, ?_, by show e.bi_valid.toInt = 0; exact bitsE⟩
      have a3 := account.2.2.1
      rw [dlEq, eqIn] at a3
      exact UInt32.toNat_inj.mp (by simp; omega)
    · have l2 : e2.level = 0 := by show e.level = 0; rw [fieldsE]; exact level0
      have ss2 : e2.strstart = d.strstart := ssE
      have dlN : (directLeft left len).toNat = len.toNat := by
        unfold directLeft; split
        · rfl
        · rename_i small
          have : ¬ len.toNat < left.toNat := fun c => small (UInt32.lt_iff_toNat_lt.mpr c)
          omega
      have w2 := work_l0 l2 shape2
      have w1 := work_l0 level0 shape
      have bsLo := zero.1
      have bsN := Int.toNat_of_nonneg bsLo
      have bs2N : 0 ≤ e2.block_start.toInt := by rw [bs2]; omega
      have bsN2 := Int.toNat_of_nonneg bs2N
      rw [dlN] at bs2
      have bsHi := shape.blockStart
      rw [w2, w1, ss2]
      by_cases l0 : len.toNat = 0
      · refine ⟨by omega, Or.inr ?_⟩
        have lz : len = 0 := UInt32.toNat_inj.mp (by rw [l0]; rfl)
        have mz : decide (len < min_block) = true := decide_eq_true (UInt32.lt_iff_toNat_lt.mpr (by omega))
        rw [mz, Bool.true_and] at stopF
        change (if (flush == Z_FINISH && all) = true then (1 : Int32) else 0) ≠ 0
        have fz : (flush == Z_FINISH) = true := by
          cases c : (flush == Z_FINISH)
          · rw [lz] at stopF; simp [bne, c] at stopF
          · rfl
        have az : all = true := by
          cases c : all
          · dsimp only [all] at c; rw [c] at stopF; simp at stopF
          · rfl
        rw [fz, az]; decide
      · exact ⟨by omega, Or.inl (by omega)⟩


set_option maxHeartbeats 4000000 in
open Zlib.Deflate.Universal in
/-- **One iteration of the first loop of `deflate_stored`.** -/
theorem stored_iterationQ {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (buffers : StreamBuffers h r) (pend0 : d.pending = 0)
    (out : z.next_out ≠ .null) (input : z.avail_in ≠ 0 → z.next_in ≠ .null) (level0 : d.level = 0)
    (flush : Int32) (min_block : UInt32) (st : StoredS) (empty : z.avail_in = 0) (mbPos : 0 < min_block.toNat)
    (mbLe : min_block.toNat + 5 ≤ d.pending_buf_size.toNat) (mbW : min_block.toNat ≤ d.w_size.toNat) :
    ∃ st' g z' d', storedBody (some (.tab ds)) flush (some r) min_block st h = .ok (st', g) ∧
      StoredStep h g r ds z z' d d' ∧ (st'.brk = false → z'.avail_out.toNat < z.avail_out.toNat) ∧
      (st.last = 0 → st'.last ≠ 0 → flush = Z_FINISH ∧ z'.avail_in = 0 ∧ d'.bi_valid.toInt = 0) ∧
      (st'.brk = true → g = h ∧ z' = z ∧ d' = d ∧ (flush = Z_FINISH → FinRoom z d)) ∧
      (st'.brk = false → Zlib.Deflate.Universal.Quiet.work d' ≤ Zlib.Deflate.Universal.Quiet.work d ∧ (Zlib.Deflate.Universal.Quiet.work d' < Zlib.Deflate.Universal.Quiet.work d ∨ st'.last ≠ 0)) := by
  have good := inv.good
  have shape := inv.shape
  have zero := shape.levelZero level0
  have bits := inv.bi_valid_le
  have hvN := header_bytes_value d.bi_valid bits.1 bits.2
  unfold storedBody
  simp only [bind_app, ldDeflateState_tab good.live.hs, ldZ_eq, good.live.hz]
  by_cases full : z.avail_out < (d.bi_valid.toUInt32 + 42) >>> 3
  · refine ⟨_, h, z, d, by simp only [full, decide_true, ite_true]; rfl,
      ⟨inv, buffers, pend0, out, input, StoredFields.refl d,
      Zlib.Deflate.Universal.Fr.refl inv.good buffers, ⟨fun _ a g => ⟨a, g, rfl⟩, fun _ => rfl⟩⟩,
      fun no => by simp at no, fun zero nz => by exact absurd zero nz, fun _ => ⟨rfl, rfl, rfl, fun _ => ?_⟩,
      fun no => by simp at no⟩
    have fullN : z.avail_out.toNat < ((d.bi_valid.toUInt32 + 42) >>> 3).toNat := UInt32.lt_iff_toNat_lt.mp full
    rw [hvN] at fullN
    unfold FinRoom
    have := d.strstart.toNat_lt
    have := shape.blockStart
    have : (d.bi_valid.toInt.toNat + 42) / 8 ≤ 6 := by have := bits.2; omega
    have := (stored_geom good).1
    omega
  · have fullN : ¬ z.avail_out.toNat < ((d.bi_valid.toUInt32 + 42) >>> 3).toNat :=
      fun c => full (UInt32.lt_iff_toNat_lt.mpr c)
    rw [hvN] at fullN
    have room := shape.room
    have ws := good.inv.wsz
    have wsize := good.inv.wsize
    have wbits := good.inv.wbits_hi
    have wpow : 2 ^ d.w_bits.toNat ≤ 2 ^ 15 := Nat.pow_le_pow_right (by omega) wbits
    obtain ⟨lsubEq, word, _⟩ := Zlib.Deflate.Universal.Block.flush_length_general (d := d) (by omega)
      shape.blockStart (by omega)
    have lsubRun := congrFun lsubEq h
    have leftN : ((Int64.ofInt ((d.strstart.toNat : Int) - d.block_start.toInt)).toUInt64.toUInt32).toNat =
        ((d.strstart.toNat : Int) - d.block_start.toInt).toNat := by
      rw [UInt64.toNat_toUInt32, word]
      apply Nat.mod_eq_of_lt
      omega
    simp only [full, decide_false, Bool.false_eq_true, ite_false, bind_app, lsubRun, pure_app]
    obtain ⟨left, hleft⟩ : ∃ l, l = (Int64.ofInt ((d.strstart.toNat : Int) - d.block_start.toInt)).toUInt64.toUInt32 :=
      ⟨_, rfl⟩
    rw [← hleft]
    rw [← hleft] at leftN
    have leftEq : (left.toNat : Int) = d.strstart.toNat - d.block_start.toInt := by
      rw [leftN]; have := shape.blockStart; omega
    have haveN : (z.avail_out - (d.bi_valid.toUInt32 + 42) >>> 3).toNat + (d.bi_valid.toInt.toNat + 42) / 8 =
        z.avail_out.toNat := by
      rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by rw [hvN]; omega)), hvN]
      omega
    have maxN : MAX_STORED.toNat = 65535 := rfl
    have e0 : z.avail_in.toNat = 0 := by rw [empty]; rfl
    have leftLt : left.toNat < 2 ^ 32 := left.toNat_lt
    by_cases c1 : (decide (left < MAX_STORED) && decide (z.avail_in < MAX_STORED - left)) = true
    · have c1N : left.toNat < 65535 ∧ z.avail_in.toNat < 65535 - left.toNat := by
        simp only [Bool.and_eq_true, decide_eq_true_eq] at c1
        obtain ⟨a, b⟩ := c1
        have a' := UInt32.lt_iff_toNat_lt.mp a
        have b' := UInt32.lt_iff_toNat_lt.mp b
        rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by omega))] at b'
        omega
      have sumN : (left + z.avail_in).toNat = left.toNat + z.avail_in.toNat := by
        rw [UInt32.toNat_add]; omega
      simp only [c1, ite_true]
      by_cases c2 : left + z.avail_in > z.avail_out - (d.bi_valid.toUInt32 + 42) >>> 3
      · simp only [c2, decide_true, ite_true]
        exact stored_restQ inv buffers pend0 out input level0 flush min_block _ _ left _ haveN leftEq
          (Nat.le_refl _) (stored_len_input _ _ _ (by have := UInt32.lt_iff_toNat_lt.mp c2; omega)
            (fun _ => by have := UInt32.lt_iff_toNat_lt.mp c2; omega)) empty
          (by have := UInt32.lt_iff_toNat_lt.mp c2; rw [sumN] at this; omega) mbPos (Or.inr (Or.inl rfl)) mbLe mbW
      · simp only [c2, decide_false, Bool.false_eq_true, ite_false]
        have c2N : ¬ (z.avail_out - (d.bi_valid.toUInt32 + 42) >>> 3).toNat < (left + z.avail_in).toNat :=
          fun c => c2 (UInt32.lt_iff_toNat_lt.mpr c)
        exact stored_restQ inv buffers pend0 out input level0 flush min_block _ _ left _ haveN leftEq
          (by omega) (stored_len_input _ _ _ (by omega) (fun _ => by omega)) empty
          (by rw [sumN]; omega) mbPos (Or.inl (by rw [sumN]; omega)) mbLe mbW
    · simp only [c1, Bool.false_eq_true, ite_false]
      have c1N : ¬ (left.toNat < 65535 ∧ z.avail_in.toNat < 65535 - left.toNat) := by
        intro ⟨a, b⟩
        apply c1
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        refine ⟨UInt32.lt_iff_toNat_lt.mpr (by rw [maxN]; exact a), UInt32.lt_iff_toNat_lt.mpr ?_⟩
        rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by rw [maxN]; omega)), maxN]
        exact b
      by_cases c2 : MAX_STORED > z.avail_out - (d.bi_valid.toUInt32 + 42) >>> 3
      · simp only [c2, decide_true, ite_true]
        exact stored_restQ inv buffers pend0 out input level0 flush min_block _ _ left _ haveN leftEq
          (Nat.le_refl _) (stored_len_input _ _ _ (by have := UInt32.lt_iff_toNat_lt.mp c2; rw [maxN] at this; omega)
            (fun c => absurd c c1N)) empty
          (by
            have := UInt32.lt_iff_toNat_lt.mp c2; rw [maxN] at this
            have : ¬ left.toNat < 65535 := fun lt => c1N ⟨lt, by omega⟩
            omega) mbPos (Or.inr (Or.inl rfl)) mbLe mbW
      · simp only [c2, decide_false, Bool.false_eq_true, ite_false]
        have c2N : ¬ (z.avail_out - (d.bi_valid.toUInt32 + 42) >>> 3).toNat < MAX_STORED.toNat :=
          fun c => c2 (UInt32.lt_iff_toNat_lt.mpr c)
        rw [maxN] at c2N
        exact stored_restQ inv buffers pend0 out input level0 flush min_block _ _ left _ haveN leftEq
          (by rw [maxN]; omega) (stored_len_input _ _ _ (by rw [maxN]; exact Nat.le_refl _) (fun c => absurd c c1N)) empty
          (by
            rw [maxN]
            have : ¬ left.toNat < 65535 := fun lt => c1N ⟨lt, by omega⟩
            omega) mbPos (Or.inr (Or.inr maxN)) mbLe mbW

/-- **The first loop of `deflate_stored` with no input**: it does not raise the work term, an unchanged
work term means no output or a last block, and a stop without a last block under `Z_FINISH` leaves
the output room of `FinRoom`. -/
theorem stored_loopQ {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : Zlib.Deflate.Universal.DInv h r ds z d) (buffers : StreamBuffers h r) (pend0 : d.pending = 0)
    (out : z.next_out ≠ .null) (input : z.avail_in ≠ 0 → z.next_in ≠ .null) (level0 : d.level = 0)
    (flush : Int32) (min_block : UInt32) (st0 : StoredS) (start : st0.last = 0) (empty : z.avail_in = 0)
    (mbPos : 0 < min_block.toNat) (mbLe : min_block.toNat + 5 ≤ d.pending_buf_size.toNat)
    (mbW : min_block.toNat ≤ d.w_size.toNat) :
    ∃ st g z' d', cdoWhile (storedBody (some (.tab ds)) flush (some r) min_block)
        (fun st => pure (!st.brk && st.last == 0, st)) st0 h = .ok (st, g) ∧
      StoredStep h g r ds z z' d d' ∧
      (st.last ≠ 0 → flush = Z_FINISH ∧ z'.avail_in = 0 ∧ d'.bi_valid.toInt = 0) ∧
      Zlib.Deflate.Universal.Quiet.work d' ≤ Zlib.Deflate.Universal.Quiet.work d ∧ (Zlib.Deflate.Universal.Quiet.work d' = Zlib.Deflate.Universal.Quiet.work d → z'.avail_out = z.avail_out ∨ st.last ≠ 0) ∧
      (st.last = 0 → flush = Z_FINISH → FinRoom z' d') := by
  let W : ZStream → DeflateState → Prop := fun z' d' =>
    Zlib.Deflate.Universal.Quiet.work d' ≤ Zlib.Deflate.Universal.Quiet.work d ∧ (Zlib.Deflate.Universal.Quiet.work d' = Zlib.Deflate.Universal.Quiet.work d → z'.avail_out = z.avail_out)
  let P : StoredS → Heap → Prop := fun s g => s.last = 0 ∧ ∃ z' d', StoredStep h g r ds z z' d d' ∧ W z' d'
  let Q : StoredS → Heap → Prop := fun s g => ∃ z' d', StoredStep h g r ds z z' d d' ∧
    (s.last ≠ 0 → flush = Z_FINISH ∧ z'.avail_in = 0 ∧ d'.bi_valid.toInt = 0) ∧
    Zlib.Deflate.Universal.Quiet.work d' ≤ Zlib.Deflate.Universal.Quiet.work d ∧ (Zlib.Deflate.Universal.Quiet.work d' = Zlib.Deflate.Universal.Quiet.work d → z'.avail_out = z.avail_out ∨ s.last ≠ 0) ∧
    (s.last = 0 → flush = Z_FINISH → FinRoom z' d')
  let μ : StoredS → Heap → Nat := fun _ g => match r.get g with | some z' => z'.avail_out.toNat | none => 0
  have step : ∀ s g, P s g → ∃ s1 g1 c s2 g2, storedBody (some (.tab ds)) flush (some r) min_block s g = .ok (s1, g1) ∧
      (fun st : StoredS => (pure (!st.brk && st.last == 0, st) : M (Bool × StoredS))) s1 g1 = .ok ((c, s2), g2) ∧
      (c = true → P s2 g2 ∧ μ s2 g2 < μ s g) ∧ (c = false → Q s2 g2) := by
    intro s g ⟨l0, z1, d1, now, w1⟩
    have level1 : d1.level = 0 := by rw [now.fields]; exact level0
    have empty1 : z1.avail_in = 0 := by
      have := Zlib.Deflate.Universal.fr_avail now.fr
      rw [empty] at this
      exact UInt32.toNat_inj.mp (by change _ ≤ 0 at this; change _ = 0; omega)
    have pbs1 : d1.pending_buf_size = d.pending_buf_size := by rw [now.fields]
    have ws1 : d1.w_size = d.w_size := by rw [now.fields]
    obtain ⟨s1, g1, z2, d2, run, next, dec, lastF, brkI, emitI⟩ := stored_iterationQ now.inv now.buffers now.pending
      now.out now.input level1 flush min_block s empty1 mbPos (by rw [pbs1]; exact mbLe) (by rw [ws1]; exact mbW)
    have total := StoredStep.trans inv.good buffers now next
    refine ⟨s1, g1, !s1.brk && s1.last == 0, s1, g1, run, rfl, fun c => ⟨⟨?_, z2, d2, total, ?_⟩, ?_⟩,
      fun c => ?_⟩
    · simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at c
      exact c.2
    · have brk : s1.brk = false := by
        cases e : s1.brk
        · rfl
        · rw [e] at c; simp at c
      have last0 : s1.last = 0 := by
        simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at c
        exact c.2
      obtain ⟨le2, lt2⟩ := emitI brk
      rcases lt2 with lt2 | nz
      · exact ⟨by have := w1.1; omega, fun e => by have := w1.1; omega⟩
      · exact absurd last0 nz
    · have brk : s1.brk = false := by
        cases e : s1.brk
        · rfl
        · rw [e] at c; simp at c
      show (match r.get g1 with | some z' => z'.avail_out.toNat | none => 0) <
        (match r.get g with | some z' => z'.avail_out.toNat | none => 0)
      rw [next.inv.good.live.hz, now.inv.good.live.hz]
      exact dec brk
    · by_cases b : s1.brk = true
      · obtain ⟨hg, hz, hd, fr⟩ := brkI b
        subst hg hz hd
        exact ⟨_, _, total, lastF l0, w1.1, fun e => Or.inl (w1.2 e), fun _ f => fr f⟩
      · have b' : s1.brk = false := by simpa using b
        have nz : s1.last ≠ 0 := by
          rw [b'] at c; simpa using c
        obtain ⟨le2, _⟩ := emitI b'
        exact ⟨z2, d2, total, lastF l0, by have := w1.1; omega, fun _ => Or.inr nz, fun e => absurd e nz⟩
  have bound : μ st0 h < fuel := by
    show (match r.get h with | some z' => z'.avail_out.toNat | none => 0) < 2 ^ 64
    rw [inv.good.live.hz]
    have := z.avail_out.toNat_lt
    show z.avail_out.toNat < 2 ^ 64
    omega
  obtain ⟨st, g, run, ⟨z', d', final, lastF, le, eq, fin⟩⟩ := C.cdoWhile_decreasing P Q μ step
    ⟨start, z, d, StoredStep.refl inv buffers pend0 out input, Nat.le_refl _, fun _ => rfl⟩ bound
  exact ⟨st, g, z', d', run, final, lastF, le, eq, fin⟩

theorem min_toNat (a b : UInt32) : (MIN a b).toNat = min a.toNat b.toNat := by
  unfold MIN
  split
  · rename_i lt; have := UInt32.lt_iff_toNat_lt.mp lt; omega
  · rename_i nlt
    have : ¬ b.toNat < a.toNat := fun c => nlt (UInt32.lt_iff_toNat_lt.mpr c)
    omega

set_option maxHeartbeats 4000000 in
open Zlib.Trees.Proofs.Out (TreesInvAt BitsDiff) in
/-- **The final stored block of `deflate_stored`.** `len` bytes of the window from `block_start`
go into `pending_buf` behind a stored header, `block_start` moves past them, and the pending bytes
are flushed. -/
theorem stored_block_flushQ {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r) (out : z.next_out ≠ .null)
    (pending : d.pending = 0) (cursor : d.pending_out = d.pending_buf) (bits : d.bi_valid.toInt ≤ 7)
    (low : 0 ≤ d.block_start.toInt) (len : UInt32)
    (span : d.block_start.toInt + len.toNat ≤ d.strstart.toNat) (range : d.strstart.toNat ≤ d.window_size.toNat)
    (room : (d.bi_valid.toInt.toNat + 42) / 8 + len.toNat ≤ d.pending_buf_size.toNat) (lastv : Bool) :
    ∃ (p : BPtr) (H1 : Heap) (bs : Int64) (H2 after : Heap) (z' : ZStream) (e : DeflateState) (produced : Nat),
      Ptr.add d.window d.block_start.toInt h = .ok (p, h) ∧
      Zlib.Trees._tr_stored_block (some (.tab ds)) p len.toUInt64 (if lastv then 1 else 0) h = .ok ((), H1) ∧
      ladd d.block_start len.toUInt64.toInt64 H1 = .ok (bs, H1) ∧
      wr (some (.tab ds)) (fun d => { d with block_start := bs }) H1 = .ok ((), H2) ∧
      flush_pending (some r) H2 = .ok ((), after) ∧
      DGood after r ds z' e ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
      StoredFields d e ∧ e.block_start.toInt = d.block_start.toInt + len.toNat ∧ e.bi_valid.toInt = 0 ∧
      (e.pending = 0 → e.pending_out = e.pending_buf) ∧ after.static = h.static ∧ after.nalloc = h.nalloc ∧
      (∀ w, d.window = .ref (.blk w) 0 → after.bytes w = h.bytes w) ∧
      (∀ p, d.prev = .ref (.blk p) 0 → after.words p = h.words p) ∧
      (∀ q, d.head = .ref (.blk q) 0 → after.words q = h.words q) ∧ Totals z z' 0 produced ∧
      Fr h r ds d z after z' e ∧ produced = min ((d.bi_valid.toInt.toNat + 42) / 8 + len.toNat) z.avail_out.toNat ∧
      e.pending.toNat + produced = (d.bi_valid.toInt.toNat + 42) / 8 + len.toNat := by
  obtain ⟨w, p, q, pb, blocks⟩ := good.inv.blocks
  obtain ⟨buf, getB, sizeB⟩ := blocks.ba
  obtain ⟨wa, getW, sizeW⟩ := blocks.wa
  have trees : TreesInvAt h ds d pb buf := Zlib.Deflate.Universal.trees_at_of_good good blocks.pbuf getB
  have bufSize : buf.size = d.pending_buf_size.toNat := trees.base.psize.symm
  have wsz := good.inv.wsz
  have lenLt := len.toNat_lt
  have bsN : (d.block_start.toInt.toNat : Int) = d.block_start.toInt := Int.toNat_of_nonneg low
  have add : Ptr.add d.window d.block_start.toInt h = .ok (.ref (.blk w) d.block_start.toInt.toNat, h) := by
    rw [blocks.win]
    have := Ptr.add_ok (off := 0) (k := d.block_start.toInt) (show Space.get h (BRef.blk w) = some wa from getW)
      (by omega) (by omega)
    have e0 : ((0 : Nat) : Int) + d.block_start.toInt = d.block_start.toInt := by omega
    rw [e0] at this
    exact this
  have lenN : len.toUInt64.toNat = len.toNat := by simp
  obtain ⟨next, r1, run1, trees1, size1, aligned1, pend1, diff1⟩ :=
    Zlib.Trees.Proofs.Out.stored_block_exact (off := d.block_start.toInt.toNat) trees getW (Ne.symm blocks.wb)
      bits len.toUInt64
      (by rw [lenN]; omega) (by rw [pending, UInt64.toNat_zero]; have := trees.base.lit_lo; omega)
      (by rw [pending, lenN, UInt64.toNat_zero]; omega) lastv
  replace run1 : Zlib.Trees._tr_stored_block (some (.tab ds)) (.ref (.blk w) d.block_start.toInt.toNat) len.toUInt64
      (if lastv then 1 else 0) h = .ok ((), setD (Zlib.Trees.Proofs.Out.setB h pb next) ds r1) := run1
  replace trees1 : TreesInvAt (setD (Zlib.Trees.Proofs.Out.setB h pb next) ds r1) ds r1 pb next := trees1
  have good1 := output_bits_good good cursor getB size1 diff1 trees1
  have buffers1 := output_bits_buffers good buffers cursor getB size1 diff1 trees1
  have sizes1 := output_bits_sizes good getB size1 diff1
  obtain ⟨pp, aa, vv, uu, hr1⟩ := diff1
  have bs1 : r1.block_start = d.block_start := by rw [hr1]
  have lenI : len.toUInt64.toInt64.toInt = (len.toNat : Int) := Zlib.Deflate.Universal.u32_toInt64_toInt len
  have ssLt := d.strstart.toNat_lt
  have lad := ladd_value d.block_start len.toUInt64.toInt64 (setD (Zlib.Trees.Proofs.Out.setB h pb next) ds r1)
    (by rw [lenI]; omega) (by rw [lenI]; omega)
  rw [lenI] at lad
  let r2 := { r1 with block_start := Int64.ofInt (d.block_start.toInt + len.toNat) }
  have state1 : (setD (Zlib.Trees.Proofs.Out.setB h pb next) ds r1).dstates ds = some r1 := setD_dstates_same _ _ _
  have wrt : wr (some (.tab ds)) (fun x => { x with block_start := Int64.ofInt (d.block_start.toInt + len.toNat) })
      (setD (Zlib.Trees.Proofs.Out.setB h pb next) ds r1) = .ok ((), setD (Zlib.Trees.Proofs.Out.setB h pb next) ds r2) := by
    rw [wrD_eq, state1]; dsimp only; rw [setD_setD]
  let H2 := setD (Zlib.Trees.Proofs.Out.setB h pb next) ds r2
  have inv2 : DStInv (setD (Zlib.Trees.Proofs.Out.setB h pb next) ds r1) ds r2 :=
    { good1.inv with blocks := good1.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }
  have good2 : DGood H2 r ds z r2 := by
    have g := good1.setD' (d' := r2) rfl good1.live.status inv2 (by trkeep)
    rw [setD_setD] at g; exact g
  have buffers2 : StreamBuffers H2 r := by
    have b := Zlib.Deflate.Universal.state_write_buffers good1 buffers1 (d' := r2) ⟨rfl, rfl, rfl, rfl⟩
      (by have g := good1.setD' (d' := r2) rfl good1.live.status inv2 (by trkeep); exact g)
    rw [setD_setD] at b; exact b
  have trees2 : TreesInvAt H2 ds r2 pb next :=
    ⟨⟨setD_dstates_same _ _ _, trees1.base.wf, trees1.base.static, trees1.base.pbuf, trees1.base.bytes,
      trees1.base.rw, trees1.base.size, trees1.base.psize, trees1.base.sym, trees1.base.lit_lo, trees1.base.lit_hi,
      trees1.base.sym_end, trees1.base.pending_le⟩,
      ⟨trees1.run.ldyn, trees1.run.lstat, trees1.run.ddyn, trees1.run.dstat, trees1.run.bldyn, trees1.run.blstat,
        trees1.run.bi_lo, trees1.run.bi_hi, trees1.run.bi_buf, trees1.run.sym_next_le, trees1.run.sym_next_mod⟩⟩
  have cursor2 : r2.pending_out = r2.pending_buf := by
    show r1.pending_out = r1.pending_buf; rw [hr1]; exact cursor
  have room2 : 8 * r2.pending.toNat + r2.bi_valid.toInt.toNat ≤ 8 * next.size := by
    show 8 * r1.pending.toNat + r1.bi_valid.toInt.toNat ≤ 8 * next.size
    rw [pend1, aligned1, size1, pending, lenN, UInt64.toNat_zero]; simp only [Int.toNat_zero]; omega
  have depth1 : r1.depth = d.depth := by rw [hr1]
  have sizes2 : ByteSizes h H2 := sizes1.chain ⟨fun ref a get => ⟨a, by
      show Space.get (setD (Zlib.Trees.Proofs.Out.setB h pb next) ds r2) ref = some a
      rw [byte_view_setD_depth (h := Zlib.Trees.Proofs.Out.setB h pb next) (d := d) (result := r2) good.live.hs depth1]
      rw [byte_view_setD_depth (h := Zlib.Trees.Proofs.Out.setB h pb next) (d := d) (result := r1) good.live.hs depth1] at get
      exact get, rfl⟩, fun ref => by cases ref <;> rfl⟩
  have fieldsW : r2.window = d.window ∧ r2.prev = d.prev ∧ r2.head = d.head ∧ r2.pending_buf = d.pending_buf := by
    show r1.window = d.window ∧ r1.prev = d.prev ∧ r1.head = d.head ∧ r1.pending_buf = d.pending_buf
    rw [hr1]; exact ⟨rfl, rfl, rfl, rfl⟩
  have keysW : Keys d r2 := by
    show Keys d { r1 with block_start := Int64.ofInt (d.block_start.toInt + len.toNat) }
    rw [hr1]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨pa, getP, _⟩ := blocks.pa
  obtain ⟨qa, getQ, _⟩ := blocks.qa
  have getW2 : H2.bytes w = some wa := by
    show (upd h.bytes pb (some next)) w = some wa
    rw [upd_ne _ _ _ _ blocks.wb]; exact getW
  have bsR : (Int64.ofInt (d.block_start.toInt + len.toNat)).toInt = d.block_start.toInt + len.toNat :=
    int64_ofInt_toInt _ (by omega) (by omega)
  have finish : ∀ (produced : Nat) (after : Heap) (z' : ZStream) (result : DeflateState),
      flush_pending (some r) H2 = .ok ((), after) → DGood after r ds z' result → StreamBuffers after r →
      StreamAccounting z z' 0 produced → Totals z z' 0 produced →
      BufferFrame H2 after (fun b => StreamRoot r b ∨ DeflateOwned ds r2 b) [⟨z.next_out, produced⟩] →
      Zlib.Deflate.Proofs.Shape H2 after → ByteSizes H2 after →
      result.bi_valid.toInt.toNat = r2.bi_valid.toInt.toNat % 8 →
      result = { r2 with pending := result.pending, pending_out := result.pending_out, bi_buf := result.bi_buf, bi_valid := result.bi_valid, bi_used := result.bi_used } →
      (result.pending = 0 → result.pending_out = result.pending_buf) →
      after.static = H2.static → after.nalloc = H2.nalloc →
      (after.bytes w = some wa ∧ after.words p = some pa ∧ after.words q = some qa) →
      produced = min (r2.pending.toNat + r2.bi_valid.toInt.toNat / 8) z.avail_out.toNat →
      result.pending.toNat + produced = r2.pending.toNat + r2.bi_valid.toInt.toNat / 8 →
      ∃ (p : BPtr) (H1 : Heap) (bs : Int64) (H2 after : Heap) (z' : ZStream) (e : DeflateState) (produced : Nat),
        Ptr.add d.window d.block_start.toInt h = .ok (p, h) ∧
        Zlib.Trees._tr_stored_block (some (.tab ds)) p len.toUInt64 (if lastv then 1 else 0) h = .ok ((), H1) ∧
        ladd d.block_start len.toUInt64.toInt64 H1 = .ok (bs, H1) ∧
        wr (some (.tab ds)) (fun d => { d with block_start := bs }) H1 = .ok ((), H2) ∧
        flush_pending (some r) H2 = .ok ((), after) ∧
        DGood after r ds z' e ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
        StoredFields d e ∧ e.block_start.toInt = d.block_start.toInt + len.toNat ∧ e.bi_valid.toInt = 0 ∧
        (e.pending = 0 → e.pending_out = e.pending_buf) ∧ after.static = h.static ∧ after.nalloc = h.nalloc ∧
        (∀ w, d.window = .ref (.blk w) 0 → after.bytes w = h.bytes w) ∧
        (∀ p, d.prev = .ref (.blk p) 0 → after.words p = h.words p) ∧
        (∀ q, d.head = .ref (.blk q) 0 → after.words q = h.words q) ∧ Totals z z' 0 produced ∧
        Fr h r ds d z after z' e ∧ produced = min ((d.bi_valid.toInt.toNat + 42) / 8 + len.toNat) z.avail_out.toNat ∧
        e.pending.toNat + produced = (d.bi_valid.toInt.toNat + 42) / 8 + len.toNat := by
    intro produced after z' result run goodA buffersA account totals bufferF shapeF _ valid fields cursorA staticA nallocA kept count rem
    have sumE : r2.pending.toNat + r2.bi_valid.toInt.toNat / 8 = (d.bi_valid.toInt.toNat + 42) / 8 + len.toNat := by
      show r1.pending.toNat + r1.bi_valid.toInt.toNat / 8 = _
      rw [pend1, aligned1, pending, lenN]; simp
    have bv : result.bi_valid.toInt = 0 := by
      have v1 : r2.bi_valid.toInt = 0 := aligned1
      rw [v1] at valid
      have := goodA.inv.bits.1
      have v2 : result.bi_valid.toInt.toNat = 0 := by rw [valid]; rfl
      omega
    have fieldsS : StoredFields d result := by
      unfold StoredFields
      rw [fields]
      dsimp only [r2]
      rw [hr1]
    refine ⟨_, _, _, _, after, z', result, produced, add, run1, lad, wrt, run, goodA, buffersA, account, fieldsS,
      ?_, bv, cursorA, by rw [staticA]; rfl, by rw [nallocA]; rfl, fun w' e => ?_, fun p' e => ?_, fun q' e => ?_, totals, ?_, by rw [count, sumE], by rw [rem, sumE]⟩
    · rw [fields]; exact bsR
    · have : w' = w := by simpa only [blocks.win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using e.symm
      subst this; rw [kept.1, getW]
    · have : p' = p := by simpa only [blocks.prev, Ptr.ref.injEq, WRef.blk.injEq, and_true] using e.symm
      subst this; rw [kept.2.1, getP]
    · have : q' = q := by simpa only [blocks.head, Ptr.ref.injEq, WRef.blk.injEq, and_true] using e.symm
      subst this; rw [kept.2.2, getQ]
    · have privH2 : PrivStep h H2 r ds d :=
        (priv_setB h r ds pb d next (Or.inr (Or.inr (Or.inr (Or.inr blocks.pbuf)))) (by simp [getB])).trans
          (priv_setD _ r ds d r2 (by simpa [Zlib.Trees.Proofs.Out.setB] using good.live.hs))
      have keysE : Keys r2 result := by rw [fields]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      exact Fr.trans good buffers (Fr.priv good buffers privH2 keysW)
        (Fr.flush account (by rw [totals.1]; simp) totals.2 bufferF shapeF keysE)
  obtain ⟨ob, pointer⟩ := Zlib.Deflate.Universal.output_reference good.live.hz buffers out
  have zEq : good2.live.hz = good2.live.hz := rfl
  rcases pointer with ⟨oo, pointer⟩ | ⟨oo, pointer⟩
  · obtain ⟨produced, after, z', result, _written, _remaining, run, goodA, buffersA, accountA,
      sizesA, storageA, count, rem, _low, validA, fieldsA, _bytes, _pendingA, _outputA⟩ :=
      flush_pending_raw_bits good2 trees2 buffers2 pointer cursor2 room2
    have cursorA := raw_pending_run_empty_cursor good2 trees2 buffers2 pointer cursor2 room2 run goodA.live.hs
    have kept := storageA.private_arrays good2 buffers2 pointer (by rw [fieldsW.1]; exact blocks.win) getW2
      (by rw [fieldsW.2.1]; exact blocks.prev) getP (by rw [fieldsW.2.2.1]; exact blocks.head) getQ
      (by rw [fieldsW.2.2.2]; exact blocks.pbuf)
    have tot := flush_pending_run_counter_effects good2 trees2 buffers2 pointer cursor2 room2 run goodA.live.hz accountA
    have bufferA := flush_pending_run_buffer_frame good2 trees2 buffers2 pointer cursor2 room2 run goodA.live.hz accountA
    exact finish produced after z' result run goodA buffersA accountA ⟨by rw [tot.1]; simp, tot.2⟩ bufferA
      storageA.shape sizesA validA
      fieldsA cursorA storageA.frame.1.symm storageA.nalloc kept count rem
  · obtain ⟨produced, after, z', result, _written, _remaining, run, goodA, buffersA, accountA,
      sizesA, storageA, count, rem, _low, validA, fieldsA, _bytes, _pendingA, _outputA, bufferF0⟩ :=
      flush_pending_foreign_bits_frame good2 trees2 buffers2 pointer cursor2 room2
    have cursorA := foreign_pending_run_empty_cursor good2 trees2 buffers2 pointer cursor2 room2 run goodA.live.hs
    have kept := storageA.foreign_private_arrays good2 buffers2 pointer (by rw [fieldsW.1]; exact blocks.win) getW2
      (by rw [fieldsW.2.1]; exact blocks.prev) getP (by rw [fieldsW.2.2.1]; exact blocks.head) getQ
      (by rw [fieldsW.2.2.2]; exact blocks.pbuf)
    have tot := default_foreign_flush_pending_run_counter_effects good2 trees2 buffers2 pointer cursor2 room2 run
      goodA.live.hz accountA
    have bufferA := buffer_frame_weaken bufferF0 (large := fun b => StreamRoot r b ∨ DeflateOwned ds r2 b)
      (fun b c => by
        rcases c with root | same | pbe
        · exact Or.inl root
        · exact Or.inr (Or.inl same)
        · subst pbe; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (fieldsW.2.2.2.trans blocks.pbuf))))))
    exact finish produced after z' result run goodA buffersA accountA ⟨by rw [tot.1]; simp, tot.2⟩ bufferA
      storageA.shape sizesA validA
      fieldsA cursorA storageA.frame.1.symm storageA.nalloc kept count rem

set_option maxHeartbeats 8000000 in
open Zlib.Deflate.Universal in
/-- **The final block of `deflate_stored` keeps the invariant.** -/
theorem stored_finalQ {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (buffers : StreamBuffers h r) (pend0 : d.pending = 0) (out : z.next_out ≠ .null)
    (level0 : d.level = 0) (flush last0 : Int32) (lastZero : last0 = 0) (empty : z.avail_in = 0)
    (fin : flush = Z_FINISH → FinRoom z d) :
    ∃ ret g z' d', storedFinal (some (.tab ds)) flush (some r) last0 h = .ok (ret, g) ∧
      r.get g = some z' ∧ g.dstates ds = some d' ∧ QEnd flush z d z' d' ret ∧
      (ret = finish_started → z'.avail_out = 0) := by
  have good := inv.good
  have shape := inv.shape
  have zero := shape.levelZero level0
  have bits := inv.bi_valid_le
  have hvN := header_bytes_value d.bi_valid bits.1 bits.2
  have room := shape.room
  have wsz := good.inv.wsz
  have wsize := good.inv.wsize
  have wbits := good.inv.wbits_hi
  have wpow : 2 ^ d.w_bits.toNat ≤ 2 ^ 15 := Nat.pow_le_pow_right (by omega) wbits
  have la : d.lookahead.toNat = 0 := by rw [zero.2.1]; rfl
  obtain ⟨lsubEq, word, _⟩ := Zlib.Deflate.Universal.Block.flush_length_general (d := d) (by omega)
    shape.blockStart (by omega)
  have lsubRun := congrFun lsubEq h
  have pbs := good.inv.blocks
  obtain ⟨w0, p0, q0, b0, blocks⟩ := pbs
  have psize := blocks.psize
  have lit := good.inv.lit
  have hsize := good.inv.hsize
  have hbits := good.inv.hbits_lo
  have hpow : 2 ^ 8 ≤ 2 ^ d.hash_bits.toNat := Nat.pow_le_pow_right (by omega) hbits
  have PLe : (d.bi_valid.toInt.toNat + 42) / 8 ≤ 6 := by omega
  have hvU : (((d.bi_valid.toUInt32 + 42) >>> 3).toUInt64).toNat = (d.bi_valid.toInt.toNat + 42) / 8 := by
    rw [UInt32.toNat_toUInt64, hvN]
  have pbsLe : (((d.bi_valid.toUInt32 + 42) >>> 3).toUInt64) ≤ d.pending_buf_size := by
    rw [UInt64.le_iff_toNat_le, hvU]; omega
  have HvN : ((MIN (d.pending_buf_size - ((d.bi_valid.toUInt32 + 42) >>> 3).toUInt64) MAX_STORED.toUInt64).toUInt32).toNat ≤
      d.pending_buf_size.toNat - (d.bi_valid.toInt.toNat + 42) / 8 := by
    have sub : (d.pending_buf_size - ((d.bi_valid.toUInt32 + 42) >>> 3).toUInt64).toNat =
        d.pending_buf_size.toNat - (d.bi_valid.toInt.toNat + 42) / 8 := by
      rw [UInt64.toNat_sub_of_le _ _ pbsLe, hvU]
    have m : MAX_STORED.toUInt64.toNat = 65535 := rfl
    unfold MIN
    split
    · rename_i lt
      have lt' := UInt64.lt_iff_toNat_lt.mp lt
      rw [sub, m] at lt'
      rw [UInt64.toNat_toUInt32, m]
      omega
    · rw [UInt64.toNat_toUInt32, sub]
      exact Nat.mod_le _ _
  have hz := good.live.hz
  have readAvail : zrd (some r) (·.avail_in) h = .ok (z.avail_in, h) := by simp [zrd_eq, hz]
  unfold storedFinal
  simp only [bind_app, ldDeflateState_tab good.live.hs, lsubRun, pure_app, readAvail]
  obtain ⟨left, hleft⟩ : ∃ l, l = (Int64.ofInt ((d.strstart.toNat : Int) - d.block_start.toInt)).toUInt64.toUInt32 :=
    ⟨_, rfl⟩
  rw [← hleft]
  have leftN : left.toNat = ((d.strstart.toNat : Int) - d.block_start.toInt).toNat := by
    rw [hleft, UInt64.toNat_toUInt32, word]
    apply Nat.mod_eq_of_lt
    have := shape.blockStart; have := zero.1; omega
  obtain ⟨Hv, hHv⟩ : ∃ x, x = (MIN (d.pending_buf_size - ((d.bi_valid.toUInt32 + 42) >>> 3).toUInt64)
      MAX_STORED.toUInt64).toUInt32 := ⟨_, rfl⟩
  rw [← hHv]
  rw [← hHv] at HvN
  have lenLe := min_toNat_le left Hv
  have lenLe2 : (MIN left Hv).toNat ≤ Hv.toNat := by
    unfold MIN; split
    · exact Nat.le_refl _
    · rename_i nlt
      have : ¬ Hv.toNat < left.toNat := fun c => nlt (UInt32.lt_iff_toNat_lt.mpr c)
      omega
  have geo := stored_geom good
  have hv6 : (d.bi_valid.toInt.toNat + 42) / 8 ≤ 6 := by omega
  have HvEq : Hv.toNat = min (d.pending_buf_size.toNat - (d.bi_valid.toInt.toNat + 42) / 8) 65535 := by
    rw [hHv]
    have sub : (d.pending_buf_size - ((d.bi_valid.toUInt32 + 42) >>> 3).toUInt64).toNat =
        d.pending_buf_size.toNat - (d.bi_valid.toInt.toNat + 42) / 8 := by
      rw [UInt64.toNat_sub_of_le _ _ pbsLe, hvU]
    have m : MAX_STORED.toUInt64.toNat = 65535 := rfl
    unfold MIN
    split
    · rename_i lt
      have lt' := UInt64.lt_iff_toNat_lt.mp lt
      rw [sub, m] at lt'
      rw [UInt64.toNat_toUInt32, m]
      omega
    · rename_i nlt
      have nlt' : ¬ 65535 < d.pending_buf_size.toNat - (d.bi_valid.toInt.toNat + 42) / 8 :=
        fun c => nlt (UInt64.lt_iff_toNat_lt.mpr (by rw [sub, m]; exact c))
      rw [UInt64.toNat_toUInt32, sub]
      omega
  have lenEq : (MIN left Hv).toNat = min left.toNat Hv.toNat := min_toNat left Hv
  have mbEq : (MIN Hv d.w_size).toNat = min Hv.toNat d.w_size.toNat := min_toNat Hv d.w_size
  have bsLo := zero.1
  have bsHi := shape.blockStart
  have leftI : (left.toNat : Int) = (d.strstart.toNat : Int) - d.block_start.toInt := by rw [leftN]; omega
  have wd := work_l0 level0 shape
  by_cases c : (decide (left ≥ MIN Hv d.w_size) || ((left != 0 || flush == Z_FINISH) && flush != Z_NO_FLUSH &&
      z.avail_in == 0 && decide (left ≤ Hv))) = true
  · obtain ⟨p, H1, bs, H2, after, z', e, produced, add, blk, lad, wrt, fl, goodA, buffersA, accA, fieldsA, bsA,
        bvA, cursorA, staticA, nallocA, winA, prevA, headA, totA, frA, cntA, remA⟩ :=
      stored_block_flushQ good buffers out pend0 (shape.cursor pend0) bits.2 zero.1 (MIN left Hv)
        (by have := shape.blockStart; omega) (by omega) (by omega)
        (flush == Z_FINISH && z.avail_in == 0 && MIN left Hv == left)
    have shapeA : Shape e := shape_stored shape fieldsA level0 (by rw [bsA]; omega)
      (by rw [bsA]; have := shape.blockStart; omega) (by omega) cursorA
    have invA : DInv after r ds z' e := dinv_stored_keep inv goodA fieldsA shapeA zero.2.2 staticA winA prevA headA
      accA.2.2.2.2.2.2.2.1 accA.2.2.2.2.2.2.2.2.1
    have levelA : e.level = 0 := by rw [fieldsA]; exact level0
    have ssA : e.strstart = d.strstart := by rw [fieldsA]
    have gzA : e.gzindex = d.gzindex := by rw [fieldsA]
    have we := work_l0 levelA shapeA
    have bsAN := Int.toNat_of_nonneg (show 0 ≤ e.block_start.toInt by rw [bsA]; omega)
    have bsN := Int.toNat_of_nonneg bsLo
    have workEq : Zlib.Deflate.Universal.Quiet.work e + (MIN left Hv).toNat = Zlib.Deflate.Universal.Quiet.work d := by
      rw [we, wd, ssA]; omega
    have outA := accA.2.2.2.1
    have fullFin : flush = Z_FINISH → z'.avail_out = 0 := by
      intro f
      have fr := fin f
      unfold FinRoom at fr
      exact UInt32.toNat_inj.mp (by
        have : z'.avail_out.toNat = 0 := by omega
        rw [this]; rfl)
    simp only [c, ite_true, bind_app, add, blk, lad, wrt, fl]
    by_cases l0 : ((if (flush == Z_FINISH && z.avail_in == 0 && MIN left Hv == left) = true then (1 : Int32) else 0) != 0) = true
    · obtain ⟨wrRun, invB, buffersB⟩ := bi_used_step invA buffersA levelA
      have finF : flush = Z_FINISH := by
        by_cases cf : (flush == Z_FINISH && z.avail_in == 0 && MIN left Hv == left) = true
        · simp only [Bool.and_eq_true, beq_iff_eq] at cf; exact cf.1.1
        · rw [if_neg cf] at l0; simp at l0
      exact ⟨finish_started, _, z', _, by simp only [l0, ite_true, bind_app, wrRun]; rfl, invB.good.live.hz,
        invB.good.live.hs, ⟨by show Zlib.Deflate.Universal.Quiet.work e ≤ _; omega, fun _ => Or.inl rfl,
          fun e => absurd e (by decide), gzA⟩, fun _ => fullFin finF⟩
    · simp only [Bool.not_eq_true] at l0
      have lenPos : 0 < (MIN left Hv).toNat := by
        rcases Nat.eq_zero_or_pos (MIN left Hv).toNat with z0 | p0
        · exfalso
          have left0 : left.toNat = 0 := by omega
          have leftZ : left = 0 := UInt32.toNat_inj.mp (by rw [left0]; rfl)
          have nf : flush ≠ Z_FINISH := by
            intro f
            have m0 : MIN left Hv = left := UInt32.toNat_inj.mp (by omega)
            rw [f, empty, m0] at l0
            simp at l0
          have h1 : ¬ (left ≥ MIN Hv d.w_size) := by
            intro ge
            have := UInt32.le_iff_toNat_le.mp ge
            omega
          rw [leftZ] at c h1
          simp [h1, nf] at c
        · exact p0
      refine ⟨need_more, after, z', e, by simp only [l0, Bool.false_eq_true, ite_false, bind_app, pure_app],
        invA.good.live.hz, invA.good.live.hs,
        ⟨by omega, fun ew => absurd ew (by omega), fun _ room => ⟨?_, fun f => room (fullFin f)⟩, gzA⟩,
        fun e => absurd e (by decide)⟩
      have r0 : z'.avail_out.toNat ≠ 0 := fun x => room (UInt32.toNat_inj.mp (by rw [x]; rfl))
      exact UInt64.toNat_inj.mp (by
        have : e.pending.toNat = 0 := by omega
        rw [this]; rfl)
  · simp only [Bool.not_eq_true] at c
    simp only [c, Bool.false_eq_true, ite_false]
    subst lastZero
    refine ⟨need_more, h, z, d, by simp [bind_app], good.live.hz, good.live.hs,
      ⟨Nat.le_refl _, fun _ => Or.inr (Or.inr ⟨rfl, pend0⟩), fun _ _ => ⟨pend0, ?_⟩, rfl⟩,
      fun e => absurd e (by decide)⟩
    intro f
    have h1 : ¬ (left ≥ MIN Hv d.w_size) := by
      intro ge; rw [decide_eq_true ge] at c; simp at c
    have h2 : ¬ (left ≤ Hv) := by
      intro le
      rw [f, empty, decide_eq_true le] at c
      simp [show (Z_FINISH != Z_NO_FLUSH) = true by decide] at c
    have a1 : ¬ (MIN Hv d.w_size).toNat ≤ left.toNat := fun x => h1 (UInt32.le_iff_toNat_le.mpr x)
    have a2 : ¬ left.toNat ≤ Hv.toNat := fun x => h2 (UInt32.le_iff_toNat_le.mpr x)
    omega


/-- The refill of `deflate_stored` with no input only raises `high_water`. -/
theorem stored_refill_empty {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d e : DeflateState}
    (hz : r.get h = some z) (empty : z.avail_in = 0) (hs : h.dstates ds = some e) :
    storedRefill (some (.tab ds)) (some r) d h =
      .ok ((), setD h ds { e with high_water := if e.high_water < e.strstart.toUInt64 then e.strstart.toUInt64 else e.high_water }) := by
  have rd0 : zrd (some r) (·.avail_in) h = .ok (0, h) := by simp [zrd_eq, hz, empty]
  have gt0 : ∀ x : UInt32, (decide (0 > x)) = false := fun x => by
    apply decide_eq_false
    intro c
    have := UInt32.lt_iff_toNat_lt.mp c
    simp at this
  unfold storedRefill storedRead
  simp only [bind_app, rd0, gt0, Bool.false_and, Bool.false_eq_true, ite_false, pure_app]
  split
  · simp only [bne_self_eq_false, Bool.false_eq_true, ite_false]
    rw [wrD_eq, hs]
  · rename_i ng
    have hz0 : (d.window_size - d.strstart.toUInt64).toUInt32 = 0 :=
      UInt32.toNat_inj.mp (Nat.eq_zero_of_not_pos (fun c => ng (UInt32.lt_iff_toNat_lt.mpr c)))
    rw [hz0]
    simp only [bne_self_eq_false, Bool.false_eq_true, ite_false]
    rw [wrD_eq, hs]

/-- A state with the same work term, nothing pending and the same `gzindex` can stand in for the start. -/
theorem qend_same_work {flush : Int32} {z z1 : ZStream} {d d' d1 : DeflateState} {b : block_state}
    (q : QEnd flush z d' z1 d1 b) (pend : d'.pending = 0)
    (w : Zlib.Deflate.Universal.Quiet.work d' = Zlib.Deflate.Universal.Quiet.work d)
    (gz : d'.gzindex = d.gzindex) : QEnd flush z d z1 d1 b :=
  QEnd.after ⟨Nat.le_refl _, Nat.le_of_eq w, fun _ => ⟨rfl, pend⟩, gz⟩ q

set_option maxHeartbeats 8000000 in
/-- The end of `deflate_stored` (`storedEnd`) with no input. -/
theorem stored_endQ {g : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv g r ds z d) (buffers : StreamBuffers g r) (pend0 : d.pending = 0)
    (out : z.next_out ≠ .null) (level0 : d.level = 0)
    (flush : Int32) (mb used0 : UInt32) (st : StoredS) (u0 : used0 = 0) (empty : z.avail_in = 0)
    (fin : st.last = 0 → flush = Z_FINISH → FinRoom z d) :
    ∃ ret g' z' d', storedEnd (some (.tab ds)) flush (some r) mb used0 st g = .ok (ret, g') ∧
      r.get g' = some z' ∧ g'.dstates ds = some d' ∧ QEnd flush z d z' d' ret ∧
      (ret = finish_started → z'.avail_out = 0) ∧ (st.last ≠ 0 → ret = finish_done) := by
  have good := inv.good
  have hz := good.live.hz
  have readAvail : ∀ H : Heap, r.get H = some z → zrd (some r) (·.avail_in) H = .ok (z.avail_in, H) := by
    intro H hzH; simp [zrd_eq, hzH]
  subst u0
  have keepRun : (if ((0 : UInt32) - z.avail_in != 0) = true then storedKeep (some (.tab ds)) (some r) (0 - z.avail_in)
      else pure ()) g = .ok ((), g) := by rw [empty]; rfl
  obtain ⟨hwRun, inv2, buffers2, _, _⟩ := high_water_step inv buffers level0
  have hz2 := inv2.good.live.hz
  unfold storedEnd
  simp only [ite_seq]
  simp only [bind_app, readAvail g hz, keepRun, hwRun]
  by_cases lastC : (st.last != 0) = true
  · obtain ⟨wrRun, inv3, buffers3⟩ := bi_used_step inv2 buffers2 level0
    exact ⟨finish_done, _, z, _, by simp only [lastC, ite_true, bind_app, wrRun]; rfl, inv3.good.live.hz,
      inv3.good.live.hs, ⟨Nat.le_of_eq rfl, fun _ => Or.inr (Or.inl rfl), fun e => absurd e (by decide), rfl⟩,
      fun e => absurd e (by decide), fun _ => rfl⟩
  · simp only [Bool.not_eq_true] at lastC
    have l0 : st.last = 0 := by simpa using lastC
    simp only [lastC, Bool.false_eq_true, ite_false, bind_app, ldDeflateState_tab inv2.good.live.hs, readAvail _ hz2]
    by_cases early : (flush != Z_NO_FLUSH && flush != Z_FINISH && z.avail_in == 0 &&
        d.strstart.toUInt64.toInt64 == d.block_start) = true
    · exact ⟨block_done, _, z, _, by simp only [early, ite_true]; rfl, hz2, inv2.good.live.hs,
        ⟨Nat.le_of_eq rfl, fun _ => Or.inr (Or.inr ⟨rfl, pend0⟩), fun e => absurd e (by decide), rfl⟩,
        fun e => absurd e (by decide), fun e => absurd l0 e⟩
    · simp only [Bool.not_eq_true] at early
      simp only [early, Bool.false_eq_true, ite_false]
      have refillRun := stored_refill_empty (d := { d with high_water := if d.high_water < d.strstart.toUInt64 then
        d.strstart.toUInt64 else d.high_water }) hz2 empty inv2.good.live.hs
      obtain ⟨_, inv3, buffers3, _, _⟩ := high_water_step inv2 buffers2 level0
      obtain ⟨ret, g4, z4, e4, finalRun, hz4, hs4, q, started⟩ :=
        stored_finalQ inv3 buffers3 pend0 out level0 flush st.last l0 empty (fun f => fin l0 f)
      refine ⟨ret, g4, z4, e4, ?_, hz4, hs4,
        qend_same_work q pend0 rfl rfl, started, fun e => absurd l0 e⟩
      simp only [bind_app, refillRun, finalRun]

/-- **`deflate_stored` with no input** lowers the work term, and a `finish_started` return leaves
the output full. -/
theorem stored_q {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (entry : StratIn h r z d) (flush : Int32) (level : d.level = 0)
    (empty : z.avail_in = 0) :
    ∃ bstate after z' d', C.run (Zlib.Deflate.deflate_stored (some (.tab ds)) flush) h = .ok (bstate, after) ∧
      r.get after = some z' ∧ after.dstates ds = some d' ∧ QEnd flush z d z' d' bstate ∧
      (bstate = finish_started → z'.avail_out = 0) := by
  have good := inv.good
  have hz := good.live.hz
  have strm := good.live.back
  have geo := stored_geom good
  have mbN : ((MIN (d.pending_buf_size - 5) d.w_size.toUInt64).toUInt32).toNat =
      min (d.pending_buf_size.toNat - 5) d.w_size.toNat := by
    have sub : (d.pending_buf_size - 5).toNat = d.pending_buf_size.toNat - 5 :=
      UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))
    have wsN : d.w_size.toUInt64.toNat = d.w_size.toNat := by simp
    unfold MIN
    split
    · rename_i lt
      have lt' := UInt64.lt_iff_toNat_lt.mp lt
      rw [sub, wsN] at lt'
      rw [UInt64.toNat_toUInt32, wsN]
      omega
    · rename_i nlt
      have nlt' : ¬ d.w_size.toNat < d.pending_buf_size.toNat - 5 :=
        fun c => nlt (UInt64.lt_iff_toNat_lt.mpr (by rw [sub, wsN]; exact c))
      rw [UInt64.toNat_toUInt32, sub]
      omega
  obtain ⟨st, g, z1, d1, loopRun, step, lastF, wle, weq, finR⟩ := stored_loopQ inv entry.buffers entry.pending
    entry.out entry.input level flush (MIN (d.pending_buf_size - 5) d.w_size.toUInt64).toUInt32
    { last := 0, len := 0, left := 0, have_ := 0, all := false, brk := false } rfl empty
    (by rw [mbN]; omega) (by rw [mbN]; omega) (by rw [mbN]; omega)
  have level1 : d1.level = 0 := by rw [step.fields]; exact level
  have empty1 : z1.avail_in = 0 := by
    have := fr_avail step.fr
    rw [empty] at this
    exact UInt32.toNat_inj.mp (by change _ ≤ 0 at this; change _ = 0; omega)
  have gz1 : d1.gzindex = d.gzindex := by rw [step.fields]
  have readAvail : zrd (some r) (·.avail_in) h = .ok (z.avail_in, h) := by simp [zrd_eq, hz]
  obtain ⟨ret, g', z', d', endRun, hz', hs', q, started, lastD⟩ :=
    stored_endQ step.inv step.buffers step.pending step.out level1 flush
      (MIN (d.pending_buf_size - 5) d.w_size.toUInt64).toUInt32 z.avail_in st empty empty1 finR
  refine ⟨ret, g', z', d', ?_, hz', hs', ?_, started⟩
  · simp only [C.run, deflate_stored_source, bind_app, ldDeflateState_tab good.live.hs, strm, readAvail, loopRun,
      endRun]
  · by_cases l0 : st.last = 0
    · have down : QDown z d z1 d1 :=
        ⟨fr_avail step.fr, wle, fun e => ⟨(weq e).resolve_right (fun nz => nz l0), step.pending⟩, gz1⟩
      exact QEnd.after down q
    · have rd := lastD l0
      subst rd
      exact ⟨Nat.le_trans q.le wle, fun _ => Or.inr (Or.inl rfl), q.more, q.gz.trans gz1⟩

end Zlib.Deflate.Engine.Proofs


namespace Zlib.Deflate.Universal.Quiet
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs Zlib.Deflate.Universal Zlib.Deflate.Universal.Call
set_option autoImplicit false

/-- The dispatch at a nonzero level, with no input, lowers the work term. -/
theorem dispatch_q_nz {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (ov : Block.OverlayAt d.lit_bufsize.toNat) (entry : StrategyEntry h r z d)
    (flush : Int32) (l0 : d.level ≠ 0) (empty : z.avail_in = 0) :
    ∃ b a z' d', dispatch (some (.tab ds)) flush d h = .ok (b, a) ∧ r.get a = some z' ∧
      a.dstates ds = some d' ∧ QEnd flush z d z' d' b := by
  have lo := inv.good.inv.level_lo
  have hi := inv.good.inv.level_hi
  have slo := inv.good.inv.strat_lo
  have shi := inv.good.inv.strat_hi
  have safe : FlushSafeAt d.lit_bufsize.toNat := Block.flushSafeAt_of ov
  have l0' : (d.level == 0) = false := by simp [l0]
  have nz : d.level.toInt ≠ 0 := fun e => l0 (Int32.toInt_inj.mp (by simpa using e))
  by_cases hf : d.strategy = Z_HUFFMAN_ONLY
  · have s2 : d.strategy.toInt = 2 := by rw [hf]; rfl
    obtain ⟨b, a, z', d', run, hz, hs, q⟩ := huff_q safe inv entry.toIn flush l0 s2 empty
    refine ⟨b, a, z', d', ?_, hz, hs, q⟩
    simp only [C.run] at run
    simp [dispatch, l0', hf, run]
  have hf' : (d.strategy == Z_HUFFMAN_ONLY) = false := by simp [hf]
  have s2 : d.strategy.toInt ≠ 2 := fun e => hf (Int32.toInt_inj.mp (by rw [e]; rfl))
  by_cases rl : d.strategy = Z_RLE
  · have s3 : d.strategy.toInt = 3 := by rw [rl]; rfl
    obtain ⟨b, a, z', d', run, hz, hs, q⟩ := rle_q safe inv entry.toIn flush l0 s3 empty
    refine ⟨b, a, z', d', ?_, hz, hs, q⟩
    simp only [C.run] at run
    simp [dispatch, l0', hf', rl, run, show Z_RLE ≠ Z_HUFFMAN_ONLY by decide]
  have rl' : (d.strategy == Z_RLE) = false := by simp [rl]
  have s3 : d.strategy.toInt ≠ 3 := fun e => rl (Int32.toInt_inj.mp (by rw [e]; rfl))
  by_cases fast : d.level.toInt ≤ 3
  · obtain ⟨b, a, z', d', run, hz, hs, q⟩ := fast_q safe inv entry.toIn flush ⟨by omega, fast, s2, s3⟩ empty
    refine ⟨b, a, z', d', ?_, hz, hs, q⟩
    simp only [C.run] at run
    have values : d.level = 1 ∨ d.level = 2 ∨ d.level = 3 := by
      have : d.level.toInt = 1 ∨ d.level.toInt = 2 ∨ d.level.toInt = 3 := by omega
      simp only [← Int32.toInt_inj]; exact this
    unfold dispatch
    rcases values with e | e | e <;>
      simp [l0', hf', rl', e, config_at, configuration_table, bind_app, pure_app] <;> exact run
  · obtain ⟨b, a, z', d', run, hz, hs, q⟩ := slow_q safe inv entry.toIn flush ⟨by omega, s2, s3⟩ empty
    refine ⟨b, a, z', d', ?_, hz, hs, q⟩
    simp only [C.run] at run
    have values : d.level = 4 ∨ d.level = 5 ∨ d.level = 6 ∨ d.level = 7 ∨ d.level = 8 ∨ d.level = 9 := by
      have : d.level.toInt = 4 ∨ d.level.toInt = 5 ∨ d.level.toInt = 6 ∨ d.level.toInt = 7 ∨
          d.level.toInt = 8 ∨ d.level.toInt = 9 := by omega
      simp only [← Int32.toInt_inj]; exact this
    unfold dispatch
    rcases values with e | e | e | e | e | e <;>
      simp [l0', hf', rl', e, config_at, configuration_table, bind_app, pure_app] <;> exact run

/-- **`StratQuiet` at a nonzero level** (`deflate_huff`, `deflate_rle`, `deflate_fast`,
`deflate_slow`). -/
theorem strat_quiet_nz {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState} {flush : Int32}
    (inv : DInv h r ds z d) (ov : Block.OverlayAt d.lit_bufsize.toNat) (entry : StrategyEntry h r z d)
    (l0 : d.level ≠ 0) (empty : z.avail_in = 0)
    {b : block_state} {after : Heap} {z1 : ZStream} {d1 : DeflateState}
    (run : dispatch (some (.tab ds)) flush d h = .ok (b, after))
    (hz1 : r.get after = some z1) (hs1 : after.dstates ds = some d1) :
    StratQuiet flush z d z1 d1 b := by
  obtain ⟨b', a', z', d', run', hz', hs', q⟩ := dispatch_q_nz inv ov entry flush l0 empty
  have e := run.symm.trans run'
  simp only [Except.ok.injEq, Prod.mk.injEq] at e
  obtain ⟨hb, ha⟩ := e
  subst hb ha
  have zE : z' = z1 := Option.some.inj (hz'.symm.trans hz1)
  have dE : d' = d1 := Option.some.inj (hs'.symm.trans hs1)
  subst zE dE
  obtain ⟨b2, a2, z2, d2, run2, inv2, _, _, meaning⟩ := dispatch_spec inv ov entry flush
  have e2 := run.symm.trans run2
  simp only [Except.ok.injEq, Prod.mk.injEq] at e2
  obtain ⟨hb2, ha2⟩ := e2
  subst hb2 ha2
  have zE2 : z2 = z' := Option.some.inj (inv2.good.live.hz.symm.trans hz')
  have dE2 : d2 = d' := Option.some.inj (inv2.good.live.hs.symm.trans hs')
  subst zE2 dE2
  refine ⟨q.le, q.eq, q.more, fun st => ?_, q.gz⟩
  rcases meaning with ⟨l, _⟩ | ⟨_, m⟩
  · exact absurd l l0
  · rcases m.more (Or.inr st) with full | ⟨nm, _⟩
    · exact full
    · rw [st] at nm; exact absurd nm (by decide)

/-- **`StratQuiet`**: a strategy run with no input, dispatched as in `deflate`, does not raise the work
term of the potential; an unchanged work term means a finishing return or no output and nothing
pending; `need_more` with output room leaves nothing pending and was not asked for `Z_FINISH`;
`finish_started` leaves the output full; `gzindex` is kept. -/
theorem strat_quiet {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState} {flush : Int32}
    (inv : DInv h r ds z d) (ov : Block.OverlayAt d.lit_bufsize.toNat) (entry : StrategyEntry h r z d)
    (busy : d.status = BUSY_STATE) (empty : z.avail_in = 0)
    {b : block_state} {after : Heap} {z1 : ZStream} {d1 : DeflateState}
    (run : dispatch (some (.tab ds)) flush d h = .ok (b, after))
    (hz1 : r.get after = some z1) (hs1 : after.dstates ds = some d1) :
    StratQuiet flush z d z1 d1 b := by
  by_cases l0 : d.level = 0
  · obtain ⟨b', a', z', d', run', hz', hs', q, started⟩ := stored_q inv entry.toIn flush l0 empty
    have runD : dispatch (some (.tab ds)) flush d h = .ok (b', a') := by
      simp only [C.run] at run'
      simp [dispatch, l0, run']
    have e := run.symm.trans runD
    simp only [Except.ok.injEq, Prod.mk.injEq] at e
    obtain ⟨hb, ha⟩ := e
    subst hb ha
    have zE : z' = z1 := Option.some.inj (hz'.symm.trans hz1)
    have dE : d' = d1 := Option.some.inj (hs'.symm.trans hs1)
    subst zE dE
    exact ⟨q.le, q.eq, q.more, started, q.gz⟩
  · exact strat_quiet_nz inv ov entry l0 empty run hz1 hs1

end Zlib.Deflate.Universal.Quiet

#print axioms Zlib.Deflate.Universal.huff_q
#print axioms Zlib.Deflate.Universal.rle_q
#print axioms Zlib.Deflate.Universal.fast_q
#print axioms Zlib.Deflate.Universal.slow_q
#print axioms Zlib.Deflate.Engine.Proofs.stored_q
#print axioms Zlib.Deflate.Universal.Quiet.strat_quiet_nz
#print axioms Zlib.Deflate.Universal.Quiet.strat_quiet

