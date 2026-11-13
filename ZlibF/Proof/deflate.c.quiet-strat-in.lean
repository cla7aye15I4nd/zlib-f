import ZlibF.Proof.«deflate.c.quiet-strat»

/-!
# deflate.c: a strategy run with input (`DeflateQuietIn`)

`strat_quiet_in` bounds a strategy run with input: the work term of the potential rises by at most
four per input byte the run consumed (`work d1 + 4·avail_in1 ≤ work d + 4·avail_in`), `gzindex` is
kept, and a run that consumed no input satisfies `StratQuiet`.

The loops of `deflate.c.quiet-strat` are run again with the weighted relation `QDI`: `fill_window`
reading `k` bytes raises the lookahead by `k`, so the work term by `3k`, and lowers `avail_in` by
`k`; every other step lowers the work term and reads nothing. When no byte was read, `QDI` gives
back `QDown`.
-/

namespace Zlib.Deflate.Universal
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Engine.Proofs
open Zlib.Deflate.Proofs
open ZlibF.Math.DeflateSymbols
open Zlib.Trees.Proofs.Out (TreesInvAt)
set_option autoImplicit false

/-! ## The weighted work term between two states -/

/-- From `z`, `d` to `z'`, `d'`: input only consumed, the work term plus four per input byte not
higher, `QDown` when no input was consumed, and `gzindex` kept. -/
structure QDI (z : ZStream) (d : DeflateState) (z' : ZStream) (d' : DeflateState) : Prop where
  avail : z'.avail_in.toNat ≤ z.avail_in.toNat
  le : Quiet.work d' + z'.avail_in.toNat * 4 ≤ Quiet.work d + z.avail_in.toNat * 4
  same : z'.avail_in = z.avail_in → QDown z d z' d'
  gz : d'.gzindex = d.gzindex

theorem QDI.refl {z : ZStream} {d : DeflateState} (pending : d.pending = 0) : QDI z d z d :=
  ⟨Nat.le_refl _, Nat.le_refl _, fun _ => QDown.refl pending, rfl⟩

theorem avail_eq_of {z1 z2 z3 : ZStream} (a : z2.avail_in.toNat ≤ z1.avail_in.toNat)
    (b : z3.avail_in.toNat ≤ z2.avail_in.toNat) (e : z3.avail_in = z1.avail_in) :
    z2.avail_in = z1.avail_in ∧ z3.avail_in = z2.avail_in := by
  have e' : z3.avail_in.toNat = z1.avail_in.toNat := by rw [e]
  exact ⟨UInt32.toNat_inj.mp (by omega), UInt32.toNat_inj.mp (by omega)⟩

theorem QDI.trans {z1 z2 z3 : ZStream} {d1 d2 d3 : DeflateState} (one : QDI z1 d1 z2 d2)
    (two : QDI z2 d2 z3 d3) : QDI z1 d1 z3 d3 :=
  ⟨Nat.le_trans two.avail one.avail, Nat.le_trans two.le one.le,
    fun e => let p := avail_eq_of one.avail two.avail e; (one.same p.1).trans (two.same p.2),
    two.gz.trans one.gz⟩

theorem QDI.of_down {z z' : ZStream} {d d' : DeflateState} (q : QDown z d z' d')
    (e : z'.avail_in = z.avail_in) : QDI z d z' d' := by
  refine ⟨q.avail, ?_, fun _ => q, q.gz⟩
  have := q.le
  rw [e]; omega

theorem QDI.of_lt {h h' : Heap} {r : ZStreamRef} {ds : Nat} {z z' : ZStream} {d d' : DeflateState}
    (fr : Fr h r ds d z h' z' d') (lt : Quiet.work d' < Quiet.work d) (gz : d'.gzindex = d.gzindex) :
    QDI z d z' d' := by
  have a := fr_avail fr
  exact ⟨a, by omega, fun _ => QDown.of_lt fr lt gz, gz⟩

/-- `fill_window` reading `k` bytes raises the work term by `3k` and lowers `avail_in` by `k`. -/
theorem fill_downI {roll : Prop} {h after : Heap} {r : ZStreamRef} {ds : Nat} {z z' : ZStream}
    {d d' : DeflateState} (post : FillPost roll h after r ds z z' d d')
    (pending : d.pending = 0) (lv : d.level ≠ 0) : QDI z d z' d' ∧ d'.pending = 0 := by
  obtain ⟨used, account, _⟩ := post.account
  obtain ⟨sLevel, _, _, _, _, sAvail, _, sSym, _, _, _, _, _, _, _, sPending, _⟩ := post.same
  have consumed := post.consumed
  have a1 := account.2.2.1
  have o1 := account.2.2.2.1
  have lv' : d'.level ≠ 0 := by rw [sLevel]; exact lv
  have w1 := work_nz lv
  have w2 := work_nz lv'
  rw [sAvail, sSym] at w2
  have gz : d'.gzindex = d.gzindex := by
    obtain ⟨base, choice, eq⟩ := post.fields
    rcases choice with same | ⟨_, same⟩ <;> subst same <;> exact (congrArg DeflateState.gzindex eq).trans rfl
  have out : z'.avail_out = z.avail_out := UInt32.toNat_inj.mp (by omega)
  refine ⟨⟨by omega, by omega, fun e => ?_, gz⟩, sPending.trans pending⟩
  have e' : z'.avail_in.toNat = z.avail_in.toNat := by rw [e]
  exact ⟨by omega, by omega, fun _ => ⟨out, sPending.trans pending⟩, gz⟩

/-- What `StratQuiet` asks of a run with input: the weighted bound, and `QEnd` when no input was
consumed. -/
structure QEndI (flush : Int32) (z : ZStream) (d : DeflateState) (z' : ZStream) (d' : DeflateState)
    (b : block_state) : Prop where
  avail : z'.avail_in.toNat ≤ z.avail_in.toNat
  le : Quiet.work d' + z'.avail_in.toNat * 4 ≤ Quiet.work d + z.avail_in.toNat * 4
  same : z'.avail_in = z.avail_in → QEnd flush z d z' d' b
  gz : d'.gzindex = d.gzindex

theorem QEndI.of_end {flush : Int32} {z z' : ZStream} {d d' : DeflateState} {b : block_state}
    (q : QEnd flush z d z' d' b) (e : z'.avail_in = z.avail_in) : QEndI flush z d z' d' b := by
  refine ⟨by rw [e]; exact Nat.le_refl _, ?_, fun _ => q, q.gz⟩
  have := q.le
  rw [e]; omega

theorem QEndI.after {flush : Int32} {z0 z z' : ZStream} {d0 d d' : DeflateState} {b : block_state}
    (down : QDI z0 d0 z d) (fin : QEndI flush z d z' d' b) : QEndI flush z0 d0 z' d' b :=
  ⟨Nat.le_trans fin.avail down.avail, Nat.le_trans fin.le down.le,
    fun e => let p := avail_eq_of down.avail fin.avail e; QEnd.after (down.same p.1) (fin.same p.2),
    fin.gz.trans down.gz⟩

theorem QEndI.more_of {flush : Int32} {z0 z : ZStream} {d0 d : DeflateState} (down : QDI z0 d0 z d)
    (why : z.avail_out = 0 ∨ (d.pending = 0 ∧ flush = Z_NO_FLUSH)) : QEndI flush z0 d0 z d need_more :=
  ⟨down.avail, down.le, fun e => QEnd.more_of (down.same e) why, down.gz⟩

/-! ## Strategy loops with input -/

/-- The measure: one more than the work term plus four per input byte. -/
def qMeasureI (r : ZStreamRef) (ds : Nat) (st : LoopS) (h : Heap) : Nat :=
  if st.brk || st.ret.isSome then 0 else
    match r.get h, h.dstates ds with
    | some z, some d => 1 + Quiet.work d + z.avail_in.toNat * 4
    | _, _ => 0

theorem qMeasureI_bound (r : ZStreamRef) (ds : Nat) (st : LoopS) (h : Heap) : qMeasureI r ds st h < fuel := by
  unfold qMeasureI fuel
  split
  · decide
  · split
    · rename_i z d _ _
      have := Quiet.work_lt d
      have := z.avail_in.toNat_lt
      omega
    · decide

theorem qMeasureI_head {r : ZStreamRef} {ds : Nat} {st : LoopS} {h : Heap} {z : ZStream} {d : DeflateState}
    (get : r.get h = some z) (state : h.dstates ds = some d)
    (brk : st.brk = false) (ret : st.ret = none) : qMeasureI r ds st h = 1 + Quiet.work d + z.avail_in.toNat * 4 := by
  simp [qMeasureI, brk, ret, get, state]

theorem qMeasureI_exit {r : ZStreamRef} {ds : Nat} {st : LoopS} {h : Heap}
    (exit : st.brk = true ∨ st.ret.isSome = true) : qMeasureI r ds st h = 0 := by
  rcases exit with e | e <;> simp [qMeasureI, e]

/-- The states of a strategy loop with input. -/
def QLoopI (K : DeflateState → Prop) (r : ZStreamRef) (ds : Nat) (z0 : ZStream) (d0 : DeflateState)
    (flush : Int32) (st : LoopS) (h : Heap) : Prop :=
  ∃ z d, Head K h r ds z d ∧ QDI z0 d0 z d ∧
    ((st.brk = false ∧ st.ret = none ∧ d.pending = 0) ∨
     (st.ret = some need_more ∧ (z.avail_out = 0 ∨ (d.pending = 0 ∧ flush = Z_NO_FLUSH))) ∨
     (st.brk = true ∧ st.ret = none ∧ d.pending = 0 ∧ d.lookahead = 0))

/-- One iteration with input: a continuing iteration lowers the weighted work term. -/
def QStepI (K : DeflateState → Prop) (r : ZStreamRef) (ds : Nat) (flush : Int32) (z : ZStream)
    (d : DeflateState) (st st' : LoopS) (h' : Heap) : Prop :=
  ∃ z' d', Head K h' r ds z' d' ∧ QDI z d z' d' ∧
    ((st'.brk = false ∧ st'.ret = none ∧ d'.pending = 0 ∧
        Quiet.work d' + z'.avail_in.toNat * 4 < Quiet.work d + z.avail_in.toNat * 4) ∨
     (st'.ret = some need_more ∧ (z'.avail_out = 0 ∨ (d'.pending = 0 ∧ flush = Z_NO_FLUSH))) ∨
     (st'.brk = true ∧ st'.ret = none ∧ d'.pending = 0 ∧ d'.lookahead = 0))

theorem q_loopI {K : DeflateState → Prop} {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream}
    {d : DeflateState} (body : LoopS → M LoopS) (flush : Int32)
    (head : Head K h r ds z d) (pending : d.pending = 0)
    (step : ∀ (st : LoopS) (h1 : Heap) (z1 : ZStream) (d1 : DeflateState), Head K h1 r ds z1 d1 →
      d1.pending = 0 → st.brk = false → st.ret = none →
      ∃ st' h', body st h1 = .ok (st', h') ∧ QStepI K r ds flush z1 d1 st st' h') :
    ∃ st h', cwhile forever body {} h = .ok (st, h') ∧ QLoopI K r ds z d flush st h' ∧
      (st.brk = true ∨ st.ret.isSome = true) := by
  have start : QLoopI K r ds z d flush {} h :=
    ⟨z, d, head, QDI.refl pending, Or.inl ⟨rfl, rfl, pending⟩⟩
  obtain ⟨st, h', run, loop, exit⟩ := cwhile_measure (cond := forever) (body := body)
    (QLoopI K r ds z d flush)
    (fun st h' => QLoopI K r ds z d flush st h' ∧ (st.brk = true ∨ st.ret.isSome = true)) (qMeasureI r ds)
    (fun st h1 ⟨z1, d1, head1, down1, cases⟩ => by
      rcases cases with ⟨brk, ret, pend1⟩ | ⟨ret, why⟩ | ⟨brk, ret, pend1, la1⟩
      · refine ⟨true, st, h1, (by simp [forever, brk, ret]), (fun _ => ?_), (fun e => by cases e)⟩
        obtain ⟨st', h', run', z', d', head', down', cases'⟩ := step st h1 z1 d1 head1 pend1 brk ret
        have m0 := qMeasureI_head (st := st) head1.inv.good.live.hz head1.inv.good.live.hs brk ret
        refine ⟨st', h', run', ⟨z', d', head', down1.trans down', ?_⟩, ?_⟩
        · rcases cases' with ⟨b, r', p, _⟩ | m | e
          · exact Or.inl ⟨b, r', p⟩
          · exact Or.inr (Or.inl m)
          · exact Or.inr (Or.inr e)
        · rcases cases' with ⟨b, r', _, lt⟩ | ⟨m, _⟩ | ⟨b, _⟩
          · rw [qMeasureI_head head'.inv.good.live.hz head'.inv.good.live.hs b r', m0]; omega
          · rw [qMeasureI_exit (Or.inr (by rw [m]; rfl)), m0]; omega
          · rw [qMeasureI_exit (Or.inl b), m0]; omega
      · refine ⟨false, st, h1, (by simp [forever, ret]), (fun e => by cases e), (fun _ => ?_)⟩
        exact ⟨⟨z1, d1, head1, down1, Or.inr (Or.inl ⟨ret, why⟩)⟩, Or.inr (by rw [ret]; rfl)⟩
      · refine ⟨false, st, h1, (by simp [forever, brk]), (fun e => by cases e), (fun _ => ?_)⟩
        exact ⟨⟨z1, d1, head1, down1, Or.inr (Or.inr ⟨brk, ret, pend1, la1⟩)⟩, Or.inl brk⟩)
    start (qMeasureI_bound r ds {} h)
  exact ⟨st, h', run, loop, exit⟩

theorem qstep_of_iterI {K : DeflateState → Prop} {h1 h' : Heap} {r : ZStreamRef} {ds : Nat}
    {z z1 z' : ZStream} {d d1 d' : DeflateState} {flush : Int32} {st st' : LoopS}
    (down1 : QDI z d z1 d1) (fr : Fr h1 r ds d1 z1 h' z' d') (head' : Head K h' r ds z' d')
    (lt : Quiet.work d' < Quiet.work d1) (gz : d'.gzindex = d1.gzindex) (brk' : st'.brk = st.brk)
    (brk : st.brk = false) (ret : st.ret = none)
    (cases : (st'.ret = st.ret ∧ d'.pending = 0) ∨ (st'.ret = some need_more ∧ z'.avail_out = 0)) :
    QStepI K r ds flush z d st st' h' := by
  have a := fr_avail fr
  have l1 := down1.le
  refine ⟨z', d', head', down1.trans (QDI.of_lt fr lt gz), ?_⟩
  rcases cases with ⟨e, p⟩ | ⟨e, o⟩
  · exact Or.inl ⟨brk'.trans brk, e.trans ret, p, by omega⟩
  · exact Or.inr (Or.inl ⟨e, Or.inl o⟩)

/-! ## The ends and the iterations -/

set_option maxHeartbeats 1600000 in
/-- The end of the compression functions (`finish_tail`) with the work term. -/
theorem finish_tail_qI {kind : DeflateState → Prop} {h : Heap} {r : ZStreamRef}
    {ds : Nat} {z : ZStream} {d : DeflateState} (head : Head kind h r ds z d) (pending : d.pending = 0)
    (flush : Int32) (quiet : d.match_available = 0) (look0 : d.lookahead = 0) :
    ∃ bstate after z' d', finish_tail (some (.tab ds)) flush h = .ok (bstate, after) ∧
      r.get after = some z' ∧ after.dstates ds = some d' ∧ QEndI flush z d z' d' bstate := by
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
        QEndI.of_end ⟨le, fun _ => Or.inr (Or.inl rfl), fun e => absurd e (by decide), gz⟩ keeps.availIn⟩
      simp [finish_tail, finish, bind_app, run']
    · subst started
      refine ⟨finish_started, after, z', result, ?_, invA.good.live.hz, invA.good.live.hs,
        QEndI.of_end ⟨le, fun _ => Or.inl rfl, fun e => absurd e (by decide), gz⟩ keeps.availIn⟩
      simp [finish_tail, finish, bind_app, run']
  · have finishB : (flush == Z_FINISH) = false := by simpa using finish
    have rdSym : rd (some (.tab ds)) (·.sym_next) h = .ok (d.sym_next, h) := by
      simp [rdD_eq, head.inv.good.live.hs]
    by_cases symbols : d.sym_next = 0
    · refine ⟨block_done, h, z, d, ?_, head.inv.good.live.hz, head.inv.good.live.hs,
        QEndI.of_end ⟨Nat.le_refl _, fun _ => Or.inr (Or.inr ⟨rfl, pending⟩), fun e => absurd e (by decide), rfl⟩ rfl⟩
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
          QEndI.of_end ⟨Nat.le_of_lt lt, fun e => absurd e (Nat.ne_of_lt lt), fun e => absurd e (by decide), gz⟩ keeps.availIn⟩
        simp [finish_tail, finishB, bind_app, rdSym, symbolsB, symbols, run']
      · subst more
        refine ⟨need_more, after, z', result, ?_, invA.good.live.hz, invA.good.live.hs,
          QEndI.of_end ⟨Nat.le_of_lt lt, fun e => absurd e (Nat.ne_of_lt lt),
            fun _ room => absurd (fullOut (Option.some_ne_none _)) room, gz⟩ keeps.availIn⟩
        simp [finish_tail, finishB, bind_app, rdSym, symbolsB, symbols, run']


set_option maxHeartbeats 1600000 in
/-- `finish_tail` from a state ready for a block flush that holds symbols, with the work term. -/
theorem finish_tail_readyQI {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream}
    {d : DeflateState} {buf : Array UInt8} {xs : List Symbol} (ready : BlockReady h r ds z d pb buf xs)
    (safe : FlushSafeAt d.lit_bufsize.toNat) (symbols : d.sym_next ≠ 0) (flush : Int32)
    (quiet : d.match_available = 0) (look0 : d.lookahead = 0) :
    ∃ bstate after z' d', finish_tail (some (.tab ds)) flush h = .ok (bstate, after) ∧
      r.get after = some z' ∧ after.dstates ds = some d' ∧ QEndI flush z d z' d' bstate := by
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
        QEndI.of_end ⟨le, fun _ => Or.inr (Or.inl rfl), fun e => absurd e (by decide), gz⟩ keeps.availIn⟩
      simp [finish_tail, finish, bind_app, run']
    · subst started
      refine ⟨finish_started, after, z', result, ?_, invA.good.live.hz, invA.good.live.hs,
        QEndI.of_end ⟨le, fun _ => Or.inl rfl, fun e => absurd e (by decide), gz⟩ keeps.availIn⟩
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
        QEndI.of_end ⟨Nat.le_of_lt lt, fun e => absurd e (Nat.ne_of_lt lt), fun e => absurd e (by decide), gz⟩ keeps.availIn⟩
      simp [finish_tail, finishB, bind_app, rdSym, symbols, run']
    · subst more
      refine ⟨need_more, after, z', result, ?_, invA.good.live.hz, invA.good.live.hs,
        QEndI.of_end ⟨Nat.le_of_lt lt, fun e => absurd e (Nat.ne_of_lt lt),
          fun _ room => absurd (fullOut (Option.some_ne_none _)) room, gz⟩ keeps.availIn⟩
      simp [finish_tail, finishB, bind_app, rdSym, symbols, run']


set_option maxHeartbeats 2400000 in
/-- **One iteration of `deflate_rle`** with input. -/
theorem rle_body_qI {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (head : Head RleKind h r ds z d) (pending : d.pending = 0)
    (flush : Int32) (st : LoopS) (brk : st.brk = false) (ret : st.ret = none) :
    ∃ st' h', deflate_rle_body (some (.tab ds)) flush st h = .ok (st', h') ∧
      QStepI RleKind r ds flush z d st st' h' := by
  have rdLook : rd (some (.tab ds)) (·.lookahead) h = .ok (d.lookahead, h) := by
    simp [rdD_eq, head.inv.good.live.hs]
  have finishIter : ∀ {h1 : Heap} {z1 : ZStream} {d1 : DeflateState}, Head RleKind h1 r ds z1 d1 →
      QDI z d z1 d1 → d1.pending = 0 → 1 ≤ d1.lookahead.toNat →
      d1.strstart.toNat + 258 < d1.window_size.toNat →
      ∃ st' h', (do
          wr (some (.tab ds)) (fun d => { d with match_length := 0 })
          rleScan (some (.tab ds))
          rleEmit (some (.tab ds)) st) h1 = .ok (st', h') ∧ QStepI RleKind r ds flush z d st st' h' := by
    intro h1 z1 d1 head1 down1 pending1 look1 room1
    obtain ⟨st', h', iterRun, brk', z', d', head', fr', la', gz', cases⟩ := rle_emit_iterQ head1 look1 room1 pending1 st
    exact ⟨st', h', iterRun, qstep_of_iterI down1 fr' head'
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
    obtain ⟨down1, pending1⟩ := fill_downI post pending head.level
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
    obtain ⟨st', h', iterRun, step⟩ := finishIter head (QDI.refl pending) pending (by omega) (by omega)
    refine ⟨st', h', ?_, step⟩
    simp only [bind_app, rdLook, M_ite_app, small, ite_false]
    exact iterRun


set_option maxHeartbeats 2400000 in
/-- **One iteration of `deflate_fast`** with input. -/
theorem fast_body_qI {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (head : Head FastKind h r ds z d) (pending : d.pending = 0)
    (flush : Int32) (st : LoopS) (brk : st.brk = false) (ret : st.ret = none) :
    ∃ st' h', deflate_fast_body (some (.tab ds)) flush st h = .ok (st', h') ∧
      QStepI FastKind r ds flush z d st st' h' := by
  have rdLook : rd (some (.tab ds)) (·.lookahead) h = .ok (d.lookahead, h) := by
    simp [rdD_eq, head.inv.good.live.hs]
  have finishIter : ∀ {h1 : Heap} {z1 : ZStream} {d1 : DeflateState}, Head FastKind h1 r ds z1 d1 →
      QDI z d z1 d1 → d1.pending = 0 → 1 ≤ d1.lookahead.toNat →
      d1.strstart.toNat + 262 ≤ d1.window_size.toNat →
      ∃ st' h', (do
          let hash_head ← fastSearch (some (.tab ds))
          fastEmit (some (.tab ds)) st hash_head) h1 = .ok (st', h') ∧ QStepI FastKind r ds flush z d st st' h' := by
    intro h1 z1 d1 head1 down1 pending1 look1 room1
    obtain ⟨st', h', iterRun, brk', z', d', head', fr', la', gz', cases⟩ := fast_iterQ head1 pending1 look1 room1 st
    exact ⟨st', h', iterRun, qstep_of_iterI down1 fr' head'
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
    obtain ⟨down1, pending1⟩ := fill_downI post pending head.level
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
    obtain ⟨st', h', iterRun, step⟩ := finishIter head (QDI.refl pending) pending (by omega) (by omega)
    refine ⟨st', h', ?_, step⟩
    simp only [bind_app, rdLook, M_ite_app, small, ite_false]
    simp only [bind_app] at iterRun
    exact iterRun


set_option maxHeartbeats 2400000 in
/-- **One iteration of `deflate_slow`** with input. -/
theorem slow_body_qI {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (head : Head SlowKind h r ds z d) (pending : d.pending = 0)
    (flush : Int32) (st : LoopS) (brk : st.brk = false) (ret : st.ret = none) :
    ∃ st' h', deflate_slow_body (some (.tab ds)) flush st h = .ok (st', h') ∧
      QStepI SlowKind r ds flush z d st st' h' := by
  have rdLook : rd (some (.tab ds)) (·.lookahead) h = .ok (d.lookahead, h) := by
    simp [rdD_eq, head.inv.good.live.hs]
  have finishIter : ∀ {h1 : Heap} {z1 : ZStream} {d1 : DeflateState}, Head SlowKind h1 r ds z1 d1 →
      QDI z d z1 d1 → d1.pending = 0 → 1 ≤ d1.lookahead.toNat →
      d1.strstart.toNat + 262 ≤ d1.window_size.toNat →
      ∃ st' h', (do
          let hash_head ← slowSearch (some (.tab ds))
          slowDecision (some (.tab ds)) flush st hash_head) h1 = .ok (st', h') ∧
        QStepI SlowKind r ds flush z d st st' h' := by
    intro h1 z1 d1 head1 down1 pending1 look1 room1
    obtain ⟨st', h', iterRun, brk', z', d', head', fr', wlt, gz', cases⟩ := slow_iterQ head1 pending1 look1 room1 flush st
    exact ⟨st', h', iterRun, qstep_of_iterI down1 fr' head' wlt gz' brk' brk ret cases⟩
  rw [slow_body_source]
  by_cases small : d.lookahead < MIN_LOOKAHEAD_u
  · have short : d.lookahead.toNat < 262 := UInt32.lt_iff_toNat_lt.mp small
    obtain ⟨after1, z1, d1, fillRun, inv1, buffers1, post⟩ :=
      fill_window_inv head.inv head.level head.buffers head.input short
    obtain ⟨sLevel, sStrategy, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := post.same
    have head1 : Head SlowKind after1 r ds z1 d1 :=
      head_after_fill head inv1 buffers1 post (fun k => by unfold SlowKind; rw [sStrategy, sLevel]; exact k)
    obtain ⟨down1, pending1⟩ := fill_downI post pending head.level
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
    obtain ⟨st', h', iterRun, step⟩ := finishIter head (QDI.refl pending) pending (by omega) (by omega)
    refine ⟨st', h', ?_, step⟩
    simp only [bind_app, rdLook, M_ite_app, small, ite_false]
    simp only [bind_app] at iterRun
    exact iterRun



set_option maxHeartbeats 2400000 in
/-- **One iteration of `deflate_huff`** with input. -/
theorem huff_body_qI {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (head : Head HuffKind h r ds z d) (pending : d.pending = 0)
    (flush : Int32) (st : LoopS) (brk : st.brk = false) (ret : st.ret = none) :
    ∃ st' h', deflate_huff_body (some (.tab ds)) flush st h = .ok (st', h') ∧
      QStepI HuffKind r ds flush z d st st' h' := by
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
    obtain ⟨down1, pending1⟩ := fill_downI post pending head.level
    have rdLook1 : rd (some (.tab ds)) (·.lookahead) after1 = .ok (d1.lookahead, after1) := by
      simp [rdD_eq, inv1.good.live.hs]
    by_cases empty1 : d1.lookahead = 0
    · have empty1B : (d1.lookahead == 0) = true := by simp [empty1]
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
    · have empty1B : (d1.lookahead == 0) = false := by simpa using empty1
      have look1 : 1 ≤ d1.lookahead.toNat := by
        have : d1.lookahead.toNat ≠ 0 := fun e => empty1 (UInt32.toNat_inj.mp e)
        omega
      obtain ⟨st', h', iterRun, brk', z', d', head', fr', la', gz', cases⟩ := huff_literal_iterQ head1 look1 pending1 st
      refine ⟨st', h', ?_, qstep_of_iterI down1 fr' head'
        (work_lt_noLazy head1.level head'.level (idle_of_roll head'.inv.shape (Or.inl head'.kind)) (by omega))
        gz' brk' brk ret cases⟩
      simp only [bind_app, rdLook, emptyB, ite_true]
      rw [show fill_window (some (.tab ds)) h = .ok ((), after1) from fillRun]
      simp only [bind_app, rdLook1, empty1B, Bool.false_eq_true, ite_false]
      exact iterRun
  · have emptyB : (d.lookahead == 0) = false := by simpa using emptyL
    have look : 1 ≤ d.lookahead.toNat := by
      have : d.lookahead.toNat ≠ 0 := fun e => emptyL (UInt32.toNat_inj.mp e)
      omega
    obtain ⟨st', h', iterRun, brk', z', d', head', fr', la', gz', cases⟩ := huff_literal_iterQ head look pending st
    refine ⟨st', h', ?_, qstep_of_iterI (QDI.refl pending) fr' head'
      (work_lt_noLazy head.level head'.level (idle_of_roll head'.inv.shape (Or.inl head'.kind)) (by omega))
      gz' brk' brk ret cases⟩
    simp only [bind_app, rdLook, emptyB, Bool.false_eq_true, ite_false]
    exact iterRun

/-- **`deflate_huff` with input** does not raise the work term plus four per input byte. -/
theorem huff_qI {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream}
    {d : DeflateState} (safe : FlushSafeAt d.lit_bufsize.toNat) (inv : DInv h r ds z d) (entry : StratIn h r z d)
    (flush : Int32) (level : d.level ≠ 0) (huff : d.strategy.toInt = 2) :
    ∃ bstate after z' d', C.run (Zlib.Deflate.deflate_huff (some (.tab ds)) flush) h = .ok (bstate, after) ∧
      r.get after = some z' ∧ after.dstates ds = some d' ∧ QEndI flush z d z' d' bstate := by
  have head : Head HuffKind h r ds z d := ⟨inv, entry.buffers, entry.out, entry.input, level, huff, safe⟩
  obtain ⟨st, h1, loopRun, ⟨z1, d1, head1, down1, cases⟩, exit⟩ :=
    q_loopI (deflate_huff_body (some (.tab ds)) flush) flush head entry.pending
      (fun st _ _ _ hd p b r => huff_body_qI hd p flush st b r)
  rcases cases with ⟨brk, ret0, _⟩ | ⟨ret, why⟩ | ⟨brk, ret, pending1, empty1⟩
  · rcases exit with e | e
    · rw [brk] at e; cases e
    · rw [ret0] at e; cases e
  · refine ⟨need_more, h1, z1, d1, ?_, head1.inv.good.live.hz, head1.inv.good.live.hs, QEndI.more_of down1 why⟩
    simp [C.run, deflate_huff, bind_app, loopRun, ret]
  · obtain ⟨wrRun, head2⟩ := clear_insert_head head1 id
    obtain ⟨bstate, after, z', d', tailRun, hz', hs', fin⟩ := finish_tail_qI head2 pending1 flush
      (idle_of_roll head1.inv.shape (Or.inl head1.kind) : d1.match_available = 0) empty1
    refine ⟨bstate, after, z', d', ?_, hz', hs', QEndI.after down1 (QEndI.after (QDI.of_down (insert_down pending1 0) rfl) fin)⟩
    simp only [C.run, deflate_huff, bind_app, loopRun, ret, wrRun]
    exact tailRun

/-- **`deflate_rle` with input** does not raise the work term plus four per input byte. -/
theorem rle_qI {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream}
    {d : DeflateState} (safe : FlushSafeAt d.lit_bufsize.toNat) (inv : DInv h r ds z d) (entry : StratIn h r z d)
    (flush : Int32) (level : d.level ≠ 0) (rle : d.strategy.toInt = 3) :
    ∃ bstate after z' d', C.run (Zlib.Deflate.deflate_rle (some (.tab ds)) flush) h = .ok (bstate, after) ∧
      r.get after = some z' ∧ after.dstates ds = some d' ∧ QEndI flush z d z' d' bstate := by
  have head : Head RleKind h r ds z d := ⟨inv, entry.buffers, entry.out, entry.input, level, rle, safe⟩
  obtain ⟨st, h1, loopRun, ⟨z1, d1, head1, down1, cases⟩, exit⟩ :=
    q_loopI (deflate_rle_body (some (.tab ds)) flush) flush head entry.pending
      (fun st _ _ _ hd p b r => rle_body_qI hd p flush st b r)
  rcases cases with ⟨brk, ret0, _⟩ | ⟨ret, why⟩ | ⟨brk, ret, pending1, empty1⟩
  · rcases exit with e | e
    · rw [brk] at e; cases e
    · rw [ret0] at e; cases e
  · refine ⟨need_more, h1, z1, d1, ?_, head1.inv.good.live.hz, head1.inv.good.live.hs, QEndI.more_of down1 why⟩
    simp [C.run, deflate_rle, bind_app, loopRun, ret]
  · obtain ⟨wrRun, head2⟩ := clear_insert_head head1 id
    obtain ⟨bstate, after, z', d', tailRun, hz', hs', fin⟩ := finish_tail_qI head2 pending1 flush
      (idle_of_roll head1.inv.shape (Or.inr head1.kind) : d1.match_available = 0) empty1
    refine ⟨bstate, after, z', d', ?_, hz', hs', QEndI.after down1 (QEndI.after (QDI.of_down (insert_down pending1 0) rfl) fin)⟩
    simp only [C.run, deflate_rle, bind_app, loopRun, ret, wrRun]
    exact tailRun

/-- **`deflate_fast` with input** does not raise the work term plus four per input byte. -/
theorem fast_qI {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream}
    {d : DeflateState} (safe : FlushSafeAt d.lit_bufsize.toNat) (inv : DInv h r ds z d) (entry : StratIn h r z d)
    (flush : Int32) (fast : 1 ≤ d.level.toInt ∧ d.level.toInt ≤ 3 ∧ d.strategy.toInt ≠ 2 ∧ d.strategy.toInt ≠ 3) :
    ∃ bstate after z' d', C.run (Zlib.Deflate.deflate_fast (some (.tab ds)) flush) h = .ok (bstate, after) ∧
      r.get after = some z' ∧ after.dstates ds = some d' ∧ QEndI flush z d z' d' bstate := by
  have level : d.level ≠ 0 := by
    intro zero; have := fast.1; rw [zero] at this; exact absurd this (by decide)
  have head : Head FastKind h r ds z d := ⟨inv, entry.buffers, entry.out, entry.input, level, fast, safe⟩
  obtain ⟨st, h1, loopRun, ⟨z1, d1, head1, down1, cases⟩, exit⟩ :=
    q_loopI (deflate_fast_body (some (.tab ds)) flush) flush head entry.pending
      (fun st _ _ _ hd p b r => fast_body_qI hd p flush st b r)
  rcases cases with ⟨brk, ret0, _⟩ | ⟨ret, why⟩ | ⟨brk, ret, pending1, empty1⟩
  · rcases exit with e | e
    · rw [brk] at e; cases e
    · rw [ret0] at e; cases e
  · refine ⟨need_more, h1, z1, d1, ?_, head1.inv.good.live.hz, head1.inv.good.live.hs, QEndI.more_of down1 why⟩
    simp [C.run, deflate_fast, bind_app, loopRun, ret]
  · obtain ⟨wrRun, head2⟩ := set_insert_head head1 empty1 (fun _ k => k)
    obtain ⟨bstate, after, z', d', tailRun, hz', hs', fin⟩ := finish_tail_qI head2 pending1 flush
      (idle_of_low head1.inv.shape head1.kind.2.1 : d1.match_available = 0) empty1
    refine ⟨bstate, after, z', d', ?_, hz', hs', QEndI.after down1 (QEndI.after (QDI.of_down (insert_down pending1 _) rfl) fin)⟩
    simp only [C.run, deflate_fast, bind_app, loopRun, ret, wrRun]
    exact tailRun

/-- **`deflate_slow` with input** does not raise the work term plus four per input byte. -/
theorem slow_qI {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream}
    {d : DeflateState} (safe : FlushSafeAt d.lit_bufsize.toNat) (inv : DInv h r ds z d) (entry : StratIn h r z d)
    (flush : Int32) (slow : 4 ≤ d.level.toInt ∧ d.strategy.toInt ≠ 2 ∧ d.strategy.toInt ≠ 3) :
    ∃ bstate after z' d', C.run (Zlib.Deflate.deflate_slow (some (.tab ds)) flush) h = .ok (bstate, after) ∧
      r.get after = some z' ∧ after.dstates ds = some d' ∧ QEndI flush z d z' d' bstate := by
  have level : d.level ≠ 0 := by
    intro zero; have := slow.1; rw [zero] at this; exact absurd this (by decide)
  have head : Head SlowKind h r ds z d := ⟨inv, entry.buffers, entry.out, entry.input, level, slow, safe⟩
  obtain ⟨st, h1, loopRun, ⟨z1, d1, head1, down1, cases⟩, exit⟩ :=
    q_loopI (deflate_slow_body (some (.tab ds)) flush) flush head entry.pending
      (fun st _ _ _ hd p b r => slow_body_qI hd p flush st b r)
  rcases cases with ⟨brk, ret0, _⟩ | ⟨ret, why⟩ | ⟨brk, ret, pending1, empty1⟩
  · rcases exit with e | e
    · rw [brk] at e; cases e
    · rw [ret0] at e; cases e
  · refine ⟨need_more, h1, z1, d1, ?_, head1.inv.good.live.hz, head1.inv.good.live.hs, QEndI.more_of down1 why⟩
    simp [C.run, deflate_slow, bind_app, loopRun, ret]
  · have ld1 : ldDeflateState (some (.tab ds)) h1 = .ok (d1, h1) := ldDeflateState_tab head1.inv.good.live.hs
    by_cases avail : d1.match_available ≠ 0
    · have availB : (d1.match_available != 0) = true := by simpa using avail
      obtain ⟨c, b, buf, xs, h3, readC, tallyRun, state3, ready, symbols, priv3⟩ :=
        slow_end_literal head1 pending1 empty1 avail
      obtain ⟨bstate, after, z', d', tailRun, hz', hs', fin⟩ :=
        finish_tail_readyQI ready head1.safe symbols flush rfl empty1
      have lt : Quiet.work (endState (literalState d1 c)) < Quiet.work d1 :=
        work_lt_end head1.level head1.level rfl rfl avail
      have downE : QDown z1 d1 z1 (endState (literalState d1 c)) :=
        ⟨Nat.le_refl _, Nat.le_of_lt lt, fun e => absurd e (Nat.ne_of_lt lt), rfl⟩
      refine ⟨bstate, after, z', d', ?_, hz', hs', QEndI.after down1 (QEndI.after (QDI.of_down downE rfl) fin)⟩
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
      obtain ⟨bstate, after, z', d', tailRun, hz', hs', fin⟩ := finish_tail_qI head2 pending1 flush idle empty1
      refine ⟨bstate, after, z', d', ?_, hz', hs', QEndI.after down1 (QEndI.after (QDI.of_down (insert_down pending1 _) rfl) fin)⟩
      simp only [C.run, deflate_slow, bind_app, loopRun, ret, ld1, availB, Bool.false_eq_true, ite_false, wrRun]
      exact tailRun

end Zlib.Deflate.Universal

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Universal
set_option autoImplicit false

/-! ## `deflate_stored` with input -/

set_option maxHeartbeats 4000000 in
open Zlib.Deflate.Universal in
/-- **The rest of an iteration.** With the header room (`have = avail_out - hv`), a length within
it whose input part is available, and `left = strstart - block_start`, the break test, the
emission and the direct copies keep the loop invariant; a completed iteration consumes output. -/
theorem stored_restG {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (buffers : StreamBuffers h r) (pend0 : d.pending = 0)
    (out : z.next_out ≠ .null) (input : z.avail_in ≠ 0 → z.next_in ≠ .null) (level0 : d.level = 0)
    (flush : Int32) (min_block : UInt32) (st : StoredS) (have_ left len : UInt32)
    (haveEq : have_.toNat + (d.bi_valid.toInt.toNat + 42) / 8 = z.avail_out.toNat)
    (leftEq : (left.toNat : Int) = d.strstart.toNat - d.block_start.toInt)
    (lenHave : len.toNat ≤ have_.toNat)
    (lenIn : (len - directLeft left len).toNat ≤ z.avail_in.toNat)
    (mbPos : 0 < min_block.toNat)
    (lenCase : len.toNat = left.toNat + z.avail_in.toNat ∨ len.toNat = have_.toNat ∨ len.toNat = 65535)
    (mbW : min_block.toNat ≤ d.w_size.toNat) :
    ∃ st' g z' d', storedRest (some (.tab ds)) flush (some r) min_block st have_ left len z h = .ok (st', g) ∧
      StoredStep h g r ds z z' d d' ∧ (st'.brk = false → z'.avail_out.toNat < z.avail_out.toNat) ∧
      (st.last = 0 → st'.last ≠ 0 → flush = Z_FINISH ∧ z'.avail_in = 0 ∧ d'.bi_valid.toInt = 0) ∧
      (st'.brk = true → g = h ∧ z' = z ∧ d' = d ∧
        (flush = Z_FINISH → z.avail_out.toNat < (d.bi_valid.toInt.toNat + 42) / 8 + min_block.toNat)) ∧
      (st'.brk = false → Zlib.Deflate.Universal.Quiet.work d' ≤ Zlib.Deflate.Universal.Quiet.work d ∧
        (z'.avail_in = z.avail_in → Zlib.Deflate.Universal.Quiet.work d' < Zlib.Deflate.Universal.Quiet.work d ∨ st'.last ≠ 0)) := by
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
    have geo := stored_geom good
    rcases lenCase with c | c | c
    · exfalso
      have ge : len ≥ left := UInt32.le_iff_toNat_le.mpr (by omega)
      have sub : len - left = z.avail_in :=
        UInt32.toNat_inj.mp (by rw [UInt32.toNat_sub_of_le _ _ ge]; omega)
      rw [fin, decide_eq_true ge, sub] at s2
      simp [show (Z_FINISH == Z_NO_FLUSH) = false by decide] at s2
    · omega
    · omega
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
      have w2 := work_l0 l2 shape2
      have w1 := work_l0 level0 shape
      have bsLo := zero.1
      have bsN := Int.toNat_of_nonneg bsLo
      have bs2N : 0 ≤ e2.block_start.toInt := by rw [bs2]; omega
      have bsN2 := Int.toNat_of_nonneg bs2N
      have bsHi := shape.blockStart
      have a3 := account.2.2.1
      have subN : (len - directLeft left len).toNat = len.toNat - (directLeft left len).toNat :=
        UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr dl.1)
      rw [w2, w1, ss2]
      refine ⟨by omega, fun ea => ?_⟩
      have ea' : z2.avail_in.toNat = z.avail_in.toNat := by rw [ea]
      by_cases l0 : len.toNat = 0
      · refine Or.inr ?_
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
      · exact Or.inl (by omega)

set_option maxHeartbeats 4000000 in
open Zlib.Deflate.Universal in
/-- **One iteration of the first loop of `deflate_stored`.** -/
theorem stored_iterationG {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (buffers : StreamBuffers h r) (pend0 : d.pending = 0)
    (out : z.next_out ≠ .null) (input : z.avail_in ≠ 0 → z.next_in ≠ .null) (level0 : d.level = 0)
    (flush : Int32) (min_block : UInt32) (st : StoredS) (mbPos : 0 < min_block.toNat)
    (mbW : min_block.toNat ≤ d.w_size.toNat) :
    ∃ st' g z' d', storedBody (some (.tab ds)) flush (some r) min_block st h = .ok (st', g) ∧
      StoredStep h g r ds z z' d d' ∧ (st'.brk = false → z'.avail_out.toNat < z.avail_out.toNat) ∧
      (st.last = 0 → st'.last ≠ 0 → flush = Z_FINISH ∧ z'.avail_in = 0 ∧ d'.bi_valid.toInt = 0) ∧
      (st'.brk = true → g = h ∧ z' = z ∧ d' = d ∧
        (flush = Z_FINISH → z.avail_out.toNat < (d.bi_valid.toInt.toNat + 42) / 8 + min_block.toNat)) ∧
      (st'.brk = false → Zlib.Deflate.Universal.Quiet.work d' ≤ Zlib.Deflate.Universal.Quiet.work d ∧
        (z'.avail_in = z.avail_in → Zlib.Deflate.Universal.Quiet.work d' < Zlib.Deflate.Universal.Quiet.work d ∨ st'.last ≠ 0)) := by
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
        exact stored_restG inv buffers pend0 out input level0 flush min_block _ _ left _ haveN leftEq
          (Nat.le_refl _) (stored_len_input _ _ _ (by have := UInt32.lt_iff_toNat_lt.mp c2; omega)
            (fun _ => by have := UInt32.lt_iff_toNat_lt.mp c2; omega)) mbPos (Or.inr (Or.inl rfl)) mbW
      · simp only [c2, decide_false, Bool.false_eq_true, ite_false]
        have c2N : ¬ (z.avail_out - (d.bi_valid.toUInt32 + 42) >>> 3).toNat < (left + z.avail_in).toNat :=
          fun c => c2 (UInt32.lt_iff_toNat_lt.mpr c)
        exact stored_restG inv buffers pend0 out input level0 flush min_block _ _ left _ haveN leftEq
          (by omega) (stored_len_input _ _ _ (by omega) (fun _ => by omega)) mbPos (Or.inl (by rw [sumN])) mbW
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
        exact stored_restG inv buffers pend0 out input level0 flush min_block _ _ left _ haveN leftEq
          (Nat.le_refl _) (stored_len_input _ _ _ (by have := UInt32.lt_iff_toNat_lt.mp c2; rw [maxN] at this; omega)
            (fun c => absurd c c1N)) mbPos (Or.inr (Or.inl rfl)) mbW
      · simp only [c2, decide_false, Bool.false_eq_true, ite_false]
        have c2N : ¬ (z.avail_out - (d.bi_valid.toUInt32 + 42) >>> 3).toNat < MAX_STORED.toNat :=
          fun c => c2 (UInt32.lt_iff_toNat_lt.mpr c)
        rw [maxN] at c2N
        exact stored_restG inv buffers pend0 out input level0 flush min_block _ _ left _ haveN leftEq
          (by rw [maxN]; omega) (stored_len_input _ _ _ (by rw [maxN]; exact Nat.le_refl _) (fun c => absurd c c1N)) mbPos (Or.inr (Or.inr maxN)) mbW

/-- **The first loop of `deflate_stored` with input**: it does not raise the work term; with no input
consumed an unchanged work term means no output or a last block; a stop without a last block under
`Z_FINISH` leaves less output room than a header and `min_block`. -/
theorem stored_loopG {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : Zlib.Deflate.Universal.DInv h r ds z d) (buffers : StreamBuffers h r) (pend0 : d.pending = 0)
    (out : z.next_out ≠ .null) (input : z.avail_in ≠ 0 → z.next_in ≠ .null) (level0 : d.level = 0)
    (flush : Int32) (min_block : UInt32) (st0 : StoredS) (start : st0.last = 0)
    (mbPos : 0 < min_block.toNat) (mbW : min_block.toNat ≤ d.w_size.toNat) :
    ∃ st g z' d', cdoWhile (storedBody (some (.tab ds)) flush (some r) min_block)
        (fun st => pure (!st.brk && st.last == 0, st)) st0 h = .ok (st, g) ∧
      StoredStep h g r ds z z' d d' ∧
      (st.last ≠ 0 → flush = Z_FINISH ∧ z'.avail_in = 0 ∧ d'.bi_valid.toInt = 0) ∧
      Zlib.Deflate.Universal.Quiet.work d' ≤ Zlib.Deflate.Universal.Quiet.work d ∧
      (z'.avail_in = z.avail_in → Zlib.Deflate.Universal.Quiet.work d' = Zlib.Deflate.Universal.Quiet.work d →
        z'.avail_out = z.avail_out ∨ st.last ≠ 0) ∧
      (st.last = 0 → flush = Z_FINISH →
        z'.avail_out.toNat < (d'.bi_valid.toInt.toNat + 42) / 8 + min_block.toNat) := by
  let W : ZStream → DeflateState → Prop := fun z' d' =>
    Zlib.Deflate.Universal.Quiet.work d' ≤ Zlib.Deflate.Universal.Quiet.work d ∧
    (z'.avail_in = z.avail_in → Zlib.Deflate.Universal.Quiet.work d' = Zlib.Deflate.Universal.Quiet.work d →
      z'.avail_out = z.avail_out)
  let P : StoredS → Heap → Prop := fun s g => s.last = 0 ∧ ∃ z' d', StoredStep h g r ds z z' d d' ∧ W z' d'
  let Q : StoredS → Heap → Prop := fun s g => ∃ z' d', StoredStep h g r ds z z' d d' ∧
    (s.last ≠ 0 → flush = Z_FINISH ∧ z'.avail_in = 0 ∧ d'.bi_valid.toInt = 0) ∧
    Zlib.Deflate.Universal.Quiet.work d' ≤ Zlib.Deflate.Universal.Quiet.work d ∧
    (z'.avail_in = z.avail_in → Zlib.Deflate.Universal.Quiet.work d' = Zlib.Deflate.Universal.Quiet.work d →
      z'.avail_out = z.avail_out ∨ s.last ≠ 0) ∧
    (s.last = 0 → flush = Z_FINISH → z'.avail_out.toNat < (d'.bi_valid.toInt.toNat + 42) / 8 + min_block.toNat)
  let μ : StoredS → Heap → Nat := fun _ g => match r.get g with | some z' => z'.avail_out.toNat | none => 0
  have step : ∀ s g, P s g → ∃ s1 g1 c s2 g2, storedBody (some (.tab ds)) flush (some r) min_block s g = .ok (s1, g1) ∧
      (fun st : StoredS => (pure (!st.brk && st.last == 0, st) : M (Bool × StoredS))) s1 g1 = .ok ((c, s2), g2) ∧
      (c = true → P s2 g2 ∧ μ s2 g2 < μ s g) ∧ (c = false → Q s2 g2) := by
    intro s g ⟨l0, z1, d1, now, w1⟩
    have level1 : d1.level = 0 := by rw [now.fields]; exact level0
    have ws1 : d1.w_size = d.w_size := by rw [now.fields]
    obtain ⟨s1, g1, z2, d2, run, next, dec, lastF, brkI, emitI⟩ := stored_iterationG now.inv now.buffers now.pending
      now.out now.input level1 flush min_block s mbPos (by rw [ws1]; exact mbW)
    have total := StoredStep.trans inv.good buffers now next
    have av1 := Zlib.Deflate.Universal.fr_avail now.fr
    have av2 := Zlib.Deflate.Universal.fr_avail next.fr
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
      refine ⟨by have := w1.1; omega, fun ea ew => ?_⟩
      have p := Zlib.Deflate.Universal.avail_eq_of av1 av2 ea
      rcases lt2 p.2 with lt2 | nz
      · have := w1.1; omega
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
        exact ⟨_, _, total, lastF l0, w1.1, fun ea ew => Or.inl (w1.2 ea ew), fun _ f => fr f⟩
      · have b' : s1.brk = false := by simpa using b
        have nz : s1.last ≠ 0 := by
          rw [b'] at c; simpa using c
        obtain ⟨le2, _⟩ := emitI b'
        exact ⟨z2, d2, total, lastF l0, by have := w1.1; omega, fun _ _ => Or.inr nz, fun e => absurd e nz⟩
  have bound : μ st0 h < fuel := by
    show (match r.get h with | some z' => z'.avail_out.toNat | none => 0) < 2 ^ 64
    rw [inv.good.live.hz]
    have := z.avail_out.toNat_lt
    show z.avail_out.toNat < 2 ^ 64
    omega
  obtain ⟨st, g, run, ⟨z', d', final, lastF, le, eq, fin⟩⟩ := C.cdoWhile_decreasing P Q μ step
    ⟨start, z, d, StoredStep.refl inv buffers pend0 out input, Nat.le_refl _, fun _ _ => rfl⟩ bound
  exact ⟨st, g, z', d', run, final, lastF, le, eq, fin⟩

set_option maxHeartbeats 8000000 in
/-- **The refill of the window keeps `DInv`.** -/
theorem stored_refillG {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (buffers : StreamBuffers h r) (level0 : d.level = 0)
    (input : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ g zF eF used, storedRefill (some (.tab ds)) (some r) d h = .ok ((), g) ∧ DInv g r ds zF eF ∧
      StreamBuffers g r ∧ ByteSizes h g ∧ StreamAccounting z zF used 0 ∧
      (∃ ss ins m bs hw, eF = keepState d ss ins m bs hw) ∧ g.static = h.static ∧ g.nalloc = h.nalloc ∧
          Totals z zF used 0 ∧ PrivStep h g r ds d ∧
      (((eF.strstart.toNat : Int) - eF.block_start.toInt ≤ (d.strstart.toNat : Int) - d.block_start.toInt + used) ∧
        (used = 0 → z.avail_in ≠ 0 → d.strstart.toNat = d.window_size.toNat ∧ d.block_start.toInt < d.w_size.toNat ∧
          eF.strstart = d.strstart ∧ eF.block_start = d.block_start)) := by
  have good := inv.good
  have shape := inv.shape
  have zero := shape.levelZero level0
  obtain ⟨w, wa, win, getW, sizeW⟩ := window_block good
  have wsz := good.inv.wsz
  have wsize := good.inv.wsize
  have wbits := good.inv.wbits_hi
  have wbitsLo := good.inv.wbits_lo
  have wpow : 2 ^ d.w_bits.toNat ≤ 2 ^ 15 := Nat.pow_le_pow_right (by omega) wbits
  have wpowLo : 2 ^ 9 ≤ 2 ^ d.w_bits.toNat := Nat.pow_le_pow_right (by omega) wbitsLo
  have room := shape.room
  have la : d.lookahead.toNat = 0 := by rw [zero.2.1]; rfl
  have insLe := shape.insert
  have bsHi := shape.blockStart
  have hwLe := shape.highWater
  have hz := good.live.hz
  have state0 := good.live.hs
  have getWv : Space.get h (BRef.blk w) = some wa := getW
  have ro : Space.ro h (BRef.blk w) = false := by
    obtain ⟨w0, p0, q0, b0, blocks⟩ := good.inv.blocks
    have : w0 = w := by simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.win.symm
    subst this; exact blocks.wro
  have hash0 : LevelHash h d := ⟨inv.hashing.chains, inv.hashing.slid⟩
  have readAvail : ∀ H : Heap, r.get H = some z → zrd (some r) (·.avail_in) H = .ok (z.avail_in, H) := by
    intro H hzH; simp [zrd_eq, hzH]
  have have0N : ((d.window_size - d.strstart.toUInt64).toUInt32).toNat = d.window_size.toNat - d.strstart.toNat := by
    rw [UInt64.toNat_toUInt32, UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]
    simp; omega
  have ssLt := d.strstart.toNat_lt
  have aLt := z.avail_in.toNat_lt
  have hSelf : setD { h with bytes := upd h.bytes w (some wa) } ds d = h := by
    rw [upd_self _ _ _ getW]; exact setD_self state0
  unfold storedRefill
  simp only [bind_app, readAvail h hz]
  by_cases cond : (decide (z.avail_in > (d.window_size - d.strstart.toUInt64).toUInt32) &&
      decide (d.block_start ≥ d.w_size.toUInt64.toInt64)) = true
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at cond
    obtain ⟨more, far⟩ := cond
    have moreN := UInt32.lt_iff_toNat_lt.mp more
    rw [have0N] at moreN
    have wsN : d.w_size.toUInt64.toInt64.toInt = d.w_size.toNat := u32_toInt64_toInt _
    have farN : (d.w_size.toNat : Int) ≤ d.block_start.toInt := by
      have := Int64.le_iff_toInt_le.mp far; rw [wsN] at this; exact this
    have wide : d.w_size.toNat ≤ d.strstart.toNat := by omega
    have slide := stored_slide_run state0 win getWv ro (by omega) wide (by omega) zero.1 bsHi
    obtain ⟨wa1, hwa1⟩ : ∃ x, x = copyRange wa wa 0 d.w_size.toNat (d.strstart - d.w_size).toNat := ⟨_, rfl⟩
    rw [← hwa1] at slide
    have size1 : wa1.size = wa.size := by rw [hwa1, size_copyRange]
    have ssN : (d.strstart - d.w_size).toNat = d.strstart.toNat - d.w_size.toNat :=
      UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr wide)
    have hz1 : r.get (setD (Space.put h (BRef.blk w) wa1) ds (refillSlide d)) = some z := by
      show r.get (Space.put h (BRef.blk w) wa1) = some z
      rw [view_put_stream]; exact hz
    have i1 : (refillSlide d).insert.toNat ≤ d.insert.toNat ∧
        (refillSlide d).insert.toNat ≤ (d.strstart - d.w_size).toNat := by
      show (if d.insert > d.strstart - d.w_size then d.strstart - d.w_size else d.insert).toNat ≤ _ ∧
        (if d.insert > d.strstart - d.w_size then d.strstart - d.w_size else d.insert).toNat ≤ _
      split
      · rename_i gt; have := UInt32.lt_iff_toNat_lt.mp gt; omega
      · rename_i ngt
        have : ¬ (d.strstart - d.w_size).toNat < d.insert.toNat := fun c => ngt (UInt32.lt_iff_toNat_lt.mpr c)
        omega
    have m1 : (refillSlide d).«matches».toNat ≤ 2 := by
      have := shape.slides.1
      show (if d.«matches» < 2 then d.«matches» + 1 else d.«matches»).toNat ≤ 2
      split
      · rename_i lt; have := UInt32.lt_iff_toNat_lt.mp lt; rw [UInt32.toNat_add]; simp at this ⊢; omega
      · omega
    have bs1 : (Int64.ofInt (d.block_start.toInt - d.w_size.toNat)).toInt = d.block_start.toInt - d.w_size.toNat :=
      int64_ofInt_toInt _ (by omega) (by omega)
    have hashE : LevelHash (setD { h with bytes := upd h.bytes w (some wa1) } ds (refillSlide d)) (refillSlide d) :=
      level_hash_slide hash0 zero.2.1 zero.2.1 ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl
        ⟨d.w_bits.toNat, wsize⟩ (by omega) wide ssN i1.1 (fun _ _ => rfl)
        (fun w' wa' e g' => by
          have : w' = w := by simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using e.symm
          subst this
          have : wa' = wa := Option.some.inj (g'.symm.trans getW)
          subst this
          refine ⟨wa1, upd_same _ _ _, fun i lt => ?_⟩
          rw [hwa1, bfn_copyRange _ _ _ _ _ _ (by omega), if_pos (by omega)]
          congr 1; omega)
    have have1N : ((d.window_size - d.strstart.toUInt64).toUInt32 + d.w_size).toNat =
        d.window_size.toNat - d.strstart.toNat + d.w_size.toNat := by
      rw [UInt32.toNat_add, have0N]; omega
    have finishA : ∀ n : UInt32, n.toNat ≤ z.avail_in.toNat →
        n.toNat ≤ d.window_size.toNat - d.strstart.toNat + d.w_size.toNat → 1 ≤ n.toNat →
        ∃ g zF eF used, storedRead (some (.tab ds)) (some r) n (setD (Space.put h (BRef.blk w) wa1) ds (refillSlide d)) =
            .ok ((), g) ∧ DInv g r ds zF eF ∧ StreamBuffers g r ∧ ByteSizes h g ∧ StreamAccounting z zF used 0 ∧
          (∃ ss ins m bs hw, eF = keepState d ss ins m bs hw) ∧ g.static = h.static ∧ g.nalloc = h.nalloc ∧
          Totals z zF used 0 ∧ PrivStep h g r ds d ∧
          ((eF.strstart.toNat : Int) - eF.block_start.toInt ≤ (d.strstart.toNat : Int) - d.block_start.toInt + used) ∧
          used ≠ 0 := by
      intro n avail fitN one
      have shapeF : Shape (refillRead (refillSlide d) n) := shape_refill shape level0 (d.strstart - d.w_size) (refillSlide d).insert
        (refillSlide d).«matches» (Int64.ofInt (d.block_start.toInt - d.w_size.toNat)) d.high_water n
        (by omega) i1.2 (by rw [bs1]; omega) (by rw [bs1]; omega) hwLe m1 (fun _ => by omega) (by omega)
      obtain ⟨g, zF, run, invG, buffersG, sizesG, acc, st, na, tot, pv⟩ := refill_finish inv buffers level0 win getW
        (refillSlide d) wa1 size1 ⟨_, _, _, _, _, rfl⟩ hashE n avail
        (by show (d.strstart - d.w_size).toNat + n.toNat ≤ wa.size; omega) (by omega) i1.2 input shapeF
      refine ⟨g, zF, _, n.toNat, run, invG, buffersG, sizesG, acc, ⟨_, _, _, _, _, rfl⟩, st, na, tot, pv, ?_, by omega⟩
      show (((d.strstart - d.w_size) + n).toNat : Int) - (Int64.ofInt (d.block_start.toInt - d.w_size.toNat)).toInt ≤ _
      rw [bs1, UInt32.toNat_add, ssN, Nat.mod_eq_of_lt (by omega)]
      push_cast
      omega
    have condT : (decide (z.avail_in > (d.window_size - d.strstart.toUInt64).toUInt32) &&
        decide (d.block_start ≥ d.w_size.toUInt64.toInt64)) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨more, far⟩
    simp only [condT, ite_true, bind_app, slide, readAvail _ hz1]
    by_cases c2 : (d.window_size - d.strstart.toUInt64).toUInt32 + d.w_size > z.avail_in
    · have c2N := UInt32.lt_iff_toNat_lt.mp c2
      rw [have1N] at c2N
      simp only [c2, decide_true, ite_true]
      obtain ⟨g, zF, eF, used, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, wk, nz⟩ := finishA _ (Nat.le_refl _) (by omega) (by omega)
      exact ⟨g, zF, eF, used, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, wk, fun e => absurd e nz⟩
    · have c2N : ¬ z.avail_in.toNat < ((d.window_size - d.strstart.toUInt64).toUInt32 + d.w_size).toNat :=
        fun c => c2 (UInt32.lt_iff_toNat_lt.mpr c)
      rw [have1N] at c2N
      simp only [c2, decide_false, Bool.false_eq_true, ite_false]
      obtain ⟨g, zF, eF, used, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, wk, nz⟩ :=
        finishA _ (by rw [have1N]; omega) (by rw [have1N]; exact Nat.le_refl _) (by rw [have1N]; omega)
      exact ⟨g, zF, eF, used, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, wk, fun e => absurd e nz⟩
  · simp only [Bool.not_eq_true] at cond
    simp only [cond, Bool.false_eq_true, ite_false, bind_app, readAvail h hz]
    have finishB : ∀ n : UInt32, n.toNat ≤ z.avail_in.toNat → n.toNat ≤ d.window_size.toNat - d.strstart.toNat →
        ∃ g zF eF used, storedRead (some (.tab ds)) (some r) n h = .ok ((), g) ∧ DInv g r ds zF eF ∧
          StreamBuffers g r ∧ ByteSizes h g ∧ StreamAccounting z zF used 0 ∧
          (∃ ss ins m bs hw, eF = keepState d ss ins m bs hw) ∧ g.static = h.static ∧ g.nalloc = h.nalloc ∧
          Totals z zF used 0 ∧ PrivStep h g r ds d ∧
          ((eF.strstart.toNat : Int) - eF.block_start.toInt ≤ (d.strstart.toNat : Int) - d.block_start.toInt + used) ∧
          used = n.toNat ∧ (n.toNat = 0 → eF.strstart = d.strstart ∧ eF.block_start = d.block_start) := by
      intro n avail fitN
      have same : keepState d d.strstart d.insert d.«matches» d.block_start d.high_water = d := rfl
      have shapeF := shape_refill shape level0 d.strstart d.insert d.«matches» d.block_start d.high_water n
        (by omega) insLe zero.1 bsHi hwLe shape.slides.1 (fun av => by have := shape.available av; omega) (by omega)
      have hashE : LevelHash (setD { h with bytes := upd h.bytes w (some wa) } ds
          (keepState d d.strstart d.insert d.«matches» d.block_start d.high_water))
          (keepState d d.strstart d.insert d.«matches» d.block_start d.high_water) := by
        rw [same, hSelf]; exact hash0
      obtain ⟨g, zF, run, invG, buffersG, sizesG, acc, st, na, tot, pv⟩ := refill_finish inv buffers level0 win getW
        (keepState d d.strstart d.insert d.«matches» d.block_start d.high_water) wa rfl ⟨_, _, _, _, _, rfl⟩
        hashE n avail (by show d.strstart.toNat + n.toNat ≤ wa.size; omega) (by omega) insLe input shapeF
      rw [same, hSelf] at run
      refine ⟨g, zF, _, n.toNat, run, invG, buffersG, sizesG, acc, ⟨_, _, _, _, _, rfl⟩, st, na, tot, pv, ?_, rfl, fun n0 => by
        have : n = 0 := UInt32.toNat_inj.mp (by rw [n0]; rfl)
        subst this
        exact ⟨by show d.strstart + 0 = d.strstart; simp, rfl⟩⟩
      show ((d.strstart + n).toNat : Int) - d.block_start.toInt ≤ _
      rw [UInt32.toNat_add, Nat.mod_eq_of_lt (by omega)]
      push_cast
      omega
    by_cases c2 : (d.window_size - d.strstart.toUInt64).toUInt32 > z.avail_in
    · have c2N := UInt32.lt_iff_toNat_lt.mp c2
      rw [have0N] at c2N
      simp only [c2, decide_true, ite_true]
      obtain ⟨g, zF, eF, used, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, wk, un, _⟩ := finishB _ (Nat.le_refl _) (by omega)
      refine ⟨g, zF, eF, used, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, wk, fun u0 nz => absurd ?_ nz⟩
      exact UInt32.toNat_inj.mp (by rw [u0] at un; rw [← un]; rfl)
    · have c2N : ¬ z.avail_in.toNat < ((d.window_size - d.strstart.toUInt64).toUInt32).toNat :=
        fun c => c2 (UInt32.lt_iff_toNat_lt.mpr c)
      rw [have0N] at c2N
      simp only [c2, decide_false, Bool.false_eq_true, ite_false]
      obtain ⟨g, zF, eF, used, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, wk, un, n0⟩ :=
        finishB _ (by rw [have0N]; omega) (by rw [have0N]; exact Nat.le_refl _)
      refine ⟨g, zF, eF, used, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, wk, fun u0 nz => ?_⟩
      have nfacts := n0 (by rw [← un, u0])
      rw [u0, have0N] at un
      have aN : z.avail_in.toNat ≠ 0 := fun c => nz (UInt32.toNat_inj.mp (by rw [c]; rfl))
      refine ⟨by omega, ?_, nfacts.1, nfacts.2⟩
      have nc : ¬ (z.avail_in > (d.window_size - d.strstart.toUInt64).toUInt32 ∧
          d.block_start ≥ d.w_size.toUInt64.toInt64) := by
        intro ⟨x, y⟩; rw [decide_eq_true x, decide_eq_true y] at cond; simp at cond
      have gt : z.avail_in > (d.window_size - d.strstart.toUInt64).toUInt32 := by
        rw [GT.gt, UInt32.lt_iff_toNat_lt, have0N]; omega
      have lt : ¬ d.block_start ≥ d.w_size.toUInt64.toInt64 := fun c => nc ⟨gt, c⟩
      have wsN : d.w_size.toUInt64.toInt64.toInt = d.w_size.toNat := u32_toInt64_toInt _
      have hlt : ¬ ((d.w_size.toNat : Int) ≤ d.block_start.toInt) :=
        fun c => lt (Int64.le_iff_toInt_le.mpr (by rw [wsN]; exact c))
      omega

set_option maxHeartbeats 8000000 in
open Zlib.Deflate.Universal in
/-- The final block of `deflate_stored` with input: it lowers the work term and reads nothing. -/
theorem stored_finalG {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (buffers : StreamBuffers h r) (pend0 : d.pending = 0) (out : z.next_out ≠ .null)
    (level0 : d.level = 0) (flush last0 : Int32) (lastZero : last0 = 0) :
    ∃ ret g z' d', storedFinal (some (.tab ds)) flush (some r) last0 h = .ok (ret, g) ∧
      r.get g = some z' ∧ g.dstates ds = some d' ∧ Zlib.Deflate.Universal.Quiet.work d' ≤ Zlib.Deflate.Universal.Quiet.work d ∧ z'.avail_in = z.avail_in ∧
      d'.gzindex = d.gzindex ∧
      (z.avail_in ≠ 0 → (d.w_size.toNat : Int) < (d.strstart.toNat : Int) - d.block_start.toInt →
        (flush = Z_FINISH → z.avail_out.toNat + 1 ≤ (d.bi_valid.toInt.toNat + 42) / 8 +
          min (d.pending_buf_size.toNat - 5) d.w_size.toNat) →
        QEnd flush z d z' d' ret ∧ ret ≠ finish_started) := by
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
    have inA : z'.avail_in = z.avail_in := UInt32.toNat_inj.mp (by have := accA.2.2.1; omega)
    simp only [c, ite_true, bind_app, add, blk, lad, wrt, fl]
    by_cases l0 : ((if (flush == Z_FINISH && z.avail_in == 0 && MIN left Hv == left) = true then (1 : Int32) else 0) != 0) = true
    · obtain ⟨wrRun, invB, buffersB⟩ := bi_used_step invA buffersA levelA
      refine ⟨finish_started, _, z', _, by simp only [l0, ite_true, bind_app, wrRun]; rfl, invB.good.live.hz,
        invB.good.live.hs, by show Zlib.Deflate.Universal.Quiet.work e ≤ _; omega, inA, gzA, fun nz _ _ => ?_⟩
      exfalso
      by_cases cf : (flush == Z_FINISH && z.avail_in == 0 && MIN left Hv == left) = true
      · simp only [Bool.and_eq_true, beq_iff_eq] at cf; exact nz cf.1.2
      · rw [if_neg cf] at l0; simp at l0
    · simp only [Bool.not_eq_true] at l0
      refine ⟨need_more, after, z', e, by simp only [l0, Bool.false_eq_true, ite_false, bind_app, pure_app],
        invA.good.live.hz, invA.good.live.hs, by omega, inA, gzA, fun nz wide finB => ⟨?_, fun e => absurd e (by decide)⟩⟩
      have lenPos : 0 < (MIN left Hv).toNat := by omega
      have fullFin : flush = Z_FINISH → z'.avail_out = 0 := by
        intro f
        have fr := finB f
        exact UInt32.toNat_inj.mp (by
          have : z'.avail_out.toNat = 0 := by omega
          rw [this]; rfl)
      refine ⟨by omega, fun ew => absurd ew (by omega), fun _ room => ⟨?_, fun f => room (fullFin f)⟩, gzA⟩
      have r0 : z'.avail_out.toNat ≠ 0 := fun x => room (UInt32.toNat_inj.mp (by rw [x]; rfl))
      exact UInt64.toNat_inj.mp (by
        have : e.pending.toNat = 0 := by omega
        rw [this]; rfl)
  · simp only [Bool.not_eq_true] at c
    simp only [c, Bool.false_eq_true, ite_false]
    subst lastZero
    refine ⟨need_more, h, z, d, by simp [bind_app], good.live.hz, good.live.hs, Nat.le_refl _, rfl, rfl,
      fun _ wide _ => ?_⟩
    exfalso
    have h1 : ¬ (left ≥ MIN Hv d.w_size) := by
      intro ge; rw [decide_eq_true ge] at c; simp at c
    have a1 : ¬ (MIN Hv d.w_size).toNat ≤ left.toNat := fun x => h1 (UInt32.le_iff_toNat_le.mpr x)
    omega

/-- A run that ends with a state write leaves the written state. -/
theorem wr_last {α : Type} {m : M α} {f : DeflateState → DeflateState} {ds : Nat} {h g : Heap}
    (run : (m >>= fun _ => wr (some (.tab ds)) f) h = .ok ((), g)) : ∃ v, g.dstates ds = some (f v) := by
  rw [bind_app] at run
  cases hm : m h with
  | error e => rw [hm] at run; cases run
  | ok p =>
    obtain ⟨a, h1⟩ := p
    rw [hm] at run
    simp only at run
    rw [wrD_eq] at run
    cases hv : h1.dstates ds with
    | none => rw [hv] at run; cases run
    | some v =>
      rw [hv] at run
      simp only [Except.ok.injEq, Prod.mk.injEq] at run
      rw [← run.2]
      exact ⟨v, setD_dstates_same _ _ _⟩

theorem wr_state {f : DeflateState → DeflateState} {ds : Nat} {h g : Heap} {v : DeflateState}
    (run : wr (some (.tab ds)) f h = .ok ((), g)) (hs : h.dstates ds = some v) : g.dstates ds = some (f v) := by
  rw [wrD_eq, hs] at run
  simp only [Except.ok.injEq, Prod.mk.injEq] at run
  rw [← run.2]
  exact setD_dstates_same _ _ _

/-- A run whose every path ends with the state write `f`. -/
def EndsWith (ds : Nat) (f : DeflateState → DeflateState) {α : Type} (m : M α) : Prop :=
  ∀ h x g, m h = .ok (x, g) → ∃ v, g.dstates ds = some (f v)

theorem EndsWith.wr' {ds : Nat} {f : DeflateState → DeflateState} : EndsWith ds f (wr (some (.tab ds)) f) := by
  intro h x g run
  rw [wrD_eq] at run
  cases hv : h.dstates ds with
  | none => rw [hv] at run; cases run
  | some v =>
    rw [hv] at run
    simp only [Except.ok.injEq, Prod.mk.injEq] at run
    rw [← run.2]
    exact ⟨v, setD_dstates_same _ _ _⟩

theorem EndsWith.bind' {ds : Nat} {f : DeflateState → DeflateState} {α β : Type} {m : M α} {k : α → M β}
    (hk : ∀ a, EndsWith ds f (k a)) : EndsWith ds f (m >>= k) := by
  intro h x g run
  rw [bind_app] at run
  cases hm : m h with
  | error e => rw [hm] at run; cases run
  | ok p =>
    obtain ⟨a, h1⟩ := p
    rw [hm] at run
    exact hk a h1 x g run

theorem EndsWith.ite' {ds : Nat} {f : DeflateState → DeflateState} {α : Type} (c : Prop) [Decidable c]
    {a b : M α} (ha : EndsWith ds f a) (hb : EndsWith ds f b) : EndsWith ds f (if c then a else b) := by
  split
  · exact ha
  · exact hb

/-- `storedKeep` ends with `s->block_start = s->strstart`. -/
theorem keep_last {ds : Nat} {strm : ZStreamPtr} {used : UInt32} {h gm : Heap}
    (run : storedKeep (some (.tab ds)) strm used h = .ok ((), gm)) :
    ∃ v : DeflateState, gm.dstates ds = some { v with block_start := v.strstart.toUInt64.toInt64 } := by
  have ends : EndsWith ds (fun d => { d with block_start := d.strstart.toUInt64.toInt64 })
      (storedKeep (some (.tab ds)) strm used) := by
    unfold storedKeep
    repeat' first
      | exact EndsWith.wr'
      | (apply EndsWith.bind'; intro _)
      | apply EndsWith.ite'
  exact ends h () gm run

set_option maxHeartbeats 8000000 in
open Zlib.Deflate.Universal in
/-- **The end of `deflate_stored` with input** (`storedEnd`): the work term rises by at most the bytes
the refill reads; with no input consumed and input left, it ends as `QEnd` asks. -/
theorem stored_endG {g : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv g r ds z d) (buffers : StreamBuffers g r) (pend0 : d.pending = 0)
    (out : z.next_out ≠ .null) (input : z.avail_in ≠ 0 → z.next_in ≠ .null) (level0 : d.level = 0)
    (flush : Int32) (mb used0 : UInt32) (st : StoredS) (consumed : Nat)
    (count : used0.toNat = z.avail_in.toNat + consumed)
    (cursor : consumed ≠ 0 → ∃ ref io, z.next_in = .ref ref io ∧ consumed ≤ io)
    (lastF : st.last ≠ 0 → flush = Z_FINISH ∧ z.avail_in = 0 ∧ d.bi_valid.toInt = 0) :
    ∃ ret g' z' d', storedEnd (some (.tab ds)) flush (some r) mb used0 st g = .ok (ret, g') ∧
      r.get g' = some z' ∧ g'.dstates ds = some d' ∧
      Quiet.work d' + z'.avail_in.toNat * 4 ≤ Quiet.work d + z.avail_in.toNat * 4 ∧
      z'.avail_in.toNat ≤ z.avail_in.toNat ∧ d'.gzindex = d.gzindex ∧
      (z'.avail_in = z.avail_in → z.avail_in ≠ 0 → consumed = 0 →
        (flush = Z_FINISH → z.avail_out.toNat + 1 ≤ (d.bi_valid.toInt.toNat + 42) / 8 +
          min (d.pending_buf_size.toNat - 5) d.w_size.toNat) →
        QEnd flush z d z' d' ret ∧ ret ≠ finish_started) := by
  have good := inv.good
  have hz := good.live.hz
  have readAvail : ∀ H : Heap, r.get H = some z → zrd (some r) (·.avail_in) H = .ok (z.avail_in, H) := by
    intro H hzH; simp [zrd_eq, hzH]
  have usedN : (used0 - z.avail_in).toNat = consumed := by
    rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by omega))]; omega
  have w0 := work_l0 level0 inv.shape
  obtain ⟨g1, g2, e2, keepRun, hwRun, inv2, buffers2, pend1, level1, bv1, wk2, gz2, keep0⟩ : ∃ g1 g2 e2,
      (if (used0 - z.avail_in != 0) = true then storedKeep (some (.tab ds)) (some r) (used0 - z.avail_in)
        else pure ()) g = .ok ((), g1) ∧
      wr (some (.tab ds)) (fun d => { d with high_water := if d.high_water < d.strstart.toUInt64 then d.strstart.toUInt64 else d.high_water }) g1 =
        .ok ((), g2) ∧
      DInv g2 r ds z e2 ∧ StreamBuffers g2 r ∧ e2.pending = 0 ∧ e2.level = 0 ∧ e2.bi_valid = d.bi_valid ∧
      Quiet.work e2 ≤ Quiet.work d ∧ e2.gzindex = d.gzindex ∧
      (consumed = 0 → e2.strstart = d.strstart ∧ e2.block_start = d.block_start ∧
        e2.pending_buf_size = d.pending_buf_size ∧ e2.w_size = d.w_size) := by
    by_cases u0 : (used0 - z.avail_in != 0) = true
    · have nz : consumed ≠ 0 := by
        intro c; rw [← usedN] at c; simp at u0; exact u0 (UInt32.toNat_inj.mp (by rw [c]; rfl))
      obtain ⟨ref, io, src, le⟩ := cursor nz
      obtain ⟨ia, inGet, inBound⟩ := caller_input_array good buffers src
      have apartW : ∀ w, d.window = .ref (.blk w) 0 → ref ≠ .blk w :=
        fun w win => Ne.symm (caller_input_window_separate good buffers win src)
      obtain ⟨gm, g2, e2, run, wrun, inv2, buffers2, _, ⟨ss, ins, m, bs, hw, rfl⟩, _, _, privK⟩ :=
        stored_keep inv buffers level0 (used0 - z.avail_in) src inGet (by omega) (by rw [usedN]; exact le)
          apartW (input_not_state good buffers src)
      obtain ⟨v, hv⟩ := keep_last run
      have hs2 := wr_state wrun hv
      have e2eq := Option.some.inj (inv2.good.live.hs.symm.trans hs2)
      have bsEq : (keepState d ss ins m bs hw).block_start = (keepState d ss ins m bs hw).strstart.toUInt64.toInt64 := by
        rw [e2eq]
      have wk : Quiet.work (keepState d ss ins m bs hw) = 0 := by
        rw [work_l0 (show (keepState d ss ins m bs hw).level = 0 from level0) inv2.shape, bsEq, u32_toInt64_toInt]
        simp
      exact ⟨gm, g2, _, by simp only [u0, ite_true, run], wrun, inv2, buffers2, pend0, level0, rfl,
        by rw [wk]; exact Nat.zero_le _, rfl, fun c => absurd c nz⟩
    · obtain ⟨hwRun, inv2, buffers2, _, _⟩ := high_water_step inv buffers level0
      exact ⟨g, _, _, by simp only [u0, Bool.false_eq_true, ite_false]; rfl, hwRun, inv2, buffers2, pend0, level0, rfl,
        Nat.le_of_eq rfl, rfl, fun _ => ⟨rfl, rfl, rfl, rfl⟩⟩
  have hz2 := inv2.good.live.hz
  unfold storedEnd
  simp only [ite_seq]
  simp only [bind_app, readAvail g hz, keepRun, hwRun]
  by_cases lastC : (st.last != 0) = true
  · obtain ⟨wrRun, inv3, buffers3⟩ := bi_used_step inv2 buffers2 level1
    have facts := lastF (by simpa using lastC)
    refine ⟨finish_done, _, z, _, by simp only [lastC, ite_true, bind_app, wrRun]; rfl, inv3.good.live.hz,
      inv3.good.live.hs, by show Quiet.work e2 + _ ≤ _; omega, Nat.le_refl _, gz2, fun _ nz => absurd facts.2.1 nz⟩
  · simp only [Bool.not_eq_true] at lastC
    simp only [lastC, Bool.false_eq_true, ite_false, bind_app, ldDeflateState_tab inv2.good.live.hs, readAvail _ hz2]
    by_cases early : (flush != Z_NO_FLUSH && flush != Z_FINISH && z.avail_in == 0 &&
        (e2.strstart.toUInt64.toInt64 == e2.block_start)) = true
    · refine ⟨block_done, _, z, _, by simp only [early, ite_true]; rfl, hz2, inv2.good.live.hs, by omega,
        Nat.le_refl _, gz2, fun _ nz => ?_⟩
      exfalso
      simp only [Bool.and_eq_true, beq_iff_eq] at early
      exact nz early.1.2
    · simp only [Bool.not_eq_true] at early
      simp only [early, Bool.false_eq_true, ite_false]
      obtain ⟨g3, z3, e3, u3, refillRun, inv3, buffers3, _, acc3, ⟨_, _, _, _, _, ke3⟩, _, _, tot3, priv3, wk3, un3⟩ :=
        stored_refillG inv2 buffers2 level1 input
      have pend3 : e3.pending = 0 := by rw [ke3]; exact pend1
      have level3 : e3.level = 0 := by rw [ke3]; exact level1
      obtain ⟨ret, g4, z4, e4, finalRun, hz4, hs4, wk4, in4, gz4, B4⟩ :=
        stored_finalG inv3 buffers3 pend3 (output_valid_after acc3 out) level3 flush st.last (by simpa using lastC)
      have a3 := acc3.2.2.1
      have o3 := acc3.2.2.2.1
      have w2 := work_l0 level1 inv2.shape
      have w3 := work_l0 level3 inv3.shape
      have bs2 := (inv2.shape.levelZero level1).1
      have bs3 := (inv3.shape.levelZero level3).1
      have bs2N := Int.toNat_of_nonneg bs2
      have bs3N := Int.toNat_of_nonneg bs3
      have hi2 := inv2.shape.blockStart
      have hi3 := inv3.shape.blockStart
      have in4N : z4.avail_in.toNat = z3.avail_in.toNat := by rw [in4]
      refine ⟨ret, g4, z4, e4, by simp only [bind_app, refillRun, finalRun], hz4, hs4, by omega, by omega,
        gz4.trans (by rw [ke3]; exact gz2), fun ea nz c0 finB => ?_⟩
      have eaN : z4.avail_in.toNat = z.avail_in.toNat := by rw [ea]
      have u30 : u3 = 0 := by omega
      obtain ⟨ssW, bsW, ssE, bsE⟩ := un3 u30 nz
      obtain ⟨ss2, bs2', pbs2, ws2⟩ := keep0 c0
      have in3 : z3.avail_in = z.avail_in := UInt32.toNat_inj.mp (by omega)
      have out3 : z3.avail_out = z.avail_out := UInt32.toNat_inj.mp (by omega)
      have wsz := inv2.good.inv.wsz
      have bvE : e3.bi_valid = d.bi_valid := by rw [ke3]; exact bv1
      have pbsE : e3.pending_buf_size = d.pending_buf_size := by rw [ke3]; exact pbs2
      have wsE : e3.w_size = d.w_size := by rw [ke3]; exact ws2
      have ws3 : e3.w_size = e2.w_size := by rw [ke3]; rfl
      obtain ⟨q, ns⟩ := B4 (by rw [in3]; exact nz) (by rw [ssE, bsE, ws3]; omega)
        (by rw [bvE, pbsE, wsE, out3]; exact finB)
      have wE : Quiet.work e3 = Quiet.work e2 := by rw [w3, w2, ssE, bsE]
      have down : QDown z d z3 e3 :=
        ⟨by omega, by omega, fun _ => ⟨out3, pend3⟩, by rw [ke3]; exact gz2⟩
      exact ⟨QEnd.after down q, ns⟩

set_option maxHeartbeats 4000000 in
/-- **`deflate_stored` with input**: the work term rises by at most four per input byte consumed, and a
call that consumed none of its input ends as `QEnd` asks, without `finish_started`. -/
theorem stored_qI {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (entry : StratIn h r z d) (flush : Int32) (level : d.level = 0) :
    ∃ bstate after z' d', C.run (Zlib.Deflate.deflate_stored (some (.tab ds)) flush) h = .ok (bstate, after) ∧
      r.get after = some z' ∧ after.dstates ds = some d' ∧
      Zlib.Deflate.Universal.Quiet.work d' + z'.avail_in.toNat * 4 ≤
        Zlib.Deflate.Universal.Quiet.work d + z.avail_in.toNat * 4 ∧ d'.gzindex = d.gzindex ∧
      (z'.avail_in = z.avail_in → z.avail_in ≠ 0 → QEnd flush z d z' d' bstate ∧ bstate ≠ finish_started) := by
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
  obtain ⟨st, g, z1, d1, loopRun, step, lastF, wle, weq, finR⟩ := stored_loopG inv entry.buffers entry.pending
    entry.out entry.input level flush (MIN (d.pending_buf_size - 5) d.w_size.toUInt64).toUInt32
    { last := 0, len := 0, left := 0, have_ := 0, all := false, brk := false } rfl
    (by rw [mbN]; omega) (by rw [mbN]; omega)
  have level1 : d1.level = 0 := by rw [step.fields]; exact level
  obtain ⟨u1, p1, acc1, tot1⟩ := step.account
  have count : z.avail_in.toNat = z1.avail_in.toNat + u1 := by have := acc1.2.2.1; omega
  have cursor : u1 ≠ 0 → ∃ ref io, z1.next_in = .ref ref io ∧ u1 ≤ io := by
    intro nz
    have nzIn : z.avail_in ≠ 0 := by
      intro e; have := acc1.1; rw [e] at this; simp at this; omega
    obtain ⟨ref, io0, src0⟩ : ∃ ref io, z.next_in = .ref ref io := by
      cases p : z.next_in with
      | null => exact absurd p (entry.input nzIn)
      | ref ref io => exact ⟨ref, io, rfl⟩
    refine ⟨ref, io0 + u1, ?_, by omega⟩
    rw [acc1.2.2.2.2.1, src0]; rfl
  have gz1 : d1.gzindex = d.gzindex := by rw [step.fields]
  have pbs1 : d1.pending_buf_size = d.pending_buf_size := by rw [step.fields]
  have ws1 : d1.w_size = d.w_size := by rw [step.fields]
  have readAvail : zrd (some r) (·.avail_in) h = .ok (z.avail_in, h) := by simp [zrd_eq, hz]
  obtain ⟨ret, g', z', d', endRun, hz', hs', le2, av2, gz2, B⟩ :=
    stored_endG step.inv step.buffers step.pending step.out step.input level1 flush
      (MIN (d.pending_buf_size - 5) d.w_size.toUInt64).toUInt32 z.avail_in st u1 count cursor lastF
  refine ⟨ret, g', z', d', ?_, hz', hs', by omega, gz2.trans gz1, fun ea nz => ?_⟩
  · simp only [C.run, deflate_stored_source, bind_app, ldDeflateState_tab good.live.hs, strm, readAvail, loopRun,
      endRun]
  · have eaN : z'.avail_in.toNat = z.avail_in.toNat := by rw [ea]
    have u0 : u1 = 0 := by omega
    have in1 : z1.avail_in = z.avail_in := UInt32.toNat_inj.mp (by omega)
    have l0 : st.last = 0 := Classical.byContradiction fun c => nz (by rw [← in1]; exact (lastF c).2.1)
    obtain ⟨q, ns⟩ := B (ea.trans in1.symm) (by rw [in1]; exact nz) u0
      (fun f => by have := finR l0 f; rw [mbN] at this; rw [pbs1, ws1]; omega)
    have down : QDown z d z1 d1 :=
      ⟨by omega, wle, fun e => ⟨(weq in1 e).resolve_right (fun c => c l0), step.pending⟩, gz1⟩
    exact ⟨QEnd.after down q, ns⟩

end Zlib.Deflate.Engine.Proofs

namespace Zlib.Deflate.Universal.Quiet
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs Zlib.Deflate.Universal Zlib.Deflate.Universal.Call
set_option autoImplicit false

/-- The work term of a reachable state is below `2^18`: the lookahead and `strstart` stay within
the window, of at most `2^16` bytes. -/
theorem work_lt_of_inv {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) : work d < 2 ^ 18 := by
  have room := inv.shape.room
  have wsz := inv.good.inv.wsz
  have ws := slide_window_sizes inv.good
  have a : (if d.match_available = 0 then 0 else 2) ≤ 2 := by split <;> omega
  have b : (if d.sym_next = 0 then 0 else 1) ≤ 1 := by split <;> omega
  have c : (if d.level = 0 then d.strstart.toNat - d.block_start.toInt.toNat else 0) ≤ d.strstart.toNat := by
    split <;> omega
  unfold work
  omega

/-- The pending count of a reachable state is at most `pending_buf_size = 4·lit_bufsize ≤ 2^17`. -/
theorem pending_le_of_inv {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) : d.pending.toNat ≤ 2 ^ 17 := by
  have := inv.good.inv.pending_le
  have := (stored_geom inv.good).2.1
  omega

/-- The dispatch at a nonzero level, with input, does not raise the weighted work term. -/
theorem dispatch_qI_nz {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (ov : Block.OverlayAt d.lit_bufsize.toNat) (entry : StrategyEntry h r z d)
    (flush : Int32) (l0 : d.level ≠ 0) :
    ∃ b a z' d', dispatch (some (.tab ds)) flush d h = .ok (b, a) ∧ r.get a = some z' ∧
      a.dstates ds = some d' ∧ QEndI flush z d z' d' b := by
  have lo := inv.good.inv.level_lo
  have hi := inv.good.inv.level_hi
  have slo := inv.good.inv.strat_lo
  have shi := inv.good.inv.strat_hi
  have safe : FlushSafeAt d.lit_bufsize.toNat := Block.flushSafeAt_of ov
  have l0' : (d.level == 0) = false := by simp [l0]
  have nz : d.level.toInt ≠ 0 := fun e => l0 (Int32.toInt_inj.mp (by simpa using e))
  by_cases hf : d.strategy = Z_HUFFMAN_ONLY
  · have s2 : d.strategy.toInt = 2 := by rw [hf]; rfl
    obtain ⟨b, a, z', d', run, hz, hs, q⟩ := huff_qI safe inv entry.toIn flush l0 s2
    refine ⟨b, a, z', d', ?_, hz, hs, q⟩
    simp only [C.run] at run
    simp [dispatch, l0', hf, run]
  have hf' : (d.strategy == Z_HUFFMAN_ONLY) = false := by simp [hf]
  have s2 : d.strategy.toInt ≠ 2 := fun e => hf (Int32.toInt_inj.mp (by rw [e]; rfl))
  by_cases rl : d.strategy = Z_RLE
  · have s3 : d.strategy.toInt = 3 := by rw [rl]; rfl
    obtain ⟨b, a, z', d', run, hz, hs, q⟩ := rle_qI safe inv entry.toIn flush l0 s3
    refine ⟨b, a, z', d', ?_, hz, hs, q⟩
    simp only [C.run] at run
    simp [dispatch, l0', hf', rl, run, show Z_RLE ≠ Z_HUFFMAN_ONLY by decide]
  have rl' : (d.strategy == Z_RLE) = false := by simp [rl]
  have s3 : d.strategy.toInt ≠ 3 := fun e => rl (Int32.toInt_inj.mp (by rw [e]; rfl))
  by_cases fast : d.level.toInt ≤ 3
  · obtain ⟨b, a, z', d', run, hz, hs, q⟩ := fast_qI safe inv entry.toIn flush ⟨by omega, fast, s2, s3⟩
    refine ⟨b, a, z', d', ?_, hz, hs, q⟩
    simp only [C.run] at run
    have values : d.level = 1 ∨ d.level = 2 ∨ d.level = 3 := by
      have : d.level.toInt = 1 ∨ d.level.toInt = 2 ∨ d.level.toInt = 3 := by omega
      simp only [← Int32.toInt_inj]; exact this
    unfold dispatch
    rcases values with e | e | e <;>
      simp [l0', hf', rl', e, config_at, configuration_table, bind_app, pure_app] <;> exact run
  · obtain ⟨b, a, z', d', run, hz, hs, q⟩ := slow_qI safe inv entry.toIn flush ⟨by omega, s2, s3⟩
    refine ⟨b, a, z', d', ?_, hz, hs, q⟩
    simp only [C.run] at run
    have values : d.level = 4 ∨ d.level = 5 ∨ d.level = 6 ∨ d.level = 7 ∨ d.level = 8 ∨ d.level = 9 := by
      have : d.level.toInt = 4 ∨ d.level.toInt = 5 ∨ d.level.toInt = 6 ∨ d.level.toInt = 7 ∨
          d.level.toInt = 8 ∨ d.level.toInt = 9 := by omega
      simp only [← Int32.toInt_inj]; exact this
    unfold dispatch
    rcases values with e | e | e | e | e | e <;>
      simp [l0', hf', rl', e, config_at, configuration_table, bind_app, pure_app] <;> exact run

/-- **`DeflateQuietIn` for one strategy run**: the work term rises by at most four per input byte the
run consumed, `gzindex` is kept, and a run that consumed no input satisfies `StratQuiet`. -/
theorem strat_quiet_in {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState} {flush : Int32}
    (inv : DInv h r ds z d) (ov : Block.OverlayAt d.lit_bufsize.toNat) (entry : StrategyEntry h r z d)
    (busy : d.status = BUSY_STATE)
    {b : block_state} {after : Heap} {z1 : ZStream} {d1 : DeflateState}
    (run : dispatch (some (.tab ds)) flush d h = .ok (b, after))
    (hz1 : r.get after = some z1) (hs1 : after.dstates ds = some d1) :
    work d1 + z1.avail_in.toNat * 4 ≤ work d + z.avail_in.toNat * 4 ∧ d1.gzindex = d.gzindex ∧
    (z1.avail_in = z.avail_in → StratQuiet flush z d z1 d1 b) := by
  by_cases l0 : d.level = 0
  · obtain ⟨b', a', z', d', run', hz', hs', le, gz, B⟩ := stored_qI inv entry.toIn flush l0
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
    refine ⟨le, gz, fun ea => ?_⟩
    by_cases a0 : z.avail_in = 0
    · exact strat_quiet inv ov entry busy a0 run hz1 hs1
    · obtain ⟨q, ns⟩ := B ea a0
      exact ⟨q.le, q.eq, q.more, fun e => absurd e ns, q.gz⟩
  · obtain ⟨b', a', z', d', run', hz', hs', q⟩ := dispatch_qI_nz inv ov entry flush l0
    have e := run.symm.trans run'
    simp only [Except.ok.injEq, Prod.mk.injEq] at e
    obtain ⟨hb, ha⟩ := e
    subst hb ha
    have zE : z' = z1 := Option.some.inj (hz'.symm.trans hz1)
    have dE : d' = d1 := Option.some.inj (hs'.symm.trans hs1)
    subst zE dE
    refine ⟨q.le, q.gz, fun ea => ?_⟩
    have qe := q.same ea
    obtain ⟨b2, a2, z2, d2, run2, inv2, _, _, meaning⟩ := dispatch_spec inv ov entry flush
    have e2 := run.symm.trans run2
    simp only [Except.ok.injEq, Prod.mk.injEq] at e2
    obtain ⟨hb2, ha2⟩ := e2
    subst hb2 ha2
    have zE2 : z2 = z' := Option.some.inj (inv2.good.live.hz.symm.trans hz')
    have dE2 : d2 = d' := Option.some.inj (inv2.good.live.hs.symm.trans hs')
    subst zE2 dE2
    refine ⟨qe.le, qe.eq, qe.more, fun st => ?_, qe.gz⟩
    rcases meaning with ⟨l, _⟩ | ⟨_, m⟩
    · exact absurd l l0
    · rcases m.more (Or.inr st) with full | ⟨nm, _⟩
      · exact full
      · rw [st] at nm; exact absurd nm (by decide)

end Zlib.Deflate.Universal.Quiet

#print axioms Zlib.Deflate.Universal.huff_qI
#print axioms Zlib.Deflate.Universal.rle_qI
#print axioms Zlib.Deflate.Universal.fast_qI
#print axioms Zlib.Deflate.Universal.slow_qI
#print axioms Zlib.Deflate.Engine.Proofs.stored_qI
#print axioms Zlib.Deflate.Universal.Quiet.work_lt_of_inv
#print axioms Zlib.Deflate.Universal.Quiet.pending_le_of_inv
#print axioms Zlib.Deflate.Universal.Quiet.strat_quiet_in
