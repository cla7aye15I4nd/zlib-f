import ZlibF.Proof.«deflate.c.quiet-strat-in»

/-!
# deflate.c: a strategy run with input leaves nothing pending on `need_more` with room (`DeflateQuietIn`)

`strat_quiet_in2` is `strat_quiet_in` with one more fact: a run that returns `need_more` with output
room left has nothing pending. The loops of `deflate.c.quiet-strat-in` already carry it at their
`need_more` exits (the loop invariant gives `avail_out = 0 ∨ pending = 0`); here `QEndI2` keeps it,
and the final block of `deflate_stored` gives it from its flush. The proofs follow the originals.
-/

namespace Zlib.Deflate.Universal
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Engine.Proofs
open Zlib.Deflate.Proofs
open ZlibF.Math.DeflateSymbols
open Zlib.Trees.Proofs.Out (TreesInvAt)
set_option autoImplicit false

/-- `QEndI`, and nothing pending on `need_more` with room. -/
structure QEndI2 (flush : Int32) (z : ZStream) (d : DeflateState) (z' : ZStream) (d' : DeflateState)
    (b : block_state) : Prop where
  avail : z'.avail_in.toNat ≤ z.avail_in.toNat
  le : Quiet.work d' + z'.avail_in.toNat * 4 ≤ Quiet.work d + z.avail_in.toNat * 4
  same : z'.avail_in = z.avail_in → QEnd flush z d z' d' b
  gz : d'.gzindex = d.gzindex
  more : b = need_more → z'.avail_out ≠ 0 → d'.pending = 0

theorem QEndI2.of_end {flush : Int32} {z z' : ZStream} {d d' : DeflateState} {b : block_state}
    (q : QEnd flush z d z' d' b) (e : z'.avail_in = z.avail_in) : QEndI2 flush z d z' d' b := by
  refine ⟨by rw [e]; exact Nat.le_refl _, ?_, fun _ => q, q.gz, fun nm room => (q.more nm room).1⟩
  have := q.le
  rw [e]; omega

theorem QEndI2.after {flush : Int32} {z0 z z' : ZStream} {d0 d d' : DeflateState} {b : block_state}
    (down : QDI z0 d0 z d) (fin : QEndI2 flush z d z' d' b) : QEndI2 flush z0 d0 z' d' b :=
  ⟨Nat.le_trans fin.avail down.avail, Nat.le_trans fin.le down.le,
    fun e => let p := avail_eq_of down.avail fin.avail e; QEnd.after (down.same p.1) (fin.same p.2),
    fin.gz.trans down.gz, fin.more⟩

theorem QEndI2.more_of {flush : Int32} {z0 z : ZStream} {d0 d : DeflateState} (down : QDI z0 d0 z d)
    (why : z.avail_out = 0 ∨ (d.pending = 0 ∧ flush = Z_NO_FLUSH)) : QEndI2 flush z0 d0 z d need_more :=
  ⟨down.avail, down.le, fun e => QEnd.more_of (down.same e) why, down.gz,
    fun _ room => (why.resolve_left room).1⟩

set_option maxHeartbeats 1600000 in
/-- The end of the compression functions (`finish_tail`) with the work term. -/
theorem finish_tail_qI2 {kind : DeflateState → Prop} {h : Heap} {r : ZStreamRef}
    {ds : Nat} {z : ZStream} {d : DeflateState} (head : Head kind h r ds z d) (pending : d.pending = 0)
    (flush : Int32) (quiet : d.match_available = 0) (look0 : d.lookahead = 0) :
    ∃ bstate after z' d', finish_tail (some (.tab ds)) flush h = .ok (bstate, after) ∧
      r.get after = some z' ∧ after.dstates ds = some d' ∧ QEndI2 flush z d z' d' bstate := by
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
        QEndI2.of_end ⟨le, fun _ => Or.inr (Or.inl rfl), fun e => absurd e (by decide), gz⟩ keeps.availIn⟩
      simp [finish_tail, finish, bind_app, run']
    · subst started
      refine ⟨finish_started, after, z', result, ?_, invA.good.live.hz, invA.good.live.hs,
        QEndI2.of_end ⟨le, fun _ => Or.inl rfl, fun e => absurd e (by decide), gz⟩ keeps.availIn⟩
      simp [finish_tail, finish, bind_app, run']
  · have finishB : (flush == Z_FINISH) = false := by simpa using finish
    have rdSym : rd (some (.tab ds)) (·.sym_next) h = .ok (d.sym_next, h) := by
      simp [rdD_eq, head.inv.good.live.hs]
    by_cases symbols : d.sym_next = 0
    · refine ⟨block_done, h, z, d, ?_, head.inv.good.live.hz, head.inv.good.live.hs,
        QEndI2.of_end ⟨Nat.le_refl _, fun _ => Or.inr (Or.inr ⟨rfl, pending⟩), fun e => absurd e (by decide), rfl⟩ rfl⟩
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
          QEndI2.of_end ⟨Nat.le_of_lt lt, fun e => absurd e (Nat.ne_of_lt lt), fun e => absurd e (by decide), gz⟩ keeps.availIn⟩
        simp [finish_tail, finishB, bind_app, rdSym, symbolsB, symbols, run']
      · subst more
        refine ⟨need_more, after, z', result, ?_, invA.good.live.hz, invA.good.live.hs,
          QEndI2.of_end ⟨Nat.le_of_lt lt, fun e => absurd e (Nat.ne_of_lt lt),
            fun _ room => absurd (fullOut (Option.some_ne_none _)) room, gz⟩ keeps.availIn⟩
        simp [finish_tail, finishB, bind_app, rdSym, symbolsB, symbols, run']


set_option maxHeartbeats 1600000 in
/-- `finish_tail` from a state ready for a block flush that holds symbols, with the work term. -/
theorem finish_tail_readyQI2 {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream}
    {d : DeflateState} {buf : Array UInt8} {xs : List Symbol} (ready : BlockReady h r ds z d pb buf xs)
    (safe : FlushSafeAt d.lit_bufsize.toNat) (symbols : d.sym_next ≠ 0) (flush : Int32)
    (quiet : d.match_available = 0) (look0 : d.lookahead = 0) :
    ∃ bstate after z' d', finish_tail (some (.tab ds)) flush h = .ok (bstate, after) ∧
      r.get after = some z' ∧ after.dstates ds = some d' ∧ QEndI2 flush z d z' d' bstate := by
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
        QEndI2.of_end ⟨le, fun _ => Or.inr (Or.inl rfl), fun e => absurd e (by decide), gz⟩ keeps.availIn⟩
      simp [finish_tail, finish, bind_app, run']
    · subst started
      refine ⟨finish_started, after, z', result, ?_, invA.good.live.hz, invA.good.live.hs,
        QEndI2.of_end ⟨le, fun _ => Or.inl rfl, fun e => absurd e (by decide), gz⟩ keeps.availIn⟩
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
        QEndI2.of_end ⟨Nat.le_of_lt lt, fun e => absurd e (Nat.ne_of_lt lt), fun e => absurd e (by decide), gz⟩ keeps.availIn⟩
      simp [finish_tail, finishB, bind_app, rdSym, symbols, run']
    · subst more
      refine ⟨need_more, after, z', result, ?_, invA.good.live.hz, invA.good.live.hs,
        QEndI2.of_end ⟨Nat.le_of_lt lt, fun e => absurd e (Nat.ne_of_lt lt),
          fun _ room => absurd (fullOut (Option.some_ne_none _)) room, gz⟩ keeps.availIn⟩
      simp [finish_tail, finishB, bind_app, rdSym, symbols, run']


/-- **`deflate_huff` with input** does not raise the work term plus four per input byte. -/
theorem huff_qI2 {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream}
    {d : DeflateState} (safe : FlushSafeAt d.lit_bufsize.toNat) (inv : DInv h r ds z d) (entry : StratIn h r z d)
    (flush : Int32) (level : d.level ≠ 0) (huff : d.strategy.toInt = 2) :
    ∃ bstate after z' d', C.run (Zlib.Deflate.deflate_huff (some (.tab ds)) flush) h = .ok (bstate, after) ∧
      r.get after = some z' ∧ after.dstates ds = some d' ∧ QEndI2 flush z d z' d' bstate := by
  have head : Head HuffKind h r ds z d := ⟨inv, entry.buffers, entry.out, entry.input, level, huff, safe⟩
  obtain ⟨st, h1, loopRun, ⟨z1, d1, head1, down1, cases⟩, exit⟩ :=
    q_loopI (deflate_huff_body (some (.tab ds)) flush) flush head entry.pending
      (fun st _ _ _ hd p b r => huff_body_qI hd p flush st b r)
  rcases cases with ⟨brk, ret0, _⟩ | ⟨ret, why⟩ | ⟨brk, ret, pending1, empty1⟩
  · rcases exit with e | e
    · rw [brk] at e; cases e
    · rw [ret0] at e; cases e
  · refine ⟨need_more, h1, z1, d1, ?_, head1.inv.good.live.hz, head1.inv.good.live.hs, QEndI2.more_of down1 why⟩
    simp [C.run, deflate_huff, bind_app, loopRun, ret]
  · obtain ⟨wrRun, head2⟩ := clear_insert_head head1 id
    obtain ⟨bstate, after, z', d', tailRun, hz', hs', fin⟩ := finish_tail_qI2 head2 pending1 flush
      (idle_of_roll head1.inv.shape (Or.inl head1.kind) : d1.match_available = 0) empty1
    refine ⟨bstate, after, z', d', ?_, hz', hs', QEndI2.after down1 (QEndI2.after (QDI.of_down (insert_down pending1 0) rfl) fin)⟩
    simp only [C.run, deflate_huff, bind_app, loopRun, ret, wrRun]
    exact tailRun

/-- **`deflate_rle` with input** does not raise the work term plus four per input byte. -/
theorem rle_qI2 {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream}
    {d : DeflateState} (safe : FlushSafeAt d.lit_bufsize.toNat) (inv : DInv h r ds z d) (entry : StratIn h r z d)
    (flush : Int32) (level : d.level ≠ 0) (rle : d.strategy.toInt = 3) :
    ∃ bstate after z' d', C.run (Zlib.Deflate.deflate_rle (some (.tab ds)) flush) h = .ok (bstate, after) ∧
      r.get after = some z' ∧ after.dstates ds = some d' ∧ QEndI2 flush z d z' d' bstate := by
  have head : Head RleKind h r ds z d := ⟨inv, entry.buffers, entry.out, entry.input, level, rle, safe⟩
  obtain ⟨st, h1, loopRun, ⟨z1, d1, head1, down1, cases⟩, exit⟩ :=
    q_loopI (deflate_rle_body (some (.tab ds)) flush) flush head entry.pending
      (fun st _ _ _ hd p b r => rle_body_qI hd p flush st b r)
  rcases cases with ⟨brk, ret0, _⟩ | ⟨ret, why⟩ | ⟨brk, ret, pending1, empty1⟩
  · rcases exit with e | e
    · rw [brk] at e; cases e
    · rw [ret0] at e; cases e
  · refine ⟨need_more, h1, z1, d1, ?_, head1.inv.good.live.hz, head1.inv.good.live.hs, QEndI2.more_of down1 why⟩
    simp [C.run, deflate_rle, bind_app, loopRun, ret]
  · obtain ⟨wrRun, head2⟩ := clear_insert_head head1 id
    obtain ⟨bstate, after, z', d', tailRun, hz', hs', fin⟩ := finish_tail_qI2 head2 pending1 flush
      (idle_of_roll head1.inv.shape (Or.inr head1.kind) : d1.match_available = 0) empty1
    refine ⟨bstate, after, z', d', ?_, hz', hs', QEndI2.after down1 (QEndI2.after (QDI.of_down (insert_down pending1 0) rfl) fin)⟩
    simp only [C.run, deflate_rle, bind_app, loopRun, ret, wrRun]
    exact tailRun

/-- **`deflate_fast` with input** does not raise the work term plus four per input byte. -/
theorem fast_qI2 {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream}
    {d : DeflateState} (safe : FlushSafeAt d.lit_bufsize.toNat) (inv : DInv h r ds z d) (entry : StratIn h r z d)
    (flush : Int32) (fast : 1 ≤ d.level.toInt ∧ d.level.toInt ≤ 3 ∧ d.strategy.toInt ≠ 2 ∧ d.strategy.toInt ≠ 3) :
    ∃ bstate after z' d', C.run (Zlib.Deflate.deflate_fast (some (.tab ds)) flush) h = .ok (bstate, after) ∧
      r.get after = some z' ∧ after.dstates ds = some d' ∧ QEndI2 flush z d z' d' bstate := by
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
  · refine ⟨need_more, h1, z1, d1, ?_, head1.inv.good.live.hz, head1.inv.good.live.hs, QEndI2.more_of down1 why⟩
    simp [C.run, deflate_fast, bind_app, loopRun, ret]
  · obtain ⟨wrRun, head2⟩ := set_insert_head head1 empty1 (fun _ k => k)
    obtain ⟨bstate, after, z', d', tailRun, hz', hs', fin⟩ := finish_tail_qI2 head2 pending1 flush
      (idle_of_low head1.inv.shape head1.kind.2.1 : d1.match_available = 0) empty1
    refine ⟨bstate, after, z', d', ?_, hz', hs', QEndI2.after down1 (QEndI2.after (QDI.of_down (insert_down pending1 _) rfl) fin)⟩
    simp only [C.run, deflate_fast, bind_app, loopRun, ret, wrRun]
    exact tailRun

/-- **`deflate_slow` with input** does not raise the work term plus four per input byte. -/
theorem slow_qI2 {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream}
    {d : DeflateState} (safe : FlushSafeAt d.lit_bufsize.toNat) (inv : DInv h r ds z d) (entry : StratIn h r z d)
    (flush : Int32) (slow : 4 ≤ d.level.toInt ∧ d.strategy.toInt ≠ 2 ∧ d.strategy.toInt ≠ 3) :
    ∃ bstate after z' d', C.run (Zlib.Deflate.deflate_slow (some (.tab ds)) flush) h = .ok (bstate, after) ∧
      r.get after = some z' ∧ after.dstates ds = some d' ∧ QEndI2 flush z d z' d' bstate := by
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
  · refine ⟨need_more, h1, z1, d1, ?_, head1.inv.good.live.hz, head1.inv.good.live.hs, QEndI2.more_of down1 why⟩
    simp [C.run, deflate_slow, bind_app, loopRun, ret]
  · have ld1 : ldDeflateState (some (.tab ds)) h1 = .ok (d1, h1) := ldDeflateState_tab head1.inv.good.live.hs
    by_cases avail : d1.match_available ≠ 0
    · have availB : (d1.match_available != 0) = true := by simpa using avail
      obtain ⟨c, b, buf, xs, h3, readC, tallyRun, state3, ready, symbols, priv3⟩ :=
        slow_end_literal head1 pending1 empty1 avail
      obtain ⟨bstate, after, z', d', tailRun, hz', hs', fin⟩ :=
        finish_tail_readyQI2 ready head1.safe symbols flush rfl empty1
      have lt : Quiet.work (endState (literalState d1 c)) < Quiet.work d1 :=
        work_lt_end head1.level head1.level rfl rfl avail
      have downE : QDown z1 d1 z1 (endState (literalState d1 c)) :=
        ⟨Nat.le_refl _, Nat.le_of_lt lt, fun e => absurd e (Nat.ne_of_lt lt), rfl⟩
      refine ⟨bstate, after, z', d', ?_, hz', hs', QEndI2.after down1 (QEndI2.after (QDI.of_down downE rfl) fin)⟩
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
      obtain ⟨bstate, after, z', d', tailRun, hz', hs', fin⟩ := finish_tail_qI2 head2 pending1 flush idle empty1
      refine ⟨bstate, after, z', d', ?_, hz', hs', QEndI2.after down1 (QEndI2.after (QDI.of_down (insert_down pending1 _) rfl) fin)⟩
      simp only [C.run, deflate_slow, bind_app, loopRun, ret, ld1, availB, Bool.false_eq_true, ite_false, wrRun]
      exact tailRun

end Zlib.Deflate.Universal

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Universal
set_option autoImplicit false

set_option maxHeartbeats 8000000 in
open Zlib.Deflate.Universal in
/-- The final block of `deflate_stored` with input: it lowers the work term and reads nothing. -/
theorem stored_finalG2 {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (buffers : StreamBuffers h r) (pend0 : d.pending = 0) (out : z.next_out ≠ .null)
    (level0 : d.level = 0) (flush last0 : Int32) (lastZero : last0 = 0) :
    ∃ ret g z' d', storedFinal (some (.tab ds)) flush (some r) last0 h = .ok (ret, g) ∧
      r.get g = some z' ∧ g.dstates ds = some d' ∧ Zlib.Deflate.Universal.Quiet.work d' ≤ Zlib.Deflate.Universal.Quiet.work d ∧ z'.avail_in = z.avail_in ∧
      d'.gzindex = d.gzindex ∧
      (z.avail_in ≠ 0 → (d.w_size.toNat : Int) < (d.strstart.toNat : Int) - d.block_start.toInt →
        (flush = Z_FINISH → z.avail_out.toNat + 1 ≤ (d.bi_valid.toInt.toNat + 42) / 8 +
          min (d.pending_buf_size.toNat - 5) d.w_size.toNat) →
        QEnd flush z d z' d' ret ∧ ret ≠ finish_started) ∧
      (ret = need_more → z'.avail_out ≠ 0 → d'.pending = 0) := by
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
        invB.good.live.hs, by show Zlib.Deflate.Universal.Quiet.work e ≤ _; omega, inA, gzA, fun nz _ _ => ?_,
        fun e => absurd e (by decide)⟩
      exfalso
      by_cases cf : (flush == Z_FINISH && z.avail_in == 0 && MIN left Hv == left) = true
      · simp only [Bool.and_eq_true, beq_iff_eq] at cf; exact nz cf.1.2
      · rw [if_neg cf] at l0; simp at l0
    · simp only [Bool.not_eq_true] at l0
      have pendA : z'.avail_out ≠ 0 → e.pending = 0 := by
        intro room
        have r0 : z'.avail_out.toNat ≠ 0 := fun x => room (UInt32.toNat_inj.mp (by rw [x]; rfl))
        exact UInt64.toNat_inj.mp (by
          have : e.pending.toNat = 0 := by omega
          rw [this]; rfl)
      refine ⟨need_more, after, z', e, by simp only [l0, Bool.false_eq_true, ite_false, bind_app, pure_app],
        invA.good.live.hz, invA.good.live.hs, by omega, inA, gzA, fun nz wide finB => ⟨?_, fun e => absurd e (by decide)⟩,
        fun _ room => pendA room⟩
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
      fun _ wide _ => ?_, fun _ _ => pend0⟩
    exfalso
    have h1 : ¬ (left ≥ MIN Hv d.w_size) := by
      intro ge; rw [decide_eq_true ge] at c; simp at c
    have a1 : ¬ (MIN Hv d.w_size).toNat ≤ left.toNat := fun x => h1 (UInt32.le_iff_toNat_le.mpr x)
    omega

set_option maxHeartbeats 8000000 in
open Zlib.Deflate.Universal in
/-- **The end of `deflate_stored` with input** (`storedEnd`): the work term rises by at most the bytes
the refill reads; with no input consumed and input left, it ends as `QEnd` asks. -/
theorem stored_endG2 {g : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
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
        QEnd flush z d z' d' ret ∧ ret ≠ finish_started) ∧
      (ret = need_more → z'.avail_out ≠ 0 → d'.pending = 0) := by
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
      inv3.good.live.hs, by show Quiet.work e2 + _ ≤ _; omega, Nat.le_refl _, gz2, fun _ nz => absurd facts.2.1 nz,
      fun e => absurd e (by decide)⟩
  · simp only [Bool.not_eq_true] at lastC
    simp only [lastC, Bool.false_eq_true, ite_false, bind_app, ldDeflateState_tab inv2.good.live.hs, readAvail _ hz2]
    by_cases early : (flush != Z_NO_FLUSH && flush != Z_FINISH && z.avail_in == 0 &&
        (e2.strstart.toUInt64.toInt64 == e2.block_start)) = true
    · refine ⟨block_done, _, z, _, by simp only [early, ite_true]; rfl, hz2, inv2.good.live.hs, by omega,
        Nat.le_refl _, gz2, fun _ nz => ?_, fun e => absurd e (by decide)⟩
      exfalso
      simp only [Bool.and_eq_true, beq_iff_eq] at early
      exact nz early.1.2
    · simp only [Bool.not_eq_true] at early
      simp only [early, Bool.false_eq_true, ite_false]
      obtain ⟨g3, z3, e3, u3, refillRun, inv3, buffers3, _, acc3, ⟨_, _, _, _, _, ke3⟩, _, _, tot3, priv3, wk3, un3⟩ :=
        stored_refillG inv2 buffers2 level1 input
      have pend3 : e3.pending = 0 := by rw [ke3]; exact pend1
      have level3 : e3.level = 0 := by rw [ke3]; exact level1
      obtain ⟨ret, g4, z4, e4, finalRun, hz4, hs4, wk4, in4, gz4, B4, M4⟩ :=
        stored_finalG2 inv3 buffers3 pend3 (output_valid_after acc3 out) level3 flush st.last (by simpa using lastC)
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
        gz4.trans (by rw [ke3]; exact gz2), fun ea nz c0 finB => ?_, M4⟩
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
theorem stored_qI2 {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (entry : StratIn h r z d) (flush : Int32) (level : d.level = 0) :
    ∃ bstate after z' d', C.run (Zlib.Deflate.deflate_stored (some (.tab ds)) flush) h = .ok (bstate, after) ∧
      r.get after = some z' ∧ after.dstates ds = some d' ∧
      Zlib.Deflate.Universal.Quiet.work d' + z'.avail_in.toNat * 4 ≤
        Zlib.Deflate.Universal.Quiet.work d + z.avail_in.toNat * 4 ∧ d'.gzindex = d.gzindex ∧
      (z'.avail_in = z.avail_in → z.avail_in ≠ 0 → QEnd flush z d z' d' bstate ∧ bstate ≠ finish_started) ∧
      (bstate = need_more → z'.avail_out ≠ 0 → d'.pending = 0) := by
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
  obtain ⟨ret, g', z', d', endRun, hz', hs', le2, av2, gz2, B, M⟩ :=
    stored_endG2 step.inv step.buffers step.pending step.out step.input level1 flush
      (MIN (d.pending_buf_size - 5) d.w_size.toUInt64).toUInt32 z.avail_in st u1 count cursor lastF
  refine ⟨ret, g', z', d', ?_, hz', hs', by omega, gz2.trans gz1, fun ea nz => ?_, M⟩
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

/-- The dispatch at a nonzero level, with input, does not raise the weighted work term. -/
theorem dispatch_qI_nz2 {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (ov : Block.OverlayAt d.lit_bufsize.toNat) (entry : StrategyEntry h r z d)
    (flush : Int32) (l0 : d.level ≠ 0) :
    ∃ b a z' d', dispatch (some (.tab ds)) flush d h = .ok (b, a) ∧ r.get a = some z' ∧
      a.dstates ds = some d' ∧ QEndI2 flush z d z' d' b := by
  have lo := inv.good.inv.level_lo
  have hi := inv.good.inv.level_hi
  have slo := inv.good.inv.strat_lo
  have shi := inv.good.inv.strat_hi
  have safe : FlushSafeAt d.lit_bufsize.toNat := Block.flushSafeAt_of ov
  have l0' : (d.level == 0) = false := by simp [l0]
  have nz : d.level.toInt ≠ 0 := fun e => l0 (Int32.toInt_inj.mp (by simpa using e))
  by_cases hf : d.strategy = Z_HUFFMAN_ONLY
  · have s2 : d.strategy.toInt = 2 := by rw [hf]; rfl
    obtain ⟨b, a, z', d', run, hz, hs, q⟩ := huff_qI2 safe inv entry.toIn flush l0 s2
    refine ⟨b, a, z', d', ?_, hz, hs, q⟩
    simp only [C.run] at run
    simp [dispatch, l0', hf, run]
  have hf' : (d.strategy == Z_HUFFMAN_ONLY) = false := by simp [hf]
  have s2 : d.strategy.toInt ≠ 2 := fun e => hf (Int32.toInt_inj.mp (by rw [e]; rfl))
  by_cases rl : d.strategy = Z_RLE
  · have s3 : d.strategy.toInt = 3 := by rw [rl]; rfl
    obtain ⟨b, a, z', d', run, hz, hs, q⟩ := rle_qI2 safe inv entry.toIn flush l0 s3
    refine ⟨b, a, z', d', ?_, hz, hs, q⟩
    simp only [C.run] at run
    simp [dispatch, l0', hf', rl, run, show Z_RLE ≠ Z_HUFFMAN_ONLY by decide]
  have rl' : (d.strategy == Z_RLE) = false := by simp [rl]
  have s3 : d.strategy.toInt ≠ 3 := fun e => rl (Int32.toInt_inj.mp (by rw [e]; rfl))
  by_cases fast : d.level.toInt ≤ 3
  · obtain ⟨b, a, z', d', run, hz, hs, q⟩ := fast_qI2 safe inv entry.toIn flush ⟨by omega, fast, s2, s3⟩
    refine ⟨b, a, z', d', ?_, hz, hs, q⟩
    simp only [C.run] at run
    have values : d.level = 1 ∨ d.level = 2 ∨ d.level = 3 := by
      have : d.level.toInt = 1 ∨ d.level.toInt = 2 ∨ d.level.toInt = 3 := by omega
      simp only [← Int32.toInt_inj]; exact this
    unfold dispatch
    rcases values with e | e | e <;>
      simp [l0', hf', rl', e, config_at, configuration_table, bind_app, pure_app] <;> exact run
  · obtain ⟨b, a, z', d', run, hz, hs, q⟩ := slow_qI2 safe inv entry.toIn flush ⟨by omega, s2, s3⟩
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
theorem strat_quiet_in2 {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState} {flush : Int32}
    (inv : DInv h r ds z d) (ov : Block.OverlayAt d.lit_bufsize.toNat) (entry : StrategyEntry h r z d)
    (busy : d.status = BUSY_STATE)
    {b : block_state} {after : Heap} {z1 : ZStream} {d1 : DeflateState}
    (run : dispatch (some (.tab ds)) flush d h = .ok (b, after))
    (hz1 : r.get after = some z1) (hs1 : after.dstates ds = some d1) :
    work d1 + z1.avail_in.toNat * 4 ≤ work d + z.avail_in.toNat * 4 ∧ d1.gzindex = d.gzindex ∧
    (z1.avail_in = z.avail_in → StratQuiet flush z d z1 d1 b) ∧
    (b = need_more → z1.avail_out ≠ 0 → d1.pending = 0) := by
  by_cases l0 : d.level = 0
  · obtain ⟨b', a', z', d', run', hz', hs', le, gz, B, M⟩ := stored_qI2 inv entry.toIn flush l0
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
    refine ⟨le, gz, fun ea => ?_, M⟩
    by_cases a0 : z.avail_in = 0
    · exact strat_quiet inv ov entry busy a0 run hz1 hs1
    · obtain ⟨q, ns⟩ := B ea a0
      exact ⟨q.le, q.eq, q.more, fun e => absurd e ns, q.gz⟩
  · obtain ⟨b', a', z', d', run', hz', hs', q⟩ := dispatch_qI_nz2 inv ov entry flush l0
    have e := run.symm.trans run'
    simp only [Except.ok.injEq, Prod.mk.injEq] at e
    obtain ⟨hb, ha⟩ := e
    subst hb ha
    have zE : z' = z1 := Option.some.inj (hz'.symm.trans hz1)
    have dE : d' = d1 := Option.some.inj (hs'.symm.trans hs1)
    subst zE dE
    refine ⟨q.le, q.gz, fun ea => ?_, q.more⟩
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

#print axioms Zlib.Deflate.Universal.Quiet.strat_quiet_in2
