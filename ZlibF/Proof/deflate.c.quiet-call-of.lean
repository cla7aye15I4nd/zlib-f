import ZlibF.Proof.«deflate.c.quiet-tail»
import ZlibF.Proof.«deflate.c.universal-call-assemble»

/-!
# deflate.c: one call with no input lowers the potential (`DeflateQuiet`)

`call_quiet_of` follows `deflate_call_full` through the entry phase of a call with no input: the
early returns (refusal, full output, no progress), the call with nothing pending (`cont_empty`) and
the call with output pending (`cont_pending`), with `header_quiet` and `tail_quiet` in place of
`header_step_mid` and `tail_step`. A call that starts with at least 8 bytes of output room and fills
it lowers the potential lexicographically (`LexLt`); a call that ends with output room leaves a
quiet state (`QuietD`).

The arithmetic of the pending case: with `x` bytes pending and `R ≥ 8` bytes of room, a full
output after the entry flush leaves `x − min x R < x` bytes pending; otherwise the entry flush
delivers all `x` bytes, and a tail that keeps the phase and the work delivers `R − x` more bytes and
leaves at most `6 − (R − x) < x` pending.
-/

namespace Zlib.Deflate.Universal.Quiet
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs Zlib.Deflate.Universal.Call
set_option autoImplicit false

/-- What the call (or its rest after the entry phase) gives for `DeflateQuiet`. -/
def CallQ (r : ZStreamRef) (ds : Nat) (z : ZStream) (d : DeflateState) (flush : Int32)
    (run : Except Fault (Int32 × Heap)) : Prop :=
  ∃ rc after z' d', run = .ok (rc, after) ∧ DInv after r ds z' d' ∧
    (8 ≤ z.avail_out.toNat → z'.avail_out = 0 → LexLt d' d) ∧ (z'.avail_out ≠ 0 → QuietD flush d')

theorem phase_not_finish {d : DeflateState} (nf : d.status ≠ FINISH_STATE) : phase d = 2 := by
  unfold phase; rw [if_neg nf]

theorem rank_pos_writing {d : DeflateState} (w : Writing d) : 0 < rank d := by
  unfold Writing at w
  unfold rank
  rcases w with e | e | e | e | e | e <;> rw [e] <;> decide

/-- An early return of the header phase from a state `b` with the rank and header position of `d`. -/
theorem lex_qprog {d b d' : DeflateState} (nf : d.status ≠ FINISH_STATE) (rk : rank b = rank d)
    (gz : b.gzindex = d.gzindex) (q : QProg b d') : LexLt d' d := by
  have p2 : phase d = 2 := phase_not_finish nf
  have pl := phase_le d'
  by_cases lt : phase d' < phase d
  · exact LexLt.phase lt
  · have pe : phase d' = phase d := by omega
    rcases q with r1 | ⟨st, g⟩
    · exact LexLt.rank pe (by omega)
    · refine LexLt.gzrem pe ?_ ?_
      · rw [← rk]; unfold rank; rw [st]
      · unfold gzrem; rw [← gz]; have := d'.gzindex.toNat_lt; omega

/-- The header phase moved a header state to `BUSY_STATE`; the tail follows. -/
theorem lex_header_tail {d b d3 : DeflateState} {p : Nat} (w : Writing d) (busy : b.status = BUSY_STATE)
    (t : TailRel b d3 p) : LexLt d3 d := by
  have p2 := phase_not_finish w.not_finish
  have pb := phase_two busy
  have rb := rank_zero (Or.inl busy)
  have rpos := rank_pos_writing w
  rcases t with lt | ⟨pe, re, _, _⟩
  · exact LexLt.phase (by omega)
  · exact LexLt.rank (by omega) (by omega)

/-- The tail from a state `b` with the potential components of `d` except `pending`. -/
theorem lex_tail {d b d3 : DeflateState} {p : Nat} (ph : phase b = phase d) (rk : rank b = rank d)
    (gz : gzrem b = gzrem d) (wk : work b = work d) (t : TailRel b d3 p)
    (small : p + d3.pending.toNat ≤ 6 → d3.pending.toNat < d.pending.toNat) : LexLt d3 d := by
  rcases t with lt | ⟨pe, re, ge, wl | ⟨we, sm⟩⟩
  · exact LexLt.phase (by omega)
  · exact LexLt.work (by omega) (by omega) (by omega) (by omega)
  · exact LexLt.pending (by omega) (by omega) (by omega) (by omega) (small sm)

/-- The strategy premise of `call_quiet_of`. -/
def SQ (r : ZStreamRef) (ds : Nat) (flush : Int32) : Prop :=
  ∀ {h1 : Heap} {z1 : ZStream} {d1 : DeflateState} {b : block_state} {a : Heap} {z2 : ZStream} {d2 : DeflateState},
    DInv h1 r ds z1 d1 → Block.OverlayAt d1.lit_bufsize.toNat → StrategyEntry h1 r z1 d1 → d1.status = BUSY_STATE →
    z1.avail_in = 0 → dispatch (some (.tab ds)) flush d1 h1 = .ok (b, a) → r.get a = some z2 →
    a.dstates ds = some d2 → StratQuiet flush z1 d1 z2 d2 b

/-- `cont_empty` for `DeflateQuiet`: the rest of a call with no input and nothing pending. -/
theorem cont_empty_q {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {flush : Int32}
    (inv : DInv h r ds z d) (ov : Block.OverlayAt d.lit_bufsize.toNat) (header : HeaderInv d)
    (facts : CallFacts d) (buffers : StreamBuffers h r)
    (active : ActiveHeader h r) (pend : d.pending = 0) (accepted : ¬ DeflateRefuses z d flush)
    (room : z.avail_out ≠ 0) (lower : 0 ≤ flush.toInt) (upper : flush.toInt ≤ 5) (empty : z.avail_in = 0)
    (sq : SQ r ds flush) :
    CallQ r ds z d flush
      (headerPhase (some r) (some (.tab ds)) flush
        (strategyPhase (some r) (some (.tab ds)) flush (trailerPhase (some r) (some (.tab ds)) flush))
        (setD h ds { d with last_flush := flush })) := by
  unfold DeflateRefuses at accepted
  have valid : 0 ≤ flush.toInt ∧ flush.toInt ≤ 5 := by omega
  have out : z.next_out ≠ .null := fun e => accepted (Or.inr (Or.inr (Or.inl e)))
  have input : z.avail_in ≠ 0 → z.next_in ≠ .null := fun ne => absurd empty ne
  have lfNot : flush ≠ -2 := by
    intro e; rw [e] at valid; exact absurd valid.1 (by decide)
  have lfRange : -2 ≤ flush.toInt ∧ flush.toInt ≤ 5 := ⟨by omega, valid.2⟩
  obtain ⟨pb, buf, trees⟩ := inv_trees inv
  obtain ⟨good1, trees1, buffers1⟩ := last_flush_engine (pb := pb) (buf := buf) flush inv.good trees buffers
  rcases status_cases inv.good.live.status with writing | busy
  · have entry : HeaderEntry (setD h ds { d with last_flush := flush }) z { d with last_flush := flush } ds pb buf := by
      have keep : CallerKeep h (setD h ds { d with last_flush := flush }) z ds pb :=
        CallerKeep.of_frame (HeaderFrame.state (r := r) pb inv.good.live.hs { d with last_flush := flush } rfl)
      rcases writing with e | e | e | e | e | e
      · exact fresh_header_entry inv.good trees active keep (stream_accounting_zero z) rfl rfl rfl (Or.inl e) pend room
      · exact fresh_header_entry inv.good trees active keep (stream_accounting_zero z) rfl rfl rfl (Or.inr e) pend room
      all_goals
        have size : 0 < buf.size := by have := trees.base.size; have := trees.base.lit_lo; omega
      · exact resumed_header_entry inv.good trees active header keep (stream_accounting_zero z) rfl rfl rfl rfl
          (Or.inl e) pend size
      · exact resumed_header_entry inv.good trees active header keep (stream_accounting_zero z) rfl rfl rfl rfl
          (Or.inr (Or.inl e)) pend size
      · exact resumed_header_entry inv.good trees active header keep (stream_accounting_zero z) rfl rfl rfl rfl
          (Or.inr (Or.inr (Or.inl e))) pend size
      · exact resumed_header_entry inv.good trees active header keep (stream_accounting_zero z) rfl rfl rfl rfl
          (Or.inr (Or.inr (Or.inr e))) pend size
    have low : d.bi_valid.toInt < 8 := by have := inv.shape.biValid; omega
    obtain ⟨after, z', d', produced, inv', header', buffers', acc, frame, own, out', litEq, branch, _⟩ :=
      header_quiet inv header good1 trees1 trees.base.pbuf buffers1 (inv.shape.cursor pend) out inv.alloc
        rfl rfl rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) low lfRange lfNot writing entry pend flush
        (strategyPhase (some r) (some (.tab ds)) flush (trailerPhase (some r) (some (.tab ds)) flush))
    rcases branch with ⟨run, _, _, _, full0, prog⟩ | ⟨run, busy', pend', _, lf', facts'⟩
    · exact ⟨Z_OK, after, z', d', run, inv', fun _ _ => lex_qprog writing.not_finish rfl rfl prog,
        fun nz => absurd full0 nz⟩
    · rw [run]
      have ain : z'.avail_in = z.avail_in := UInt32.toNat_inj.mp (by have := acc.2.2.1; omega)
      have empty' : z'.avail_in = 0 := ain.trans empty
      have ov' : Block.OverlayAt d'.lit_bufsize.toNat := by rw [litEq]; exact ov
      have input' : z'.avail_in ≠ 0 → z'.next_in ≠ .null := fun ne => absurd empty' ne
      obtain ⟨rc, a3, z3, d3, p3, run3, inv3, _, rel, quiet⟩ :=
        tail_quiet inv' ov' header' facts' buffers' out' pend' (Or.inl busy') lf' lower upper empty'
          (fun busyB run1 hz1 hs1 => sq inv' ov' ⟨buffers', out', input', pend', Or.inl busy'⟩ busyB empty' run1 hz1 hs1)
      exact ⟨rc, a3, z3, d3, run3, inv3, fun _ _ => lex_header_tail writing busy' rel, quiet⟩
  · have hs1 : (setD h ds { d with last_flush := flush }).dstates ds = some { d with last_flush := flush } :=
      setD_dstates_same _ _ _
    rw [header_skip hs1 busy]
    obtain ⟨inv1, header1, facts1, _, buffers1', _⟩ :=
      post_store inv facts trees buffers busy d.status flush (Or.inl rfl) lfRange lfNot
    obtain ⟨rc, a3, z3, d3, p3, run3, inv3, acc3, rel, quiet⟩ :=
      tail_quiet inv1 ov header1 facts1 buffers1' out pend busy rfl lower upper empty
        (fun busyB run1 hz1 hs1 => sq inv1 ov ⟨buffers1', out, input, pend, busy⟩ busyB empty run1 hz1 hs1)
    refine ⟨rc, a3, z3, d3, run3, inv3, fun big z0 => lex_tail rfl rfl rfl rfl rel (fun sm => ?_), quiet⟩
    have a := acc3.2.2.2.1
    have : z3.avail_out.toNat = 0 := by rw [z0]; rfl
    omega

/-- `cont_pending` for `DeflateQuiet`: a call with no input and output pending. -/
theorem call_pending_q {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {flush : Int32}
    (inv : DInv h r ds z d) (ov : Block.OverlayAt d.lit_bufsize.toNat) (header : HeaderInv d)
    (facts : CallFacts d) (buffers : StreamBuffers h r)
    (active : ActiveHeader h r) (pend : d.pending ≠ 0) (accepted : ¬ DeflateRefuses z d flush)
    (room : z.avail_out ≠ 0) (lower : 0 ≤ flush.toInt) (upper : flush.toInt ≤ 5) (empty : z.avail_in = 0)
    (sq : SQ r ds flush) :
    CallQ r ds z d flush (C.run (deflate (some r) flush) h) := by
  have accepted0 := accepted
  unfold DeflateRefuses at accepted
  have valid : 0 ≤ flush.toInt ∧ flush.toInt ≤ 5 := by omega
  have out : z.next_out ≠ .null := fun e => accepted (Or.inr (Or.inr (Or.inl e)))
  have lfNot : flush ≠ -2 := by
    intro e; rw [e] at valid; exact absurd valid.1 (by decide)
  have lfRange : -2 ≤ flush.toInt ∧ flush.toInt ≤ 5 := ⟨by omega, valid.2⟩
  obtain ⟨pb, buf, trees⟩ := inv_trees inv
  have pbuf := trees.base.pbuf
  obtain ⟨good1, trees1, buffers1⟩ := last_flush_engine (pb := pb) (buf := buf) flush inv.good trees buffers
  have low : d.bi_valid.toInt < 8 := by have := inv.shape.biValid; omega
  obtain ⟨produced, after, z1, d1, run, good', buffers', acc, count⟩ :=
    flush_cursor_run (d := { d with last_flush := flush }) good1 buffers1 low out
  obtain ⟨w0, p0, q0, b0, blocks⟩ := inv.good.inv.blocks
  have key : b0 = pb := by simpa only [pbuf, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.pbuf.symm
  subst key
  obtain ⟨po, cursor0, _⟩ := blocks.pout
  have nval := pendingLen_value d.pending z.avail_out
  have pendPos : d.pending.toNat ≠ 0 := by
    intro e; apply pend; exact UInt64.toNat_inj.mp (by rw [e]; rfl)
  have roomPos : z.avail_out.toNat ≠ 0 := by
    intro e; apply room; exact UInt32.toNat_inj.mp (by rw [e]; rfl)
  have nonzero : pendingLen d.pending z.avail_out ≠ 0 := by
    intro e; have := congrArg UInt32.toNat e; rw [nval] at this; simp at this; omega
  have stateEq := flush_cursor_state (d := { d with last_flush := flush }) good1 buffers1 pbuf cursor0 low out
    nonzero run good'
  have frame := StageFrame.of_flush_low good1 buffers1 pbuf low out run good'.live.hz acc
  have bytesPb : after.bytes b0 = h.bytes b0 := by
    have e := flush_low_pending_buf good1 buffers1 low pbuf out run
    exact e
  have nle : (pendingLen d.pending z.avail_out).toNat ≤ d.pending.toNat := by rw [nval]; omega
  have count' : produced = min d.pending.toNat z.avail_out.toNat := count
  have one : 1 ≤ produced := by rw [count']; omega
  have stEq : d1.status = d.status := by rw [stateEq]; rfl
  have p0 : d1.pending = d.pending - (pendingLen d.pending z.avail_out).toUInt64 := by rw [stateEq]; rfl
  have pendNat : d1.pending.toNat = d.pending.toNat - (pendingLen d.pending z.avail_out).toNat := by
    rw [p0, UInt64.toNat_sub_of_le]
    · simp
    · rw [UInt64.le_iff_toNat_le]; simp; omega
  have same : ∀ v : Int32, phase { d1 with status := d1.status, last_flush := v } = phase d ∧
      rank { d1 with status := d1.status, last_flush := v } = rank d ∧
      gzrem { d1 with status := d1.status, last_flush := v } = gzrem d ∧
      work { d1 with status := d1.status, last_flush := v } = work d := by
    intro v; rw [stateEq]; exact ⟨rfl, rfl, rfl, rfl⟩
  have lift := fun (v : Int32) (vr : -2 ≤ v.toInt ∧ v.toInt ≤ 5)
      (vh : d.status = INIT_STATE ∨ d.status = GZIP_STATE → v = -2 ∨ v = -1) =>
    pend_lift inv pbuf cursor0 good1 buffers1 out good' buffers' frame bytesPb stateEq nle v vr vh
  have keepH : ∀ v : Int32, HeaderInv { d1 with status := d1.status, last_flush := v } := fun v =>
    header.keep stEq (by rw [stateEq]; rfl) (by rw [stateEq]; rfl)
  have keepF : ∀ v : Int32, v ≠ -2 → CallFacts { d1 with status := d1.status, last_flush := v } := by
    intro v nv
    have sym : d1.sym_next = d.sym_next := by rw [stateEq]; rfl
    have look : d1.lookahead = d.lookahead := by rw [stateEq]; rfl
    have bits : d1.bi_valid = d.bi_valid := by rw [stateEq]; rfl
    exact { fresh := fun e => absurd e nv, freshStart := fun e => absurd e nv,
            finishSym := fun e => by show d1.sym_next = 0; rw [sym]; exact facts.finishSym (stEq ▸ e),
            finishLook := fun e => by show d1.lookahead = 0; rw [look]; exact facts.finishLook (stEq ▸ e),
            finishBits := fun e => by show d1.bi_valid = 0; rw [bits]; exact facts.finishBits (stEq ▸ e) }
  have lfEq : d1.last_flush = flush := by rw [stateEq]; rfl
  have eqd : ({ d1 with status := d1.status, last_flush := flush } : DeflateState) = d1 := by rw [← lfEq]
  have selfAfter : setD after ds { d1 with status := d1.status, last_flush := flush } = after := by
    rw [eqd]; exact setD_self good'.live.hs
  have atAfter : ¬ (d.status = INIT_STATE ∨ d.status = GZIP_STATE) →
      DInv after r ds z1 d1 ∧ HeaderInv d1 ∧ CallFacts d1 := by
    intro nh
    have i := lift flush lfRange (fun e => absurd e nh)
    rw [selfAfter, eqd] at i
    have hi := keepH flush
    have fi := keepF flush lfNot
    rw [eqd] at hi fi
    exact ⟨i, hi, fi⟩
  have entry := entry_pending_eval inv.good accepted0 room pend run good'.live.hz good'.live.hs
    (fun s => headerPhase (some r) s flush (strategyPhase (some r) s flush (trailerPhase (some r) s flush)))
  have ain1 : z1.avail_in = z.avail_in := UInt32.toNat_inj.mp (by have := acc.2.2.1; omega)
  have empty1 : z1.avail_in = 0 := ain1.trans empty
  by_cases full1 : z1.avail_out = 0
  · -- the entry flush filled the output
    have runE : C.run (deflate (some r) flush) h =
        .ok (Z_OK, setD after ds { d1 with status := d1.status, last_flush := -1 }) := by
      rw [C.run, deflate_phases, entry, if_pos full1]
    have i := lift (-1) (by decide) (fun _ => Or.inr rfl)
    obtain ⟨s1, s2, s3, s4⟩ := same (-1)
    refine ⟨_, _, _, _, runE, i, fun _ _ => LexLt.pending s1 s2 s3 s4 ?_, fun nz => absurd full1 nz⟩
    show d1.pending.toNat < d.pending.toNat
    rw [pendNat, nval]; omega
  have notFin : ¬ (d1.status = FINISH_STATE ∧ z1.avail_in ≠ 0) := fun c => c.2 empty1
  have runE : C.run (deflate (some r) flush) h =
      headerPhase (some r) (some (.tab ds)) flush
        (strategyPhase (some r) (some (.tab ds)) flush (trailerPhase (some r) (some (.tab ds)) flush)) after := by
    rw [C.run, deflate_phases, entry, if_neg full1, if_neg notFin]
  rw [runE]
  have notFull : z1.avail_out ≠ 0 := full1
  have small : produced < z.avail_out.toNat := by
    have l := acc.2.2.2.1
    have : z1.avail_out.toNat ≠ 0 := fun e => notFull (UInt32.toNat_inj.mp (by rw [e]; rfl))
    omega
  have pendZero : d1.pending = 0 := by
    have eqn : (pendingLen d.pending z.avail_out).toNat = d.pending.toNat := by
      rw [nval]; rw [count'] at small; omega
    rw [p0]
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_sub_of_le]
    · simp [eqn]
    · rw [UInt64.le_iff_toNat_le]; simp; omega
  have cursor1 : d1.pending_out = d1.pending_buf := by
    have : d1.pending_out = if d.pending - (pendingLen d.pending z.avail_out).toUInt64 == 0 then d.pending_buf
        else .ref (.blk b0) (po + (pendingLen d.pending z.avail_out).toNat) := by rw [stateEq]; rfl
    rw [this, ← p0, pendZero]
    simp only [beq_self_eq_true, ite_true]
    rw [stateEq]; rfl
  have input1 : z1.avail_in ≠ 0 → z1.next_in ≠ .null := fun ne => absurd empty1 ne
  have out1 : z1.next_out ≠ .null := by
    rw [acc.2.2.2.2.2.1]; exact Zlib.Deflate.Universal.advance_ne_null _ out
  rcases status_cases inv.good.live.status with writing | busy
  · -- a header state
    obtain ⟨keep1, records⟩ := entry_keep_any good1 buffers1 pbuf low out run good'.live.hz acc
    have keep : CallerKeep h after z ds b0 :=
      (CallerKeep.of_frame (HeaderFrame.state (r := r) b0 inv.good.live.hs { d with last_flush := flush } rfl)).trans
        keep1 (stream_accounting_zero z)
    have trees' := trees_at_of_good good' (by rw [stateEq]; exact pbuf) (by rw [bytesPb]; exact blocks.ba.choose_spec.1)
    have entryH : HeaderEntry after z1 d1 ds b0 blocks.ba.choose := by
      rcases writing with e | e | e | e | e | e
      · exact fresh_header_entry inv.good trees active keep acc records stEq (by rw [stateEq]; rfl) (Or.inl e)
          pendZero notFull
      · exact fresh_header_entry inv.good trees active keep acc records stEq (by rw [stateEq]; rfl) (Or.inr e)
          pendZero notFull
      all_goals
        have size : 0 < blocks.ba.choose.size := by
          have := trees'.base.size; have := trees'.base.lit_lo; omega
      · exact resumed_header_entry inv.good trees active header keep acc records stEq (by rw [stateEq]; rfl)
          (by rw [stateEq]; rfl) (Or.inl e) pendZero size
      · exact resumed_header_entry inv.good trees active header keep acc records stEq (by rw [stateEq]; rfl)
          (by rw [stateEq]; rfl) (Or.inr (Or.inl e)) pendZero size
      · exact resumed_header_entry inv.good trees active header keep acc records stEq (by rw [stateEq]; rfl)
          (by rw [stateEq]; rfl) (Or.inr (Or.inr (Or.inl e))) pendZero size
      · exact resumed_header_entry inv.good trees active header keep acc records stEq (by rw [stateEq]; rfl)
          (by rw [stateEq]; rfl) (Or.inr (Or.inr (Or.inr e))) pendZero size
    obtain ⟨_, _, _, static, win, prv, hd, _⟩ := StageFrame.call_facts frame good1 buffers1 pbuf out
    have fields0 : HeaderFields d d1 := by unfold HeaderFields; rw [stateEq]; rfl
    obtain ⟨a2, z2, d2, p2, inv2, header2, buffers2, acc2, frame2, own2, out2, litEq2, branch, _⟩ :=
      header_quiet inv header good' trees' (by rw [stateEq]; exact pbuf) buffers' cursor1 out1
        (by obtain ⟨za, zf⟩ := inv.alloc; exact ⟨acc.2.2.2.2.2.2.2.1.trans za, acc.2.2.2.2.2.2.2.2.1.trans zf⟩)
        fields0 stEq (by rw [stateEq]; rfl) static win prv hd (by rw [stateEq]; exact low)
        (by rw [lfEq]; exact lfRange) (by rw [lfEq]; exact lfNot) (by unfold Writing; rw [stEq]; exact writing)
        entryH pendZero flush
        (strategyPhase (some r) (some (.tab ds)) flush (trailerPhase (some r) (some (.tab ds)) flush))
    rcases branch with ⟨run2, _, _, _, full2, prog⟩ | ⟨run2, busy2, pend2, _, lf2, facts2⟩
    · exact ⟨Z_OK, a2, z2, d2, run2, inv2,
        fun _ _ => lex_qprog writing.not_finish (by rw [stateEq]; rfl) (by rw [stateEq]; rfl) prog,
        fun nz => absurd full2 nz⟩
    · rw [run2]
      have ain2 : z2.avail_in = z1.avail_in := UInt32.toNat_inj.mp (by have := acc2.2.2.1; omega)
      have empty2 : z2.avail_in = 0 := ain2.trans empty1
      have input2 : z2.avail_in ≠ 0 → z2.next_in ≠ .null := fun ne => absurd empty2 ne
      have ov2 : Block.OverlayAt d2.lit_bufsize.toNat := by rw [litEq2, stateEq]; exact ov
      obtain ⟨rc, a3, z3, d3, p3, run3, inv3, _, rel, quiet⟩ :=
        tail_quiet inv2 ov2 header2 facts2 buffers2 out2 pend2 (Or.inl busy2) (lf2.trans lfEq) lower upper empty2
          (fun busyB run1 hz1 hs1 => sq inv2 ov2 ⟨buffers2, out2, input2, pend2, Or.inl busy2⟩ busyB empty2 run1 hz1 hs1)
      exact ⟨rc, a3, z3, d3, run3, inv3, fun _ _ => lex_header_tail writing busy2 rel, quiet⟩
  · -- BUSY_STATE or FINISH_STATE: no header
    have hs1 := good'.live.hs
    rw [header_skip hs1 (by rw [stEq]; exact busy)]
    obtain ⟨i, hi, fi⟩ := atAfter (by
      intro e; rcases busy with b | b <;> rcases e with e | e <;> rw [b] at e <;> exact absurd e (by decide))
    have ov1 : Block.OverlayAt d1.lit_bufsize.toNat := by rw [stateEq]; exact ov
    have busy1 : d1.status = BUSY_STATE ∨ d1.status = FINISH_STATE := by rw [stEq]; exact busy
    obtain ⟨rc, a3, z3, d3, p3, run3, inv3, acc3, rel, quiet⟩ :=
      tail_quiet i ov1 hi fi buffers' out1 pendZero busy1 lfEq lower upper empty1
        (fun busyB run1 hz1 hs1 => sq i ov1 ⟨buffers', out1, input1, pendZero, busy1⟩ busyB empty1 run1 hz1 hs1)
    obtain ⟨s1, s2, s3, s4⟩ := same flush
    rw [eqd] at s1 s2 s3 s4
    refine ⟨rc, a3, z3, d3, run3, inv3, fun big z0 => lex_tail s1 s2 s3 s4 rel (fun sm => ?_), quiet⟩
    have a1 := acc.2.2.2.1
    have a3' := acc3.2.2.2.1
    have : z3.avail_out.toNat = 0 := by rw [z0]; rfl
    omega

/-- **One `deflate` call with no input, for `DeflateQuiet`**: from at least 8 bytes of output room, a
call that fills the output lowers the potential; a call that leaves output room leaves a quiet
state. `sq` is the strategy fact (`strat_quiet`). -/
theorem call_quiet_of {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState} {flush : Int32}
    (inv : DInv h r ds z d) (ov : Block.OverlayAt d.lit_bufsize.toNat) (header : HeaderInv d) (facts : CallFacts d)
    (buffers : StreamBuffers h r) (active : ActiveHeader h r) (out : z.next_out ≠ .null)
    (lower : 0 ≤ flush.toInt) (upper : flush.toInt ≤ 5) (empty : z.avail_in = 0)
    (sq : ∀ {h1 : Heap} {z1 : ZStream} {d1 : DeflateState} {b : block_state} {a : Heap} {z2 : ZStream} {d2 : DeflateState},
      DInv h1 r ds z1 d1 → Block.OverlayAt d1.lit_bufsize.toNat → StrategyEntry h1 r z1 d1 → d1.status = BUSY_STATE →
      z1.avail_in = 0 → dispatch (some (.tab ds)) flush d1 h1 = .ok (b, a) → r.get a = some z2 → a.dstates ds = some d2 →
      StratQuiet flush z1 d1 z2 d2 b) :
    ∃ rc after z' d', C.run (deflate (some r) flush) h = .ok (rc, after) ∧ DInv after r ds z' d' ∧
      (8 ≤ z.avail_out.toNat → z'.avail_out = 0 → LexLt d' d) ∧
      (z.avail_out ≠ 0 → z'.avail_out ≠ 0 → QuietD flush d') := by
  have noFull : ∀ {m : BPtr}, 8 ≤ z.avail_out.toNat → ({ z with msg := m } : ZStream).avail_out = 0 → False := by
    intro m big z0
    change z.avail_out = 0 at z0
    rw [z0] at big; simp at big
  by_cases refuses : DeflateRefuses z d flush
  · obtain ⟨m, run, inv', _⟩ := call_refused inv buffers lower (by omega) refuses
    refine ⟨_, _, _, _, run, inv', fun big z0 => absurd z0 (fun e => noFull big e), fun _ _ => Or.inr ?_⟩
    unfold DeflateRefuses at refuses
    rcases refuses with b | b | b | b | b
    · omega
    · omega
    · exact absurd b out
    · exact absurd empty b.2
    · exact b
  by_cases full : z.avail_out = 0
  · obtain ⟨m, run, inv', _⟩ := call_full inv buffers refuses full
    exact ⟨_, _, _, _, run, inv', fun big _ => by rw [full] at big; simp at big, fun nz => absurd full nz⟩
  by_cases pend : d.pending = 0
  · by_cases np : NoProgress z d flush
    · obtain ⟨m, run, inv', _⟩ := call_noprogress inv buffers pend refuses full np
      refine ⟨_, _, _, _, run, inv', fun big z0 => absurd z0 (fun e => noFull big e), fun _ _ => Or.inl ⟨pend, Or.inl ⟨rfl, ?_⟩⟩⟩
      rcases np with ⟨_, _, nf⟩ | ⟨_, ne⟩
      · exact nf
      · exact absurd empty ne
    · obtain ⟨rc, after, z', d', run0, inv', c1, c2⟩ :=
        cont_empty_q inv ov header facts buffers active pend refuses full lower upper empty sq
      have entry := (entry_empty_all inv.good pend refuses full inv.shape.lastFlush
        (fun s => headerPhase (some r) s flush (strategyPhase (some r) s flush (trailerPhase (some r) s flush)))).2 np
      have run : C.run (deflate (some r) flush) h = .ok (rc, after) := by
        rw [C.run, deflate_phases, entry]; exact run0
      exact ⟨rc, after, z', d', run, inv', c1, fun _ => c2⟩
  · obtain ⟨rc, after, z', d', run, inv', c1, c2⟩ :=
      call_pending_q inv ov header facts buffers active pend refuses full lower upper empty sq
    exact ⟨rc, after, z', d', run, inv', c1, fun _ => c2⟩

end Zlib.Deflate.Universal.Quiet

#print axioms Zlib.Deflate.Universal.Quiet.call_quiet_of
