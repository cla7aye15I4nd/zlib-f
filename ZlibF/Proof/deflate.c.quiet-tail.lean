import ZlibF.Proof.«deflate.c.quiet-phases»
import ZlibF.Proof.«deflate.c.quiet-trailer»
import ZlibF.Proof.«deflate.c.quiet-strat-def»
import ZlibF.Proof.«deflate.c.universal-call-tailstep»

/-!
# deflate.c: the strategy phase and the trailer with no input (`DeflateQuiet`)

`tail_quiet` follows `tail_step` from the state after the header phase (`BUSY_STATE` or
`FINISH_STATE`, nothing pending, `last_flush` the flush value) with no input, and adds what the
potential needs (`TailRel`): the phase drops, or it is kept with the header components, and the work
drops, or the work is kept and the call delivered and left pending at most 6 bytes (a flush marker).
With output room left at the end the state is `QuietD`.
-/

namespace Zlib.Deflate.Universal.Quiet
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs Zlib.Deflate.Universal.Call
open Zlib.Trees.Proofs.Out (TreesInvAt)
set_option autoImplicit false

/-- What the tail of a call does to the potential: `p` bytes delivered. -/
def TailRel (d d' : DeflateState) (p : Nat) : Prop :=
  phase d' < phase d ∨ (phase d' = phase d ∧ rank d' = rank d ∧ gzrem d' = gzrem d ∧
    (work d' < work d ∨ (work d' = work d ∧ p + d'.pending.toNat ≤ 6)))

theorem rank_zero {d : DeflateState} (busy : d.status = BUSY_STATE ∨ d.status = FINISH_STATE) : rank d = 0 := by
  unfold rank
  rcases busy with e | e <;> rw [e] <;> decide

theorem phase_two {d : DeflateState} (busy : d.status = BUSY_STATE) : phase d = 2 := by
  have ne : BUSY_STATE ≠ FINISH_STATE := by decide
  unfold phase; rw [busy]; simp [ne]

theorem phase_fin_lt {d d' : DeflateState} (busy : d.status = BUSY_STATE) (fin : d'.status = FINISH_STATE) :
    phase d' < phase d := by
  rw [phase_two busy]; unfold phase; rw [fin]; simp; split <;> omega

/-- Equal phase, rank and header position, from equal status, `wrap` and `gzindex`. -/
theorem tailRel_of {d d' : DeflateState} {p : Nat} (st : d'.status = d.status) (wr : d'.wrap = d.wrap)
    (gi : d'.gzindex = d.gzindex) (le : work d' ≤ work d) (eq : work d' = work d → p + d'.pending.toNat ≤ 6) :
    TailRel d d' p := by
  right
  refine ⟨by unfold phase; rw [st, wr], by unfold rank; rw [st], by unfold gzrem; rw [gi], ?_⟩
  by_cases e : work d' = work d
  · exact Or.inr ⟨e, eq e⟩
  · exact Or.inl (by omega)

/-- The flush marker does not raise the work: it keeps lookahead, the lazy match, the symbols and the
level, and keeps the positions or resets both. -/
theorem work_marker {d d' : DeflateState} (shape : MarkerShape d d')
    (pos : (d'.strstart = d.strstart ∧ d'.block_start = d.block_start) ∨ (d'.strstart = 0 ∧ d'.block_start = 0)) :
    work d' ≤ work d := by
  obtain ⟨p, po, bb, bv, bu, lf, sl, ss, bs, ins, rfl⟩ := shape
  unfold work
  simp only []
  rcases pos with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · simp only at e1 e2; rw [e1, e2]; exact Nat.le_refl _
  · simp only at e1 e2; rw [e1, e2]
    split
    · simp
    · simp

theorem acc_zero {z z' : ZStream} {p : Nat} (acc : StreamAccounting z z' 0 p) (same : z'.avail_out = z.avail_out) :
    p = 0 := by
  have := acc.2.2.2.1; rw [same] at this; omega

set_option maxHeartbeats 3200000 in
/-- **The strategy phase and the trailer with no input**, for the potential of `DeflateQuiet`. `sq` is
the strategy fact (`strat_quiet`). -/
theorem tail_quiet {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState} {flush : Int32}
    (inv : DInv h r ds z d) (ov : Block.OverlayAt d.lit_bufsize.toNat) (header : HeaderInv d) (facts : CallFacts d)
    (buffers : StreamBuffers h r) (out : z.next_out ≠ .null) (pend : d.pending = 0)
    (busy : d.status = BUSY_STATE ∨ d.status = FINISH_STATE) (lf : d.last_flush = flush)
    (lower : 0 ≤ flush.toInt) (upper : flush.toInt ≤ 4) (empty : z.avail_in = 0)
    (sq : ∀ {b : block_state} {after : Heap} {z1 : ZStream} {d1 : DeflateState}, d.status = BUSY_STATE →
      dispatch (some (.tab ds)) flush d h = .ok (b, after) → r.get after = some z1 → after.dstates ds = some d1 →
      StratQuiet flush z d z1 d1 b) :
    ∃ rc after z' d' p,
      strategyPhase (some r) (some (.tab ds)) flush (trailerPhase (some r) (some (.tab ds)) flush) h =
        .ok (rc, after) ∧
      DInv after r ds z' d' ∧ StreamAccounting z z' 0 p ∧ TailRel d d' p ∧ (z'.avail_out ≠ 0 → QuietD flush d') := by
  have lfNot : d.last_flush ≠ -2 := by
    rw [lf]; intro e; rw [e] at lower; exact absurd lower (by decide)
  have input : z.avail_in ≠ 0 → z.next_in ≠ .null := fun ne => absurd empty ne
  obtain ⟨pb, buf, trees⟩ := inv_trees inv
  rw [strategy_phase_eval inv.good.live.hz inv.good.live.hs]
  split
  · rename_i cond
    have notFin : d.status ≠ FINISH_STATE := fun e => by
      have la := facts.finishLook e
      simp [empty, la, e] at cond
    have busyB : d.status = BUSY_STATE := busy.resolve_right notFin
    obtain ⟨b, a, z1, d1, run1, inv1, buffers1, fr, meaning⟩ :=
      dispatch_spec inv ov ⟨buffers, out, input, pend, busy⟩ flush
    have hz1 := inv1.good.live.hz
    have hs1 := inv1.good.live.hs
    have S := sq busyB run1 hz1 hs1
    obtain ⟨symZero, blockF, finLook⟩ := gaps_facts inv ov buffers out input pend run1 hz1 hs1
    have range := dispatch_range run1
    obtain ⟨stEq, lfEq, wrEq, _, _⟩ := dispatch_keeps run1 inv.good.live.hs hs1
    obtain ⟨u1, p1, sf1, _⟩ := Fr.strat fr (keep_dispatch _ _ _ h b a run1)
    have acc1u : StreamAccounting z z1 u1 p1 := sf1.1.1
    have u0 : u1 = 0 := by have := acc1u.1; rw [empty] at this; simp at this; omega
    subst u0
    have acc1 : StreamAccounting z z1 0 p1 := acc1u
    have busy1 : d1.status = BUSY_STATE := stEq.trans busyB
    have lf1 : d1.last_flush ≠ -2 := by rw [lfEq]; exact lfNot
    have facts1 : CallFacts d1 := facts_busy busy1 lf1
    have header1 : HeaderInv d1 := HeaderInv.of_busy (Or.inl busy1)
    have out1 : z1.next_out ≠ .null := by
      rw [sf1.1.1.2.2.2.2.2.1]; exact Zlib.Deflate.Universal.advance_ne_null _ out
    obtain ⟨pb1, buf1, trees1⟩ := inv_trees inv1
    simp only [bind_app, run1]
    rcases range with nm | bd | st | fd
    · -- need_more
      subst nm
      rw [after_need_more hz1 hs1]
      have lfR : -2 ≤ (if z1.avail_out = 0 then (-1 : Int32) else d1.last_flush).toInt ∧
          (if z1.avail_out = 0 then (-1 : Int32) else d1.last_flush).toInt ≤ 5 := by
        split
        · decide
        · exact inv1.shape.lastFlush
      have lfN : (if z1.avail_out = 0 then (-1 : Int32) else d1.last_flush) ≠ -2 := by
        split
        · decide
        · exact lf1
      obtain ⟨inv2, _, _, _, _, _⟩ :=
        post_store inv1 facts1 trees1 buffers1 (Or.inl busy1) d1.status _ (Or.inl rfl) lfR lfN
      refine ⟨Z_OK, _, z1, _, p1, rfl, inv2, acc1, ?_, ?_⟩
      · refine tailRel_of stEq wrEq S.gzindex S.le (fun e => ?_)
        rcases S.eq e with x | x | ⟨same, pz⟩
        · exact absurd x (by decide)
        · exact absurd x (by decide)
        · have := acc_zero acc1 same
          show p1 + d1.pending.toNat ≤ 6
          rw [pz, this]; decide
      · intro room
        obtain ⟨pz, nf⟩ := S.more rfl room
        left
        refine ⟨pz, Or.inl ⟨?_, nf⟩⟩
        show (if z1.avail_out = 0 then (-1 : Int32) else d1.last_flush) = flush
        rw [if_neg room, lfEq, lf]
    · -- block_done: the markers, then the trailer without Z_FINISH
      subst bd
      rw [after_block]
      obtain ⟨idle, pend1, notFinish⟩ := blockF rfl
      obtain ⟨a2, z2, d2, p2, inv2, header2, facts2, buffers2, ⟨buf2, trees2, _⟩, acc2, _, mshape, out2, branch,
        bound, pos⟩ :=
        marker_quiet inv1 header1 facts1 trees1 buffers1 (inv1.shape.cursor pend1) pend1 out1
          (symZero (Or.inl rfl)) idle lf1 busy1 flush (trailerPhase (some r) (some (.tab ds)) flush)
      have wm := work_marker mshape pos
      have keepM : d2.status = d1.status ∧ d2.wrap = d1.wrap ∧ d2.gzindex = d1.gzindex := by
        obtain ⟨_, _, _, _, _, _, _, _, _, _, e⟩ := mshape; rw [e]; exact ⟨rfl, rfl, rfl⟩
      have accT : StreamAccounting z z2 0 (p1 + p2) := by
        have := stream_accounting_trans acc1 acc2; simpa using this
      have eqCase : work d2 = work d → p1 + p2 + d2.pending.toNat ≤ 6 := fun e => by
        have e1 : work d1 = work d := by have := S.le; omega
        rcases S.eq e1 with x | x | ⟨same, _⟩
        · exact absurd x (by decide)
        · exact absurd x (by decide)
        · have := acc_zero acc1 same; omega
      have rel : TailRel d d2 (p1 + p2) :=
        tailRel_of (keepM.1.trans stEq) (keepM.2.1.trans wrEq) (keepM.2.2.trans S.gzindex) (by have := S.le; omega)
          eqCase
      rcases branch with ⟨run2, _, full2⟩ | ⟨run2, pend2, _, lf2, _⟩
      · exact ⟨Z_OK, a2, z2, d2, p1 + p2, run2, inv2, accT, rel, fun room => absurd full2 room⟩
      · rw [run2]
        obtain ⟨rc, a3, z3, d3, p3, run3, inv3, _, _, _, _, _, _, _, _, _, nf3, _⟩ :=
          trailer_quiet inv2 header2 facts2 trees2 buffers2 out2 flush (fun f => absurd f notFinish)
        obtain ⟨_, a3e, z3e, d3e⟩ := nf3 notFinish
        subst a3e z3e d3e
        exact ⟨rc, a3, z3, d3, p1 + p2, run3, inv3, accT, rel,
          fun _ => Or.inl ⟨pend2, Or.inl ⟨lf2.trans (lfEq.trans lf), notFinish⟩⟩⟩
    · -- finish_started: FINISH_STATE, Z_OK, the output full
      subst st
      rw [after_started hz1 hs1]
      have lfR : -2 ≤ (if z1.avail_out = 0 then (-1 : Int32) else d1.last_flush).toInt ∧
          (if z1.avail_out = 0 then (-1 : Int32) else d1.last_flush).toInt ≤ 5 := by
        split
        · decide
        · exact inv1.shape.lastFlush
      have lfN : (if z1.avail_out = 0 then (-1 : Int32) else d1.last_flush) ≠ -2 := by
        split
        · decide
        · exact lf1
      obtain ⟨inv2, _, _, _, _, _⟩ :=
        post_store inv1 facts1 trees1 buffers1 (Or.inl busy1) FINISH_STATE _
          (Or.inr ⟨rfl, symZero (Or.inr (Or.inl rfl)), finLook (Or.inl rfl),
            gaps_finishBits inv ov buffers out input pend run1 hs1 (Or.inl rfl)⟩) lfR lfN
      exact ⟨Z_OK, _, z1, _, p1, rfl, inv2, acc1, Or.inl (phase_fin_lt busyB rfl),
        fun room => absurd (S.started rfl) room⟩
    · -- finish_done: FINISH_STATE, then the trailer
      subst fd
      rw [after_done hs1]
      have done : z1.avail_in = 0 ∧ d1.pending = 0 ∧ d1.bi_valid.toInt = 0 := by
        rcases meaning with ⟨_, m⟩ | ⟨_, m⟩
        · exact m.done rfl
        · exact m.done rfl
      have fin : flush = Z_FINISH := by
        rcases meaning with ⟨_, m⟩ | ⟨_, m⟩
        · exact m.finish (Or.inr rfl)
        · exact m.finish (Or.inr rfl)
      obtain ⟨inv2, header2, facts2, trees2, buffers2, _⟩ :=
        post_store inv1 facts1 trees1 buffers1 (Or.inl busy1) FINISH_STATE d1.last_flush
          (Or.inr ⟨rfl, symZero (Or.inr (Or.inr rfl)), finLook (Or.inr rfl),
            gaps_finishBits inv ov buffers out input pend run1 hs1 (Or.inr rfl)⟩) inv1.shape.lastFlush lf1
      obtain ⟨rc, a3, z3, d3, p3, run3, inv3, _, _, _, _, acc3, _, eq3, rcs, endF, _, wF, _, okF, wneg, _⟩ :=
        trailer_quiet inv2 header2 facts2 trees2 buffers2 out1 flush (fun _ => ⟨rfl, done.2.1⟩)
      have accT : StreamAccounting z z3 0 (p1 + p3) := by
        have := stream_accounting_trans acc1 acc3; simpa using this
      have st3 : d3.status = FINISH_STATE := by rw [eq3]
      refine ⟨rc, a3, z3, d3, p1 + p3, run3, inv3, accT, Or.inl (phase_fin_lt busyB st3), fun room => ?_⟩
      left
      by_cases w : 0 < d1.wrap.toInt
      · rcases rcs with ok | en
        · exact absurd (okF ok fin w) room
        · obtain ⟨_, _, p0⟩ := endF en
          exact ⟨p0, Or.inr ⟨st3, by
            have neg : d3.wrap.toInt = -d1.wrap.toInt := wneg w fin
            omega⟩⟩
      · rcases rcs with ok | en
        · have np : ({ d1 with status := FINISH_STATE, last_flush := d1.last_flush } : DeflateState).wrap ≤ 0 :=
            Int32.le_iff_toInt_le.mpr (by change d1.wrap.toInt ≤ 0; omega)
          have run3' := run3
          rw [fin, trailer_nonpos (r := r) inv2.good.live.hs np] at run3'
          simp only [Except.ok.injEq, Prod.mk.injEq] at run3'
          rw [ok] at run3'; exact absurd run3'.1 (by decide)
        · obtain ⟨_, _, p0⟩ := endF en
          refine ⟨p0, Or.inr ⟨st3, ?_⟩⟩
          rcases wF with e | ⟨pos, _⟩
          · rw [e]; change d1.wrap.toInt ≤ 0; omega
          · exact absurd pos w
  · -- no strategy runs: the trailer
    rename_i cond
    have finCase : flush = Z_FINISH → d.status = FINISH_STATE := fun f =>
      Classical.byContradiction fun ne => cond (by simp [f, ne, Z_FINISH, Z_NO_FLUSH])
    obtain ⟨rc, a3, z3, d3, p3, run3, inv3, _, _, _, _, acc3, _, eq3, rcs, endF, nf, wF, _, okF, wneg, _⟩ :=
      trailer_quiet inv header facts trees buffers out flush (fun f => ⟨finCase f, pend⟩)
    refine ⟨rc, a3, z3, d3, p3, run3, inv3, acc3, ?_⟩
    have same : a3 = h → z3 = z ∧ d3 = d := fun e => by
      subst e
      exact ⟨Option.some.inj (inv3.good.live.hz.symm.trans inv.good.live.hz),
        Option.some.inj (inv3.good.live.hs.symm.trans inv.good.live.hs)⟩
    have unchanged : (a3 = h → TailRel d d3 p3 ∧ (z3.avail_out ≠ 0 → QuietD flush d3)) := fun e => by
      obtain ⟨ze, de⟩ := same e
      have p0 : p3 = 0 := acc_zero acc3 (by rw [ze])
      rw [de]
      refine ⟨tailRel_of rfl rfl rfl (Nat.le_refl _) (fun _ => by rw [p0, pend]; decide), fun _ => ?_⟩
      by_cases f : flush = Z_FINISH
      · by_cases w : 0 < d.wrap.toInt
        · have := wneg w f; rw [de] at this; omega
        · exact Or.inl ⟨pend, Or.inr ⟨finCase f, by omega⟩⟩
      · exact Or.inl ⟨pend, Or.inl ⟨lf, f⟩⟩
    by_cases f : flush = Z_FINISH
    · have st := finCase f
      by_cases w : 0 < d.wrap.toInt
      · have neg := wneg w f
        have st3 : d3.status = FINISH_STATE := by rw [eq3]; exact st
        refine ⟨Or.inl ?_, fun room => ?_⟩
        · have h3 : ¬ (0 < d3.wrap.toInt) := by omega
          unfold phase; rw [st3, st]; simp [h3, w]
        · rcases rcs with ok | en
          · exact absurd (okF ok f w) room
          · obtain ⟨_, _, p0⟩ := endF en
            exact Or.inl ⟨p0, Or.inr ⟨st3, by omega⟩⟩
      · have np : d.wrap ≤ 0 := Int32.le_iff_toInt_le.mpr (by change d.wrap.toInt ≤ 0; omega)
        have run3' := run3
        rw [f, trailer_nonpos (r := r) inv.good.live.hs np] at run3'
        simp only [Except.ok.injEq, Prod.mk.injEq] at run3'
        exact unchanged run3'.2.symm
    · exact unchanged (nf f).2.1

end Zlib.Deflate.Universal.Quiet
#print axioms Zlib.Deflate.Universal.Quiet.tail_quiet
