import ZlibF.Proof.«deflate.c.quiet-tail»
import ZlibF.Proof.«deflate.c.quiet-in-strat»

/-!
# deflate.c: the strategy phase and the trailer with input (`DeflateQuietIn`)

`tail_in` is `tail_quiet` for a call that may have input. The strategy run raises the work term by
at most four per input byte it consumed (`strat_quiet_in2`); a run that consumed none is the run of
`tail_quiet`. `TailRelIn` is `TailRel` with the input: the phase drops, or it is kept with the header
components and the work term plus four per input byte does not rise, and with no input consumed the
work drops or the call delivered and left pending at most 6 bytes. With output room left at the end
the input is used up and the state is `QuietD`.
-/

namespace Zlib.Deflate.Universal.Quiet
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs Zlib.Deflate.Universal.Call
open Zlib.Trees.Proofs.Out (TreesInvAt)
set_option autoImplicit false

/-- What the tail of a call with input does to the potential: input `a` before, `a'` after, `p` bytes
delivered. -/
def TailRelIn (d : DeflateState) (a : Nat) (d' : DeflateState) (a' p : Nat) : Prop :=
  a' ≤ a ∧ (phase d' < phase d ∨ (phase d' = phase d ∧ rank d' = rank d ∧ gzrem d' = gzrem d ∧
    work d' + 4 * a' ≤ work d + 4 * a ∧
    (a' = a → work d' < work d ∨ (work d' = work d ∧ p + d'.pending.toNat ≤ 6))))

theorem tailRelIn_of {d d' : DeflateState} {a a' p : Nat} (st : d'.status = d.status) (wr : d'.wrap = d.wrap)
    (gi : d'.gzindex = d.gzindex) (ale : a' ≤ a) (le : work d' + 4 * a' ≤ work d + 4 * a)
    (eq : a' = a → work d' = work d → p + d'.pending.toNat ≤ 6) : TailRelIn d a d' a' p := by
  refine ⟨ale, Or.inr ⟨by unfold phase; rw [st, wr], by unfold rank; rw [st], by unfold gzrem; rw [gi], le,
    fun e => ?_⟩⟩
  by_cases w : work d' = work d
  · exact Or.inr ⟨w, eq e w⟩
  · exact Or.inl (by omega)

/-- **The open fact of `deflate_stored` with input**: on return, the input is used up or the output is
full, and `need_more` or `finish_started` with output room left come only with no input left and,
for `need_more`, without `Z_FINISH`. The other strategies prove it (`StratMeaning.stop`,
`StratMeaning.more`); for `deflate_stored` it is open. -/
def StoredStop : Prop :=
  ∀ {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState} {flush : Int32} {b : block_state}
    {a : Heap} {z1 : ZStream} {d1 : DeflateState},
    DInv h r ds z d → StrategyEntry h r z d → d.level = 0 → dispatch (some (.tab ds)) flush d h = .ok (b, a) →
    r.get a = some z1 → a.dstates ds = some d1 →
    (z1.avail_in = 0 ∨ z1.avail_out = 0) ∧
    (b = need_more ∨ b = finish_started → z1.avail_out = 0 ∨ (b = need_more ∧ z1.avail_in = 0 ∧ flush ≠ Z_FINISH))

set_option maxHeartbeats 3200000 in
/-- **The strategy phase and the trailer, with input**, for the potential of `DeflateQuietIn`. -/
theorem tail_in {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState} {flush : Int32}
    (inv : DInv h r ds z d) (ov : Block.OverlayAt d.lit_bufsize.toNat) (header : HeaderInv d) (facts : CallFacts d)
    (buffers : StreamBuffers h r) (out : z.next_out ≠ .null) (input : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (pend : d.pending = 0) (busy : d.status = BUSY_STATE ∨ d.status = FINISH_STATE) (lf : d.last_flush = flush)
    (lower : 0 ≤ flush.toInt) (upper : flush.toInt ≤ 5) (finIn : d.status = FINISH_STATE → z.avail_in = 0)
    (sstop : StoredStop) :
    ∃ rc after z' d' u p,
      strategyPhase (some r) (some (.tab ds)) flush (trailerPhase (some r) (some (.tab ds)) flush) h =
        .ok (rc, after) ∧
      DInv after r ds z' d' ∧ StreamAccounting z z' u p ∧ TailRelIn d z.avail_in.toNat d' z'.avail_in.toNat p ∧
      (z'.avail_out ≠ 0 → z'.avail_in = 0 ∧ QuietD flush d') := by
  have lfNot : d.last_flush ≠ -2 := by
    rw [lf]; intro e; rw [e] at lower; exact absurd lower (by decide)
  obtain ⟨pb, buf, trees⟩ := inv_trees inv
  rw [strategy_phase_eval inv.good.live.hz inv.good.live.hs]
  split
  · rename_i cond
    have notFin : d.status ≠ FINISH_STATE := fun e => by
      have la := facts.finishLook e
      simp [finIn e, la, e] at cond
    have busyB : d.status = BUSY_STATE := busy.resolve_right notFin
    have entry : StrategyEntry h r z d := ⟨buffers, out, input, pend, busy⟩
    obtain ⟨b, a, z1, d1, run1, inv1, buffers1, fr, meaning⟩ := dispatch_spec inv ov entry flush
    have hz1 := inv1.good.live.hz
    have hs1 := inv1.good.live.hs
    obtain ⟨W, gz1, SQ1, M1⟩ := strat_quiet_in2 inv ov entry busyB run1 hz1 hs1
    have M : (z1.avail_in = 0 ∨ z1.avail_out = 0) ∧
        (b = need_more ∨ b = finish_started → z1.avail_out = 0 ∨ (b = need_more ∧ z1.avail_in = 0 ∧ flush ≠ Z_FINISH)) ∧
        (b = finish_done → z1.avail_in = 0 ∧ d1.pending = 0 ∧ d1.bi_valid.toInt = 0) ∧
        (b = finish_started ∨ b = finish_done → flush = Z_FINISH) := by
      rcases meaning with ⟨l0, m⟩ | ⟨_, m⟩
      · exact ⟨(sstop inv entry l0 run1 hz1 hs1).1, (sstop inv entry l0 run1 hz1 hs1).2, m.done, m.finish⟩
      · refine ⟨m.stop, fun c => ?_, m.done, m.finish⟩
        rcases m.more c with o | ⟨x, i, f⟩
        · exact Or.inl o
        · exact Or.inr ⟨x, i, by rw [f]; decide⟩
    obtain ⟨stopM, moreM, doneM, finM⟩ := M
    obtain ⟨symZero, blockF, finLook⟩ := gaps_facts inv ov buffers out input pend run1 hz1 hs1
    have range := dispatch_range run1
    obtain ⟨stEq, lfEq, wrEq, _, _⟩ := dispatch_keeps run1 inv.good.live.hs hs1
    obtain ⟨u1, p1, sf1, _⟩ := Fr.strat fr (keep_dispatch _ _ _ h b a run1)
    have acc1 : StreamAccounting z z1 u1 p1 := sf1.1.1
    have a1le : z1.avail_in.toNat ≤ z.avail_in.toNat := by have := acc1.2.2.1; omega
    have busy1 : d1.status = BUSY_STATE := stEq.trans busyB
    have lf1 : d1.last_flush ≠ -2 := by rw [lfEq]; exact lfNot
    have facts1 : CallFacts d1 := facts_busy busy1 lf1
    have header1 : HeaderInv d1 := HeaderInv.of_busy (Or.inl busy1)
    have out1 : z1.next_out ≠ .null := by
      rw [sf1.1.1.2.2.2.2.2.1]; exact Zlib.Deflate.Universal.advance_ne_null _ out
    have sameIn : z1.avail_in.toNat = z.avail_in.toNat → z1.avail_in = z.avail_in := fun e => UInt32.toNat_inj.mp e
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
      refine ⟨Z_OK, _, z1, _, u1, p1, rfl, inv2, acc1, ?_, ?_⟩
      · refine tailRelIn_of stEq wrEq gz1 a1le (by show work d1 + _ ≤ _; have := W; omega) (fun ea e => ?_)
        have S := SQ1 (sameIn ea)
        rcases S.eq e with x | x | ⟨same, pz⟩
        · exact absurd x (by decide)
        · exact absurd x (by decide)
        · have := acc1.2.2.2.1; rw [same] at this
          show p1 + d1.pending.toNat ≤ 6
          rw [pz]; simp; omega
      · intro room
        rcases moreM (Or.inl rfl) with full | ⟨_, a0, nf⟩
        · exact absurd full room
        · refine ⟨a0, Or.inl ⟨M1 rfl room, Or.inl ⟨?_, nf⟩⟩⟩
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
      have accT : StreamAccounting z z2 u1 (p1 + p2) := by
        have := stream_accounting_trans acc1 acc2; simpa using this
      have in2 : z2.avail_in.toNat = z1.avail_in.toNat := by have := acc2.2.2.1; omega
      have eqCase : z2.avail_in.toNat = z.avail_in.toNat → work d2 = work d → p1 + p2 + d2.pending.toNat ≤ 6 :=
        fun ea e => by
          have ea1 := sameIn (in2.symm.trans ea)
          have S := SQ1 ea1
          have e1 : work d1 = work d := by have := S.le; omega
          rcases S.eq e1 with x | x | ⟨same, _⟩
          · exact absurd x (by decide)
          · exact absurd x (by decide)
          · have := acc1.2.2.2.1; rw [same] at this; omega
      have rel : TailRelIn d z.avail_in.toNat d2 z2.avail_in.toNat (p1 + p2) :=
        tailRelIn_of (keepM.1.trans stEq) (keepM.2.1.trans wrEq) (keepM.2.2.trans gz1) (by omega)
          (by have := W; omega) eqCase
      rcases branch with ⟨run2, _, full2⟩ | ⟨run2, pend2, _, lf2, _⟩
      · exact ⟨Z_OK, a2, z2, d2, u1, p1 + p2, run2, inv2, accT, rel, fun room => absurd full2 room⟩
      · rw [run2]
        obtain ⟨rc, a3, z3, d3, p3, run3, inv3, _, _, _, _, _, _, _, _, _, nf3, _⟩ :=
          trailer_quiet inv2 header2 facts2 trees2 buffers2 out2 flush (fun f => absurd f notFinish)
        obtain ⟨_, a3e, z3e, d3e⟩ := nf3 notFinish
        subst a3e z3e d3e
        refine ⟨rc, a3, z3, d3, u1, p1 + p2, run3, inv3, accT, rel, fun room => ⟨?_,
          Or.inl ⟨pend2, Or.inl ⟨lf2.trans (lfEq.trans lf), notFinish⟩⟩⟩⟩
        have o2 := acc2.2.2.2.1
        have r2 : z3.avail_out.toNat ≠ 0 := fun x => room (UInt32.toNat_inj.mp (by rw [x]; rfl))
        rcases stopM with i0 | o0
        · apply UInt32.toNat_inj.mp; rw [in2, i0]
        · have : z1.avail_out.toNat = 0 := by rw [o0]; rfl
          omega
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
      refine ⟨Z_OK, _, z1, _, u1, p1, rfl, inv2, acc1, ⟨a1le, Or.inl (phase_fin_lt busyB rfl)⟩, fun room => ?_⟩
      rcases moreM (Or.inr rfl) with full | ⟨x, _⟩
      · exact absurd full room
      · exact absurd x (by decide)
    · -- finish_done: FINISH_STATE, then the trailer
      subst fd
      rw [after_done hs1]
      have done : z1.avail_in = 0 ∧ d1.pending = 0 ∧ d1.bi_valid.toInt = 0 := doneM rfl
      have fin : flush = Z_FINISH := finM (Or.inr rfl)
      obtain ⟨inv2, header2, facts2, trees2, buffers2, _⟩ :=
        post_store inv1 facts1 trees1 buffers1 (Or.inl busy1) FINISH_STATE d1.last_flush
          (Or.inr ⟨rfl, symZero (Or.inr (Or.inr rfl)), finLook (Or.inr rfl),
            gaps_finishBits inv ov buffers out input pend run1 hs1 (Or.inr rfl)⟩) inv1.shape.lastFlush lf1
      obtain ⟨rc, a3, z3, d3, p3, run3, inv3, _, _, _, _, acc3, _, eq3, rcs, endF, _, wF, _, okF, wneg, _⟩ :=
        trailer_quiet inv2 header2 facts2 trees2 buffers2 out1 flush (fun _ => ⟨rfl, done.2.1⟩)
      have accT : StreamAccounting z z3 u1 (p1 + p3) := by
        have := stream_accounting_trans acc1 acc3; simpa using this
      have in3 : z3.avail_in = 0 := by
        apply UInt32.toNat_inj.mp
        have := acc3.2.2.1; rw [done.1] at this; simp at this ⊢; omega
      have st3 : d3.status = FINISH_STATE := by rw [eq3]
      refine ⟨rc, a3, z3, d3, u1, p1 + p3, run3, inv3, accT,
        ⟨by have := acc3.2.2.1; omega, Or.inl (phase_fin_lt busyB st3)⟩, fun room => ⟨in3, ?_⟩⟩
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
    have empty : z.avail_in = 0 := Classical.byContradiction fun ne => cond (by simp [ne])
    have finCase : flush = Z_FINISH → d.status = FINISH_STATE := fun f =>
      Classical.byContradiction fun ne => cond (by simp [f, ne, Z_FINISH, Z_NO_FLUSH])
    obtain ⟨rc, a3, z3, d3, p3, run3, inv3, _, _, _, _, acc3, _, eq3, rcs, endF, nf, wF, _, okF, wneg, _⟩ :=
      trailer_quiet inv header facts trees buffers out flush (fun f => ⟨finCase f, pend⟩)
    have in3 : z3.avail_in = z.avail_in := UInt32.toNat_inj.mp (by have := acc3.2.2.1; omega)
    refine ⟨rc, a3, z3, d3, 0, p3, run3, inv3, acc3, ?_⟩
    have same : a3 = h → z3 = z ∧ d3 = d := fun e => by
      subst e
      exact ⟨Option.some.inj (inv3.good.live.hz.symm.trans inv.good.live.hz),
        Option.some.inj (inv3.good.live.hs.symm.trans inv.good.live.hs)⟩
    have unchanged : (a3 = h → TailRelIn d z.avail_in.toNat d3 z3.avail_in.toNat p3 ∧
        (z3.avail_out ≠ 0 → z3.avail_in = 0 ∧ QuietD flush d3)) := fun e => by
      obtain ⟨ze, de⟩ := same e
      have p0 : p3 = 0 := acc_zero acc3 (by rw [ze])
      rw [de, in3]
      refine ⟨tailRelIn_of rfl rfl rfl (Nat.le_refl _) (Nat.le_refl _) (fun _ _ => by rw [p0, pend]; decide),
        fun _ => ⟨empty, ?_⟩⟩
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
        refine ⟨⟨Nat.le_of_eq (by rw [in3]), Or.inl ?_⟩, fun room => ⟨in3.trans empty, ?_⟩⟩
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

#print axioms Zlib.Deflate.Universal.Quiet.tail_in
