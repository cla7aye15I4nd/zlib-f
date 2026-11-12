import ZlibF.Proof.«deflate.c.universal-strategy-gaps»

/-!
# deflate.c: the strategy phase and the trailer of one call (the composition)

Owner 2 of the deflate split (`deflate_call`). `tail_step` composes the dispatch (`dispatch_spec`),
batch B's facts about the returned block state (`gaps_facts`), batch C's `dispatch_keeps` and
`dispatch_range`, the stores after a strategy (`post_store`), the markers (`marker_step`) and the
trailer (`tail_trailer`). The one hypothesis is `FinishBits`, the `CallFacts` clause
`FINISH_STATE → bi_valid = 0` (deflate owner; batch B's `gaps_finishBits` is its input).
-/

namespace Zlib.Deflate.Universal.Call
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs
open Zlib.Trees.Proofs.Out (TreesInvAt)
set_option autoImplicit false

/-- The call facts of a state after a strategy in `BUSY_STATE` that kept `last_flush`. -/
theorem facts_busy {d : DeflateState} (busy : d.status = BUSY_STATE) (lf : d.last_flush ≠ -2) : CallFacts d :=
  { fresh := fun e => absurd e lf, freshStart := fun e => absurd e lf,
    finishSym := fun e => absurd (busy.symm.trans e) (by decide),
    finishLook := fun e => absurd (busy.symm.trans e) (by decide),
    finishBits := fun e => absurd (busy.symm.trans e) (by decide) }

/-- **The strategy phase and the trailer** from the state after the header phase. -/
theorem tail_step (tiny : Block.TinyOverlay) (finishBits : FinishBits)
    {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (header : HeaderInv d) (facts : CallFacts d) (buffers : StreamBuffers h r)
    (out : z.next_out ≠ .null) (input : z.avail_in ≠ 0 → z.next_in ≠ .null) (pend : d.pending = 0)
    (busy : d.status = BUSY_STATE ∨ d.status = FINISH_STATE) (lfNot : d.last_flush ≠ -2)
    (finIn : d.status = FINISH_STATE → z.avail_in = 0) (flush : Int32) :
    TailOut h r ds z d flush
      (strategyPhase (some r) (some (.tab ds)) flush (trailerPhase (some r) (some (.tab ds)) flush) h) := by
  rw [strategy_phase_eval inv.good.live.hz inv.good.live.hs]
  split
  · rename_i cond
    have notFin : d.status ≠ FINISH_STATE := fun e => by
      have ai := finIn e
      have la := facts.finishLook e
      simp [ai, la, e] at cond
    have busyB : d.status = BUSY_STATE := busy.resolve_right notFin
    have out0 : DispatchOut h r ds z d flush (dispatch (some (.tab ds)) flush d h) :=
      dispatch_spec tiny inv ⟨buffers, out, input, pend, busy⟩ flush
    obtain ⟨b, a, z1, d1, run1, inv1, buffers1, fr, meaning⟩ := out0
    have hz1 := inv1.good.live.hz
    have hs1 := inv1.good.live.hs
    obtain ⟨symZero, blockF, finLook⟩ := gaps_facts tiny inv buffers out input pend run1 hz1 hs1
    have range := dispatch_range run1
    obtain ⟨stEq, lfEq, _, _, _⟩ := dispatch_keeps run1 inv.good.live.hs hs1
    obtain ⟨u1, p1, sf1, keys1⟩ := Fr.strat fr (keep_dispatch _ _ _ h b a run1)
    have seg1 : Seg h a r ds d z z1 d1 := ⟨u1, p1, sf1, fun x => keys1.owned ds x⟩
    have busy1 : d1.status = BUSY_STATE := stEq.trans busyB
    have lf1 : d1.last_flush ≠ -2 := by rw [lfEq]; exact lfNot
    have facts1 : CallFacts d1 := facts_busy busy1 lf1
    have header1 : HeaderInv d1 := HeaderInv.of_busy (Or.inl busy1)
    have out1 : z1.next_out ≠ .null := by
      rw [sf1.1.1.2.2.2.2.2.1]; exact Zlib.Deflate.Universal.advance_ne_null _ out
    obtain ⟨pb1, buf1, trees1⟩ := inv_trees inv1
    simp only [bind_app, run1]
    rcases range with nm | bd | st | fd
    · -- need_more: Z_OK
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
      obtain ⟨inv2, header2, facts2, _, buffers2, sf2⟩ :=
        post_store inv1 facts1 trees1 buffers1 (Or.inl busy1) d1.status _ (Or.inl rfl) lfR lfN
      exact ⟨Z_OK, _, z1, _, rfl, inv2, header2, facts2, buffers2,
        seg1.trans ⟨0, 0, sf2, fun _ => Iff.rfl⟩ inv.good buffers, Or.inl rfl, fun e => absurd e (by decide)⟩
    · -- block_done: the markers, then the trailer without Z_FINISH
      subst bd
      rw [after_block]
      obtain ⟨idle, pend1, notFinish⟩ := blockF rfl
      obtain ⟨a2, z2, d2, produced, inv2, header2, facts2, buffers2, _, _, mframe, mshape, out2, branch⟩ :=
        marker_step inv1 header1 facts1 trees1 buffers1 (inv1.shape.cursor pend1) pend1 out1
          (symZero (Or.inl rfl)) idle lf1 busy1 flush (trailerPhase (some r) (some (.tab ds)) flush)
      have own2 : ∀ x, DeflateOwned ds d2 x ↔ DeflateOwned ds d1 x := by
        obtain ⟨_, _, _, _, _, _, _, _, _, _, e⟩ := mshape
        intro x; rw [e]; exact Iff.rfl
      have seg2 := seg1.trans ⟨0, produced, mframe.1, own2⟩ inv.good buffers
      rcases branch with ⟨run2, _⟩ | ⟨run2, _, _, _⟩
      · exact ⟨Z_OK, a2, z2, d2, run2, inv2, header2, facts2, buffers2, seg2, Or.inl rfl,
          fun e => absurd e (by decide)⟩
      · rw [run2]
        obtain ⟨rc, a3, z3, d3, run3, inv3, header3, facts3, buffers3, seg3, rcs, endF⟩ :=
          tail_trailer inv2 header2 facts2 buffers2 out2 flush (fun f => absurd f notFinish)
        exact ⟨rc, a3, z3, d3, run3, inv3, header3, facts3, buffers3, seg2.trans seg3 inv.good buffers, rcs, endF⟩
    · -- finish_started: FINISH_STATE, Z_OK
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
      obtain ⟨inv2, header2, facts2, _, buffers2, sf2⟩ :=
        post_store inv1 facts1 trees1 buffers1 (Or.inl busy1) FINISH_STATE _
          (Or.inr ⟨rfl, symZero (Or.inr (Or.inl rfl)), finLook (Or.inl rfl),
            gaps_finishBits tiny inv buffers out input pend run1 hs1 (Or.inl rfl)⟩) lfR lfN
      exact ⟨Z_OK, _, z1, _, rfl, inv2, header2, facts2, buffers2,
        seg1.trans ⟨0, 0, sf2, fun _ => Iff.rfl⟩ inv.good buffers, Or.inl rfl, fun e => absurd e (by decide)⟩
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
      obtain ⟨inv2, header2, facts2, _, buffers2, sf2⟩ :=
        post_store inv1 facts1 trees1 buffers1 (Or.inl busy1) FINISH_STATE d1.last_flush
          (Or.inr ⟨rfl, symZero (Or.inr (Or.inr rfl)), finLook (Or.inr rfl),
            gaps_finishBits tiny inv buffers out input pend run1 hs1 (Or.inr rfl)⟩) inv1.shape.lastFlush lf1
      have seg2 := seg1.trans ⟨0, 0, sf2, fun _ => Iff.rfl⟩ inv.good buffers
      have bv : ({ d1 with status := FINISH_STATE, last_flush := d1.last_flush } : DeflateState).bi_valid = 0 := by
        show d1.bi_valid = 0
        exact Int32.toInt_inj.mp (by rw [done.2.2]; rfl)
      obtain ⟨rc, a3, z3, d3, run3, inv3, header3, facts3, buffers3, seg3, rcs, endF⟩ :=
        tail_trailer inv2 header2 facts2 buffers2 out1 flush (fun _ => ⟨rfl, done.2.1, done.1, bv⟩)
      exact ⟨rc, a3, z3, d3, run3, inv3, header3, facts3, buffers3, seg2.trans seg3 inv.good buffers, rcs, endF⟩
  · -- no strategy runs: the trailer
    rename_i cond
    refine tail_trailer inv header facts buffers out flush (fun f => ?_)
    have st : d.status = FINISH_STATE := Classical.byContradiction fun ne => cond (by
      simp [f, ne, Z_FINISH, Z_NO_FLUSH])
    refine ⟨st, pend, Classical.byContradiction fun ne => cond (by simp [ne]), finishBits inv facts st⟩

end Zlib.Deflate.Universal.Call
