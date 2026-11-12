import ZlibF.Proof.«deflate.c.universal-call-strateval»
import ZlibF.Proof.«deflate.c.universal-call-markerstep»
import ZlibF.Proof.«deflate.c.universal-call-trailerstep»

/-!
# deflate.c: the strategy phase and the trailer of one call

Owner 2 of the deflate split (`deflate_call`). From the state after the header phase
(`BUSY_STATE` or `FINISH_STATE`, nothing pending), the strategy phase and the trailer keep
`DInv ∧ HeaderInv ∧ CallFacts`, give the call segment (`Seg`: the strategy frame and the owned
blocks), return `Z_OK` or `Z_STREAM_END`, and give the `Z_STREAM_END` facts of `Goal.deflate`.

The facts the strategy specs do not state yet (batch B) are the hypothesis `StrategyGaps`; the
`CallFacts` clause the deflate owner adds is `FinishBits`. Both are listed in the shared note
`batch2-deflate-call-interface.md` (M5–M9, M13, M14, M16, M17, M19, M20 and M18).
-/

namespace Zlib.Deflate.Universal.Call
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs
open Zlib.Trees.Proofs.Out (TreesInvAt)
set_option autoImplicit false

/-- **What the strategy specs still owe `deflate_call`** (batch B), stated about the dispatch.
`noRoom` (M19): the dispatch with a full output (reachable after the header phase).
`facts`: the range of the block state (M16), the status, `last_flush` and `wrap` kept (M5, M17),
no symbol after a block or finishing return (M6), no lazy match and nothing pending after
`block_done`, which comes only without `Z_FINISH` (M9, M13, M20), no lookahead after a finishing
return (M14). -/
structure StrategyGaps : Prop where
  noRoom : ∀ {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState} (flush : Int32),
    DInv h r ds z d → StreamBuffers h r → z.next_out ≠ .null → (z.avail_in ≠ 0 → z.next_in ≠ .null) →
    z.avail_out = 0 → d.pending = 0 → (d.status = BUSY_STATE ∨ d.status = FINISH_STATE) →
    DispatchOut h r ds z d flush (dispatch (some (.tab ds)) flush d h)
  facts : ∀ {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState} {flush : Int32}
    {bstate : block_state} {after : Heap} {z' : ZStream} {d' : DeflateState},
    DInv h r ds z d → StreamBuffers h r → dispatch (some (.tab ds)) flush d h = .ok (bstate, after) →
    r.get after = some z' → after.dstates ds = some d' →
    (bstate = need_more ∨ bstate = block_done ∨ bstate = finish_started ∨ bstate = finish_done) ∧
    d'.status = d.status ∧ d'.last_flush = d.last_flush ∧ d'.wrap = d.wrap ∧
    (bstate = block_done ∨ bstate = finish_started ∨ bstate = finish_done → d'.sym_next = 0) ∧
    (bstate = block_done → d'.match_available = 0 ∧ d'.pending = 0 ∧ flush ≠ Z_FINISH) ∧
    (bstate = finish_started ∨ bstate = finish_done → d'.lookahead = 0)

/-- **The `CallFacts` clause the deflate owner adds** (M18): a finished stream holds no bits. -/
def FinishBits : Prop :=
  ∀ {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState},
    DInv h r ds z d → CallFacts d → d.status = FINISH_STATE → d.bi_valid = 0

/-- A segment of a call: its strategy frame and the owned blocks kept. -/
def Seg (h0 h1 : Heap) (r : ZStreamRef) (ds : Nat) (d0 : DeflateState) (z0 z1 : ZStream) (d1 : DeflateState) : Prop :=
  ∃ used produced, StratFrame h0 h1 r ds d0 z0 z1 used produced ∧ ∀ b, DeflateOwned ds d1 b ↔ DeflateOwned ds d0 b

theorem Seg.trans {h0 h1 h2 : Heap} {r : ZStreamRef} {ds : Nat} {d0 d1 d2 : DeflateState} {z0 z1 z2 : ZStream}
    (one : Seg h0 h1 r ds d0 z0 z1 d1) (two : Seg h1 h2 r ds d1 z1 z2 d2) (good : DGood h0 r ds z0 d0)
    (buffers : StreamBuffers h0 r) : Seg h0 h2 r ds d0 z0 z2 d2 := by
  obtain ⟨u1, p1, f1, o1⟩ := one
  obtain ⟨u2, p2, f2, o2⟩ := two
  exact ⟨u1 + u2, p1 + p2, StratFrame.trans f1 f2 o1 good.uniq (output_target good buffers),
    fun b => (o2 b).trans (o1 b)⟩

/-- The trees of a state under the invariant. -/
theorem inv_trees {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState} (inv : DInv h r ds z d) :
    ∃ pb buf, TreesInvAt h ds d pb buf := by
  obtain ⟨d0, b0, buf0, trees⟩ := inv.good.trees
  have de : d0 = d := Option.some.inj (trees.base.dstate.symm.trans inv.good.live.hs)
  rw [de] at trees
  exact ⟨b0, buf0, trees⟩

/-- What the strategy phase with the trailer concludes. -/
def TailOut (h0 : Heap) (r : ZStreamRef) (ds : Nat) (z0 : ZStream) (d0 : DeflateState) (flush : Int32)
    (run : Except Fault (Int32 × Heap)) : Prop :=
  ∃ rc after z' d', run = .ok (rc, after) ∧ DInv after r ds z' d' ∧ HeaderInv d' ∧ CallFacts d' ∧
    StreamBuffers after r ∧ Seg h0 after r ds d0 z0 z' d' ∧ (rc = Z_OK ∨ rc = Z_STREAM_END) ∧
    (rc = Z_STREAM_END → flush = Z_FINISH ∧ d'.status = FINISH_STATE ∧ z'.avail_in = 0 ∧ d'.pending = 0 ∧
      d'.bi_valid = 0)

/-- The trailer alone. -/
theorem tail_trailer {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (header : HeaderInv d) (facts : CallFacts d) (buffers : StreamBuffers h r)
    (out : z.next_out ≠ .null) (flush : Int32)
    (endFacts : flush = Z_FINISH → d.status = FINISH_STATE ∧ d.pending = 0 ∧ z.avail_in = 0 ∧ d.bi_valid = 0) :
    TailOut h r ds z d flush (trailerPhase (some r) (some (.tab ds)) flush h) := by
  obtain ⟨pb, buf, trees⟩ := inv_trees inv
  obtain ⟨rc, after, z1, d1, produced, run, inv1, header1, facts1, buffers1, _, acc, stage, shapeEq, rcs, endF,
    _, _, _⟩ := trailer_step inv header facts trees buffers out flush (fun f => ⟨(endFacts f).1, (endFacts f).2.1⟩)
  refine ⟨rc, after, z1, d1, run, inv1, header1, facts1, buffers1, ⟨0, produced, stage.1, ?_⟩, rcs, ?_⟩
  · intro b; rw [shapeEq]; exact Iff.rfl
  · intro e
    obtain ⟨f, st, p⟩ := endF e
    obtain ⟨_, _, ain, bv⟩ := endFacts f
    refine ⟨f, st, ?_, p, ?_⟩
    · have h3 := acc.2.2.1
      rw [ain] at h3
      exact UInt32.toNat_inj.mp (by simp at h3 ⊢; omega)
    · rw [shapeEq]; exact bv

/-- The call facts of a state after a strategy in `BUSY_STATE` that kept `last_flush`. -/
theorem facts_busy {d : DeflateState} (busy : d.status = BUSY_STATE) (lf : d.last_flush ≠ -2) : CallFacts d :=
  { fresh := fun e => absurd e lf, freshStart := fun e => absurd e lf,
    finishSym := fun e => absurd (busy.symm.trans e) (by decide),
    finishLook := fun e => absurd (busy.symm.trans e) (by decide) }

/-- **The strategy phase and the trailer** from the state after the header phase. -/
theorem tail_step (tiny : Block.TinyOverlay) (gaps : StrategyGaps) (finishBits : FinishBits)
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
    have out0 : DispatchOut h r ds z d flush (dispatch (some (.tab ds)) flush d h) := by
      by_cases room : z.avail_out = 0
      · exact gaps.noRoom flush inv buffers out input room pend busy
      · exact dispatch_spec tiny inv ⟨buffers, out, input, room, pend, busy⟩ flush
    obtain ⟨b, a, z1, d1, run1, inv1, buffers1, fr, meaning⟩ := out0
    have hz1 := inv1.good.live.hz
    have hs1 := inv1.good.live.hs
    obtain ⟨range, stEq, lfEq, _, symZero, blockF, finLook⟩ := gaps.facts inv buffers run1 hz1 hs1
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
          (symZero (Or.inl rfl)) idle lf1 flush (trailerPhase (some r) (some (.tab ds)) flush)
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
          (Or.inr ⟨rfl, symZero (Or.inr (Or.inl rfl)), finLook (Or.inl rfl)⟩) lfR lfN
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
          (Or.inr ⟨rfl, symZero (Or.inr (Or.inr rfl)), finLook (Or.inr rfl)⟩) inv1.shape.lastFlush lf1
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
