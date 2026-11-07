import ZlibF.Proof.«deflate.c.engine.literal-empty-cursor»

/-! # Every actual strategy decision keeps public controls and the cursor phase -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- All real match, literal and defer decisions preserve the cursor
phase and public controls on every return. Exhausted output is included. -/
theorem slow_decision_run_controls {h after : Heap} {r : ZStreamRef}
    {ds w ob oo origin base : Nat} {z : ZStream} {d result : DeflateState}
    {wa : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    {flush : Int32} {st next : LoopS} {candidate : UInt32}
    (cut : SearchBoundary h r ds z d input origin base xs w wa)
    (buffers : StreamBuffers h r) (lookahead : 1 ≤ d.lookahead.toNat)
    (strict : d.sym_next.toNat < d.sym_end.toNat)
    (positive : 0 < d.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : d.lit_bufsize.toNat = 16384) (ready : PublishReady d) (clear : BlockInit.BlockClear d)
    (run : slowDecision (some (.tab ds)) flush st candidate h = .ok (next, after))
    (live : after.dstates ds = some result) : StrategyControls d result := by
  by_cases selected : (d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length) = true
  · exact slow_match_run_controls cut buffers selected strict positive pointer memory ready clear run live
  · have branch := Bool.eq_false_iff.mpr selected
    by_cases available : d.match_available = 0
    · obtain ⟨other, otherD, tested, boundaryA, _endA, _buffersA, frameA, _rest⟩ :=
        slow_defer_search_boundary cut buffers lookahead branch available strict flush st candidate
      have heaps : other = after := (Prod.mk.inj (Except.ok.inj (tested.symm.trans run))).2
      rw [heaps] at boundaryA
      have states : otherD = result := Option.some.inj (boundaryA.good.live.hs.symm.trans live)
      rw [← states]
      exact StrategyControls.slow ready frameA
    · have room := literal_room cut.good.inv strict
      by_cases full : d.sym_next.toNat + 3 = d.sym_end.toNat
      · exact slow_literal_full_run_controls cut buffers lookahead branch available full positive pointer memory ready clear run live
      · have space : d.sym_next.toNat + 3 < d.sym_end.toNat := by omega
        obtain ⟨other, otherD, tested, boundaryA, _endA, _buffersA, frameA, _rest⟩ :=
          slow_literal_search_boundary cut buffers lookahead branch available space flush st candidate
        have heaps : other = after := (Prod.mk.inj (Except.ok.inj (tested.symm.trans run))).2
        rw [heaps] at boundaryA
        have states : otherD = result := Option.some.inj (boundaryA.good.live.hs.symm.trans live)
        rw [← states]
        exact StrategyControls.slow ready frameA

end Zlib.Deflate.Engine.Proofs
