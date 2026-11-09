import ZlibF.Proof.«deflate.c.engine.generic-foreign-macro-content»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-slow-literal-loop»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-search-prefix»
import ZlibF.Proof.«deflate.c.engine.strategy-controls»
import ZlibF.Proof.«deflate.c.engine.finish-ready-step»
import ZlibF.Proof.«deflate.c.engine.positive-flush-loop»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-literal-controls»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

theorem default_foreign_slow_decision_run_controls {h after : Heap} {r : ZStreamRef}
    {ds w owner oo origin base : Nat} {z : ZStream} {d result : DeflateState}
    {wa : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    {flush : Int32} {st next : LoopS} {candidate : UInt32}
    (cut : SearchBoundary h r ds z d input origin base xs w wa)
    (buffers : StreamBuffers h r) (lookahead : 1 ≤ d.lookahead.toNat)
    (strict : d.sym_next.toNat < d.sym_end.toNat)
    (positive : 0 < d.level.toInt) (pointer : z.next_out = .ref (.dstate_depth owner) oo)
    (memory : d.lit_bufsize.toNat = 16384)
    (comparisonRoom : d.strstart.toNat + 262 ≤ d.window_size.toNat) (ready : PublishReady d) (clear : BlockInit.BlockClear d)
    (run : slowDecision (some (.tab ds)) flush st candidate h = .ok (next, after))
    (live : after.dstates ds = some result) : StrategyControls d result := by
  by_cases selected : (d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length) = true
  · exact default_foreign_slow_match_run_controls cut buffers selected strict positive pointer memory comparisonRoom ready clear run live
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
      · exact default_foreign_slow_literal_full_run_controls cut buffers lookahead branch available full positive pointer memory comparisonRoom ready clear run live
      · have space : d.sym_next.toNat + 3 < d.sym_end.toNat := by omega
        obtain ⟨other, otherD, tested, boundaryA, _endA, _buffersA, frameA, _rest⟩ :=
          slow_literal_search_boundary cut buffers lookahead branch available space flush st candidate
        have heaps : other = after := (Prod.mk.inj (Except.ok.inj (tested.symm.trans run))).2
        rw [heaps] at boundaryA
        have states : otherD = result := Option.some.inj (boundaryA.good.live.hs.symm.trans live)
        rw [← states]
        exact StrategyControls.slow ready frameA

end Zlib.Deflate.Engine.Proofs
