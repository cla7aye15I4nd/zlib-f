import ZlibF.Proof.«deflate.c.engine.generic-foreign-macro-content»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-slow-literal-loop»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-search-prefix»
import ZlibF.Proof.«deflate.c.engine.strategy-controls»
import ZlibF.Proof.«deflate.c.engine.finish-ready-step»
import ZlibF.Proof.«deflate.c.engine.positive-flush-loop»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

theorem default_foreign_slow_match_run_controls {h after : Heap} {r : ZStreamRef}
    {ds w owner oo origin base : Nat} {z : ZStream} {d result : DeflateState}
    {wa : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    {flush : Int32} {st next : LoopS} {candidate : UInt32}
    (cut : SearchBoundary h r ds z d input origin base xs w wa)
    (buffers : StreamBuffers h r)
    (selected : (d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length) = true)
    (strict : d.sym_next.toNat < d.sym_end.toNat)
    (positive : 0 < d.level.toInt) (pointer : z.next_out = .ref (.dstate_depth owner) oo)
    (memory : d.lit_bufsize.toNat = 16384)
    (comparisonRoom : d.strstart.toNat + 262 ≤ d.window_size.toNat) (ready : PublishReady d)
    (clear : BlockInit.BlockClear d)
    (run : slowDecision (some (.tab ds)) flush st candidate h = .ok (next, after))
    (live : after.dstates ds = some result) :
    StrategyControls d result := by
  obtain ⟨head, emittedHeap, emitted, emitRun, emittedBoundary, emittedFrontier, emittedBuffers, emitFrame,
      emittedFlag, emittedStart, _emittedLook, _emittedEnd, _emittedCount, _emittedEndCount, _storage⟩ :=
    slow_match_emit_search_boundary cut buffers selected strict candidate
  have readyE := ready.slow emitFrame
  have configE := ConfigFrame.slow emitFrame
  have clearE := clear.slow emitFrame
  by_cases full : (d.sym_next + 3 == d.sym_end) = true
  · have windowMax : d.window_size.toNat ≤ 65536 := by
      have power := Nat.pow_le_pow_right (n := 2) (by decide) cut.good.inv.wbits_hi
      rw [cut.good.inv.wsz, cut.good.inv.wsize]
      omega
    have smallE : emitted.strstart.toNat < 65536 := by
      rw [emittedStart]
      have previous := cut.previous.1
      omega
    have memoryE : emitted.lit_bufsize.toNat = 16384 := by
      rw [configE.memory]; exact memory
    obtain ⟨_produced, other, otherZ, otherD, _before, _written, _remaining, _kind, _body, _padding,
        macroRun, boundaryA, _endA, _buffersA, _accountA, _clearA, frameA, _lowA, _phaseA, cursorA, _rest⟩ :=
      default_foreign_flush_macro_content_encoding emittedBoundary emittedFrontier emittedBuffers
        (by rw [configE.level]; exact positive) pointer readyE.2.1 memoryE readyE.1
        (by have low := readyE.2.2; omega) clearE emittedFlag false
    have flushRun : FLUSH_BLOCK (some (.tab ds)) 0 emittedHeap =
        .ok ((if otherZ.avail_out == 0 then some need_more else none), other) := by
      have run0 : FLUSH_BLOCK_ONLY (some (.tab ds)) 0 emittedHeap = .ok ((), other) := macroRun
      unfold FLUSH_BLOCK
      simp only [bind_app, run0, ldDeflateState_tab boundaryA.good.live.hs,
        boundaryA.good.live.back, zrd_eq, boundaryA.good.live.hz]
      by_cases empty : (otherZ.avail_out == 0) = true <;> simp [empty, pure_app]
    have actualRun : slowDecision (some (.tab ds)) flush st candidate h =
        .ok ((if otherZ.avail_out == 0 then { st with hash_head := head, bflush := true, ret := some need_more }
          else { st with hash_head := head, bflush := true }), other) := by
      rw [slow_decision_match_source cut.good.live.hs selected flush st candidate]
      simp only [bind_app, emitRun, full, ite_true, flushRun]
      by_cases empty : (otherZ.avail_out == 0) = true <;> simp [empty, pure_app]
    have heaps : other = after := (Prod.mk.inj (Except.ok.inj (actualRun.symm.trans run))).2
    rw [heaps] at boundaryA
    have states : otherD = result := Option.some.inj (boundaryA.good.live.hs.symm.trans live)
    rw [← states]
    exact ⟨cursorA, by rw [frameA, emitFrame], by rw [frameA, emitFrame]⟩
  · have nonfull := Bool.eq_false_iff.mpr full
    have actualRun : slowDecision (some (.tab ds)) flush st candidate h =
        .ok ({ st with hash_head := head, bflush := false }, emittedHeap) := by
      rw [slow_decision_match_source cut.good.live.hs selected flush st candidate]
      simp only [bind_app, emitRun, nonfull, Bool.false_eq_true, ite_false, pure_app]
    have heaps : emittedHeap = after := (Prod.mk.inj (Except.ok.inj (actualRun.symm.trans run))).2
    rw [heaps] at emittedBoundary
    have states : emitted = result := Option.some.inj (emittedBoundary.good.live.hs.symm.trans live)
    rw [← states]
    exact StrategyControls.slow ready emitFrame

end Zlib.Deflate.Engine.Proofs
