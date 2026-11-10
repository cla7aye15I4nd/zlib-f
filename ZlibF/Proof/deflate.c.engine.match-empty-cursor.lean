import ZlibF.Proof.«deflate.c.engine.control-empty-cursor»
import ZlibF.Proof.«deflate.c.engine.decision-ready»
import ZlibF.Proof.«deflate.c.engine.strategy-controls»

/-! # Selected match decisions retain the empty-cursor phase -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The actual selected matching decision retains the phase on every
return, including a full block that exhausts caller output. -/
theorem slow_match_run_controls {h after : Heap} {r : ZStreamRef}
    {ds w ob oo origin base : Nat} {z : ZStream} {d result : DeflateState}
    {wa : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    {flush : Int32} {st next : LoopS} {candidate : UInt32}
    (cut : SearchBoundary h r ds z d input origin base xs w wa)
    (buffers : StreamBuffers h r)
    (selected : (d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length) = true)
    (strict : d.sym_next.toNat < d.sym_end.toNat)
    (positive : 0 < d.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : d.lit_bufsize.toNat = 16384) (ready : PublishReady d)
    (clear : BlockInit.BlockClear d)
    (run : slowDecision (some (.tab ds)) flush st candidate h = .ok (next, after))
    (live : after.dstates ds = some result) :
    StrategyControls d result := by
  obtain ⟨head, emittedHeap, emitted, emitRun, emittedBoundary, emittedFrontier, emittedBuffers, emitFrame,
      emittedFlag, _emittedStart, _emittedLook, _emittedEnd, _emittedCount, _emittedEndCount, _storage⟩ :=
    slow_match_emit_search_boundary cut buffers selected strict candidate
  have readyE := ready.slow emitFrame
  have configE := ConfigFrame.slow emitFrame
  have clearE := clear.slow emitFrame
  by_cases full : (d.sym_next + 3 == d.sym_end) = true
  · obtain ⟨produced, other, otherZ, otherD, flushRun, boundaryA, _endA, _buffersA, _accountA, _clearA,
        _frameA, _lowA, _phaseA⟩ :=
      flush_nonfinal_end_boundary emittedBoundary emittedFrontier emittedBuffers
        (by rw [configE.level]; exact positive) pointer readyE.2.1
        (by rw [configE.memory]; exact memory) readyE.1 (by have low := readyE.2.2; omega) clearE emittedFlag
    have cursorA := flush_control_run_empty_cursor emittedBoundary emittedBuffers
      (by rw [configE.level]; exact positive) pointer readyE.2.1
      (by rw [configE.memory]; exact memory) readyE.1 (by have low := readyE.2.2; omega)
      clearE emittedFlag false flushRun boundaryA.good.live.hs
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
    exact ⟨cursorA, by rw [_frameA, emitFrame], by rw [_frameA, emitFrame]⟩
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
