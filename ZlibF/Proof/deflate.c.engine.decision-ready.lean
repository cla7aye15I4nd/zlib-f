import ZlibF.Proof.«deflate.c.engine.short-strategy-step»

/-! # Continuing decisions retain readiness at zero output capacity -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- A selected nonfull match preserves publication readiness even when
no output capacity remains. The source does not test output here. -/
theorem slow_match_nonfull_run_ready {h after : Heap} {r : ZStreamRef}
    {ds w origin base : Nat} {z : ZStream} {d result : DeflateState}
    {wa : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    {flush : Int32} {st next : LoopS} {candidate : UInt32}
    (cut : SearchBoundary h r ds z d input origin base xs w wa)
    (buffers : StreamBuffers h r)
    (selected : (d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length) = true)
    (strict : d.sym_next.toNat < d.sym_end.toNat)
    (nonfull : (d.sym_next + 3 == d.sym_end) = false)
    (ready : PublishReady d)
    (run : slowDecision (some (.tab ds)) flush st candidate h = .ok (next, after))
    (live : after.dstates ds = some result) : PublishReady result := by
  obtain ⟨head, emittedHeap, emitted, emitRun, boundaryE, _endE, _buffersE, frameE, _rest⟩ :=
    slow_match_emit_search_boundary cut buffers selected strict candidate
  have actualRun : slowDecision (some (.tab ds)) flush st candidate h =
      .ok ({ st with hash_head := head, bflush := false }, emittedHeap) := by
    rw [slow_decision_match_source cut.good.live.hs selected flush st candidate]
    simp only [bind_app, emitRun, nonfull, Bool.false_eq_true, ite_false, pure_app]
  have heaps : emittedHeap = after := (Prod.mk.inj (Except.ok.inj (actualRun.symm.trans run))).2
  rw [heaps] at boundaryE
  have states : emitted = result := Option.some.inj (boundaryE.good.live.hs.symm.trans live)
  rw [← states]
  exact ready.slow frameE

/-- An actual tested full-block return with no return marker has positive
remaining output, so its established publication phase supplies readiness. -/
theorem decision_tested_run_ready {h after other : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d result : DeflateState} {flush : Int32} {st next : LoopS}
    {candidate head : UInt32}
    (actual : slowDecision (some (.tab ds)) flush st candidate h = .ok (next, after))
    (tested : slowDecision (some (.tab ds)) flush st candidate h =
      .ok ((if z.avail_out == 0 then { st with hash_head := head, bflush := true, ret := some need_more }
        else { st with hash_head := head, bflush := true }), other))
    (good : DGood other r ds z d) (live : after.dstates ds = some result)
    (phase : 0 < z.avail_out.toNat → PublishReady d)
    (running : next.ret = none) : PublishReady result := by
  have equal := Prod.mk.inj (Except.ok.inj (actual.symm.trans tested))
  have nonzero : z.avail_out ≠ 0 := by
    intro zero
    have control := equal.1
    simp only [zero, beq_self_eq_true, ite_true] at control
    rw [control] at running
    cases running
  have positive : 0 < z.avail_out.toNat := by
    have nz : z.avail_out.toNat ≠ 0 := fun zero => nonzero (UInt32.toNat_inj.mp zero)
    omega
  rw [← equal.2] at good
  have states : d = result := Option.some.inj (good.live.hs.symm.trans live)
  rw [← states]
  exact phase positive

/-- Every continuing real decision preserves publication readiness without
requiring positive initial output. Full decisions establish it by their
actual output test; nonfull decisions preserve it in the state frame. -/
theorem slow_decision_run_ready {h after : Heap} {r : ZStreamRef}
    {ds w ob oo origin base : Nat} {z : ZStream} {d result : DeflateState}
    {wa : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    {flush : Int32} {st next : LoopS} {candidate : UInt32}
    (cut : SearchBoundary h r ds z d input origin base xs w wa)
    (buffers : StreamBuffers h r) (lookahead : 1 ≤ d.lookahead.toNat)
    (strict : d.sym_next.toNat < d.sym_end.toNat)
    (positive : 0 < d.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : d.lit_bufsize.toNat = 16384) (ready : PublishReady d)
    (clear : BlockInit.BlockClear d)
    (run : slowDecision (some (.tab ds)) flush st candidate h = .ok (next, after))
    (live : after.dstates ds = some result) (running : next.ret = none) : PublishReady result := by
  have bits : d.bi_valid.toInt ≤ 7 := by have low := ready.2.2; omega
  by_cases selected : (d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length) = true
  · by_cases full : (d.sym_next + 3 == d.sym_end) = true
    · obtain ⟨produced, head, other, z', otherD, base', ys, tested, boundaryA, _endA, _buffersA,
          _accountA, _clearA, _startA, _lookA, _endpointA, _strictA, _baseA, _configA, _lowA, phaseA, _unchanged⟩ :=
        slow_match_search_boundary cut buffers selected strict positive pointer ready.2.1 memory ready.1 bits clear flush st candidate
      simp only [full, ite_true] at tested
      exact decision_tested_run_ready run tested boundaryA.good live phaseA running
    · exact slow_match_nonfull_run_ready cut buffers selected strict (Bool.eq_false_iff.mpr full) ready run live
  · have branch := Bool.eq_false_iff.mpr selected
    by_cases available : d.match_available = 0
    · obtain ⟨other, otherD, tested, boundaryA, _endA, _buffersA, frameA, _rest⟩ :=
        slow_defer_search_boundary cut buffers lookahead branch available strict flush st candidate
      have heaps : other = after := (Prod.mk.inj (Except.ok.inj (tested.symm.trans run))).2
      rw [heaps] at boundaryA
      have states : otherD = result := Option.some.inj (boundaryA.good.live.hs.symm.trans live)
      rw [← states]
      exact ready.slow frameA
    · have room := literal_room cut.good.inv strict
      by_cases full : d.sym_next.toNat + 3 = d.sym_end.toNat
      · obtain ⟨produced, other, z', otherD, tested, boundaryA, _endA, _buffersA, _accountA,
            _clearA, _startA, _lookA, _endpointA, _strictA, _configA, _lowA, phaseA⟩ :=
          slow_literal_full_search_boundary cut buffers lookahead branch available full positive pointer
            ready.2.1 memory ready.1 bits clear flush st candidate
        exact decision_tested_run_ready run tested boundaryA.good live phaseA running
      · have space : d.sym_next.toNat + 3 < d.sym_end.toNat := by omega
        obtain ⟨other, otherD, tested, boundaryA, _endA, _buffersA, frameA, _rest⟩ :=
          slow_literal_search_boundary cut buffers lookahead branch available space flush st candidate
        have heaps : other = after := (Prod.mk.inj (Except.ok.inj (tested.symm.trans run))).2
        rw [heaps] at boundaryA
        have states : otherD = result := Option.some.inj (boundaryA.good.live.hs.symm.trans live)
        rw [← states]
        exact ready.slow frameA

end Zlib.Deflate.Engine.Proofs
