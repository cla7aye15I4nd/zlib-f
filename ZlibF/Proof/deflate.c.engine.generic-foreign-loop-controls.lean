import ZlibF.Proof.«deflate.c.engine.generic-foreign-body-controls»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-body-composable»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-continuation-ready»
import ZlibF.Proof.«deflate.c.engine.finish-loop-controls»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The same actual loop retains public controls and the empty cursor, including zero capacity. -/
theorem default_foreign_slow_loop_run_controls {h after : Heap} {r : ZStreamRef} {ds owner oo origin base : Nat}
    {z : ZStream} {d result : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    {final : LoopS} {flush : Int32}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.dstate_depth owner) oo)
    (memory : config.memory.toNat=16384) (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (run : cwhile forever (deflate_slow_body (some (.tab ds)) flush) {} h = .ok (final, after))
    (live : after.dstates ds = some result) : StrategyControls d result := by
  let Inv : LoopS → Heap → Prop := fun st heap =>
    ∃ currentZ currentD currentInput currentOrigin currentBase ys offset,
      StrategyBoundary heap r ds currentZ currentD currentInput currentOrigin currentBase ys config ∧
      EndFrontier heap currentD ∧ StreamBuffers heap r ∧
      currentZ.next_out = .ref (.dstate_depth owner) offset ∧
      (currentZ.avail_in ≠ 0 → currentZ.next_in ≠ .null) ∧
      (st.ret = none → PublishReady currentD) ∧ StrategyControls d currentD
  have step : ∀ st heap, Inv st heap → st.brk = false → st.ret = none →
      ∀ next after, deflate_slow_body (some (.tab ds)) flush st heap = .ok (next, after) → Inv next after := by
    intro st heap inv _brk running next after actual
    obtain ⟨currentZ, currentD, currentInput, currentOrigin, currentBase, ys, offset,
      state, endS, buffersS, pointerS, validS, readyS, controlsS⟩ := inv
    obtain ⟨used, produced, expected, other, nextZ, nextD, nextBase, nextYs, nextInput, nextOrigin,
        _before, _written, _remaining, _blockBits, bodyRun, stateA, endA, buffersA, accountA, _rest⟩ :=
      default_foreign_slow_body_composable_prefix (offset := currentD.bi_valid.toInt.toNat)
        state endS buffersS positive pointerS memory wrap (readyS running) validS rfl flush st
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj (bodyRun.symm.trans actual))
    have controlsA := default_foreign_slow_body_run_controls state endS buffersS positive pointerS memory wrap
      (readyS running) validS bodyRun stateA.good.live.hs
    have readyA := default_foreign_slow_body_run_ready_phase state endS buffersS positive pointerS memory wrap
      (readyS running) validS bodyRun stateA.good.live.hs
    have pointerA : nextZ.next_out = .ref (.dstate_depth owner) (offset + produced) := by
      rw [accountA.2.2.2.2.2.1, pointerS]
      rfl
    exact ⟨nextZ, nextD, nextInput, nextOrigin, nextBase, nextYs, offset + produced,
      stateA, endA, buffersA, pointerA, input_valid_accounting_output validS accountA, readyA,
      ⟨controlsA.empty_cursor, controlsA.status.trans controlsS.status, controlsA.last_flush.trans controlsS.last_flush⟩⟩
  have initial : Inv {} h :=
    ⟨z, d, input, origin, base, xs, oo, boundary, frontier, buffers, pointer, inputValid,
      fun _ => publish, ⟨fun _ => publish.2.1, rfl, rfl⟩⟩
  have post := forever_run_invariant Inv (deflate_slow_body (some (.tab ds)) flush) step initial run
  obtain ⟨nextZ, nextD, nextInput, nextOrigin, nextBase, nextYs, offset,
    stateA, _endA, _buffersA, _pointerA, _validA, _readyA, controls⟩ := post
  have states : nextD = result := Option.some.inj (stateA.good.live.hs.symm.trans live)
  rw [← states]
  exact controls

end Zlib.Deflate.Engine.Proofs
