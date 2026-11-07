import ZlibF.Proof.«deflate.c.engine.finish-body-controls»
import ZlibF.Proof.«deflate.c.engine.finish-ready-loop»

/-! # Public controls retained by the actual complete FINISH loop -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- An additional invariant of an established actual forever-loop run.
This is preservation, not a replacement for the proved termination bound. -/
theorem forever_run_invariant (Inv : LoopS → Heap → Prop) (body : LoopS → M LoopS)
    (step : ∀ st h, Inv st h → st.brk = false → st.ret = none →
      ∀ next after, body st h = .ok (next, after) → Inv next after)
    {st final : LoopS} {h after : Heap} (initial : Inv st h)
    (run : cwhile forever body st h = .ok (final, after)) : Inv final after := by
  have go : ∀ n st h, Inv st h → ∀ final after,
      cwhile.go forever body n st h = .ok (final, after) → Inv final after := by
    intro n
    induction n with
    | zero => intro st h inv final after run; simp only [cwhile.go] at run; cases run
    | succ n ih =>
      intro st h inv final after run
      by_cases stopped : (st.brk || st.ret.isSome) = true
      · have condition : forever st h = .ok ((false, st), h) := by simp [forever, stopped, pure_app]
        simp only [cwhile.go, bind_app, condition, Bool.false_eq_true, ite_false, pure_app] at run
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj run)
        exact inv
      · have guard : (st.brk || st.ret.isSome) = false := Bool.eq_false_iff.mpr stopped
        have condition : forever st h = .ok ((true, st), h) := by simp [forever, guard, pure_app]
        have brk : st.brk = false := (Bool.or_eq_false_iff.mp guard).1
        have running : st.ret = none := by
          cases ret : st.ret with
          | none => rfl
          | some value => simp [ret] at guard
        simp only [cwhile.go, bind_app, condition, ite_true] at run
        cases bodyRun : body st h with
        | error fault => simp only [bodyRun] at run; cases run
        | ok pair =>
          obtain ⟨next, middle⟩ := pair
          simp only [bodyRun] at run
          exact ih next middle (step st h inv brk running next middle bodyRun) final after run
  exact go fuel st h initial final after run

/-- The established actual complete FINISH loop retains the empty-cursor
phase and both public control fields. Its separate execution theorem
continues to supply termination, accounting and content preservation. -/
theorem slow_finish_loop_run_controls {h after : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d result : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    {final : LoopS}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (run : cwhile forever (deflate_slow_body (some (.tab ds)) Z_FINISH) {} h = .ok (final, after))
    (live : after.dstates ds = some result) : StrategyControls d result := by
  let Inv : LoopS → Heap → Prop := fun st heap =>
    ∃ currentZ currentD currentInput currentOrigin currentBase ys offset,
      StrategyBoundary heap r ds currentZ currentD currentInput currentOrigin currentBase ys config ∧
      EndFrontier heap currentD ∧ StreamBuffers heap r ∧
      currentZ.next_out = .ref (.blk ob) offset ∧
      (currentZ.avail_in ≠ 0 → currentZ.next_in ≠ .null) ∧
      (st.ret = none → PublishReady currentD) ∧ StrategyControls d currentD
  have step : ∀ st heap, Inv st heap → st.brk = false → st.ret = none →
      ∀ next after, deflate_slow_body (some (.tab ds)) Z_FINISH st heap = .ok (next, after) → Inv next after := by
    intro st heap inv _brk running next after actual
    obtain ⟨currentZ, currentD, currentInput, currentOrigin, currentBase, ys, offset,
      state, endS, buffersS, pointerS, validS, readyS, controlsS⟩ := inv
    obtain ⟨used, produced, expected, other, nextZ, nextD, nextBase, nextYs, nextInput, nextOrigin,
      bodyRun, stateA, endA, buffersA, accountA, _agreesA, _endpointA, _baseA, _reasonA, _retA, readyA, _decrease, _breakA⟩ :=
      slow_finish_ready_step state endS buffersS positive pointerS memory wrap (readyS running) validS st
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj (bodyRun.symm.trans actual))
    have controlsA := slow_finish_body_run_controls state endS buffersS positive pointerS memory wrap
      (readyS running) validS bodyRun stateA.good.live.hs
    have pointerA : nextZ.next_out = .ref (.blk ob) (offset + produced) := by
      rw [accountA.2.2.2.2.2.1, pointerS]
      rfl
    exact ⟨nextZ, nextD, nextInput, nextOrigin, nextBase, nextYs, offset + produced,
      stateA, endA, buffersA, pointerA, input_valid_accounting_output validS accountA, readyA,
      ⟨controlsA.empty_cursor, controlsA.status.trans controlsS.status, controlsA.last_flush.trans controlsS.last_flush⟩⟩
  have initial : Inv {} h :=
    ⟨z, d, input, origin, base, xs, oo, boundary, frontier, buffers, pointer, inputValid,
      fun _ => publish, ⟨fun _ => publish.2.1, rfl, rfl⟩⟩
  have post := forever_run_invariant Inv (deflate_slow_body (some (.tab ds)) Z_FINISH) step initial run
  obtain ⟨nextZ, nextD, nextInput, nextOrigin, nextBase, nextYs, offset,
    stateA, _endA, _buffersA, _pointerA, _validA, _readyA, controls⟩ := post
  have states : nextD = result := Option.some.inj (stateA.good.live.hs.symm.trans live)
  rw [← states]
  exact controls

end Zlib.Deflate.Engine.Proofs
