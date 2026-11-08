import ZlibF.Proof.«deflate.c.engine.finish-loop-controls»
import ZlibF.Proof.«deflate.c.engine.no-flush-ready-step»

/-! # The actual NO_FLUSH loop returns before the EOF tail -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Every successful actual forever-loop run stops at its real control
test. This is a property of the translated condition, not an execution
contract for a C callee. -/
theorem forever_run_stopped {body : LoopS → M LoopS} {st final : LoopS} {h after : Heap}
    (run : cwhile forever body st h = .ok (final, after)) :
    (final.brk || final.ret.isSome) = true := by
  have go : ∀ n st h final after,
      cwhile.go forever body n st h = .ok (final, after) → (final.brk || final.ret.isSome) = true := by
    intro n
    induction n with
    | zero => intro st h final after run; simp only [cwhile.go] at run; cases run
    | succ n ih =>
      intro st h final after run
      by_cases stopped : (st.brk || st.ret.isSome) = true
      · have cond : forever st h = .ok ((false, st), h) := by simp [forever, stopped, pure_app]
        simp only [cwhile.go, bind_app, cond, Bool.false_eq_true, ite_false, pure_app] at run
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj run)
        exact stopped
      · have guard : (st.brk || st.ret.isSome) = false := Bool.eq_false_iff.mpr stopped
        have cond : forever st h = .ok ((true, st), h) := by simp [forever, guard, pure_app]
        simp only [cwhile.go, bind_app, cond, ite_true] at run
        cases bodyRun : body st h with
        | error fault => simp only [bodyRun] at run; cases run
        | ok pair =>
          obtain ⟨next, middle⟩ := pair
          simp only [bodyRun] at run
          exact ih next middle final after run
  exact go fuel st h final after run

/-- The actual initialized NO_FLUSH loop can stop only with need_more.
In particular it never enters the EOF settlement/final-block tail. All
real refill and full block paths, including zero prepared output, are
covered by the existing actual body execution theorem. -/
theorem slow_no_flush_loop_run_control {h after : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig} {final : LoopS}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (run : cwhile forever (deflate_slow_body (some (.tab ds)) Z_NO_FLUSH) {} h = .ok (final, after)) :
    final.ret = some need_more := by
  let Inv : LoopS → Heap → Prop := fun st heap =>
    ∃ currentZ currentD currentInput currentOrigin currentBase ys offset,
      StrategyBoundary heap r ds currentZ currentD currentInput currentOrigin currentBase ys config ∧
      EndFrontier heap currentD ∧ StreamBuffers heap r ∧ currentZ.next_out = .ref (.blk ob) offset ∧
      (currentZ.avail_in ≠ 0 → currentZ.next_in ≠ .null) ∧
      (st.ret = none → PublishReady currentD) ∧ st.brk = false ∧ (st.ret = none ∨ st.ret = some need_more)
  have step : ∀ st heap, Inv st heap → st.brk = false → st.ret = none →
      ∀ next middle, deflate_slow_body (some (.tab ds)) Z_NO_FLUSH st heap = .ok (next, middle) → Inv next middle := by
    intro st heap inv _brk running next middle actual
    obtain ⟨currentZ, currentD, currentInput, currentOrigin, currentBase, ys, offset,
      state, endS, buffersS, pointerS, validS, readyS, brkS, _retS⟩ := inv
    obtain ⟨used, produced, expected, other, nextZ, nextD, nextBase, nextYs, nextInput, nextOrigin,
      bodyRun, stateA, endA, buffersA, accountA, _agrees, _endpoint, _base,
      brkA, retA, readyA, _less, _reason⟩ :=
      slow_no_flush_ready_step state endS buffersS positive pointerS memory wrap (readyS running) validS st
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj (bodyRun.symm.trans actual))
    have pointerA : nextZ.next_out = .ref (.blk ob) (offset + produced) := by
      rw [accountA.2.2.2.2.2.1, pointerS]
      rfl
    have retNext : expected.ret = none ∨ expected.ret = some need_more := by
      rcases retA with same | returned
      · exact Or.inl (same.trans running)
      · exact Or.inr returned
    exact ⟨nextZ, nextD, nextInput, nextOrigin, nextBase, nextYs, offset + produced,
      stateA, endA, buffersA, pointerA, input_valid_accounting_output validS accountA,
      readyA, brkA.trans brkS, retNext⟩
  have initial : Inv {} h :=
    ⟨z, d, input, origin, base, xs, oo, boundary, frontier, buffers, pointer, inputValid,
      fun _ => publish, rfl, Or.inl rfl⟩
  have post := forever_run_invariant Inv (deflate_slow_body (some (.tab ds)) Z_NO_FLUSH) step initial run
  obtain ⟨_z, _d, _input, _origin, _base, _ys, _offset, _state, _end, _buffers, _pointer,
    _valid, _ready, brkA, retA⟩ := post
  have stopped := forever_run_stopped run
  rcases retA with running | returned
  · simp only [brkA, running, Option.isSome_none, Bool.or_self, Bool.false_eq_true] at stopped
  · exact returned

end Zlib.Deflate.Engine.Proofs
