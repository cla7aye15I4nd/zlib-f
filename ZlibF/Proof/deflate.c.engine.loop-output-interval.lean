import ZlibF.Proof.«deflate.c.engine.body-output-interval»
import ZlibF.Proof.«deflate.c.engine.loop-full-storage»

/-! # Exact raw caller output intervals through actual strategy execution -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Both actual ordinary loops preserve every caller byte outside their combined accounted output interval. -/
theorem slow_ordinary_loop_run_output_effect {h after : Heap} {r : ZStreamRef}
    {ds ob oo origin base used produced : Nat} {z z' : ZStream} {d : DeflateState}
    {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig} {final : LoopS} {flush : Int32}
    (flag : flush = Z_NO_FLUSH ∨ flush = Z_FINISH)
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (run : cwhile forever (deflate_slow_body (some (.tab ds)) flush) {} h = .ok (final, after))
    (live : r.get after = some z') (account : StreamAccounting z z' used produced) :
    RawOutputInterval h after ob oo produced := by
  let Inv : LoopS → Heap → Prop := fun st heap =>
    ∃ currentZ currentD currentInput currentOrigin currentBase ys offset accepted delivered,
      StrategyBoundary heap r ds currentZ currentD currentInput currentOrigin currentBase ys config ∧
      EndFrontier heap currentD ∧ StreamBuffers heap r ∧
      currentZ.next_out = .ref (.blk ob) offset ∧
      (currentZ.avail_in ≠ 0 → currentZ.next_in ≠ .null) ∧
      (st.ret = none → PublishReady currentD) ∧ StreamAccounting z currentZ accepted delivered ∧
      currentZ.total_in = z.total_in + UInt64.ofNat accepted ∧
      currentZ.total_out = z.total_out + UInt64.ofNat delivered ∧
      RawOutputInterval h heap ob oo delivered
  have step : ∀ st heap, Inv st heap → st.brk = false → st.ret = none →
      ∀ next after, deflate_slow_body (some (.tab ds)) flush st heap = .ok (next, after) → Inv next after := by
    intro st heap inv _brk running next after actual
    obtain ⟨currentZ, currentD, currentInput, currentOrigin, currentBase, ys, offset, accepted, delivered,
      state, endS, buffersS, pointerS, validS, readyS, accountS, inputS, outputS, effectS⟩ := inv
    obtain ⟨read, written, expected, other, nextZ, nextD, nextBase, nextYs, nextInput, nextOrigin,
      bodyRun, stateA, endA, buffersA, accountA, readyA, inputA, outputA⟩ :=
      slow_ordinary_body_counter_execution flag state endS buffersS positive pointerS memory wrap (readyS running) validS st
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj (bodyRun.symm.trans actual))
    have pointerExact : currentZ.next_out = .ref (.blk ob) (oo + delivered) := by
      rw [accountS.2.2.2.2.2.1, pointer]
      rfl
    have bodyEffect : RawOutputInterval heap other ob (oo + delivered) written := by
      rcases flag with rfl | rfl
      · exact slow_no_flush_body_run_output_effect state endS buffersS positive pointerExact memory wrap
          (readyS running) validS actual stateA.good.live.hz accountA
      · exact slow_finish_body_run_output_effect state endS buffersS positive pointerExact memory wrap
          (readyS running) validS actual stateA.good.live.hz accountA
    have whole := effectS.trans bodyEffect
    have pointerA : nextZ.next_out = .ref (.blk ob) (offset + written) := by
      rw [accountA.2.2.2.2.2.1, pointerS]
      rfl
    have effects := stream_counter_effects_trans inputS outputS inputA outputA
    exact ⟨nextZ, nextD, nextInput, nextOrigin, nextBase, nextYs, offset + written, accepted + read, delivered + written,
      stateA, endA, buffersA, pointerA, input_valid_accounting_output validS accountA, readyA,
      stream_accounting_trans accountS accountA, effects.1, effects.2, whole⟩
  have initial : Inv {} h :=
    ⟨z, d, input, origin, base, xs, oo, 0, 0, boundary, frontier, buffers, pointer, inputValid,
      fun _ => publish, stream_accounting_zero z, by simp, by simp, RawOutputInterval.of_same rfl⟩
  have post := forever_run_invariant Inv (deflate_slow_body (some (.tab ds)) flush) step initial run
  obtain ⟨nextZ, nextD, nextInput, nextOrigin, nextBase, nextYs, offset, accepted, delivered,
    stateA, _endA, _buffersA, _pointerA, _validA, _readyA, accountA, _inputA, _outputA, effect⟩ := post
  have streams : nextZ = z' := Option.some.inj (stateA.good.live.hz.symm.trans live)
  rw [streams] at accountA
  have count : delivered = produced := (stream_accounting_counts_unique accountA account).2
  rw [← count]
  exact effect

end Zlib.Deflate.Engine.Proofs
