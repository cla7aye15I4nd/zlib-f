import ZlibF.Proof.«deflate.c.engine.body-counters»
import ZlibF.Proof.«deflate.c.engine.finish-loop-controls»

/-! # The actual ordinary loops accumulate exact wrapping totals -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Both complete actual ordinary loops retain exact wrapping totals.
The known actual execution supplies termination; induction accumulates
the real accepted and delivered counts on the same returned heap. -/
theorem slow_ordinary_loop_run_counter_effects {h after : Heap} {r : ZStreamRef}
    {ds ob oo origin base used produced : Nat} {z returned : ZStream} {d : DeflateState}
    {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig} {final : LoopS} {flush : Int32}
    (flag : flush = Z_NO_FLUSH ∨ flush = Z_FINISH)
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (run : cwhile forever (deflate_slow_body (some (.tab ds)) flush) {} h = .ok (final, after))
    (live : r.get after = some returned) (account : StreamAccounting z returned used produced) :
    returned.total_in = z.total_in + UInt64.ofNat used ∧
      returned.total_out = z.total_out + UInt64.ofNat produced := by
  let Inv : LoopS → Heap → Prop := fun st heap =>
    ∃ currentZ currentD currentInput currentOrigin currentBase ys offset accepted delivered,
      StrategyBoundary heap r ds currentZ currentD currentInput currentOrigin currentBase ys config ∧
      EndFrontier heap currentD ∧ StreamBuffers heap r ∧
      currentZ.next_out = .ref (.blk ob) offset ∧
      (currentZ.avail_in ≠ 0 → currentZ.next_in ≠ .null) ∧
      (st.ret = none → PublishReady currentD) ∧ StreamAccounting z currentZ accepted delivered ∧
      currentZ.total_in = z.total_in + UInt64.ofNat accepted ∧
      currentZ.total_out = z.total_out + UInt64.ofNat delivered
  have step : ∀ st heap, Inv st heap → st.brk = false → st.ret = none →
      ∀ next after, deflate_slow_body (some (.tab ds)) flush st heap = .ok (next, after) → Inv next after := by
    intro st heap inv _brk running next after actual
    obtain ⟨currentZ, currentD, currentInput, currentOrigin, currentBase, ys, offset, accepted, delivered,
      state, endS, buffersS, pointerS, validS, readyS, accountS, inputS, outputS⟩ := inv
    obtain ⟨read, written, expected, other, nextZ, nextD, nextBase, nextYs, nextInput, nextOrigin,
      bodyRun, stateA, endA, buffersA, accountA, readyA, inputA, outputA⟩ :=
      slow_ordinary_body_counter_execution flag state endS buffersS positive pointerS memory wrap (readyS running) validS st
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj (bodyRun.symm.trans actual))
    have pointerA : nextZ.next_out = .ref (.blk ob) (offset + written) := by
      rw [accountA.2.2.2.2.2.1, pointerS]
      rfl
    have effects := stream_counter_effects_trans inputS outputS inputA outputA
    exact ⟨nextZ, nextD, nextInput, nextOrigin, nextBase, nextYs, offset + written, accepted + read, delivered + written,
      stateA, endA, buffersA, pointerA, input_valid_accounting_output validS accountA, readyA,
      stream_accounting_trans accountS accountA, effects⟩
  have initial : Inv {} h :=
    ⟨z, d, input, origin, base, xs, oo, 0, 0, boundary, frontier, buffers, pointer, inputValid,
      fun _ => publish, stream_accounting_zero z, by simp, by simp⟩
  have post := forever_run_invariant Inv (deflate_slow_body (some (.tab ds)) flush) step initial run
  obtain ⟨nextZ, nextD, nextInput, nextOrigin, nextBase, nextYs, offset, accepted, delivered,
    stateA, _endA, _buffersA, _pointerA, _validA, _readyA, accountA, inputA, outputA⟩ := post
  have same : nextZ = returned := Option.some.inj (stateA.good.live.hz.symm.trans live)
  exact stream_counter_effects_identify same accountA account inputA outputA

end Zlib.Deflate.Engine.Proofs
