import ZlibF.Proof.«deflate.c.engine.generic-foreign-continuation-ready»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-body-all-scalar-counters»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-body-physical»
import ZlibF.Proof.«deflate.c.engine.loop-full-storage»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The same actual all-scalar loop accumulates the proved body effects. Zero caller
output capacity is included through the actual continuation-readiness proof. -/
theorem default_foreign_slow_loop_run_counter_effects {h after : Heap} {r : ZStreamRef}
    {ds owner oo origin base used produced : Nat} {z returned : ZStream} {d : DeflateState}
    {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig} {final : LoopS} {flush : Int32}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.dstate_depth owner) oo)
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
      currentZ.next_out = .ref (.dstate_depth owner) offset ∧
      (currentZ.avail_in ≠ 0 → currentZ.next_in ≠ .null) ∧
      (st.ret = none → PublishReady currentD) ∧ StreamAccounting z currentZ accepted delivered ∧
      currentZ.total_in = z.total_in + UInt64.ofNat accepted ∧
      currentZ.total_out = z.total_out + UInt64.ofNat delivered
  have step : ∀ st heap, Inv st heap → st.brk = false → st.ret = none →
      ∀ next after, deflate_slow_body (some (.tab ds)) flush st heap = .ok (next, after) → Inv next after := by
    intro st heap inv _brk running next after actual
    obtain ⟨currentZ, currentD, currentInput, currentOrigin, currentBase, ys, offset, accepted, delivered,
      state, endS, buffersS, pointerS, validS, readyS, accountS, inputS, outputS⟩ := inv
    obtain ⟨read,written,expected,other,nextZ,nextD,nextBase,nextYs,nextInput,nextOrigin,
      _before,_bytes,_remaining,bodyRun,stateA,endA,buffersA,accountA,_rest⟩ :=
      default_foreign_slow_body_strategy_encoding state endS buffersS positive pointerS memory wrap (readyS running) validS flush st
    have readyA := default_foreign_slow_body_run_ready_phase state endS buffersS positive pointerS memory wrap
      (readyS running) validS bodyRun stateA.good.live.hs
    have bodyCounters := default_foreign_slow_body_run_counter_effects state endS buffersS positive pointerS memory wrap
      (readyS running) validS bodyRun stateA.good.live.hz accountA
    have inputA := bodyCounters.1
    have outputA := bodyCounters.2
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj (bodyRun.symm.trans actual))
    have pointerA : nextZ.next_out = .ref (.dstate_depth owner) (offset + written) := by
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
