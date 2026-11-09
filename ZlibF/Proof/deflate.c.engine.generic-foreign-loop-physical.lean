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
theorem default_foreign_slow_loop_run_full_storage {h after : Heap} {r : ZStreamRef}
    {ds owner oo origin base : Nat} {z : ZStream} {d : DeflateState}
    {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig} {final : LoopS} {flush : Int32}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.dstate_depth owner) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (run : cwhile forever (deflate_slow_body (some (.tab ds)) flush) {} h = .ok (final, after))
 :
    Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = owner) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  let Inv : LoopS → Heap → Prop := fun st heap =>
    ∃ currentZ currentD currentInput currentOrigin currentBase ys offset accepted delivered,
      StrategyBoundary heap r ds currentZ currentD currentInput currentOrigin currentBase ys config ∧
      EndFrontier heap currentD ∧ StreamBuffers heap r ∧
      currentZ.next_out = .ref (.dstate_depth owner) offset ∧
      (currentZ.avail_in ≠ 0 → currentZ.next_in ≠ .null) ∧
      (st.ret = none → PublishReady currentD) ∧ StreamAccounting z currentZ accepted delivered ∧
      currentZ.total_in = z.total_in + UInt64.ofNat accepted ∧
      currentZ.total_out = z.total_out + UInt64.ofNat delivered ∧
      Shape h heap ∧ Frame h heap (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = owner) ∧
      heap.nalloc = h.nalloc ∧ heap.nextBlk = h.nextBlk
  have step : ∀ st heap, Inv st heap → st.brk = false → st.ret = none →
      ∀ next after, deflate_slow_body (some (.tab ds)) flush st heap = .ok (next, after) → Inv next after := by
    intro st heap inv _brk running next after actual
    obtain ⟨currentZ, currentD, currentInput, currentOrigin, currentBase, ys, offset, accepted, delivered,
      state, endS, buffersS, pointerS, validS, readyS, accountS, inputS, outputS, shapeS, fullS, allocS, nextS⟩ := inv
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
    have bodyEffects : Shape heap other ∧
        Frame heap other (fun b => StreamRoot r b ∨ DeflateOwned ds currentD b ∨ b = owner) ∧
        LiveChange heap other (fun _ => False) (fun _ => False) ∧ other.nalloc = heap.nalloc ∧ other.nextBlk = heap.nextBlk :=
      default_foreign_slow_body_run_full_storage state endS buffersS positive pointerS memory wrap (readyS running) validS actual
    obtain ⟨shapeA, fullA, _liveA, allocA, nextA⟩ := bodyEffects
    have owned := ConfigFrame.owned (ds := ds) (show ConfigFrame d currentD from state.configuration.trans boundary.configuration.symm)
    rw [owned] at fullA
    have whole := full_frame_trans_shape fullS fullA shapeS
    have pointerA : nextZ.next_out = .ref (.dstate_depth owner) (offset + written) := by
      rw [accountA.2.2.2.2.2.1, pointerS]
      rfl
    have effects := stream_counter_effects_trans inputS outputS inputA outputA
    exact ⟨nextZ, nextD, nextInput, nextOrigin, nextBase, nextYs, offset + written, accepted + read, delivered + written,
      stateA, endA, buffersA, pointerA, input_valid_accounting_output validS accountA, readyA,
      stream_accounting_trans accountS accountA, effects.1, effects.2, shapeS.trans shapeA, whole, allocA.trans allocS, nextA.trans nextS⟩
  have initial : Inv {} h :=
    ⟨z, d, input, origin, base, xs, oo, 0, 0, boundary, frontier, buffers, pointer, inputValid,
      fun _ => publish, stream_accounting_zero z, by simp, by simp, Shape.refl h, (full_storage_refl h _).2.1, rfl, rfl⟩
  have post := forever_run_invariant Inv (deflate_slow_body (some (.tab ds)) flush) step initial run
  obtain ⟨nextZ, nextD, nextInput, nextOrigin, nextBase, nextYs, offset, accepted, delivered,
    stateA, _endA, _buffersA, _pointerA, _validA, _readyA, accountA, inputA, outputA, shape, frame, alloc, next⟩ := post
  exact ⟨shape, frame, full_shape_live_change shape, alloc, next⟩

end Zlib.Deflate.Engine.Proofs
