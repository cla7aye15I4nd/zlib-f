import ZlibF.Proof.«deflate.c.engine.body-full-storage»
import ZlibF.Proof.«deflate.c.engine.loop-counters»

/-! # Complete object and allocation effects of the actual strategy -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The fixed engine configuration includes every private allocation key. -/
theorem ConfigFrame.owned {ds : Nat} {before after : DeflateState} (frame : ConfigFrame before after) :
    DeflateOwned ds after = DeflateOwned ds before := by
  have window := congrArg EngineConfig.window frame
  have prev := congrArg EngineConfig.prev frame
  have head := congrArg EngineConfig.head frame
  have pending := congrArg EngineConfig.pending frame
  change after.window = before.window at window
  change after.prev = before.prev at prev
  change after.head = before.head at head
  change after.pending_buf = before.pending_buf at pending
  funext b
  simp only [DeflateOwned, window, prev, head, pending]

/-- Both actual ordinary source loops retain every represented heap object outside their fixed private and output allocations, with exact live/allocation ledgers. -/
theorem slow_ordinary_loop_run_full_storage {h after : Heap} {r : ZStreamRef}
    {ds ob oo origin base : Nat} {z : ZStream} {d : DeflateState}
    {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig} {final : LoopS} {flush : Int32}
    (flag : flush = Z_NO_FLUSH ∨ flush = Z_FINISH)
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (run : cwhile forever (deflate_slow_body (some (.tab ds)) flush) {} h = .ok (final, after))
 :
    Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = ob) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  let Inv : LoopS → Heap → Prop := fun st heap =>
    ∃ currentZ currentD currentInput currentOrigin currentBase ys offset accepted delivered,
      StrategyBoundary heap r ds currentZ currentD currentInput currentOrigin currentBase ys config ∧
      EndFrontier heap currentD ∧ StreamBuffers heap r ∧
      currentZ.next_out = .ref (.blk ob) offset ∧
      (currentZ.avail_in ≠ 0 → currentZ.next_in ≠ .null) ∧
      (st.ret = none → PublishReady currentD) ∧ StreamAccounting z currentZ accepted delivered ∧
      currentZ.total_in = z.total_in + UInt64.ofNat accepted ∧
      currentZ.total_out = z.total_out + UInt64.ofNat delivered ∧
      Shape h heap ∧ Frame h heap (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = ob) ∧
      heap.nalloc = h.nalloc ∧ heap.nextBlk = h.nextBlk
  have step : ∀ st heap, Inv st heap → st.brk = false → st.ret = none →
      ∀ next after, deflate_slow_body (some (.tab ds)) flush st heap = .ok (next, after) → Inv next after := by
    intro st heap inv _brk running next after actual
    obtain ⟨currentZ, currentD, currentInput, currentOrigin, currentBase, ys, offset, accepted, delivered,
      state, endS, buffersS, pointerS, validS, readyS, accountS, inputS, outputS, shapeS, fullS, allocS, nextS⟩ := inv
    obtain ⟨read, written, expected, other, nextZ, nextD, nextBase, nextYs, nextInput, nextOrigin,
      bodyRun, stateA, endA, buffersA, accountA, readyA, inputA, outputA⟩ :=
      slow_ordinary_body_counter_execution flag state endS buffersS positive pointerS memory wrap (readyS running) validS st
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj (bodyRun.symm.trans actual))
    have bodyEffects : Shape heap other ∧
        Frame heap other (fun b => StreamRoot r b ∨ DeflateOwned ds currentD b ∨ b = ob) ∧
        LiveChange heap other (fun _ => False) (fun _ => False) ∧ other.nalloc = heap.nalloc ∧ other.nextBlk = heap.nextBlk := by
      rcases flag with rfl | rfl
      · exact slow_no_flush_body_run_full_storage state endS buffersS positive pointerS memory wrap (readyS running) validS actual
      · exact slow_finish_body_run_full_storage state endS buffersS positive pointerS memory wrap (readyS running) validS actual
    obtain ⟨shapeA, fullA, _liveA, allocA, nextA⟩ := bodyEffects
    have owned := ConfigFrame.owned (ds := ds) (show ConfigFrame d currentD from state.configuration.trans boundary.configuration.symm)
    rw [owned] at fullA
    have whole := full_frame_trans_shape fullS fullA shapeS
    have pointerA : nextZ.next_out = .ref (.blk ob) (offset + written) := by
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
