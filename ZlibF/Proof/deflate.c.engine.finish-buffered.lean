import ZlibF.Proof.«deflate.c.engine.finish-call-controls»
import ZlibF.Proof.«deflate.c.engine.finish-ready-call»
import ZlibF.Proof.«deflate.c.engine.buffered-boundary»

/-! # The complete FINISH strategy preserves the caller-independent boundary -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The actual complete default-memory FINISH strategy returns the same
BufferedBoundary established by initialization and legal rebuffering.
Every input length and raw output capacity, including zero, is covered
at the prepared entry. The real loop supplies termination and accounting;
its added control invariant covers early and final returns.
Public wrapper composition, full output history and heap frame remain
separate obligations. This is not the public Goal.deflate. -/
theorem deflate_slow_finish_buffered {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : BufferedBoundary h r ds z d input origin base xs config) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ used produced ret after z' result base' ys extended nextOrigin,
      deflate_slow (some (.tab ds)) Z_FINISH h = .ok (ret, after) ∧
      BufferedBoundary after r ds z' result extended nextOrigin base' ys config ∧ StrategyControls d result ∧
      (0 < z'.avail_out.toNat → PublishReady result) ∧ StreamBuffers after r ∧ StreamAccounting z z' used produced ∧
      (∀ i, i < origin + fillEnd d → extended i = input i) ∧
      nextOrigin + fillEnd result = origin + fillEnd d + used ∧ base ≤ base' ∧
      (ret ≠ need_more → result.lookahead = 0 ∧ result.bi_valid.toInt = 0) ∧
      ((ret = need_more ∧ z'.avail_out = 0) ∨
       (ret = finish_started ∧ z'.avail_out = 0 ∧ z'.avail_in = 0) ∨
       (ret = finish_done ∧ 0 < z'.avail_out.toNat ∧ z'.avail_in = 0)) := by
  have strategy := boundary.strategy publish
  obtain ⟨used, produced, ret, after, z', result, base', ys, extended, nextOrigin, run,
      stateA, endA, buffersA, accountA, agreesA, endpointA, baseA, zeroA, classification⟩ :=
    deflate_slow_finish_ready strategy boundary.end_frontier buffers positive pointer memory wrap publish inputValid
  have controls := deflate_slow_finish_run_controls strategy boundary.end_frontier buffers positive pointer memory wrap publish
    inputValid run stateA.good.live.hs
  exact ⟨used, produced, ret, after, z', result, base', ys, extended, nextOrigin, run,
    stateA.buffered endA controls.empty_cursor, controls, stateA.resume, buffersA, accountA, agreesA, endpointA, baseA, zeroA, classification⟩

end Zlib.Deflate.Engine.Proofs
