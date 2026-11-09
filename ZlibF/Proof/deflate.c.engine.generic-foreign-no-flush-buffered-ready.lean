import ZlibF.Proof.«deflate.c.engine.generic-foreign-no-flush-ready-call»
import ZlibF.Proof.«deflate.c.engine.buffered-boundary»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Complete actual NO_FLUSH returns the public BufferedBoundary and controls for every
prepared foreign-output capacity, including zero, with the original stop/consumption facts. -/
theorem default_foreign_deflate_slow_no_flush_buffered_ready {h : Heap} {r : ZStreamRef} {ds owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : BufferedBoundary h r ds z d input origin base xs config) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.dstate_depth owner) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ used produced after z' result base' ys extended nextOrigin,
      deflate_slow (some (.tab ds)) Z_NO_FLUSH h = .ok (need_more, after) ∧
      BufferedBoundary after r ds z' result extended nextOrigin base' ys config ∧ StrategyControls d result ∧
      StreamBuffers after r ∧ StreamAccounting z z' used produced ∧
      (∀ i, i < origin + fillEnd d → extended i = input i) ∧
      nextOrigin + fillEnd result = origin + fillEnd d + used ∧ base ≤ base' ∧
      ((z'.avail_in = 0 ∧ result.lookahead.toNat < 262) ∨ z'.avail_out = 0) ∧
      (0 < z'.avail_out.toNat → used = z.avail_in.toNat) := by
  obtain ⟨used, produced, after, z', result, base', ys, extended, nextOrigin, run,
      stateA, endA, controlsA, buffersA, accountA, agreesA, endpointA, baseA, stoppedA, consumedA⟩ :=
    default_foreign_deflate_slow_no_flush_ready (boundary.strategy publish) boundary.end_frontier buffers positive pointer memory wrap publish inputValid
  exact ⟨used, produced, after, z', result, base', ys, extended, nextOrigin, run,
    stateA.buffered endA controlsA.empty_cursor, controlsA, buffersA, accountA, agreesA, endpointA, baseA, stoppedA, consumedA⟩

end Zlib.Deflate.Engine.Proofs
