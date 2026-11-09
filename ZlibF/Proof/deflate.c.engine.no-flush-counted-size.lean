import ZlibF.Proof.«deflate.c.engine.loop-counted-size»
import ZlibF.Proof.«deflate.c.engine.no-flush-loop-control»

/-! # Actual NO_FLUSH strategy calls retain the counted prefix budget -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The actual NO_FLUSH loop always returns before EOF settlement and
the final block. Its complete strategy call therefore spends only the
counted full-block budget, with no extra final-block charge per call.
This precise prefix form supports repeated utility calls on large inputs. -/
theorem deflate_slow_no_flush_counted_size {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List Symbol} {config : EngineConfig}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (window : config.windowBits = 15)
    (strategy : config.strategy = Z_DEFAULT_STRATEGY)
    (publish : PublishReady d) (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (candidate : ShortCandidateQuality d) (floor : StoredSourceFloor d)
    (quality : ∀ s ∈ xs, s.distance ≠ 0 → s.value = 0 → s.distance ≤ 4096) :
    ∃ used produced blocks after z' result extended nextOrigin nextBase ys,
      deflate_slow (some (.tab ds)) Z_NO_FLUSH h = .ok (need_more, after) ∧
      StrategyBoundary after r ds z' result extended nextOrigin nextBase ys config ∧ EndFrontier after result ∧
      StreamBuffers after r ∧ StreamAccounting z z' used produced ∧
      nextOrigin + fillEnd result = origin + fillEnd d + used ∧ base ≤ nextBase ∧
      ShortCandidateQuality result ∧ StoredSourceFloor result ∧
      (∀ s ∈ ys, s.distance ≠ 0 → s.value = 0 → s.distance ≤ 4096) ∧
      16383 * blocks ≤ nextBase - base ∧
      produced + result.pending.toNat + (result.bi_valid.toInt.toNat + 7) / 8 ≤
        (d.bi_valid.toInt.toNat + 7) / 8 + (nextBase - base) + 5 * blocks := by
  obtain ⟨_used, _produced, terminated, _z, _d, _base, _ys, _input, _origin, safe, _rest⟩ :=
    deflate_slow_no_flush_ready boundary frontier buffers positive pointer memory wrap publish inputValid
  have loopExists : ∃ final after,
      cwhile forever (deflate_slow_body (some (.tab ds)) Z_NO_FLUSH) {} h = .ok (final, after) := by
    cases loop : cwhile forever (deflate_slow_body (some (.tab ds)) Z_NO_FLUSH) {} h with
    | error fault =>
      unfold deflate_slow at safe
      rw [bind_app, loop] at safe
      cases safe
    | ok pair => exact ⟨pair.1, pair.2, rfl⟩
  obtain ⟨final, after, loop⟩ := loopExists
  have returned := slow_no_flush_loop_run_control boundary frontier buffers positive pointer memory wrap publish inputValid loop
  obtain ⟨used, produced, blocks, z', result, extended, nextOrigin, nextBase, ys,
    stateA, endA, buffersA, accountA, endpointA, baseA, _readyA, candidateA, floorA, qualityA, minimumA, costA⟩ :=
    slow_loop_run_counted_size boundary frontier buffers positive pointer memory wrap window strategy publish inputValid
      candidate floor quality loop
  refine ⟨used, produced, blocks, after, z', result, extended, nextOrigin, nextBase, ys,
    ?_, stateA, endA, buffersA, accountA, endpointA, baseA, candidateA, floorA, qualityA, minimumA, costA⟩
  unfold deflate_slow
  rw [bind_app, loop]
  simp only [returned]
  rfl

end Zlib.Deflate.Engine.Proofs
