import ZlibF.Proof.«deflate.c.engine.public-data-full-storage»
import ZlibF.Proof.«deflate.c.engine.common-no-flush-source»
import ZlibF.Proof.«deflate.c.engine.public-busy-counters»
/-! # Full object and allocation frames for both public data paths -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Actual BUSY NO_FLUSH dispatch includes idle calls and exhausted prepared output. -/
theorem public_common_slow_no_flush_full_storage_execution {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : BufferedBoundary h r ds z d input origin base xs config) (buffers : StreamBuffers h r)
    (status : d.status = BUSY_STATE) (low : 4 ≤ d.level.toInt) (high : d.level.toInt ≤ 9) (strategy : d.strategy = 0)
    (pointer : z.next_out = .ref (.blk ob) oo) (memory : config.memory.toNat = 16384)
    (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ used produced after z' result,
      publicDataTail (some r) (some (.tab ds)) Z_NO_FLUSH h = .ok (Z_OK, after) ∧
      DGood after r ds z' result ∧ StreamAccounting z z' used produced ∧
      z'.total_in = z.total_in + UInt64.ofNat used ∧ z'.total_out = z.total_out + UInt64.ofNat produced ∧
      Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = ob) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  by_cases active : z.avail_in ≠ 0 ∨ d.lookahead ≠ 0
  · have positive : 0 < config.level.toInt := by
      have eq := congrArg EngineConfig.level boundary.configuration
      change d.level = config.level at eq
      rw [← eq]
      omega
    obtain ⟨used, produced, middle, zm, dm, nextBase, ys, nextInput, nextOrigin, strategyRun,
        stateM, controlsM, buffersM, accountM, _agrees, _endpoint, _base, _stopped, _consumed⟩ :=
      deflate_slow_no_flush_buffered_ready boundary buffers positive pointer memory wrap publish inputValid
    have effectsM := deflate_slow_no_flush_run_counter_effects (boundary.strategy publish) boundary.end_frontier
      buffers positive pointer memory wrap publish inputValid strategyRun stateM.good.live.hz accountM
    obtain ⟨shapeM, frameM, _liveM, allocM, nextM⟩ :=
      deflate_slow_no_flush_run_full_storage (boundary.strategy publish) boundary.end_frontier
        buffers positive pointer memory wrap publish inputValid strategyRun
    have source : publicDataTail (some r) (some (.tab ds)) Z_NO_FLUSH h =
        publicStrategyReturn (some r) (some (.tab ds)) Z_NO_FLUSH need_more middle := by
      rw [public_common_slow_no_flush_source boundary.good.live.hz boundary.good.live.hs status low high strategy active]
      simp only [bind_app, strategyRun]
    have returned := public_need_more_return stateM.good.live.hz stateM.good.live.hs Z_NO_FLUSH
    by_cases empty : zm.avail_out = 0
    · simp only [empty, BEq.rfl, ite_true] at returned
      have stateF := last_flush_buffered_boundary stateM (-1)
      exact ⟨used, produced, _, zm, _, source.trans returned, stateF.good, accountM, effectsM.1, effectsM.2,
        full_storage_state_trans shapeM frameM allocM nextM stateM.good.live.hs (Or.inr (Or.inl (Or.inl rfl))) _⟩
    · simp only [beq_eq_false_iff_ne.mpr empty, Bool.false_eq_true, ite_false] at returned
      exact ⟨used, produced, middle, zm, dm, source.trans returned, stateM.good, accountM, effectsM.1, effectsM.2,
        shapeM, frameM, full_shape_live_change shapeM, allocM, nextM⟩
  · have empty : z.avail_in = 0 := by
      by_cases zero : z.avail_in = 0
      · exact zero
      · exact False.elim (active (Or.inl zero))
    have look : d.lookahead = 0 := by
      by_cases zero : d.lookahead = 0
      · exact zero
      · exact False.elim (active (Or.inr zero))
    exact ⟨0, 0, h, z, d, public_default_empty_data boundary.good status empty look,
      boundary.good, stream_accounting_zero z, by simp, by simp,
      full_storage_refl h _⟩

end Zlib.Deflate.Engine.Proofs
