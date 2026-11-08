import ZlibF.Proof.«deflate.c.engine.no-flush-buffered»
import ZlibF.Proof.«deflate.c.engine.public-no-flush-source»
import ZlibF.Proof.«deflate.c.engine.public-buffered-pending»

/-! # Actual prepared NO_FLUSH data dispatch retains the working boundary -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The actual prepared BUSY NO_FLUSH data path preserves the working
boundary, including idle dispatch and zero remaining output after a header. -/
theorem public_busy_slow_no_flush_buffered {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : BufferedBoundary h r ds z d input origin base xs config) (buffers : StreamBuffers h r)
    (status : d.status = BUSY_STATE) (level : d.level = 6) (strategy : d.strategy = 0)
    (pointer : z.next_out = .ref (.blk ob) oo) (memory : config.memory.toNat = 16384)
    (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ used produced after z' result nextInput nextOrigin nextBase ys,
      publicDataTail (some r) (some (.tab ds)) Z_NO_FLUSH h = .ok (Z_OK, after) ∧
      BufferedBoundary after r ds z' result nextInput nextOrigin nextBase ys config ∧ StreamBuffers after r ∧
      StreamAccounting z z' used produced ∧ result.status = BUSY_STATE ∧
      (result.last_flush = -1 ∨ result.last_flush = d.last_flush) := by
  by_cases active : z.avail_in ≠ 0 ∨ d.lookahead ≠ 0
  · have positive : 0 < config.level.toInt := by
      have eq := congrArg EngineConfig.level boundary.configuration
      change d.level = config.level at eq
      rw [← eq, level]
      decide
    obtain ⟨used, produced, middle, zm, dm, nextBase, ys, nextInput, nextOrigin, strategyRun,
        stateM, controlsM, buffersM, accountM, _agrees, _endpoint, _base, _stopped, _consumed⟩ :=
      deflate_slow_no_flush_buffered_ready boundary buffers positive pointer memory wrap publish inputValid
    have source : publicDataTail (some r) (some (.tab ds)) Z_NO_FLUSH h =
        publicStrategyReturn (some r) (some (.tab ds)) Z_NO_FLUSH need_more middle := by
      rw [public_busy_no_flush_slow_source boundary.good.live.hz boundary.good.live.hs status level strategy active]
      simp only [bind_app, strategyRun]
    have returned := public_need_more_return stateM.good.live.hz stateM.good.live.hs Z_NO_FLUSH
    by_cases empty : zm.avail_out = 0
    · simp only [empty, BEq.rfl, ite_true] at returned
      have stateF := last_flush_buffered_boundary stateM (-1)
      exact ⟨used, produced, _, zm, _, nextInput, nextOrigin, nextBase, ys, source.trans returned,
        stateF, last_flush_buffers stateM.good buffersM (-1), accountM, controlsM.status.trans status, Or.inl rfl⟩
    · simp only [beq_eq_false_iff_ne.mpr empty, Bool.false_eq_true, ite_false] at returned
      exact ⟨used, produced, middle, zm, dm, nextInput, nextOrigin, nextBase, ys, source.trans returned,
        stateM, buffersM, accountM, controlsM.status.trans status, Or.inr controlsM.last_flush⟩
  · have empty : z.avail_in = 0 := by
      by_cases zero : z.avail_in = 0
      · exact zero
      · exact False.elim (active (Or.inl zero))
    have look : d.lookahead = 0 := by
      by_cases zero : d.lookahead = 0
      · exact zero
      · exact False.elim (active (Or.inr zero))
    exact ⟨0, 0, h, z, d, input, origin, base, xs, public_default_empty_data boundary.good status empty look,
      boundary, buffers, stream_accounting_zero z, status, Or.inr rfl⟩

end Zlib.Deflate.Engine.Proofs
