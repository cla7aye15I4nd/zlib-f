import ZlibF.Proof.«deflate.c.engine.generic-foreign-no-flush-buffered-ready»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-finish-scalar-frame»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-nonfinish-return-physical»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-no-flush-whole-counters»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-ordinary-buffer-frame»
import ZlibF.Proof.«deflate.c.engine.generic-output-append»
import ZlibF.Proof.«deflate.c.engine.public-data-output-interval»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The real BUSY NO_FLUSH data tail preserves its exact caller interval, including idle calls and exhausted prepared output. -/
theorem public_foreign_busy_no_flush_physical_execution {h : Heap} {r : ZStreamRef} {ds owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : BufferedBoundary h r ds z d input origin base xs config) (buffers : StreamBuffers h r)
    (status : d.status = BUSY_STATE) (level : d.level = 6) (strategy : d.strategy = 0)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (memory : config.memory.toNat = 16384)
    (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ used produced after z' result,
      publicDataTail (some r) (some (.tab ds)) Z_NO_FLUSH h = .ok (Z_OK, after) ∧
      DGood after r ds z' result ∧ StreamAccounting z z' used produced ∧
      z'.total_in = z.total_in + UInt64.ofNat used ∧ z'.total_out = z.total_out + UInt64.ofNat produced ∧
      Shape h after ∧ Frame h after (fun b=>StreamRoot r b ∨ DeflateOwned ds d b ∨ b=owner) ∧
      LiveChange h after (fun _=>False) (fun _=>False) ∧ after.nalloc=h.nalloc ∧ after.nextBlk=h.nextBlk ∧
      BufferFrame h after (fun b=>StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,produced⟩] := by
  by_cases active : z.avail_in ≠ 0 ∨ d.lookahead ≠ 0
  · have positive : 0 < config.level.toInt := by
      have eq := congrArg EngineConfig.level boundary.configuration
      change d.level = config.level at eq
      rw [← eq, level]
      decide
    obtain ⟨used, produced, middle, zm, dm, nextBase, ys, nextInput, nextOrigin, strategyRun,
        stateM, controlsM, buffersM, accountM, _agrees, _endpoint, _base, _stopped, _consumed⟩ :=
      default_foreign_deflate_slow_no_flush_buffered_ready boundary buffers positive pointer memory wrap publish inputValid
    have effectsM := default_foreign_deflate_slow_no_flush_run_counter_effects (boundary.strategy publish) boundary.end_frontier
      buffers positive pointer memory wrap publish inputValid strategyRun stateM.good.live.hz accountM
    have precise:=default_foreign_deflate_slow_no_flush_run_buffer_frame (boundary.strategy publish) boundary.end_frontier
      buffers positive pointer memory wrap publish inputValid strategyRun stateM.good.live.hz accountM
    obtain ⟨shapeM,frameM,_liveM,allocM,nextM⟩ := default_foreign_deflate_slow_no_flush_run_full_storage
      (boundary.strategy publish) boundary.end_frontier buffers positive pointer memory wrap publish inputValid strategyRun
    have source : publicDataTail (some r) (some (.tab ds)) Z_NO_FLUSH h =
        publicStrategyReturn (some r) (some (.tab ds)) Z_NO_FLUSH need_more middle := by
      rw [public_busy_no_flush_slow_source boundary.good.live.hz boundary.good.live.hs status level strategy active]
      simp only [bind_app, strategyRun]
    have returned := public_need_more_return stateM.good.live.hz stateM.good.live.hs Z_NO_FLUSH
    by_cases empty : zm.avail_out = 0
    · simp only [empty, BEq.rfl, ite_true] at returned
      have stateF := last_flush_buffered_boundary stateM (-1)
      refine ⟨used, produced, _, zm, _, source.trans returned, stateF.good, accountM, effectsM.1, effectsM.2, ?_⟩
      have storage := full_storage_state_trans shapeM frameM allocM nextM stateM.good.live.hs
        (Or.inr (Or.inl (Or.inl rfl))) {dm with last_flush:= -1}
      exact ⟨storage.1,storage.2.1,storage.2.2.1,storage.2.2.2.1,storage.2.2.2.2,
        foreign_finish_scalar_buffer_frame boundary.good buffers pointer stateM.good.live.hs rfl precise⟩
    · simp only [beq_eq_false_iff_ne.mpr empty, Bool.false_eq_true, ite_false] at returned
      exact ⟨used, produced, middle, zm, dm, source.trans returned, stateM.good, accountM, effectsM.1,effectsM.2,shapeM,frameM,full_shape_live_change shapeM,allocM,nextM,precise⟩
  · have empty : z.avail_in = 0 := by
      by_cases zero : z.avail_in = 0
      · exact zero
      · exact False.elim (active (Or.inl zero))
    have look : d.lookahead = 0 := by
      by_cases zero : d.lookahead = 0
      · exact zero
      · exact False.elim (active (Or.inr zero))
    exact ⟨0, 0, h, z, d, public_default_empty_data boundary.good status empty look,
      boundary.good, stream_accounting_zero z, by simp,by simp,Shape.refl h,(full_storage_refl h _).2.1,
      full_shape_live_change (Shape.refl h),rfl,rfl,
      marker_private_buffer_frame boundary.good buffers pointer (full_storage_refl h _).2.1 (Shape.refl h)⟩


end Zlib.Deflate.Engine.Proofs
