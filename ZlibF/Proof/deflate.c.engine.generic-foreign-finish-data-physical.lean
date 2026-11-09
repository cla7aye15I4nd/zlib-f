import ZlibF.Proof.«deflate.c.engine.generic-foreign-finish-scalar-frame»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-trailer-physical»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-finish-buffered»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-finish-whole-counters»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-ordinary-buffer-frame»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-ordinary-physical»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-buffer-frame-adjacent»
import ZlibF.Proof.«deflate.c.engine.public-data-full-storage»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Real default BUSY FINISH dispatch, controls and trailer compose exact totals. -/
theorem public_foreign_busy_slow_finish_full_storage_execution {h : Heap} {r : ZStreamRef} {ds owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    {config : EngineConfig}
    (boundary : BufferedBoundary h r ds z d input origin base xs config)
    (buffers : StreamBuffers h r)
    (status : d.status = BUSY_STATE) (level : d.level = 6) (strategy : d.strategy = 0)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (memory : config.memory.toNat = 16384)
    (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ used produced rc after z' result,
      publicDataTail (some r) (some (.tab ds)) Z_FINISH h = .ok (rc, after) ∧
      DGood after r ds z' result ∧ StreamAccounting z z' used produced ∧
      z'.total_in = z.total_in + UInt64.ofNat used ∧ z'.total_out = z.total_out + UInt64.ofNat produced ∧
      Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = owner) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,produced⟩] := by
  have positive : 0 < config.level.toInt := by
    have eq := congrArg EngineConfig.level boundary.configuration
    change d.level = config.level at eq
    rw [← eq, level]
    decide
  obtain ⟨used, produced, ret, middle, middleZ, middleD, middleBase, ys, extended, nextOrigin,
      strategyRun, stateM, controlsM, resumeM, buffersM, accountM, _agreesM, _endpointM, _baseM, finishedM, classification⟩ :=
    default_foreign_deflate_slow_finish_buffered boundary buffers positive pointer memory wrap publish inputValid
  have effectsM := default_foreign_deflate_slow_finish_run_counter_effects (boundary.strategy publish) boundary.end_frontier buffers positive pointer memory wrap
    publish inputValid strategyRun stateM.good.live.hz accountM
  obtain ⟨shapeM, frameM, _liveM, allocM, nextM⟩ :=
    default_foreign_deflate_slow_finish_run_full_storage (boundary.strategy publish) boundary.end_frontier buffers positive pointer memory wrap publish inputValid strategyRun
  have preciseM := default_foreign_deflate_slow_finish_run_buffer_frame (boundary.strategy publish) boundary.end_frontier buffers
    positive pointer memory wrap publish inputValid strategyRun stateM.good.live.hz accountM
  have sourceRun : publicDataTail (some r) (some (.tab ds)) Z_FINISH h =
      publicStrategyReturn (some r) (some (.tab ds)) Z_FINISH ret middle := by
    rw [public_busy_finish_slow_source boundary.good.live.hz boundary.good.live.hs status level strategy]
    simp only [bind_app, strategyRun]
  have owned : DeflateOwned ds middleD = DeflateOwned ds d := ConfigFrame.owned
    (show ConfigFrame d middleD from stateM.configuration.trans boundary.configuration.symm)
  rcases classification with ⟨returned, exhausted⟩ | ⟨returned, exhausted, _empty⟩ | ⟨returned, remaining, empty⟩
  · subst ret
    have run := public_strategy_need_more stateM.good.live.hz stateM.good.live.hs exhausted
    exact ⟨used, produced, Z_OK, _, middleZ, _, sourceRun.trans run,
      last_flush_good stateM.good (-1), accountM, effectsM.1, effectsM.2,
      (full_storage_state_trans shapeM frameM allocM nextM stateM.good.live.hs (Or.inr (Or.inl (Or.inl rfl))) {middleD with last_flush:= -1}).1,
      (full_storage_state_trans shapeM frameM allocM nextM stateM.good.live.hs (Or.inr (Or.inl (Or.inl rfl))) {middleD with last_flush:= -1}).2.1,
      full_shape_live_change (shapeM.trans (shape_setD stateM.good.live.hs _)),allocM,nextM,
      foreign_finish_scalar_buffer_frame boundary.good buffers pointer stateM.good.live.hs rfl preciseM⟩
  · subst ret
    have goodS := finish_status_good stateM.good
    have buffersS := finish_status_buffers stateM.good buffersM
    have run := public_strategy_finish_started stateM.good.live.hz stateM.good.live.hs exhausted
    refine ⟨used, produced, Z_OK, _, middleZ, _, sourceRun.trans run,
      last_flush_good goodS (-1), accountM, effectsM.1, effectsM.2, ?_⟩
    obtain ⟨shapeS, frameS, _liveS, allocS, nextS⟩ := full_storage_state_trans shapeM frameM allocM nextM
      stateM.good.live.hs (Or.inr (Or.inl (Or.inl rfl))) { middleD with status := FINISH_STATE }
    have physical := full_storage_state_trans shapeS frameS allocS nextS goodS.live.hs (Or.inr (Or.inl (Or.inl rfl))) {middleD with status:=FINISH_STATE,last_flush:= -1}
    have preciseS := foreign_finish_scalar_buffer_frame boundary.good buffers pointer stateM.good.live.hs (result:={middleD with status:=FINISH_STATE}) rfl preciseM
    exact ⟨physical.1,physical.2.1,physical.2.2.1,physical.2.2.2.1,physical.2.2.2.2,
      foreign_finish_scalar_buffer_frame boundary.good buffers pointer goodS.live.hs rfl preciseS⟩
  · subst ret
    have finished := finishedM (by decide)
    have ready := resumeM remaining
    have goodS := finish_status_good stateM.good
    have buffersS := finish_status_buffers stateM.good buffersM
    obtain ⟨pb, buf, trees, _ledger, _balance⟩ := stateM.symbols
    have treesS := finish_status_trees trees
    have pointerM : middleZ.next_out = .ref (.dstate_depth owner) (oo + produced) := by
      rw [accountM.2.2.2.2.2.1, pointer]
      rfl
    have wrapM : middleD.wrap = 1 := by
      have eq := congrArg EngineConfig.wrap stateM.configuration
      exact eq.trans wrap
    obtain ⟨trailerProduced,after,z',result,_written,_remaining,trailerRun,goodA,_buffersA,accountA,_sizes,_amount,_left,
      _wrapA,_bitsA,_fields,_bytes,_pendingA,_wire,_adlerA,inputA,outputA,_allocA,_nextA,preciseT,_tail⟩ :=
      foreign_zlib_trailer_publish_encoding goodS treesS buffersS pointerM wrapM ready.1 ready.2.1 finished.2
    obtain ⟨shapeS, frameS, _liveS, allocS, nextS⟩ := full_storage_state_trans shapeM frameM allocM nextM
      stateM.good.live.hs (Or.inr (Or.inl (Or.inl rfl))) { middleD with status := FINISH_STATE }
    obtain ⟨shapeT, frameT, _liveT, allocT, nextT⟩ := foreign_zlib_trailer_run_full_storage goodS treesS buffersS
      pointerM wrapM ready.1 ready.2.1 finished.2 trailerRun
    have ownedS : DeflateOwned ds { middleD with status := FINISH_STATE } = DeflateOwned ds d := by
      change DeflateOwned ds middleD = DeflateOwned ds d
      exact owned
    rw [ownedS] at frameT
    have shape := shapeS.trans shapeT
    have storage : Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = owner) ∧
        LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := ⟨shape, full_frame_trans_shape frameS frameT shapeS, full_shape_live_change shape,
      allocT.trans allocS, nextT.trans nextS⟩
    have preciseS := foreign_finish_scalar_buffer_frame boundary.good buffers pointer stateM.good.live.hs (result:={middleD with status:=FINISH_STATE}) rfl preciseM
    rw [ownedS] at preciseT
    have preciseAll : BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,produced+trailerProduced⟩] := by
      obtain ⟨foreign,get,_⟩ := caller_foreign_output boundary.good buffers pointer
      rw [pointer] at preciseS ⊢
      rw [pointerM] at preciseT
      exact foreign_buffer_frame_adjacent preciseS preciseT shapeS shapeT boundary.good.uniq get (caller_foreign_owner_outside boundary.good buffers pointer)
    have run := public_strategy_finish_done stateM.good.live.hz stateM.good.live.hs
    refine ⟨used, produced + trailerProduced, if result.pending != 0 then Z_OK else Z_STREAM_END,
      after, z', result, sourceRun.trans (run.trans trailerRun), goodA, ?_, inputA.trans effectsM.1, ?_, storage.1,storage.2.1,storage.2.2.1,storage.2.2.2.1,storage.2.2.2.2,preciseAll⟩
    · simpa only [Nat.add_zero] using stream_accounting_trans accountM accountA
    · rw [outputA, effectsM.2, UInt64.ofNat_add, UInt64.add_assoc]


end Zlib.Deflate.Engine.Proofs
