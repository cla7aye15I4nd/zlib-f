import ZlibF.Proof.«deflate.c.engine.generic-foreign-finish-raw-phase»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-finish-buffered»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-zlib-trailer-valid»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-finishing-tail-phase»
import ZlibF.Proof.«deflate.c.engine.generic-output-append»
import ZlibF.Proof.«deflate.c.engine.public-finish-data-representation»

/-! # Actual FINISH data establishes the correlated working or completed representation -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The complete actual BUSY FINISH data path retains raw or wrapped
encoding for exactly the consumed original caller bytes. Need-more,
final-block output exhaustion and actual trailer publication share the
same execution and observations. A STREAM_END result gives independent
zlib validity for all previously published raw bytes and this call's output.
Prepared dispatch includes zero output capacity. Public entry and previous
pending/header phases remain separate composition obligations. -/
theorem public_foreign_busy_finish_data_completed_encoding {h : Heap} {r : ZStreamRef} {ds owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    {published actualInput : List UInt8}
    (boundary : BufferedBoundary h r ds z d input origin base xs config) (buffers : StreamBuffers h r)
    (status : d.status = BUSY_STATE) (level : d.level = 6) (strategy : d.strategy = 0)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (memory : config.memory.toNat = 16384)
    (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (snapshot : Bytes h z.next_in z.avail_in.toNat actualInput)
    (checksum : z.adler = (ZlibF.Spec.adler32 (inputPrefix input (origin + fillEnd d))).toUInt64)
    (encoding : RawPrefix h d input base published) :
    ∃ used rc after z' result written accepted,
      accepted = inputPrefix input (origin + fillEnd d) ++ actualInput.take used ∧
      publicDataTail (some r) (some (.tab ds)) Z_FINISH h = .ok (rc, after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' used written.length ∧
      Bytes after z.next_out written.length written ∧
      z'.adler = (ZlibF.Spec.adler32 accepted).toUInt64 ∧
      ((∃ nextInput nextOrigin nextBase ys,
          BufferedBoundary after r ds z' result nextInput nextOrigin nextBase ys config ∧ result.status = BUSY_STATE ∧
          RawPrefix after result nextInput nextBase (published ++ written) ∧
          inputPrefix nextInput (nextOrigin + fillEnd result) = accepted) ∨
       (FinishingPhase result config ∧ FinishedEncoding after result accepted (published ++ written))) ∧
      (rc = Z_STREAM_END → ZlibF.Spec.Zlib.Valid accepted ([120,156] ++ published ++ written)) := by
  have positive : 0 < config.level.toInt := by
    have eq := congrArg EngineConfig.level boundary.configuration
    change d.level = config.level at eq
    rw [← eq, level]
    decide
  obtain ⟨used, ret, middle, middleZ, middleD, extended, nextOrigin, nextBase, ys, rawWritten,
      strategyRun, stateM, buffersM, accountM, bytesM, _agreesM, inputLedgerM, checksumM, meaningM⟩ :=
    default_foreign_deflate_slow_finish_ready_raw_input_phase (boundary.strategy publish) boundary.end_frontier buffers
      positive pointer memory wrap publish inputValid snapshot checksum encoding
  obtain ⟨_controlUsed, _controlProduced, controlRet, controlHeap, controlZ, controlD, _controlBase,
      _controlYs, _controlInput, _controlOrigin, controlRun, controlState, controlsM, resumeM,
      _controlBuffers, _controlAccount, _controlAgrees, _controlEndpoint, _controlBaseLe, finishedM, classification⟩ :=
    default_foreign_deflate_slow_finish_buffered boundary buffers positive pointer memory wrap publish inputValid
  obtain ⟨retEq, heapEq⟩ := Prod.mk.inj (Except.ok.inj (controlRun.symm.trans strategyRun))
  subst controlRet controlHeap
  have streamEq : controlZ = middleZ := Option.some.inj (controlState.good.live.hz.symm.trans stateM.good.live.hz)
  have stateEq : controlD = middleD := Option.some.inj (controlState.good.live.hs.symm.trans stateM.good.live.hs)
  subst controlZ controlD
  let accepted := inputPrefix input (origin + fillEnd d) ++ actualInput.take used
  have sourceRun : publicDataTail (some r) (some (.tab ds)) Z_FINISH h =
      publicStrategyReturn (some r) (some (.tab ds)) Z_FINISH ret middle := by
    rw [public_busy_finish_slow_source boundary.good.live.hz boundary.good.live.hs status level strategy]
    simp only [bind_app, strategyRun]
  have noEnd : Z_OK = Z_STREAM_END → False := fun impossible => (by decide : Z_OK ≠ Z_STREAM_END) impossible
  rcases classification with ⟨returned, exhausted⟩ | ⟨returned, exhausted, _empty⟩ | ⟨returned, remaining, _empty⟩
  · subst ret
    have working : StrategyBoundary middle r ds middleZ middleD extended nextOrigin nextBase ys config ∧
        EndFrontier middle middleD ∧ nextOrigin + fillEnd middleD = origin + fillEnd d + used ∧
        RawPrefix middle middleD extended nextBase (published ++ rawWritten) := by
      rcases meaningM with ⟨_ret, strategyM, frontierM, endpointM, prefixM⟩ | ⟨impossible, _rest⟩
      · exact ⟨strategyM, frontierM, endpointM, prefixM⟩
      · rcases impossible with impossible | impossible <;> cases impossible
    obtain ⟨strategyM, frontierM, endpointM, prefixM⟩ := working
    have bufferedM := strategyM.buffered frontierM controlsM.empty_cursor
    have stateF := last_flush_buffered_boundary bufferedM (-1)
    have run := public_strategy_need_more stateM.good.live.hz stateM.good.live.hs exhausted
    have bytesF := caller_bytes_setD_depth (result := { middleD with last_flush := -1 }) stateM.good.live.hs rfl bytesM
    refine ⟨used, Z_OK, _, middleZ, _, rawWritten, accepted, rfl, sourceRun.trans run,
      stateF.good, last_flush_buffers bufferedM.good buffersM (-1), accountM, bytesF, checksumM,
      Or.inl ⟨extended, nextOrigin, nextBase, ys, stateF, controlsM.status.trans status, prefixM.last_flush bufferedM.good (-1), ?_⟩, ?_⟩
    · change inputPrefix extended (nextOrigin + fillEnd middleD) = accepted
      rw [endpointM]
      exact inputLedgerM
    · intro impossible
      exact False.elim (noEnd impossible)
  · subst ret
    obtain ⟨tailBytes, tailData, rawMeaning⟩ : ∃ tailBytes,
        Bytes middle middleD.pending_out middleD.pending.toNat tailBytes ∧
        ZlibF.Spec.Deflate.Valid accepted (published ++ rawWritten ++ tailBytes) := by
      rcases meaningM with ⟨impossible, _rest⟩ | ⟨_ret, tailBytes, tailData, _bits, rawMeaning⟩
      · cases impossible
      · exact ⟨tailBytes, tailData, rawMeaning⟩
    have finished := finishedM (by decide)
    have stateS := buffered_finish_status controlState
    have stateF := last_flush_buffered_boundary stateS (-1)
    have buffersS := finish_status_buffers stateM.good buffersM
    have bytesS := caller_bytes_setD_depth (result := { middleD with status := FINISH_STATE }) stateM.good.live.hs rfl bytesM
    have tailS := caller_bytes_setD_depth (result := { middleD with status := FINISH_STATE }) stateM.good.live.hs rfl tailData
    have bytesF := caller_bytes_setD_depth (result := { middleD with status := FINISH_STATE, last_flush := -1 }) stateS.good.live.hs rfl bytesS
    have tailF := caller_bytes_setD_depth (result := { middleD with status := FINISH_STATE, last_flush := -1 }) stateS.good.live.hs rfl tailS
    have wrapM : middleD.wrap = 1 := (congrArg EngineConfig.wrap controlState.configuration).trans wrap
    have phaseF := finishing_phase_of_buffered stateF rfl finished.1 finished.2 wrapM
    have run := public_strategy_finish_started stateM.good.live.hz stateM.good.live.hs exhausted
    refine ⟨used, Z_OK, _, middleZ, _, rawWritten, accepted, rfl, sourceRun.trans run,
      stateF.good, last_flush_buffers stateS.good buffersS (-1), accountM, bytesF, checksumM,
      Or.inr ⟨phaseF, ⟨finished.2, tailBytes, tailF, Or.inl ⟨wrapM, rawMeaning⟩⟩⟩, ?_⟩
    intro impossible
    exact False.elim (noEnd impossible)
  · subst ret
    obtain ⟨tailBytes, tailData, rawMeaning⟩ : ∃ tailBytes,
        Bytes middle middleD.pending_out middleD.pending.toNat tailBytes ∧
        ZlibF.Spec.Deflate.Valid accepted (published ++ rawWritten ++ tailBytes) := by
      rcases meaningM with ⟨impossible, _rest⟩ | ⟨_ret, tailBytes, tailData, _bits, rawMeaning⟩
      · cases impossible
      · exact ⟨tailBytes, tailData, rawMeaning⟩
    have finished := finishedM (by decide)
    have ready := resumeM remaining
    have tailLength := caller_bytes_length tailData
    have tailNil : tailBytes = [] := List.eq_nil_iff_length_eq_zero.mpr (by simpa only [ready.1, UInt64.toNat_zero] using tailLength)
    have rawValid : ZlibF.Spec.Deflate.Valid accepted (published ++ rawWritten) := by
      simpa only [tailNil, List.append_nil] using rawMeaning
    have goodS := finish_status_good stateM.good
    have buffersS := finish_status_buffers stateM.good buffersM
    obtain ⟨pb, buf, trees, _ledger, _balance⟩ := controlState.symbols
    have treesS := finish_status_trees trees
    have pointerM : middleZ.next_out = .ref (.dstate_depth owner) (oo + rawWritten.length) := by
      rw [accountM.2.2.2.2.2.1, pointer]
      rfl
    have wrapM : middleD.wrap = 1 := (congrArg EngineConfig.wrap controlState.configuration).trans wrap
    obtain ⟨trailerProduced, after, z', result, trailerWritten, trailerTail, trailerRun, goodA, buffersA,
        accountA, wrapA, bitsA, bytesA, pendingA, _trailerEq, checksumA, _allocA, _nextA, frameA, validA, drainedA⟩ :=
      foreign_zlib_trailer_publish_valid goodS treesS buffersS pointerM wrapM ready.1 ready.2.1 finished.2 checksumM rawValid
    have stateS := buffered_finish_status controlState
    have phaseS := finishing_phase_of_buffered stateS rfl finished.1 finished.2 wrapM
    have headerS := public_finishing_header_source goodS phaseS _empty
    obtain ⟨_phaseProduced, _phaseRc, phaseHeap, phaseZ, phaseD, phaseRun, phaseGood, _phaseBuffers,
        _phaseAccount, _phaseAllowed, phaseA, _phaseLast, _phaseEmpty, _phaseEnded⟩ :=
      public_foreign_finishing_tail_phase goodS buffersS phaseS pointerM _empty ready.1
    have phaseHeapEq : phaseHeap = after := (Prod.mk.inj (Except.ok.inj (phaseRun.symm.trans (headerS.trans trailerRun)))).2
    rw [phaseHeapEq] at phaseGood
    have phaseStateEq : phaseD = result := Option.some.inj (phaseGood.live.hs.symm.trans goodA.live.hs)
    rw [phaseStateEq] at phaseA
    have effect : ByteOutputInterval (setD middle ds { middleD with status := FINISH_STATE }) after
        (.dstate_depth owner) (oo + rawWritten.length) trailerProduced := by
      rw [pointerM] at frameA
      exact ByteOutputInterval.of_buffer_frame frameA
    have bytesS := caller_bytes_setD_depth (result := { middleD with status := FINISH_STATE }) stateM.good.live.hs rfl bytesM
    have earlier : Bytes after (.ref (.dstate_depth owner) oo) rawWritten.length rawWritten := by
      rw [pointer] at bytesS
      exact effect.keep_published_bytes bytesS
    have current : Bytes after (.ref (.dstate_depth owner) (oo + rawWritten.length)) trailerProduced trailerWritten := by
      rw [pointerM] at bytesA
      exact bytesA
    have combinedBytes := generic_published_bytes_append earlier current
    have trailerLength := caller_bytes_length bytesA
    have account : StreamAccounting z z' used (rawWritten ++ trailerWritten).length := by
      simpa only [List.length_append, trailerLength, Nat.add_zero] using stream_accounting_trans accountM accountA
    have run := public_strategy_finish_done stateM.good.live.hz stateM.good.live.hs
    refine ⟨used, if result.pending != 0 then Z_OK else Z_STREAM_END, after, z', result,
      rawWritten ++ trailerWritten, accepted, rfl, sourceRun.trans (run.trans trailerRun), goodA, buffersA,
      account, ?_, checksumA, Or.inr ⟨phaseA, ⟨bitsA, trailerTail, pendingA, Or.inr ⟨wrapA, ?_⟩⟩⟩, ?_⟩
    · simpa only [List.length_append, trailerLength, pointer] using combinedBytes
    · simpa only [List.append_assoc, show levelHeaderPrefix (6 : Int32) = [120,156] from by decide, show middleD.level = 6 from (congrArg EngineConfig.level controlState.configuration).trans ((congrArg EngineConfig.level boundary.configuration).symm.trans level)] using validA
    · intro ended
      have empty : result.pending = 0 := by
        by_cases empty : result.pending = 0
        · exact empty
        · simp [empty, show Z_OK ≠ Z_STREAM_END from by decide] at ended
      simpa only [List.append_assoc, show levelHeaderPrefix (6 : Int32) = [120,156] from by decide, show middleD.level = 6 from (congrArg EngineConfig.level controlState.configuration).trans ((congrArg EngineConfig.level boundary.configuration).symm.trans level)] using drainedA empty

end Zlib.Deflate.Engine.Proofs
