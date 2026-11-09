import ZlibF.Proof.«compress.c.prefix-completion»
import ZlibF.Proof.«deflate.c.engine.public-finish-phase»
import ZlibF.Proof.«deflate.c.engine.public-finish-progress»
import ZlibF.Proof.«deflate.c.engine.header-finish-boundary»
import ZlibF.Proof.«deflate.c.engine.header-buffered»

/-! # Retain the actual finish-input fact through the first complete header -/
namespace ZlibF.Spec.Public.Proofs.CompressFinishInput
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false
set_option maxRecDepth 100000

private theorem input_post_identify {h tested after : Heap} {r : ZStreamRef} {ds : Nat}
    {actualZ expectedZ : ZStream} {actualD expectedD : DeflateState} {rc expectedRc : Int32} {call : M Int32}
    (actual : call h = .ok (rc,after)) (expected : call h = .ok (expectedRc,tested))
    (getA : r.get after = some actualZ) (getD : after.dstates ds = some actualD)
    (getE : r.get tested = some expectedZ) (getED : tested.dstates ds = some expectedD)
    (post : expectedD.status = FINISH_STATE → expectedZ.avail_in = 0) :
    actualD.status = FINISH_STATE → actualZ.avail_in = 0 := by
  have heaps := (Prod.mk.inj (Except.ok.inj (expected.symm.trans actual))).2
  subst tested
  have streams : expectedZ = actualZ := Option.some.inj (getE.symm.trans getA)
  have states : expectedD = actualD := Option.some.inj (getED.symm.trans getD)
  simpa only [streams,states] using post

/-- The prepared data-tail result has no unconsumed input once its state
enters FINISH_STATE. This includes zero output after a two-byte header.
The real strategy classification and actual trailer accounting establish
this fact; the public phase interface alone omitted it. -/
theorem data_tail_finish_input {h after : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z za : ZStream} {d da : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig} {rc : Int32}
    (boundary : BufferedBoundary h r ds z d input origin base xs config) (buffers : StreamBuffers h r)
    (status : d.status = BUSY_STATE) (level : d.level = 6) (strategy : d.strategy = 0)
    (pointer : z.next_out = .ref (.blk ob) oo) (memory : config.memory.toNat = 16384)
    (wrap : config.wrap = 1) (publish : PublishReady d) (valid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (actual : publicDataTail (some r) (some (.tab ds)) Z_FINISH h = .ok (rc,after))
    (getA : r.get after = some za) (getD : after.dstates ds = some da) :
    da.status = FINISH_STATE → za.avail_in = 0 := by
  have positive : 0 < config.level.toInt := by
    have eq := congrArg EngineConfig.level boundary.configuration
    change d.level = config.level at eq
    rw [←eq,level]
    decide
  obtain ⟨used,produced,ret,middle,middleZ,middleD,middleBase,ys,extended,nextOrigin,
    strategyRun,stateM,controlsM,resumeM,buffersM,accountM,_agreesM,_endpointM,_baseM,finishing,classification⟩ :=
    deflate_slow_finish_buffered boundary buffers positive pointer memory wrap publish valid
  have source : publicDataTail (some r) (some (.tab ds)) Z_FINISH h =
      publicStrategyReturn (some r) (some (.tab ds)) Z_FINISH ret middle := by
    rw [public_busy_finish_slow_source boundary.good.live.hz boundary.good.live.hs status level strategy]
    simp only [bind_app,strategyRun]
  rcases classification with ⟨returned,exhausted⟩ | ⟨returned,exhausted,empty⟩ | ⟨returned,remaining,empty⟩
  · subst ret
    have run := public_strategy_need_more stateM.good.live.hz stateM.good.live.hs exhausted
    have stateF := last_flush_buffered_boundary stateM (-1)
    apply input_post_identify actual (source.trans run) getA getD stateF.good.live.hz stateF.good.live.hs
    intro finished
    have statusF : ({middleD with last_flush := (-1 : Int32)} : DeflateState).status = BUSY_STATE := controlsM.status.trans status
    exact False.elim ((by decide : BUSY_STATE ≠ FINISH_STATE) (statusF.symm.trans finished))
  · subst ret
    have goodS := finish_status_good stateM.good
    have stateS := buffered_finish_status stateM
    have stateF := last_flush_buffered_boundary stateS (-1)
    have run := public_strategy_finish_started stateM.good.live.hz stateM.good.live.hs exhausted
    exact input_post_identify actual (source.trans run) getA getD stateF.good.live.hz stateF.good.live.hs (fun _ => empty)
  · subst ret
    have finished := finishing (by decide)
    have ready := resumeM remaining
    have goodS := finish_status_good stateM.good
    have buffersS := finish_status_buffers stateM.good buffersM
    obtain ⟨pb,buf,trees,_ledger,_balance⟩ := stateM.symbols
    have treesS := finish_status_trees trees
    have pointerM : middleZ.next_out = .ref (.blk ob) (oo+produced) := by
      rw [accountM.2.2.2.2.2.1,pointer]
      rfl
    have wrapM : middleD.wrap = 1 := (congrArg EngineConfig.wrap stateM.configuration).trans wrap
    obtain ⟨trailerProduced,tested,ze,de,_written,_pendingBits,trailerRun,goodE,_buffersE,accountE,
      _sizes,_storage,_amount,_left,_wrap,_bits,_fields,_bytes,_pending,_trailerBits⟩ :=
      zlib_trailer_publish goodS treesS buffersS pointerM wrapM ready.1 ready.2.1 finished.2
    have run := public_strategy_finish_done stateM.good.live.hz stateM.good.live.hs
    apply input_post_identify actual (source.trans (run.trans trailerRun)) getA getD goodE.live.hz goodE.live.hs
    intro _finished
    have count := accountE.2.2.1
    rw [empty] at count
    apply UInt32.toNat_inj.mp
    simpa only [Nat.add_zero,UInt32.toNat_zero] using count

/-- A complete first header retains the strategy's FINISH input fact,
including exactly two bytes of output and zero remaining data-tail room. -/
theorem first_finish_fits_input {h after : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z za : ZStream} {d da : DeflateState} {input : Nat → UInt8} {config : EngineConfig} {rc : Int32}
    (initial : EngineStart h r ds z d) (level : d.level = 6)
    (boundary : StrategyBoundary h r ds z d input origin base [] config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (room : 2 ≤ z.avail_out.toNat)
    (memory : config.memory.toNat = 16384) (valid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (actual : deflate (some r) Z_FINISH h = .ok (rc,after))
    (getA : r.get after = some za) (getD : after.dstates ds = some da) :
    da.status = FINISH_STATE → za.avail_in = 0 := by
  obtain ⟨output,outGet,outRw,outBound,outside⟩ := caller_raw_output initial.good buffers pointer
  obtain ⟨oldD,pb,buf,trees⟩ := initial.good.trees
  have sameD : oldD = d := Option.some.inj (trees.base.dstate.symm.trans initial.good.live.hs)
  subst oldD
  have separate : ob ≠ pb := by intro same;subst ob;exact outside (Or.inr (Or.inr (Or.inr (Or.inr trees.base.pbuf))))
  have pendingRoom : 2 ≤ buf.size := by have size := trees.base.size;have lo := trees.base.lit_lo;omega
  have first := public_default_finish_header_complete initial level trees.base.pbuf trees.base.bytes pendingRoom trees.base.rw
    pointer outGet outRw separate outBound room valid
  have publish : PublishReady d := ⟨initial.pending,initial.pendingOut,by rw [initial.bits];decide⟩
  obtain ⟨stateH,endH,publishH⟩ := header_finish_strategy_boundary boundary frontier publish trees.base.pbuf trees.base.bytes outGet outside
  have buffersH := last_flush_buffers
    (header_complete_good (oo := oo) initial.good trees.base.bytes outGet separate)
    (header_complete_buffers initial.good buffers trees.base.bytes outGet separate pointer room) Z_FINISH
  have wrapConfig : config.wrap = 1 := (congrArg EngineConfig.wrap boundary.configuration).symm.trans initial.wrap
  have pointerH : (headerCompleteStream z ob oo).next_out = .ref (.blk ob) (oo+2) := rfl
  have bufferedH := stateH.buffered endH (fun _ => publishH.2.1)
  have dataRun := first.symm.trans actual
  exact data_tail_finish_input bufferedH buffersH rfl level initial.strategy pointerH memory wrapConfig publishH valid dataRun getA getD

/-- Both first-header capacities preserve FINISH_STATE => avail_in zero:
one byte leaves a BUSY split header; two or more follow the actual data tail. -/
theorem first_finish_input {h after : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z za : ZStream} {d da : DeflateState} {input : Nat → UInt8} {config : EngineConfig} {rc : Int32}
    (initial : EngineStart h r ds z d) (level : d.level = 6)
    (boundary : BufferedBoundary h r ds z d input origin base [] config) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (output : 0 < z.avail_out.toNat)
    (memory : config.memory.toNat = 16384) (valid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (actual : deflate (some r) Z_FINISH h = .ok (rc,after))
    (getA : r.get after = some za) (getD : after.dstates ds = some da) :
    da.status = FINISH_STATE → za.avail_in = 0 := by
  by_cases one : z.avail_out.toNat = 1
  · have oneWord : z.avail_out = 1 := UInt32.toNat_inj.mp one
    obtain ⟨tested,ze,de,run,stateE,_buffers,_account,_out,_pending,statusE,_last⟩ :=
      first_finish_one_buffered initial level boundary buffers pointer oneWord valid
    apply input_post_identify actual run getA getD stateE.good.live.hz stateE.good.live.hs
    intro finished
    exact False.elim ((by decide : BUSY_STATE ≠ FINISH_STATE) (statusE.symm.trans finished))
  · have publish : PublishReady d := ⟨initial.pending,initial.pendingOut,boundary.bits⟩
    exact first_finish_fits_input initial level (boundary.strategy publish) boundary.end_frontier buffers pointer
      (by omega) memory valid actual getA getD

/-- The strong ordinary-call input protocol is attached to the same
actual run and returned stream/state. All output capacities are included;
zero room uses the real clean refusal, positive room uses proved dispatch. -/
theorem ordinary_run_finish_input {h after : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z za : ZStream} {d da : DeflateState} {config : EngineConfig} {flush rc : Int32}
    (boundary : DefaultFinishBoundary h r ds z d config) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (valid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (ordinary : flush = Z_NO_FLUSH ∨ flush = Z_FINISH)
    (nonempty : flush = Z_NO_FLUSH → z.avail_in ≠ 0)
    (finishFlag : d.status = FINISH_STATE → flush = Z_FINISH)
    (accepted : d.status = FINISH_STATE → z.avail_in = 0)
    (actual : deflate (some r) flush h = .ok (rc,after))
    (getA : r.get after = some za) (getD : after.dstates ds = some da) :
    da.status = FINISH_STATE → za.avail_in = 0 := by
  by_cases zero : z.avail_out = 0
  · have lo : 0 ≤ flush.toInt := by rcases ordinary with eq | eq <;>rw [eq] <;>decide
    have hi : flush.toInt ≤ Z_BLOCK.toInt := by rcases ordinary with eq | eq <;>rw [eq] <;>decide
    have source := public_zero_output_refusal boundary.good flush lo hi
      (by rw [pointer];intro bad;cases bad) valid finishFlag zero
    obtain ⟨message,run,stateE,_buffers,_account⟩ := public_entry_refusal_protocol flush Z_BUF_ERROR boundary buffers source
    exact input_post_identify actual run getA getD stateE.good.live.hz stateE.good.live.hs accepted
  · have positive : 0 < z.avail_out.toNat := by
      have nonzero : z.avail_out.toNat ≠ 0 := fun e => zero (UInt32.toNat_inj.mp e)
      omega
    rcases ordinary with noFlush | finish
    · subst flush
      have unfinished : d.status ≠ FINISH_STATE := by intro status;exact (by decide : Z_NO_FLUSH ≠ Z_FINISH) (finishFlag status)
      obtain ⟨used,produced,tested,ze,de,run,stateE,_buffers,_account,busy⟩ :=
        boundary.no_flush buffers pointer positive valid (nonempty rfl) unfinished
      apply input_post_identify actual run getA getD stateE.good.live.hz stateE.good.live.hs
      intro finished
      exact False.elim ((by decide : BUSY_STATE ≠ FINISH_STATE) (busy.symm.trans finished))
    · subst flush
      by_cases initial : d.status = INIT_STATE
      · obtain ⟨input,origin,base,start,state⟩ : ∃input origin base,
          EngineStart h r ds z d ∧ BufferedBoundary h r ds z d input origin base [] config := by
          rcases boundary.phase with starting | ⟨input,origin,base,xs,state,busy⟩ | finishing
          · exact starting
          · exact False.elim ((by decide : BUSY_STATE ≠ INIT_STATE) (busy.symm.trans initial))
          · exact False.elim ((by decide : FINISH_STATE ≠ INIT_STATE) (finishing.status.symm.trans initial))
        have level : d.level = 6 := (congrArg EngineConfig.level state.configuration).trans boundary.configuration.level
        exact first_finish_input start level state buffers pointer positive boundary.configuration.memory valid actual getA getD
      · obtain ⟨used,produced,code,tested,ze,de,run,stateE,_buffers,_account,_allowed,_progress,empty,_started⟩ :=
          boundary.finish_progress buffers pointer positive valid accepted initial
        exact input_post_identify actual run getA getD stateE.good.live.hz stateE.good.live.hs empty

end ZlibF.Spec.Public.Proofs.CompressFinishInput
