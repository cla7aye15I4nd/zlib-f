import ZlibF.Proof.«deflate.c.engine.no-flush-loop-control»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-final-physical»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-loop-physical»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-finish-ready-loop»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-no-flush-ready-step»
import ZlibF.Proof.«deflate.c.engine.ordinary-call-full-storage»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

theorem default_foreign_slow_no_flush_ready_loop_run_control {h after : Heap} {r : ZStreamRef} {ds owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig} {final : LoopS}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.dstate_depth owner) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (run : cwhile forever (deflate_slow_body (some (.tab ds)) Z_NO_FLUSH) {} h = .ok (final, after)) :
    final.ret = some need_more := by
  let Inv : LoopS → Heap → Prop := fun st heap =>
    ∃ currentZ currentD currentInput currentOrigin currentBase ys offset,
      StrategyBoundary heap r ds currentZ currentD currentInput currentOrigin currentBase ys config ∧
      EndFrontier heap currentD ∧ StreamBuffers heap r ∧ currentZ.next_out = .ref (.dstate_depth owner) offset ∧
      (currentZ.avail_in ≠ 0 → currentZ.next_in ≠ .null) ∧
      (st.ret = none → PublishReady currentD) ∧ st.brk = false ∧ (st.ret = none ∨ st.ret = some need_more)
  have step : ∀ st heap, Inv st heap → st.brk = false → st.ret = none →
      ∀ next middle, deflate_slow_body (some (.tab ds)) Z_NO_FLUSH st heap = .ok (next, middle) → Inv next middle := by
    intro st heap inv _brk running next middle actual
    obtain ⟨currentZ, currentD, currentInput, currentOrigin, currentBase, ys, offset,
      state, endS, buffersS, pointerS, validS, readyS, brkS, _retS⟩ := inv
    obtain ⟨used, produced, expected, other, nextZ, nextD, nextBase, nextYs, nextInput, nextOrigin,
      bodyRun, stateA, endA, buffersA, accountA, _agrees, _endpoint, _base,
      brkA, retA, readyA, _less, _reason⟩ :=
      default_foreign_slow_no_flush_ready_step state endS buffersS positive pointerS memory wrap (readyS running) validS st
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj (bodyRun.symm.trans actual))
    have pointerA : nextZ.next_out = .ref (.dstate_depth owner) (offset + produced) := by
      rw [accountA.2.2.2.2.2.1, pointerS]
      rfl
    have retNext : expected.ret = none ∨ expected.ret = some need_more := by
      rcases retA with same | returned
      · exact Or.inl (same.trans running)
      · exact Or.inr returned
    exact ⟨nextZ, nextD, nextInput, nextOrigin, nextBase, nextYs, offset + produced,
      stateA, endA, buffersA, pointerA, input_valid_accounting_output validS accountA,
      readyA,brkA.trans brkS, retNext⟩
  have initial : Inv {} h :=
    ⟨z, d, input, origin, base, xs, oo, boundary, frontier, buffers, pointer, inputValid,
      fun _ => publish,rfl,Or.inl rfl⟩
  have post := forever_run_invariant Inv (deflate_slow_body (some (.tab ds)) Z_NO_FLUSH) step initial run
  obtain ⟨_z, _d, _input, _origin, _base, _ys, _offset, _state, _end, _buffers, _pointer,
    _valid, _ready,brkA,retA⟩ := post
  have stopped := forever_run_stopped run
  rcases retA with running | returned
  · simp only [brkA, running, Option.isSome_none, Bool.or_self, Bool.false_eq_true] at stopped
  · exact returned

/-- Every prepared NO_FLUSH call, including zero capacity, retains the full physical frame. -/
theorem default_foreign_deflate_slow_no_flush_run_full_storage {h after : Heap} {r : ZStreamRef} {ds owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    {config : EngineConfig} {ret : block_state}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.dstate_depth owner) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (run : deflate_slow (some (.tab ds)) Z_NO_FLUSH h = .ok (ret, after)) :
    Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = owner) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  rw [deflate_slow_eof_tail_source] at run
  cases loop : cwhile forever (deflate_slow_body (some (.tab ds)) Z_NO_FLUSH) {} h with
  | error fault => simp only [bind_app,loop] at run;cases run
  | ok pair =>
    obtain ⟨final,middle⟩ := pair
    have returned := default_foreign_slow_no_flush_ready_loop_run_control boundary frontier buffers positive pointer memory wrap publish inputValid loop
    simp only [bind_app,loop,returned,pure_app] at run
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Except.ok.inj run)
    exact default_foreign_slow_loop_run_full_storage boundary frontier buffers positive pointer memory wrap publish inputValid loop

/-- Every actual complete FINISH strategy return, including early output exhaustion and the complete final tail, retains the full object/allocation frame. -/
theorem default_foreign_deflate_slow_finish_run_full_storage {h after : Heap} {r : ZStreamRef} {ds owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    {config : EngineConfig} {ret : block_state}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.dstate_depth owner) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (run : deflate_slow (some (.tab ds)) Z_FINISH h = .ok (ret, after))
 :
    Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = owner) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  obtain ⟨used, produced, final, loopHeap, loopZ, loopD, loopBase, loopSymbols, extended, nextOrigin,
      loop, stateL, endL, buffersL, accountL, _agreesL, _endpointL, _baseL, stopped, _stopOutput, stopInput, outputL⟩ :=
    default_foreign_slow_finish_ready_loop boundary frontier buffers positive pointer memory wrap publish inputValid
  obtain ⟨shapeL, frameL, _liveL, allocL, nextL⟩ := default_foreign_slow_loop_run_full_storage
    boundary frontier buffers positive pointer memory wrap publish inputValid loop
  rcases stopped with returned | ⟨running, broke⟩
  · have earlyRun : deflate_slow (some (.tab ds)) Z_FINISH h = .ok (need_more, loopHeap) := by
      rw [deflate_slow_eof_tail_source, bind_app, loop]
      simp only [returned]
      rfl
    have eq := (Prod.mk.inj (Except.ok.inj (earlyRun.symm.trans run))).2
    rw [← eq]
    exact ⟨shapeL, frameL, full_shape_live_change shapeL, allocL, nextL⟩
  · have eof := stopInput broke
    have readyL := outputL running
    have localState : StrategyBoundary loopHeap r ds loopZ loopD extended nextOrigin loopBase loopSymbols (engineConfig loopD) := by
      rw [stateL.configuration]
      exact stateL
    have pointerL : loopZ.next_out = .ref (.dstate_depth owner) (oo + produced) := by
      rw [accountL.2.2.2.2.2.1, pointer]
      rfl
    have levelL : loopD.level = config.level := congrArg EngineConfig.level stateL.configuration
    have memoryL : loopD.lit_bufsize = config.memory := congrArg EngineConfig.memory stateL.configuration
    have wrapL : loopD.wrap = config.wrap := congrArg EngineConfig.wrap stateL.configuration
    obtain ⟨tailProduced, tailRet, tailHeap, tailZ, tailD, tailRun, tailGood, accountT, shapeT, frameT, _liveT, allocT, nextT⟩ :=
      default_foreign_slow_eof_finish_full_storage_execution localState endL buffersL eof.1 (by rw [levelL]; exact positive)
        pointerL readyL.2.1 (by rw [memoryL]; exact memory) readyL.1 (wrapL.trans wrap)
    have wholeRun : deflate_slow (some (.tab ds)) Z_FINISH h = .ok (tailRet, tailHeap) := by
      rw [deflate_slow_eof_tail_source, bind_app, loop]
      simp only [running]
      exact tailRun
    have eq := (Prod.mk.inj (Except.ok.inj (wholeRun.symm.trans run))).2
    rw [← eq]
    have owned := ConfigFrame.owned (ds := ds) (show ConfigFrame d loopD from stateL.configuration.trans boundary.configuration.symm)
    rw [owned] at frameT
    have shape := shapeL.trans shapeT
    have frame := full_frame_trans_shape frameL frameT shapeL
    exact ⟨shape, frame, full_shape_live_change shape, allocT.trans allocL, nextT.trans nextL⟩

/-- Both complete actual ordinary strategy calls retain the full private/output frame and exact object/allocation ledgers. -/
theorem default_foreign_deflate_slow_ordinary_run_full_storage {h after : Heap} {r : ZStreamRef} {ds owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    {config : EngineConfig} {ret : block_state} {flush : Int32}
    (flag : flush = Z_NO_FLUSH ∨ flush = Z_FINISH)
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.dstate_depth owner) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (run : deflate_slow (some (.tab ds)) flush h = .ok (ret, after))
 :
    Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = owner) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  rcases flag with rfl | rfl
  · exact default_foreign_deflate_slow_no_flush_run_full_storage boundary frontier buffers positive pointer memory wrap publish inputValid run
  · exact default_foreign_deflate_slow_finish_run_full_storage boundary frontier buffers positive pointer memory wrap publish inputValid run


end Zlib.Deflate.Engine.Proofs
