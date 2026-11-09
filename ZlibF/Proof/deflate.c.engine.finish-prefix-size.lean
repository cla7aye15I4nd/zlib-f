import ZlibF.Proof.«deflate.c.engine.finish-counted-size»

/-! # Exact counted working prefix of an actual FINISH need_more return -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false
set_option maxRecDepth 10000

/-- `local block_state deflate_slow(deflate_state *s, int flush)`.
A real FINISH return of need_more comes directly from its complete loop
on this same returned heap. The actual EOF tail returns only finish_started
or finish_done, and so cannot supply this result. -/
theorem deflate_slow_finish_need_more_loop_source {h after : Heap} {r : ZStreamRef}
    {ds ob oo origin base : Nat} {z : ZStream} {d : DeflateState}
    {input : Nat → UInt8} {xs : List Symbol} {config : EngineConfig}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1)
    (publish : PublishReady d) (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (observed : deflate_slow (some (.tab ds)) Z_FINISH h = .ok (need_more, after)) :
    ∃ final,
      cwhile forever (deflate_slow_body (some (.tab ds)) Z_FINISH) {} h = .ok (final, after) ∧
      final.ret = some need_more := by
  obtain ⟨used, produced, final, middle, zm, dm, nextBase, ys, extended, nextOrigin,
      loop, stateL, endL, buffersL, accountL, _agrees, _endpoint, _baseLe,
      stopped, _stopOutput, stopInput, readyL⟩ :=
    slow_finish_ready_loop boundary frontier buffers positive pointer memory wrap publish inputValid
  rcases stopped with returned | ⟨running, broke⟩
  · have run : deflate_slow (some (.tab ds)) Z_FINISH h = .ok (need_more, middle) := by
      rw [deflate_slow_eof_tail_source, bind_app, loop]
      simp only [returned]
      rfl
    have heaps : middle = after := (Prod.mk.inj (Except.ok.inj (run.symm.trans observed))).2
    exact ⟨final, by rw [← heaps]; exact loop, returned⟩
  · have eof := stopInput broke
    have localState : StrategyBoundary middle r ds zm dm extended nextOrigin nextBase ys (engineConfig dm) := by
      rw [stateL.configuration]
      exact stateL
    have pointerL : zm.next_out = .ref (.blk ob) (oo + produced) := by
      rw [accountL.2.2.2.2.2.1, pointer]
      rfl
    have levelL : dm.level = config.level := congrArg EngineConfig.level stateL.configuration
    have memoryL : dm.lit_bufsize = config.memory := congrArg EngineConfig.memory stateL.configuration
    have wrapL : dm.wrap = config.wrap := congrArg EngineConfig.wrap stateL.configuration
    obtain ⟨_tailProduced, finalHeap, z', _result, _tailSymbols, tailRun, _contentA, _rest⟩ :=
      slow_eof_finish_tail localState endL buffersL eof.1 (by rw [levelL]; exact positive)
        pointerL (readyL running).2.1 (by rw [memoryL]; exact memory) (readyL running).1 (wrapL.trans wrap)
    have run : deflate_slow (some (.tab ds)) Z_FINISH h =
        .ok ((if z'.avail_out == 0 then finish_started else finish_done), finalHeap) := by
      rw [deflate_slow_eof_tail_source, bind_app, loop]
      simp only [running]
      exact tailRun
    have code := (Prod.mk.inj (Except.ok.inj (run.symm.trans observed))).1
    split at code
    · exact False.elim ((by decide +kernel : finish_started ≠ need_more) code)
    · exact False.elim ((by decide +kernel : finish_done ≠ need_more) code)

/-- `local block_state deflate_slow(deflate_state *s, int flush)`.
This actual need_more return retains the working boundary, accepted-input
endpoint and ledger quality on the supplied returned state. Its counted
prefix has no final represented bytes and no extra final-block charge.
Every counted full block still represents at least 16,383 bytes. This is
an internal history bridge, not a public API or global size theorem. -/
theorem deflate_slow_finish_need_more_run_counted_size {h after : Heap} {r : ZStreamRef}
    {ds ob oo origin base used produced : Nat} {z zr : ZStream} {d result : DeflateState}
    {input : Nat → UInt8} {xs : List Symbol} {config : EngineConfig}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (window : config.windowBits = 15)
    (strategy : config.strategy = Z_DEFAULT_STRATEGY)
    (publish : PublishReady d) (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (candidate : ShortCandidateQuality d) (floor : StoredSourceFloor d)
    (quality : ∀ s ∈ xs, s.distance ≠ 0 → s.value = 0 → s.distance ≤ 4096)
    (observed : deflate_slow (some (.tab ds)) Z_FINISH h = .ok (need_more, after))
    (live : after.dstates ds = some result) (stream : r.get after = some zr)
    (account : StreamAccounting z zr used produced) :
    ∃ extended nextOrigin nextBase ys blocks,
      StrategyBoundary after r ds zr result extended nextOrigin nextBase ys config ∧
      EndFrontier after result ∧ StreamBuffers after r ∧
      nextOrigin + fillEnd result = origin + fillEnd d + used ∧ base ≤ nextBase ∧
      ShortCandidateQuality result ∧ StoredSourceFloor result ∧
      (∀ s ∈ ys, s.distance ≠ 0 → s.value = 0 → s.distance ≤ 4096) ∧
      16383 * blocks ≤ nextBase - base ∧
      produced + result.pending.toNat + (result.bi_valid.toInt.toNat + 7) / 8 ≤
        (d.bi_valid.toInt.toNat + 7) / 8 + (nextBase - base) + 5 * blocks := by
  obtain ⟨final, loop, _returned⟩ := deflate_slow_finish_need_more_loop_source boundary frontier buffers
    positive pointer memory wrap publish inputValid observed
  obtain ⟨read, amount, blocks, ze, de, extended, nextOrigin, nextBase, ys,
      stateE, endE, buffersE, accountE, endpoint, baseLe, _ready, candidateE, floorE, qualityE, minimum, cost⟩ :=
    slow_loop_run_counted_size boundary frontier buffers positive pointer memory wrap window strategy
      publish inputValid candidate floor quality loop
  have states : de = result := Option.some.inj (stateE.good.live.hs.symm.trans live)
  have streams : ze = zr := Option.some.inj (stateE.good.live.hz.symm.trans stream)
  subst de ze
  have readEq : read = used := by have first := accountE.2.2.1; have second := account.2.2.1; omega
  have amountEq : amount = produced := by have first := accountE.2.2.2.1; have second := account.2.2.2.1; omega
  subst read amount
  exact ⟨extended, nextOrigin, nextBase, ys, blocks, stateE, endE, buffersE, endpoint,
    baseLe, candidateE, floorE, qualityE, minimum, cost⟩

end Zlib.Deflate.Engine.Proofs
