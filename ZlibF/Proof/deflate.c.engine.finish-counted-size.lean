import ZlibF.Proof.«deflate.c.engine.loop-counted-size»
import ZlibF.Proof.«deflate.c.engine.eof-final-byte-count»
import ZlibF.Proof.«deflate.c.engine.finish-ready-loop»

/-! # Real FINISH strategy cost with one optional final block -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false
set_option maxRecDepth 10000

/-- `local block_state deflate_slow(deflate_state *s, int flush)`.
The actual FINISH run counts each complete nonfinal block. An early
need_more returns the loop's exact prefix budget without a final charge.
Only the actual EOF/final-block branch pays its remaining represented
bytes and one extra five-byte overhead. These counts can therefore be
retained when calls are composed; this is not a public bound theorem. -/
theorem deflate_slow_finish_counted_size {h : Heap} {r : ZStreamRef}
    {ds ob oo origin base : Nat} {z : ZStream} {d : DeflateState}
    {input : Nat → UInt8} {xs : List Symbol} {config : EngineConfig}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (window : config.windowBits = 15)
    (strategy : config.strategy = Z_DEFAULT_STRATEGY)
    (publish : PublishReady d) (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (candidate : ShortCandidateQuality d) (floor : StoredSourceFloor d)
    (quality : ∀ s ∈ xs, s.distance ≠ 0 → s.value = 0 → s.distance ≤ 4096) :
    ∃ used produced ret after z' result blocks closedDelta finalBytes closed,
      deflate_slow (some (.tab ds)) Z_FINISH h = .ok (ret, after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' used produced ∧
      16383 * blocks ≤ closedDelta ∧
      closedDelta + finalBytes ≤ origin + fillEnd d + used - base ∧
      produced + result.pending.toNat + (result.bi_valid.toInt.toNat + 7) / 8 ≤
        (d.bi_valid.toInt.toNat + 7) / 8 + closedDelta + finalBytes + 5 * blocks + (if closed then 5 else 0) ∧
      (closed = false → finalBytes = 0 ∧ ret = need_more) ∧
      (closed = true → ret ≠ need_more) := by
  obtain ⟨_read, _amount, final, middle, ze, de, _baseE, _symbolsE, _inputE, _originE,
      loop, stateE, _endE, _buffersE, _accountE, _agreesE, _endpointE, _baseLeE,
      stopped, _stopOutput, stopInput, _readyE⟩ :=
    slow_finish_ready_loop boundary frontier buffers positive pointer memory wrap publish inputValid
  obtain ⟨used, produced, blocks, zm, dm, extended, nextOrigin, nextBase, ys,
      stateL, endL, buffersL, accountL, endpointL, baseL, readyL, _candidateL, floorL,
      qualityL, minimumL, costL⟩ :=
    slow_loop_run_counted_size boundary frontier buffers positive pointer memory wrap window strategy
      publish inputValid candidate floor quality loop
  have streams : ze = zm := Option.some.inj (stateE.good.live.hz.symm.trans stateL.good.live.hz)
  have states : de = dm := Option.some.inj (stateE.good.live.hs.symm.trans stateL.good.live.hs)
  subst ze de
  rcases stopped with returned | ⟨running, broke⟩
  · have mass : nextBase ≤ nextOrigin + fillEnd dm := by
      have accounted := stateL.accounted
      dsimp only [fillEnd]
      omega
    refine ⟨used, produced, need_more, middle, zm, dm, blocks, nextBase - base, 0, false,
      ?_, stateL.good, buffersL, accountL, minimumL, ?_, ?_, ?_, ?_⟩
    · rw [deflate_slow_eof_tail_source, bind_app, loop]
      simp only [returned]
      rfl
    · omega
    · simpa only [Nat.add_zero, Bool.false_eq_true, ite_false] using costL
    · exact fun _ => ⟨rfl, rfl⟩
    · intro impossible
      cases impossible
  · have eof := stopInput broke
    have prepared := readyL running
    have localState : StrategyBoundary middle r ds zm dm extended nextOrigin nextBase ys (engineConfig dm) := by
      rw [stateL.configuration]
      exact stateL
    have pointerL : zm.next_out = .ref (.blk ob) (oo + produced) := by
      rw [accountL.2.2.2.2.2.1, pointer]
      rfl
    have levelL : dm.level = config.level := congrArg EngineConfig.level stateL.configuration
    have memoryL : dm.lit_bufsize = config.memory := congrArg EngineConfig.memory stateL.configuration
    have wrapL : dm.wrap = config.wrap := congrArg EngineConfig.wrap stateL.configuration
    have strategyL : dm.strategy = config.strategy := congrArg EngineConfig.strategy stateL.configuration
    obtain ⟨tailProduced, after, z', result, tailSymbols, tailRun, contentA, buffersA, accountA, massA, costA⟩ :=
      slow_eof_finish_tail_byte_count localState endL buffersL eof.1 (by rw [levelL]; exact positive)
        pointerL prepared (by rw [memoryL]; exact memory) (wrapL.trans wrap) (strategyL.trans strategy) floorL qualityL
    refine ⟨used, produced + tailProduced, if z'.avail_out == 0 then finish_started else finish_done,
      after, z', result, blocks, nextBase - base, represented tailSymbols, true,
      ?_, contentA.good, buffersA, ?_, minimumL, ?_, ?_, ?_, ?_⟩
    · rw [deflate_slow_eof_tail_source, bind_app, loop]
      simp only [running]
      exact tailRun
    · simpa only [Nat.add_zero] using stream_accounting_trans accountL accountA
    · have endL : fillEnd dm = dm.strstart.toNat := by simp only [fillEnd, eof.1, UInt32.toNat_zero, Nat.add_zero]
      rw [endL] at endpointL
      omega
    · have pendingL := prepared.1
      rw [pendingL, UInt64.toNat_zero] at costL
      simp only [ite_true]
      omega
    · intro impossible
      cases impossible
    · intro _
      split <;> decide +kernel

/-- `local block_state deflate_slow(deflate_state *s, int flush)`.
The counted budget belongs to this supplied actual FINISH execution and
its supplied accounting, rather than to another run or abstract encoder. -/
theorem deflate_slow_finish_run_counted_size {h after : Heap} {r : ZStreamRef}
    {ds ob oo origin base used produced : Nat} {z zr : ZStream} {d result : DeflateState}
    {input : Nat → UInt8} {xs : List Symbol} {config : EngineConfig} {ret : block_state}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (window : config.windowBits = 15)
    (strategy : config.strategy = Z_DEFAULT_STRATEGY)
    (publish : PublishReady d) (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (candidate : ShortCandidateQuality d) (floor : StoredSourceFloor d)
    (quality : ∀ s ∈ xs, s.distance ≠ 0 → s.value = 0 → s.distance ≤ 4096)
    (run : deflate_slow (some (.tab ds)) Z_FINISH h = .ok (ret, after))
    (live : after.dstates ds = some result) (stream : r.get after = some zr)
    (account : StreamAccounting z zr used produced) :
    ∃ blocks closedDelta finalBytes closed,
      16383 * blocks ≤ closedDelta ∧
      closedDelta + finalBytes ≤ origin + fillEnd d + used - base ∧
      produced + result.pending.toNat + (result.bi_valid.toInt.toNat + 7) / 8 ≤
        (d.bi_valid.toInt.toNat + 7) / 8 + closedDelta + finalBytes + 5 * blocks + (if closed then 5 else 0) ∧
      (closed = false → finalBytes = 0 ∧ ret = need_more) ∧
      (closed = true → ret ≠ need_more) := by
  obtain ⟨read, amount, expectedRet, expected, ze, de, blocks, delta, finalBytes, closed,
      expectedRun, goodE, _buffersE, accountE, minimum, mass, cost, early, final⟩ :=
    deflate_slow_finish_counted_size boundary frontier buffers positive pointer memory wrap window strategy
      publish inputValid candidate floor quality
  obtain ⟨codes, heaps⟩ := Prod.mk.inj (Except.ok.inj (expectedRun.symm.trans run))
  subst expectedRet expected
  have states : de = result := Option.some.inj (goodE.live.hs.symm.trans live)
  have streams : ze = zr := Option.some.inj (goodE.live.hz.symm.trans stream)
  subst de ze
  have readEq : read = used := by have first := accountE.2.2.1; have second := account.2.2.1; omega
  have amountEq : amount = produced := by have first := accountE.2.2.2.1; have second := account.2.2.2.1; omega
  subst read amount
  exact ⟨blocks, delta, finalBytes, closed, minimum, mass, cost, early, final⟩

end Zlib.Deflate.Engine.Proofs
