import ZlibF.Proof.«deflate.c.engine.finish-strategy-step»
import ZlibF.Proof.«deflate.c.engine.eof-tail»
import ZlibF.Proof.«deflate.c.engine.slow-first»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Empty actual input and lookahead take EOF even at zero prepared output
capacity. This checks the real loop and final publication, not an assumed
strategy contract. -/
theorem empty_finish_strategy_result {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (publish : PublishReady d)
    (empty : z.avail_in = 0) (look : d.lookahead = 0) :
    ∃ produced after z' result,
      deflate_slow (some (.tab ds)) Z_FINISH h =
        .ok ((if z'.avail_out == 0 then finish_started else finish_done), after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧
      StreamAccounting z z' 0 produced := by
  have short : d.lookahead.toNat < 262 := by rw [look]; decide
  have valid : z.avail_in ≠ 0 → z.next_in ≠ .null := fun nonempty => False.elim (nonempty empty)
  obtain ⟨used, filledHeap, filledZ, filled, extended, nextOrigin, fillRun, stateF, endF,
      accountF, buffersF, _startF, lookF, _agreesF, _stoppedF, frameF⟩ :=
    fill_window_strategy_end_boundary boundary frontier short wrap buffers valid
  have usedZero : used = 0 := by have bound := accountF.1; rw [empty] at bound; change used ≤ 0 at bound; omega
  subst used
  have lookZero : filled.lookahead = 0 := UInt32.toNat_inj.mp (by simpa only [look, UInt32.toNat_zero, Nat.add_zero] using lookF)
  have body : deflate_slow_body (some (.tab ds)) Z_FINISH {} h = .ok ({ brk := true }, filledHeap) := by
    rw [slow_finish_body_after_fill boundary.good.live.hs stateF.good.live.hs short fillRun, lookZero]
    rfl
  have loop := while_once (cond := forever) (body := deflate_slow_body (some (.tab ds)) Z_FINISH)
    (a := {}) (b := {}) (c := { brk := true }) (e := { brk := true })
    (h := h) (h1 := h) (h2 := filledHeap) (h3 := filledHeap) rfl body rfl
  have localF : StrategyBoundary filledHeap r ds filledZ filled extended nextOrigin base xs (engineConfig filled) := by
    rw [stateF.configuration]
    exact stateF
  have pointerF : filledZ.next_out = .ref (.blk ob) oo := by
    rw [accountF.2.2.2.2.2.1, advance_zero]
    exact pointer
  have levelF : 0 < filled.level.toInt := by
    have eq := congrArg EngineConfig.level stateF.configuration
    change filled.level = config.level at eq
    rw [eq]; exact positive
  have memoryF : filled.lit_bufsize.toNat = 16384 := by
    have eq := congrArg EngineConfig.memory stateF.configuration
    change filled.lit_bufsize = config.memory at eq
    rw [eq]; exact memory
  have wrapF : filled.wrap = 1 := (congrArg EngineConfig.wrap stateF.configuration).trans wrap
  have pendingF : filled.pending = 0 := by rw [frameF]; exact publish.1
  have cursorF : filled.pending_out = filled.pending_buf := by rw [frameF]; exact publish.2.1
  obtain ⟨produced, after, z', result, ys, tailRun, stateA, buffersA, accountA,
      _clearA, _configA, _lookA, _startA, _flagA, _insertA, _bitsA, _readyA, _symbolsA⟩ :=
    slow_eof_finish_tail localF endF buffersF lookZero levelF pointerF cursorF memoryF pendingF wrapF
  refine ⟨produced, after, z', result, ?_, stateA.good, buffersA, ?_⟩
  · rw [deflate_slow_eof_tail_source, bind_app, loop]
    exact tailRun
  · simpa only [Nat.zero_add, Nat.add_zero] using stream_accounting_trans accountF accountA

theorem empty_finish_strategy {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (publish : PublishReady d)
    (empty : z.avail_in = 0) (look : d.lookahead = 0) :
    ∃ produced ret after z' result,
      deflate_slow (some (.tab ds)) Z_FINISH h = .ok (ret, after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧
      StreamAccounting z z' 0 produced ∧ (ret = finish_started ∨ ret = finish_done) := by
  obtain ⟨produced, after, z', result, run, goodA, buffersA, accountA⟩ :=
    empty_finish_strategy_result boundary frontier buffers positive pointer memory wrap publish empty look
  refine ⟨produced, (if z'.avail_out == 0 then finish_started else finish_done),
    after, z', result, run, goodA, buffersA, accountA, ?_⟩
  split <;> simp

theorem empty_zero_output_finish_strategy {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (publish : PublishReady d)
    (empty : z.avail_in = 0) (look : d.lookahead = 0) (output : z.avail_out = 0) :
    ∃ after z' result,
      deflate_slow (some (.tab ds)) Z_FINISH h = .ok (finish_started, after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧
      StreamAccounting z z' 0 0 ∧ z'.avail_out = 0 := by
  obtain ⟨produced, after, z', result, run, goodA, buffersA, accountA⟩ :=
    empty_finish_strategy_result boundary frontier buffers positive pointer memory wrap publish empty look
  have producedZero : produced = 0 := by
    have bound := accountA.2.1
    rw [output] at bound
    change produced ≤ 0 at bound
    omega
  subst produced
  have outputZero : z'.avail_out = 0 := UInt32.toNat_inj.mp (by
    have count := accountA.2.2.2.1
    simpa only [output, UInt32.toNat_zero, Nat.add_zero] using count)
  rw [outputZero] at run
  exact ⟨after, z', result, run, goodA, buffersA, accountA, outputZero⟩


end Zlib.Deflate.Engine.Proofs
