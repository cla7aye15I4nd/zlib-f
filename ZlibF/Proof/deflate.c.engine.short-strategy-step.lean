import ZlibF.Proof.«deflate.c.engine.short-decisions»

/-! # Search and every decision restore the initialized strategy phase -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The actual body suffix following refill and its stop checks. -/
def slowSearchDecision (s : DeflateStatePtr) (flush : Int32) (st : LoopS) : M LoopS := do
  let head ← slowSearch s
  slowDecision s flush st head

/-- The real slow body executes this suffix after its refill stop tests. -/
theorem slow_body_search_decision_source (s : DeflateStatePtr) (flush : Int32) (st : LoopS) :
    deflate_slow_body s flush st = (do
      if (← rd s (·.lookahead)) < MIN_LOOKAHEAD_u then
        fill_window s
        let la ← rd s (·.lookahead)
        if la < MIN_LOOKAHEAD_u && flush == Z_NO_FLUSH then return { st with ret := some need_more }
        if la == 0 then return { st with brk := true }
      slowSearchDecision s flush st) := by
  rw [slow_body_source]
  rfl

/-- Initialized search and every decision restore the same strategy phase
for any positive input length, including full stored/fixed/dynamic output.
This is the post-refill suffix; it does not assume refill execution. -/
theorem slow_search_decision_strategy_boundary {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (lookahead : 1 ≤ d.lookahead.toNat)
    (room : 3 ≤ d.lookahead.toNat → d.strstart.toNat + 262 ≤ d.window_size.toNat)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : config.memory.toNat = 16384) (output : 0 < z.avail_out.toNat)
    (flush : Int32) (st : LoopS) :
    ∃ produced next after z' result base' ys,
      slowSearchDecision (some (.tab ds)) flush st h = .ok (next, after) ∧
      StrategyBoundary after r ds z' result input origin base' ys config ∧ EndFrontier after result ∧
      StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
      d.strstart.toNat < result.strstart.toNat ∧ result.lookahead.toNat < d.lookahead.toNat ∧
      fillEnd result = fillEnd d ∧ base ≤ base' ∧ next.brk = st.brk ∧
      (next.ret = st.ret ∨ next.ret = some need_more) ∧
      (next.ret = some need_more → st.ret = some need_more ∨ z'.avail_out = 0) ∧
      (next.ret = none → 0 < z'.avail_out.toNat) := by
  obtain ⟨w, wa, head, found, searched, searchRun, cut, searchFrame, searchedBuffers, _storage⟩ :=
    slow_search_initialized_boundary boundary.toContentBoundary frontier buffers room
  have slowFrame : SlowRecordFrame d searched := by
    unfold SlowRecordFrame
    rw [searchFrame]
  have configS : engineConfig searched = config := Eq.trans (ConfigFrame.slow slowFrame) boundary.configuration
  have levelS : searched.level = config.level := congrArg EngineConfig.level configS
  have memoryS : searched.lit_bufsize = config.memory := congrArg EngineConfig.memory configS
  have positiveS : 1 ≤ searched.lookahead.toNat := by rw [searchFrame]; exact lookahead
  have strictS : searched.sym_next.toNat < searched.sym_end.toNat := by rw [searchFrame]; exact boundary.strict
  have readyS := (boundary.resume output).slow slowFrame
  have clearS := boundary.clear.slow slowFrame
  obtain ⟨result⟩ := slow_decision_all_search_boundary cut searchedBuffers positiveS strictS
    (by rw [levelS]; exact positive) pointer readyS.2.1 (by rw [memoryS]; exact memory)
    readyS.1 (by have low := readyS.2.2; omega) clearS flush st head
  have configuration : engineConfig result.state = config := Eq.trans result.config configS
  have stateA : StrategyBoundary result.after r ds result.stream result.state input origin result.blockBase result.symbols config :=
    ⟨result.boundary, configuration, result.clear, result.bits, result.strict, result.resume⟩
  refine ⟨result.produced, result.next, result.after, result.stream, result.state, result.blockBase, result.symbols,
    ?_, stateA, result.frontier, result.buffers, result.accounting, ?_, ?_, ?_, result.base_le,
    result.brk, result.returns, result.reason, result.continues output⟩
  · unfold slowSearchDecision
    rw [bind_app, searchRun]
    exact result.run
  · have startEq : searched.strstart = d.strstart := by rw [searchFrame]
    rw [← startEq]
    exact result.progress
  · have lookEq : searched.lookahead = d.lookahead := by rw [searchFrame]
    rw [← lookEq]
    exact result.less
  · have endpoint : fillEnd searched = fillEnd d := by rw [searchFrame]; rfl
    exact result.endpoint.trans endpoint

end Zlib.Deflate.Engine.Proofs
