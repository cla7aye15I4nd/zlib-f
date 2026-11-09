import ZlibF.Proof.«deflate.c.engine.generic-foreign-macro-content»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-slow-literal-loop»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-search-prefix»
import ZlibF.Proof.«deflate.c.engine.strategy-controls»
import ZlibF.Proof.«deflate.c.engine.finish-ready-step»
import ZlibF.Proof.«deflate.c.engine.positive-flush-loop»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-decision-controls»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

theorem default_foreign_slow_search_decision_run_controls {h after : Heap} {r : ZStreamRef} {ds owner oo origin base : Nat}
    {z : ZStream} {d result : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    {flush : Int32} {st next : LoopS}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r) (lookahead : 1 ≤ d.lookahead.toNat)
    (comparisonRoom : d.strstart.toNat + 262 ≤ d.window_size.toNat)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.dstate_depth owner) oo)
    (memory : config.memory.toNat = 16384) (ready : PublishReady d)
    (run : slowSearchDecision (some (.tab ds)) flush st h = .ok (next, after))
    (live : after.dstates ds = some result) : StrategyControls d result := by
  obtain ⟨w, wa, head, found, searched, searchRun, cut, searchFrame, searchedBuffers, _storage⟩ :=
    slow_search_initialized_boundary boundary.toContentBoundary frontier buffers (fun _ => comparisonRoom)
  have slowFrame : SlowRecordFrame d searched := by unfold SlowRecordFrame; rw [searchFrame]
  have configS : engineConfig searched = config := Eq.trans (ConfigFrame.slow slowFrame) boundary.configuration
  have levelS : searched.level = config.level := congrArg EngineConfig.level configS
  have memoryS : searched.lit_bufsize = config.memory := congrArg EngineConfig.memory configS
  have positiveS : 1 ≤ searched.lookahead.toNat := by rw [searchFrame]; exact lookahead
  have strictS : searched.sym_next.toNat < searched.sym_end.toNat := by rw [searchFrame]; exact boundary.strict
  have readyS := ready.slow slowFrame
  have clearS := boundary.clear.slow slowFrame
  have decisionRun : slowDecision (some (.tab ds)) flush st head found = .ok (next, after) := by
    unfold slowSearchDecision at run
    simpa only [bind_app, searchRun] using run
  have controls := default_foreign_slow_decision_run_controls cut searchedBuffers positiveS strictS
    (by rw [levelS]; exact positive) pointer (by rw [memoryS]; exact memory)
    (by rw [searchFrame]; exact comparisonRoom) readyS clearS decisionRun live
  exact ⟨controls.empty_cursor, by rw [controls.status, searchFrame], by rw [controls.last_flush, searchFrame]⟩

end Zlib.Deflate.Engine.Proofs
