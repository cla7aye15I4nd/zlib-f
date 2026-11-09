import ZlibF.Proof.«deflate.c.engine.generic-foreign-match-interval»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-literal-interval»
import ZlibF.Proof.«deflate.c.engine.decision-full-storage»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Every actual match, literal and defer decision preserves its real foreign output interval. -/
theorem default_foreign_slow_decision_run_output_interval {h after : Heap} {r : ZStreamRef}
    {ds w owner oo origin base produced : Nat} {z z' : ZStream} {d : DeflateState}
    {wa : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    {flush : Int32} {st next : LoopS} {candidate : UInt32}
    (cut : SearchBoundary h r ds z d input origin base xs w wa)
    (buffers : StreamBuffers h r) (lookahead : 1 ≤ d.lookahead.toNat)
    (strict : d.sym_next.toNat < d.sym_end.toNat)
    (positive : 0 < d.level.toInt) (pointer : z.next_out = .ref (.dstate_depth owner) oo)
    (memory : d.lit_bufsize.toNat = 16384) (ready : PublishReady d) (clear : BlockInit.BlockClear d)
    (run : slowDecision (some (.tab ds)) flush st candidate h = .ok (next, after))
    (live : r.get after = some z') (account : StreamAccounting z z' 0 produced) :
    ByteOutputInterval h after (.dstate_depth owner) oo produced := by
  by_cases selected : (d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length) = true
  · exact default_foreign_slow_match_run_output_interval cut buffers selected strict positive pointer memory ready clear run live account
  · have branch := Bool.eq_false_iff.mpr selected
    by_cases available : d.match_available = 0
    · have storage := slow_defer_run_full_storage (ob := ds) cut.good branch available run
      have privateFrame : Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) := by
        apply full_frame_weaken storage.2.1
        intro b changed
        rcases changed with root | owned | same
        · exact Or.inl root
        · exact Or.inr owned
        · exact Or.inr (Or.inl same)
      exact ByteOutputInterval.of_foreign_private_frame cut.good buffers pointer privateFrame
    · have room := literal_room cut.good.inv strict
      by_cases full : d.sym_next.toNat + 3 = d.sym_end.toNat
      · exact default_foreign_slow_literal_full_run_output_interval cut buffers lookahead branch available full positive pointer memory ready clear run live account
      · have space : d.sym_next.toNat + 3 < d.sym_end.toNat := by omega
        obtain ⟨other, tested, _goodA, _chainsA, _rangeA, _bytesA, _strictA, shape, frame, live, alloc, next⟩ :=
          slow_literal_nonfull_full_storage_execution (ob := ds) cut.good cut.chains cut.window cut.bytes cut.range
            lookahead (cut.deferred available) branch available space flush st candidate
        have eq := (Prod.mk.inj (Except.ok.inj (tested.symm.trans run))).2
        rw [← eq]
        have privateFrame : Frame h other (fun b => StreamRoot r b ∨ DeflateOwned ds d b) := by
          apply full_frame_weaken frame
          intro b changed
          rcases changed with root | owned | same
          · exact Or.inl root
          · exact Or.inr owned
          · exact Or.inr (Or.inl same)
        exact ByteOutputInterval.of_foreign_private_frame cut.good buffers pointer privateFrame

/-- The complete actual search and decision suffix preserves the exact caller output interval. -/
theorem default_foreign_slow_search_decision_run_output_interval {h after : Heap} {r : ZStreamRef} {ds owner oo origin base produced : Nat}
    {z z' : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    {flush : Int32} {st next : LoopS}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r) (lookahead : 1 ≤ d.lookahead.toNat)
    (room : 3 ≤ d.lookahead.toNat → d.strstart.toNat + 262 ≤ d.window_size.toNat)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.dstate_depth owner) oo)
    (memory : config.memory.toNat = 16384) (ready : PublishReady d)
    (run : slowSearchDecision (some (.tab ds)) flush st h = .ok (next, after))
    (live : r.get after = some z') (account : StreamAccounting z z' 0 produced) :
    ByteOutputInterval h after (.dstate_depth owner) oo produced := by
  obtain ⟨w, wa, head, found, searched, searchRun, cut, searchFrame, searchedBuffers, _storage, shapeS, fullS, _liveS, allocS, nextS⟩ :=
    slow_search_initialized_full_storage boundary.toContentBoundary frontier buffers room
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
  have effectS : ByteOutputInterval h found (.dstate_depth owner) oo 0 :=
    .of_foreign_private_frame boundary.good buffers pointer fullS
  have effectD := default_foreign_slow_decision_run_output_interval cut searchedBuffers positiveS strictS
    (by rw [levelS]; exact positive) pointer (by rw [memoryS]; exact memory) readyS clearS decisionRun live account
  simpa only [Nat.zero_add] using effectS.trans effectD

end Zlib.Deflate.Engine.Proofs
