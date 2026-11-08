import ZlibF.Proof.«deflate.c.engine.match-decision-full-storage»
import ZlibF.Proof.«deflate.c.engine.literal-decision-full-storage»
import ZlibF.Proof.«deflate.c.engine.search-ready-step»

/-! # Complete object and allocation effects of the actual strategy -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Every actual selected-match, literal and deferral decision retains the complete heap frame and exact object ledger. -/
theorem slow_decision_run_full_storage {h after : Heap} {r : ZStreamRef}
    {ds w ob oo origin base : Nat} {z : ZStream} {d : DeflateState}
    {wa : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    {flush : Int32} {st next : LoopS} {candidate : UInt32}
    (cut : SearchBoundary h r ds z d input origin base xs w wa)
    (buffers : StreamBuffers h r) (lookahead : 1 ≤ d.lookahead.toNat)
    (strict : d.sym_next.toNat < d.sym_end.toNat)
    (positive : 0 < d.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : d.lit_bufsize.toNat = 16384) (ready : PublishReady d) (clear : BlockInit.BlockClear d)
    (run : slowDecision (some (.tab ds)) flush st candidate h = .ok (next, after))
 :
    Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = ob) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  by_cases selected : (d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length) = true
  · exact slow_match_run_full_storage cut buffers selected strict positive pointer memory ready clear run
  · have branch := Bool.eq_false_iff.mpr selected
    by_cases available : d.match_available = 0
    · exact slow_defer_run_full_storage cut.good branch available run
    · have room := literal_room cut.good.inv strict
      by_cases full : d.sym_next.toNat + 3 = d.sym_end.toNat
      · exact slow_literal_full_run_full_storage cut buffers lookahead branch available full positive pointer memory ready clear run
      · have space : d.sym_next.toNat + 3 < d.sym_end.toNat := by omega
        obtain ⟨other, tested, _goodA, _chainsA, _rangeA, _bytesA, _strictA, shape, frame, live, alloc, next⟩ :=
          slow_literal_nonfull_full_storage_execution (ob := ob) cut.good cut.chains cut.window cut.bytes cut.range
            lookahead (cut.deferred available) branch available space flush st candidate
        have eq := (Prod.mk.inj (Except.ok.inj (tested.symm.trans run))).2
        rw [← eq]
        exact ⟨shape, frame, live, alloc, next⟩

/-- The complete actual initialized search and decision suffix retains all heap objects outside its private and output footprint. -/
theorem slow_search_decision_run_full_storage {h after : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    {flush : Int32} {st next : LoopS}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r) (lookahead : 1 ≤ d.lookahead.toNat)
    (room : 3 ≤ d.lookahead.toNat → d.strstart.toNat + 262 ≤ d.window_size.toNat)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : config.memory.toNat = 16384) (ready : PublishReady d)
    (run : slowSearchDecision (some (.tab ds)) flush st h = .ok (next, after))
 :
    Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = ob) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
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
  obtain ⟨shapeD, fullD, _liveD, allocD, nextD⟩ := slow_decision_run_full_storage cut searchedBuffers positiveS strictS
    (by rw [levelS]; exact positive) pointer (by rw [memoryS]; exact memory) readyS clearS decisionRun
  have owned : DeflateOwned ds searched = DeflateOwned ds d := by rw [searchFrame]; rfl
  rw [owned] at fullD
  have shape := shapeS.trans shapeD
  have frame := full_frame_trans_shape (full_private_frame_add_output fullS) fullD shapeS
  exact ⟨shape, frame, full_shape_live_change shape, allocD.trans allocS, nextD.trans nextS⟩

end Zlib.Deflate.Engine.Proofs
