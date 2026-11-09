import ZlibF.Proof.«deflate.c.engine.generic-foreign-match-owner-fields»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-literal-owner-fields»
import ZlibF.Proof.«deflate.c.engine.search-ready-step»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

theorem default_foreign_slow_decision_run_owner_fields {h after : Heap} {r : ZStreamRef}
    {ds w owner oo origin base : Nat} {z : ZStream} {d : DeflateState}
    {wa : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    {flush : Int32} {st next : LoopS} {candidate : UInt32}
    (cut : SearchBoundary h r ds z d input origin base xs w wa)
    (buffers : StreamBuffers h r) (lookahead : 1 ≤ d.lookahead.toNat)
    (strict : d.sym_next.toNat < d.sym_end.toNat)
    (positive : 0 < d.level.toInt) (pointer : z.next_out = .ref (.dstate_depth owner) oo)
    (memory : d.lit_bufsize.toNat = 16384) (ready : PublishReady d) (clear : BlockInit.BlockClear d)
    (run : slowDecision (some (.tab ds)) flush st candidate h = .ok (next, after))
 :
    ForeignOwnerFields h after owner := by
  by_cases selected : (d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length) = true
  · exact default_foreign_slow_match_run_owner_fields cut buffers selected strict positive pointer memory ready clear run
  · have branch := Bool.eq_false_iff.mpr selected
    by_cases available : d.match_available = 0
    · obtain ⟨_shape,frame,_live,_alloc,_next⟩ := slow_defer_run_full_storage (ob:=ds) cut.good branch available run
      apply ForeignOwnerFields.of_private_frame cut.good buffers pointer
      apply full_frame_weaken frame
      intro b changed
      rcases changed with root|owned|same
      · exact Or.inl root
      · exact Or.inr owned
      · exact Or.inr (Or.inl same)
    · have room := literal_room cut.good.inv strict
      by_cases full : d.sym_next.toNat + 3 = d.sym_end.toNat
      · exact default_foreign_slow_literal_full_run_owner_fields cut buffers lookahead branch available full positive pointer memory ready clear run
      · have space : d.sym_next.toNat + 3 < d.sym_end.toNat := by omega
        obtain ⟨other, tested, _goodA, _chainsA, _rangeA, _bytesA, _strictA, shape, frame, live, alloc, next⟩ :=
          slow_literal_nonfull_full_storage_execution (ob := ds) cut.good cut.chains cut.window cut.bytes cut.range
            lookahead (cut.deferred available) branch available space flush st candidate
        have eq := (Prod.mk.inj (Except.ok.inj (tested.symm.trans run))).2
        rw [← eq]
        apply ForeignOwnerFields.of_private_frame cut.good buffers pointer
        apply full_frame_weaken frame
        intro b changed
        rcases changed with root|owned|same
        · exact Or.inl root
        · exact Or.inr owned
        · exact Or.inr (Or.inl same)

/-- The complete actual initialized search and decision suffix retains all heap objects outside its private and output footprint. -/
theorem default_foreign_slow_search_decision_run_owner_fields {h after : Heap} {r : ZStreamRef} {ds owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    {flush : Int32} {st next : LoopS}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r) (lookahead : 1 ≤ d.lookahead.toNat)
    (room : 3 ≤ d.lookahead.toNat → d.strstart.toNat + 262 ≤ d.window_size.toNat)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.dstate_depth owner) oo)
    (memory : config.memory.toNat = 16384) (ready : PublishReady d)
    (run : slowSearchDecision (some (.tab ds)) flush st h = .ok (next, after))
 :
    ForeignOwnerFields h after owner := by
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
  have ownerD := default_foreign_slow_decision_run_owner_fields cut searchedBuffers positiveS strictS
    (by rw [levelS]; exact positive) pointer (by rw [memoryS]; exact memory) readyS clearS decisionRun
  have ownerS := ForeignOwnerFields.of_private_frame boundary.good buffers pointer fullS
  exact ownerS.trans ownerD

end Zlib.Deflate.Engine.Proofs
