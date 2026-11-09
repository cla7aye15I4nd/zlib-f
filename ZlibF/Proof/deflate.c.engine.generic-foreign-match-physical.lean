import ZlibF.Proof.«deflate.c.engine.generic-foreign-macro-physical»
import ZlibF.Proof.«deflate.c.engine.match-decision-full-storage»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Both actual selected-match branches retain the complete foreign-output object footprint. -/
theorem default_foreign_slow_match_run_full_storage {h after : Heap} {r : ZStreamRef}
    {ds w owner oo origin base : Nat} {z : ZStream} {d : DeflateState}
    {wa : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    {flush : Int32} {st next : LoopS} {candidate : UInt32}
    (cut : SearchBoundary h r ds z d input origin base xs w wa)
    (buffers : StreamBuffers h r)
    (selected : (d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length) = true)
    (strict : d.sym_next.toNat < d.sym_end.toNat)
    (positive : 0 < d.level.toInt) (pointer : z.next_out = .ref (.dstate_depth owner) oo)
    (memory : d.lit_bufsize.toNat = 16384) (ready : PublishReady d)
    (clear : BlockInit.BlockClear d)
    (run : slowDecision (some (.tab ds)) flush st candidate h = .ok (next, after))
 :
    Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = owner) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  obtain ⟨head, emittedHeap, emitted, emitRun, emittedBoundary, emittedFrontier, emittedBuffers, emitFrame,
      emittedFlag, _emittedStart, _emittedLook, _emittedEnd, _emittedCount, _emittedEndCount, _storage⟩ :=
    slow_match_emit_search_boundary cut buffers selected strict candidate
  obtain ⟨shapeE, frameE, _liveE, allocE, nextE⟩ := slow_match_emit_run_full_storage cut candidate selected strict emitRun
  have readyE := ready.slow emitFrame
  have configE := ConfigFrame.slow emitFrame
  have clearE := clear.slow emitFrame
  by_cases full : (d.sym_next + 3 == d.sym_end) = true
  · obtain ⟨_amount,other,otherZ,otherD,_before,_written,_remaining,_kind,_body,_padding,
        macroRun,boundaryA,_endA,_buffersA,_accountA,_clearA,_frameA,_lowA,_phaseA,_rest⟩ :=
      default_foreign_flush_macro_content_encoding emittedBoundary emittedFrontier emittedBuffers
        (by rw [configE.level];exact positive) pointer readyE.2.1
        (by rw [configE.memory];exact memory) readyE.1 (by have low:=readyE.2.2;omega) clearE emittedFlag false
    have flushRun : FLUSH_BLOCK (some (.tab ds)) 0 emittedHeap =
        .ok ((if otherZ.avail_out==0 then some need_more else none),other) := by
      have actual : FLUSH_BLOCK_ONLY (some (.tab ds)) 0 emittedHeap=.ok ((),other) := macroRun
      unfold FLUSH_BLOCK
      simp only [bind_app,actual,ldDeflateState_tab boundaryA.good.live.hs,
        boundaryA.good.live.back,zrd_eq,boundaryA.good.live.hz]
      by_cases empty : (otherZ.avail_out==0)=true <;> simp [empty,pure_app]
    obtain ⟨shapeF, frameF, _liveF, allocF, nextF⟩ :=
      default_foreign_flush_control_run_full_storage emittedBoundary emittedBuffers
        (by rw [configE.level]; exact positive) pointer readyE.2.1
        (by rw [configE.memory]; exact memory) readyE.1 (by have low := readyE.2.2; omega)
        clearE emittedFlag false flushRun
    have tested : slowDecision (some (.tab ds)) flush st candidate h =
        .ok ((if otherZ.avail_out == 0 then { st with hash_head := head, bflush := true, ret := some need_more }
          else { st with hash_head := head, bflush := true }), other) := by
      rw [slow_decision_match_source cut.good.live.hs selected flush st candidate]
      simp only [bind_app, emitRun, full, ite_true, flushRun]
      by_cases empty : (otherZ.avail_out == 0) = true <;> simp [empty, pure_app]
    have eq := (Prod.mk.inj (Except.ok.inj (tested.symm.trans run))).2
    rw [← eq]
    have owned : DeflateOwned ds emitted = DeflateOwned ds d := by rw [emitFrame]; rfl
    rw [owned] at frameF
    have shape := shapeE.trans shapeF
    have frame := full_frame_trans_shape (full_private_frame_add_output frameE) frameF shapeE
    exact ⟨shape, frame, full_shape_live_change shape, allocF.trans allocE, nextF.trans nextE⟩
  · have nonfull := Bool.eq_false_iff.mpr full
    have tested : slowDecision (some (.tab ds)) flush st candidate h =
        .ok ({ st with hash_head := head, bflush := false }, emittedHeap) := by
      rw [slow_decision_match_source cut.good.live.hs selected flush st candidate]
      simp only [bind_app, emitRun, nonfull, Bool.false_eq_true, ite_false, pure_app]
    have eq := (Prod.mk.inj (Except.ok.inj (tested.symm.trans run))).2
    rw [← eq]
    exact ⟨shapeE, full_private_frame_add_output frameE, full_shape_live_change shapeE, allocE, nextE⟩

end Zlib.Deflate.Engine.Proofs
