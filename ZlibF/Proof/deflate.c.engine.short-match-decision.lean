import ZlibF.Proof.«deflate.c.engine.flush-end-frontier»

/-! # Every selected match decision restores the initialized boundaries -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Selected matching with every positive remaining-input length and
both full/nonfull tallies. Actual publication is conditional on the real
symbol counter. No selected encoding or callee contract is assumed. -/
theorem slow_match_search_boundary {h : Heap} {r : ZStreamRef} {ds w ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (cut : SearchBoundary h r ds z d input origin base xs w wa)
    (buffers : StreamBuffers h r)
    (selected : (d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length) = true)
    (strict : d.sym_next.toNat < d.sym_end.toNat)
    (positive : 0 < d.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (cursor : d.pending_out = d.pending_buf) (memory : d.lit_bufsize.toNat = 16384)
    (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7) (clear : BlockInit.BlockClear d)
    (flush : Int32) (st : LoopS) (hash_head : UInt32) :
    ∃ produced head after z' result base' ys,
      slowDecision (some (.tab ds)) flush st hash_head h =
        .ok ((if d.sym_next + 3 == d.sym_end then
          if z'.avail_out == 0 then { st with hash_head := head, bflush := true, ret := some need_more }
          else { st with hash_head := head, bflush := true }
          else { st with hash_head := head, bflush := false }), after) ∧
      ContentBoundary after r ds z' result input origin base' ys ∧ EndFrontier after result ∧
      StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧ BlockInit.BlockClear result ∧
      result.strstart.toNat = d.strstart.toNat + (d.prev_length.toNat - 1) ∧
      result.lookahead.toNat = d.lookahead.toNat - (d.prev_length.toNat - 1) ∧ fillEnd result = fillEnd d ∧
      result.sym_next.toNat < result.sym_end.toNat ∧ base ≤ base' ∧
      ConfigFrame d result ∧ result.bi_valid.toInt < 8 ∧ (0 < z'.avail_out.toNat → PublishReady result) ∧
      ((d.sym_next + 3 == d.sym_end) = false → z' = z) := by
  obtain ⟨head, emittedHeap, emitted, emitRun, emittedBoundary, emittedFrontier, emittedBuffers, emitFrame,
      emittedFlag, emittedStart, emittedLook, emittedEnd, emittedCount, emittedEndCount, _storage⟩ :=
    slow_match_emit_search_boundary cut buffers selected strict hash_head
  have clearE := clear.slow emitFrame
  have configE := ConfigFrame.slow emitFrame
  have readyE := PublishReady.slow (show PublishReady d from ⟨pending, cursor, by omega⟩) emitFrame
  have room := literal_room cut.good.inv strict
  obtain ⟨_, _, trees, _⟩ := cut.symbols
  have exactCount : (d.sym_next + 3).toNat = d.sym_next.toNat + 3 := literal_count trees.base room 0
  by_cases full : (d.sym_next + 3 == d.sym_end) = true
  · obtain ⟨produced, after, z', result, flushRun, boundaryA, endA, buffersA, accountA, clearA,
        frameA, lowA, phaseA⟩ :=
      flush_nonfinal_end_boundary emittedBoundary emittedFrontier emittedBuffers
        (by rw [configE.level]; exact positive) pointer
        (by rw [emitFrame]; exact cursor) (by rw [configE.memory]; exact memory)
        (by rw [emitFrame]; exact pending) (by rw [emitFrame]; exact bits) clearE emittedFlag
    have startA : result.strstart = emitted.strstart := by rw [frameA]
    have lookA : result.lookahead = emitted.lookahead := by rw [frameA]
    have endpoint : fillEnd result = fillEnd emitted := by rw [frameA]; rfl
    have strictA : result.sym_next.toNat < result.sym_end.toNat := by
      obtain ⟨_, _, treesA, ledgerA, _⟩ := boundaryA.symbols
      have count := ledgerA.count
      have extent := treesA.base.sym_end
      have lower := treesA.base.lit_lo
      simp only [List.length_nil, Nat.mul_zero] at count
      omega
    refine ⟨produced, head, after, z', result, base + represented (xs ++ [emittedMatch d]), [], ?_,
      boundaryA, endA, buffersA, accountA, clearA, ?_, ?_, ?_, strictA, Nat.le_add_right _ _,
      configE.trans (ConfigFrame.flush frameA), lowA, phaseA, ?_⟩
    · rw [slow_decision_match_source cut.good.live.hs selected flush st hash_head]
      simp only [bind_app, emitRun, full, ite_true, flushRun]
      by_cases empty : (z'.avail_out == 0) = true <;> simp [empty, pure_app]
    · rw [startA]; exact emittedStart
    · rw [lookA]; exact emittedLook
    · rw [endpoint]; exact emittedEnd
    · intro impossible; rw [full] at impossible; cases impossible
  · have notFull : (d.sym_next + 3 == d.sym_end) = false := Bool.eq_false_iff.mpr full
    have countLess : emitted.sym_next.toNat < emitted.sym_end.toNat := by
      have notEqual : d.sym_next.toNat + 3 ≠ d.sym_end.toNat := by
        intro equal
        have machine : d.sym_next + 3 = d.sym_end := UInt32.toNat_inj.mp (exactCount.trans equal)
        simp only [machine, beq_self_eq_true] at notFull
        cases notFull
      rw [emittedCount, emittedEndCount]
      omega
    refine ⟨0, head, emittedHeap, z, emitted, base, xs ++ [emittedMatch d], ?_,
      emittedBoundary, emittedFrontier, emittedBuffers, stream_accounting_zero z, clearE,
      emittedStart, emittedLook, emittedEnd, countLess, Nat.le_refl _, configE, readyE.2.2,
      fun _ => readyE, fun _ => rfl⟩
    rw [slow_decision_match_source cut.good.live.hs selected flush st hash_head]
    simp only [bind_app, emitRun, notFull, Bool.false_eq_true, ite_false, pure_app]

end Zlib.Deflate.Engine.Proofs
