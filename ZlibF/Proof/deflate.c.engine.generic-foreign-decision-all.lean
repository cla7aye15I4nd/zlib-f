import ZlibF.Proof.«deflate.c.engine.generic-foreign-slow-match-full»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-slow-literal-search»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-nonpublishing-encoding»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

theorem default_foreign_slow_decision_nonfull {h : Heap} {r : ZStreamRef} {ds w origin base : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (cut : SearchBoundary h r ds z d input origin base xs w wa)
    (buffers : StreamBuffers h r) (lookahead : 1 ≤ d.lookahead.toNat)
    (space : d.sym_next.toNat + 3 < d.sym_end.toNat)
    (ready : PublishReady d) (clear : BlockInit.BlockClear d)
    (flush : Int32) (st : LoopS) (head : UInt32) :
    Nonempty (DecisionResult h r ds z d input origin base flush st head) := by
  have strict : d.sym_next.toNat < d.sym_end.toNat := by omega
  by_cases selected : (d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length) = true
  · obtain ⟨candidate, after, result, run, contentA, frontierA, buffersA, frameA, _available,
        startA, lookA, endpoint, countA, endCount, _storage⟩ :=
      slow_match_emit_search_boundary cut buffers selected strict head
    have previous : 3 ≤ d.prev_length.toNat := by
      have guard := selected
      simp only [Bool.and_eq_true, decide_eq_true_eq] at guard
      exact UInt32.le_iff_toNat_le.mp guard.1
    obtain ⟨_, _, trees, _, _⟩ := cut.symbols
    have count : (d.sym_next + 3).toNat = d.sym_next.toNat + 3 :=
      literal_count trees.base (by omega) 0
    have flag : (d.sym_next + 3 == d.sym_end) = false := by
      apply beq_eq_false_iff_ne.mpr
      intro equal
      have same := congrArg UInt32.toNat equal
      rw [count] at same
      omega
    have readyA := ready.slow frameA
    apply decision_result_of_output (full := false) (test := false)
      (nextHead := candidate) (produced := 0) (z' := z) (result := result)
      ?_ contentA frontierA buffersA (stream_accounting_zero z) (clear.slow frameA)
      (ConfigFrame.slow frameA) readyA.2.2 (fun _ => readyA) ?_ ?_ ?_ endpoint
      (Nat.le_refl _) (fun _ => rfl)
    · rw [slow_decision_match_source cut.good.live.hs selected]
      simp only [bind_app, run, flag, Bool.false_eq_true, ite_false, pure_app, decisionNext,
        Bool.false_and]
    · rw [countA, endCount]; exact space
    · rw [startA]; omega
    · rw [lookA]; omega
  · have branch := Bool.eq_false_iff.mpr selected
    by_cases available : d.match_available = 0
    · obtain ⟨after, result, run, contentA, frontierA, buffersA, frameA, startA, lookA,
          endpoint, strictA, _storage⟩ :=
        slow_defer_search_boundary cut buffers lookahead branch available strict flush st head
      have readyA := ready.slow frameA
      apply decision_result_of_output (full := false) (test := false) (nextHead := head) (produced := 0)
        ?_ contentA frontierA buffersA (stream_accounting_zero z) (clear.slow frameA)
        (ConfigFrame.slow frameA) readyA.2.2 (fun _ => readyA) strictA ?_ ?_ endpoint
        (Nat.le_refl _) (fun _ => rfl)
      · simpa only [decisionNext, Bool.false_and, Bool.false_eq_true, ite_false] using run
      · rw [startA]; omega
      · rw [lookA]; omega
    · obtain ⟨after, result, run, contentA, frontierA, buffersA, frameA, startA, lookA,
          endpoint, strictA, _storage⟩ :=
        slow_literal_search_boundary cut buffers lookahead branch available space flush st head
      have readyA := ready.slow frameA
      apply decision_result_of_output (full := false) (test := true) (nextHead := head) (produced := 0)
        ?_ contentA frontierA buffersA (stream_accounting_zero z) (clear.slow frameA)
        (ConfigFrame.slow frameA) readyA.2.2 (fun _ => readyA) strictA ?_ ?_ endpoint
        (Nat.le_refl _) ?_
      · simpa only [decisionNext, Bool.true_and] using run
      · rw [startA]; omega
      · rw [lookA]; omega
      · intro impossible; cases impossible

theorem default_foreign_slow_decision_all {h : Heap} {r : ZStreamRef} {ds w owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (cut : SearchBoundary h r ds z d input origin base xs w wa)
    (buffers : StreamBuffers h r) (lookahead : 1 ≤ d.lookahead.toNat)
    (strict : d.sym_next.toNat < d.sym_end.toNat)
    (positive : 0 < d.level.toInt) (pointer : z.next_out = .ref (.dstate_depth owner) oo)
    (cursor : d.pending_out = d.pending_buf) (memory : d.lit_bufsize.toNat = 16384)
    (comparisonRoom : d.strstart.toNat + 262 ≤ d.window_size.toNat)
    (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7) (clear : BlockInit.BlockClear d)
    (flush : Int32) (st : LoopS) (head : UInt32) :
    Nonempty (DecisionResult h r ds z d input origin base flush st head) := by
  have initialReady : PublishReady d := ⟨pending, cursor, by omega⟩
  by_cases selected : (d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length) = true
  · by_cases full : (d.sym_next + 3 == d.sym_end) = true
    · obtain ⟨produced, candidate, after, z', result, _before, _written, _remaining, _kind, _body,
          run, contentA, frontierA, buffersA, accountA, clearA, configA, startA, lookA, endpoint,
          strictA, _smallA, bitsA, phaseA, _cursorA, _rest⟩ :=
        default_foreign_slow_match_full_encoding cut buffers selected strict full positive pointer memory initialReady clear comparisonRoom flush st head
      have previous : 3 ≤ d.prev_length.toNat := by
        have guard := selected
        simp only [Bool.and_eq_true, decide_eq_true_eq] at guard
        exact UInt32.le_iff_toNat_le.mp guard.1
      apply decision_result_of_output (full := true) (test := true) (nextHead := candidate)
        ?_ contentA frontierA buffersA accountA clearA configA bitsA phaseA strictA
        ?_ ?_ endpoint (Nat.le_add_right _ _) ?_
      · simpa only [decisionNext, Bool.true_and] using run
      · rw [startA]; omega
      · rw [lookA]; omega
      · intro impossible; cases impossible
    · have enough := literal_room cut.good.inv strict
      obtain ⟨_, _, trees, _, _⟩ := cut.symbols
      have count : (d.sym_next + 3).toNat = d.sym_next.toNat + 3 := literal_count trees.base enough 0
      have space : d.sym_next.toNat + 3 < d.sym_end.toNat := by
        have different : d.sym_next.toNat + 3 ≠ d.sym_end.toNat := by
          intro equal
          have same : d.sym_next + 3 = d.sym_end := UInt32.toNat_inj.mp (count.trans equal)
          exact full (beq_iff_eq.mpr same)
        omega
      exact default_foreign_slow_decision_nonfull cut buffers lookahead space initialReady clear flush st head
  · have branch := Bool.eq_false_iff.mpr selected
    by_cases available : d.match_available = 0
    · obtain ⟨after, result, run, boundaryA, frontierA, buffersA, frameA, startA, lookA, endpoint, strictA, _storage⟩ :=
        slow_defer_search_boundary cut buffers lookahead branch available strict flush st head
      have readyA := initialReady.slow frameA
      apply decision_result_of_output (full := false) (test := false) (nextHead := head) (produced := 0)
        ?_ boundaryA frontierA buffersA (stream_accounting_zero z) (clear.slow frameA)
        (ConfigFrame.slow frameA) readyA.2.2 (fun _ => readyA) strictA ?_ ?_ endpoint (Nat.le_refl _) (fun _ => rfl)
      · simpa only [decisionNext, Bool.false_and, Bool.false_eq_true, ite_false] using run
      · rw [startA]; omega
      · rw [lookA]; omega
    · have room := literal_room cut.good.inv strict
      by_cases full : d.sym_next.toNat + 3 = d.sym_end.toNat
      · obtain ⟨produced, after, z', result, _before, _written, _remaining, _kind, _body,
            run, boundaryA, frontierA, buffersA, accountA, clearA, startA, lookA, endpoint,
            strictA, configA, lowA, phaseA, _cursorA, _smallA, _rest⟩ :=
          default_foreign_slow_literal_full_search_boundary cut buffers lookahead branch available full positive pointer
            cursor memory comparisonRoom pending bits clear flush st head
        apply decision_result_of_output (full := true) (test := true) (nextHead := head) (produced := produced)
          ?_ boundaryA frontierA buffersA accountA clearA configA lowA phaseA strictA ?_ ?_ endpoint (Nat.le_add_right _ _) ?_
        · simpa only [decisionNext, Bool.true_and] using run
        · rw [startA]; omega
        · rw [lookA]; omega
        · intro impossible; cases impossible
      · have space : d.sym_next.toNat + 3 < d.sym_end.toNat := by omega
        obtain ⟨after, result, run, boundaryA, frontierA, buffersA, frameA, startA, lookA, endpoint, strictA, _storage⟩ :=
          slow_literal_search_boundary cut buffers lookahead branch available space flush st head
        have readyA := initialReady.slow frameA
        apply decision_result_of_output (full := false) (test := true) (nextHead := head) (produced := 0)
          ?_ boundaryA frontierA buffersA (stream_accounting_zero z) (clear.slow frameA)
          (ConfigFrame.slow frameA) readyA.2.2 (fun _ => readyA) strictA ?_ ?_ endpoint (Nat.le_refl _) ?_
        · simpa only [decisionNext, Bool.true_and] using run
        · rw [startA]; omega
        · rw [lookA]; omega
        · intro impossible; cases impossible

end Zlib.Deflate.Engine.Proofs
