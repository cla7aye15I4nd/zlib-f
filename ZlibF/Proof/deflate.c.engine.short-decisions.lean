import ZlibF.Proof.«deflate.c.engine.short-match-decision»

/-! # All real short-input decisions share the continuing strategy boundary -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The source's optional output-full return test. -/
def decisionNext (st : LoopS) (head : UInt32) (full test : Bool) (output : UInt32) : LoopS :=
  if test && output == 0 then { st with hash_head := head, bflush := full, ret := some need_more }
  else { st with hash_head := head, bflush := full }

/-- Execution evidence returned by a decision, before the next refill.
All data fields and proofs refer to one actual returned heap and stream. -/
structure DecisionResult (h : Heap) (r : ZStreamRef) (ds : Nat) (z : ZStream) (d : DeflateState)
    (input : Nat → UInt8) (origin base : Nat) (flush : Int32) (st : LoopS) (head : UInt32) where
  produced : Nat
  next : LoopS
  after : Heap
  stream : ZStream
  state : DeflateState
  blockBase : Nat
  symbols : List Symbol
  run : slowDecision (some (.tab ds)) flush st head h = .ok (next, after)
  boundary : ContentBoundary after r ds stream state input origin blockBase symbols
  frontier : EndFrontier after state
  buffers : StreamBuffers after r
  accounting : StreamAccounting z stream 0 produced
  clear : BlockInit.BlockClear state
  config : ConfigFrame d state
  bits : state.bi_valid.toInt < 8
  resume : 0 < stream.avail_out.toNat → PublishReady state
  strict : state.sym_next.toNat < state.sym_end.toNat
  progress : d.strstart.toNat < state.strstart.toNat
  less : state.lookahead.toNat < d.lookahead.toNat
  endpoint : fillEnd state = fillEnd d
  base_le : base ≤ blockBase
  brk : next.brk = st.brk
  returns : next.ret = st.ret ∨ next.ret = some need_more
  reason : next.ret = some need_more → st.ret = some need_more ∨ stream.avail_out = 0
  continues : 0 < z.avail_out.toNat → next.ret = none → 0 < stream.avail_out.toNat

/-- Common control consequences of the actual optional output test. -/
theorem decision_result_of_output {h after : Heap} {r : ZStreamRef} {ds origin base base' : Nat}
    {z z' : ZStream} {d result : DeflateState} {input : Nat → UInt8} {ys : List Symbol}
    {flush : Int32} {st : LoopS} {head nextHead : UInt32} {produced : Nat} {full test : Bool}
    (run : slowDecision (some (.tab ds)) flush st head h =
      .ok (decisionNext st nextHead full test z'.avail_out, after))
    (boundary : ContentBoundary after r ds z' result input origin base' ys)
    (frontier : EndFrontier after result) (buffers : StreamBuffers after r)
    (account : StreamAccounting z z' 0 produced) (clear : BlockInit.BlockClear result)
    (config : ConfigFrame d result) (bits : result.bi_valid.toInt < 8)
    (resume : 0 < z'.avail_out.toNat → PublishReady result)
    (strict : result.sym_next.toNat < result.sym_end.toNat)
    (progress : d.strstart.toNat < result.strstart.toNat)
    (less : result.lookahead.toNat < d.lookahead.toNat) (endpoint : fillEnd result = fillEnd d)
    (baseLe : base ≤ base') (unchanged : test = false → z' = z) :
    Nonempty (DecisionResult h r ds z d input origin base flush st head) := by
  let next := decisionNext st nextHead full test z'.avail_out
  refine ⟨⟨produced, next, after, z', result, base', ys, run, boundary, frontier, buffers, account,
    clear, config, bits, resume, strict, progress, less, endpoint, baseLe, ?_, ?_, ?_, ?_⟩⟩
  · dsimp only [next, decisionNext]; split <;> rfl
  · dsimp only [next, decisionNext]; split
    · exact Or.inr rfl
    · exact Or.inl rfl
  · intro returned
    by_cases empty : z'.avail_out = 0
    · exact Or.inr empty
    · left
      have same : next.ret = st.ret := by simp [next, decisionNext, empty]
      exact same.symm.trans returned
  · intro output returned
    by_cases tested : test = true
    · have nonzero : z'.avail_out ≠ 0 := by
        intro zero
        simp [next, decisionNext, tested, zero] at returned
      have bound : z'.avail_out.toNat ≠ 0 := fun zero => nonzero (UInt32.toNat_inj.mp zero)
      omega
    · rw [unchanged (Bool.eq_false_iff.mpr tested)]
      exact output

/-- All three real decisions, full and nonfull, preserve the initialized
content and earlier EOF boundaries with any positive lookahead. Search
has already established the state evidence, including clipped matches. -/
theorem slow_decision_all_search_boundary {h : Heap} {r : ZStreamRef} {ds w ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (cut : SearchBoundary h r ds z d input origin base xs w wa)
    (buffers : StreamBuffers h r) (lookahead : 1 ≤ d.lookahead.toNat)
    (strict : d.sym_next.toNat < d.sym_end.toNat)
    (positive : 0 < d.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (cursor : d.pending_out = d.pending_buf) (memory : d.lit_bufsize.toNat = 16384)
    (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7) (clear : BlockInit.BlockClear d)
    (flush : Int32) (st : LoopS) (head : UInt32) :
    Nonempty (DecisionResult h r ds z d input origin base flush st head) := by
  have initialReady : PublishReady d := ⟨pending, cursor, by omega⟩
  by_cases selected : (d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length) = true
  · obtain ⟨produced, nextHead, after, z', result, base', ys, run, boundaryA, frontierA,
        buffersA, accountA, clearA, startA, lookA, endpoint, strictA, baseLe, configA, lowA, phaseA, unchanged⟩ :=
      slow_match_search_boundary cut buffers selected strict positive pointer cursor memory pending bits clear flush st head
    have previous : 3 ≤ d.prev_length.toNat := by
      have guard := selected
      simp only [Bool.and_eq_true, decide_eq_true_eq] at guard
      exact UInt32.le_iff_toNat_le.mp guard.1
    apply decision_result_of_output (full := d.sym_next + 3 == d.sym_end) (test := d.sym_next + 3 == d.sym_end)
      (nextHead := nextHead) (produced := produced) (z' := z') (result := result) (ys := ys)
      ?_ boundaryA frontierA buffersA accountA clearA configA lowA phaseA strictA ?_ ?_ endpoint baseLe unchanged
    · cases fullFlag : (d.sym_next + 3 == d.sym_end) <;>
        simpa only [decisionNext, fullFlag, Bool.false_eq_true, Bool.false_and, Bool.true_and, ite_false, ite_true] using run
    · rw [startA]; omega
    · rw [lookA]; omega
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
      · obtain ⟨produced, after, z', result, run, boundaryA, frontierA, buffersA, accountA, clearA,
            startA, lookA, endpoint, strictA, configA, lowA, phaseA⟩ :=
          slow_literal_full_search_boundary cut buffers lookahead branch available full positive pointer cursor memory pending bits clear flush st head
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
