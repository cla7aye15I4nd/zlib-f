import ZlibF.Proof.«deflate.c.engine.match-counted-size»
import ZlibF.Proof.«deflate.c.engine.literal-full-byte-count»

/-! # Each actual slow decision pays for zero or one full block -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false
set_option maxRecDepth 10000

private theorem content_base_unique {h : Heap} {r : ZStreamRef} {ds origin a b : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs ys : List Symbol}
    (left : ContentBoundary h r ds z d input origin a xs)
    (right : ContentBoundary h r ds z d input origin b ys) : a = b := by
  have symbols := symbol_boundary_symbols_unique left.symbols right.symbols
  have first := left.accounted
  have second := right.accounted
  rw [symbols] at first
  omega

private theorem transfer_decision_count {h middle : Heap} {r : ZStreamRef} {ds origin base base' amount blocks : Nat}
    {z z' : ZStream} {d result : DeflateState} {input : Nat → UInt8} {ys : List Symbol}
    {flush : Int32} {st next : LoopS} {head : UInt32}
    (decision : DecisionResult h r ds z d input origin base flush st head)
    (actual : slowDecision (some (.tab ds)) flush st head h = .ok (next, middle))
    (boundary : ContentBoundary middle r ds z' result input origin base' ys)
    (account : StreamAccounting z z' 0 amount) (count : blocks ≤ 1)
    (inputCost : 16383 * blocks ≤ base' - base)
    (outputCost : amount + result.pending.toNat + (result.bi_valid.toInt.toNat + 7) / 8 ≤
      (d.bi_valid.toInt.toNat + 7) / 8 + (base' - base) + 5 * blocks) :
    ∃ k, k ≤ 1 ∧ 16383 * k ≤ decision.blockBase - base ∧
      decision.produced + decision.state.pending.toNat + (decision.state.bi_valid.toInt.toNat + 7) / 8 ≤
        (d.bi_valid.toInt.toNat + 7) / 8 + (decision.blockBase - base) + 5 * k := by
  have pair := Prod.mk.inj (Except.ok.inj (actual.symm.trans decision.run))
  rw [pair.2] at boundary
  have streams : z' = decision.stream := Option.some.inj (boundary.good.live.hz.symm.trans decision.boundary.good.live.hz)
  have states : result = decision.state := Option.some.inj (boundary.good.live.hs.symm.trans decision.boundary.good.live.hs)
  rw [streams, states] at boundary
  have bases : base' = decision.blockBase := content_base_unique boundary decision.boundary
  rw [streams] at account
  have amounts : amount = decision.produced := by
    have first := account.2.2.2.1
    have second := decision.accounting.2.2.2.1
    omega
  exact ⟨blocks, count, by rwa [← bases], by rwa [← amounts, ← states, ← bases]⟩

/-- A real decision emits either no block, or one full symbol block.
Every counted block represents at least 16383 input bytes. The output
potential includes the bytes already published plus all remaining bits.
All branch costs come from actual executions, including the two full
buffer branches. This is one step of the whole-loop cost induction. -/
theorem slow_decision_run_counted_size {h : Heap} {r : ZStreamRef} {ds w ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    {flush : Int32} {st : LoopS} {head : UInt32}
    (cut : SearchBoundary h r ds z d input origin base xs w wa) (buffers : StreamBuffers h r)
    (lookahead : 1 ≤ d.lookahead.toNat) (strict : d.sym_next.toNat < d.sym_end.toNat)
    (positive : 0 < d.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (cursor : d.pending_out = d.pending_buf) (memory : d.lit_bufsize.toNat = 16384)
    (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7) (clear : BlockInit.BlockClear d)
    (strategy : d.strategy = Z_DEFAULT_STRATEGY) (previous : PreviousShortQuality d) (floor : StoredSourceFloor d)
    (quality : ∀ s ∈ xs, s.distance ≠ 0 → s.value = 0 → s.distance ≤ 4096)
    (decision : DecisionResult h r ds z d input origin base flush st head) :
    ∃ k, k ≤ 1 ∧ 16383 * k ≤ decision.blockBase - base ∧
      decision.produced + decision.state.pending.toNat + (decision.state.bi_valid.toInt.toNat + 7) / 8 ≤
        (d.bi_valid.toInt.toNat + 7) / 8 + (decision.blockBase - base) + 5 * k := by
  by_cases selected : (d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length) = true
  · by_cases full : (d.sym_next + 3 == d.sym_end) = true
    · obtain ⟨amount, nextHead, middle, z', result, run, boundary, account, large, cost⟩ :=
        slow_match_full_counted_size cut buffers selected strict full positive pointer cursor memory strategy pending bits
          clear previous floor quality flush st head
      apply transfer_decision_count decision run boundary account (blocks := 1) (by decide)
      · simpa only [Nat.mul_one, Nat.add_sub_cancel_left] using large
      · simpa only [Nat.mul_one, Nat.add_sub_cancel_left] using cost
    · obtain ⟨answer, middle, result, emitRun, boundary, _frontier, _buffers, frame, _available,
        _start, _look, _endpoint, _count, _endCount, _storage⟩ :=
        slow_match_emit_search_boundary cut buffers selected strict head
      have nofull : (d.sym_next + 3 == d.sym_end) = false := Bool.eq_false_iff.mpr full
      have run : slowDecision (some (.tab ds)) flush st head h =
          .ok ({ st with hash_head := answer, bflush := false }, middle) := by
        rw [slow_decision_match_source cut.good.live.hs selected flush st head]
        simp only [bind_app, emitRun, nofull, Bool.false_eq_true, ite_false, pure_app]
      apply transfer_decision_count decision run boundary (stream_accounting_zero z) (blocks := 0) (by decide)
      · simp
      · rw [show result.pending = 0 from by rw [frame]; exact pending]
        rw [show result.bi_valid = d.bi_valid from by rw [frame]]
        simp
  · have branch := Bool.eq_false_iff.mpr selected
    by_cases available : d.match_available = 0
    · obtain ⟨middle, result, run, boundary, _frontier, _buffers, frame, _start, _look,
        _endpoint, _strict, _storage⟩ :=
        slow_defer_search_boundary cut buffers lookahead branch available strict flush st head
      apply transfer_decision_count decision run boundary (stream_accounting_zero z) (blocks := 0) (by decide)
      · simp
      · rw [show result.pending = 0 from by rw [frame]; exact pending]
        rw [show result.bi_valid = d.bi_valid from by rw [frame]]
        simp
    · have room := literal_room cut.good.inv strict
      by_cases full : d.sym_next.toNat + 3 = d.sym_end.toNat
      · obtain ⟨amount, middle, z', result, run, boundary, account, large, cost⟩ :=
          slow_literal_full_search_byte_count cut buffers lookahead branch available full positive pointer cursor
            memory pending bits clear strategy floor quality flush st head
        apply transfer_decision_count decision run boundary account (blocks := 1) (by decide)
        · simpa only [Nat.mul_one, Nat.add_sub_cancel_left] using large
        · simpa only [Nat.mul_one, Nat.add_sub_cancel_left] using cost
      · have space : d.sym_next.toNat + 3 < d.sym_end.toNat := by omega
        obtain ⟨middle, result, run, boundary, _frontier, _buffers, frame, _start, _look,
          _endpoint, _strict, _storage⟩ :=
          slow_literal_search_boundary cut buffers lookahead branch available space flush st head
        apply transfer_decision_count decision run boundary (stream_accounting_zero z) (blocks := 0) (by decide)
        · simp
        · rw [show result.pending = 0 from by rw [frame]; exact pending]
          rw [show result.bi_valid = d.bi_valid from by rw [frame]]
          simp

end Zlib.Deflate.Engine.Proofs
