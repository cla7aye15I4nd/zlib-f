import ZlibF.Proof.«deflate.c.engine.finish-strategy-progress»
import ZlibF.Proof.«deflate.c.engine.strategy-finish-loop»

/-! # A FINISH loop stopped by output exhaustion has consumed work -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false
set_option maxHeartbeats 3000000 in
/-- The complete actual loop preserves its input snapshot and terminates.
A need_more return strictly reduces unread input plus lookahead, even if
it occurs on the first iteration. This is progress across output retries,
not only termination of iterations inside one call. -/
theorem slow_finish_loop_progress {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (output : 0 < z.avail_out.toNat)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ used produced final after z' result base' ys extended nextOrigin,
      cwhile forever (deflate_slow_body (some (.tab ds)) Z_FINISH) {} h = .ok (final, after) ∧
      StrategyBoundary after r ds z' result extended nextOrigin base' ys config ∧ EndFrontier after result ∧
      StreamBuffers after r ∧ StreamAccounting z z' used produced ∧
      (∀ i, i < origin + fillEnd d → extended i = input i) ∧
      nextOrigin + fillEnd result = origin + fillEnd d + used ∧ base ≤ base' ∧
      (final.ret = some need_more ∨ (final.ret = none ∧ final.brk = true)) ∧
      (final.ret = some need_more → z'.avail_out = 0) ∧
      (final.brk = true → result.lookahead = 0 ∧ z'.avail_in = 0) ∧
      (final.ret = none → 0 < z'.avail_out.toNat) ∧
      (final.ret = some need_more →
        result.lookahead.toNat + z'.avail_in.toNat < d.lookahead.toNat + z.avail_in.toNat) := by
  let startEnd := origin + fillEnd d
  let Inv : LoopS → Heap → Prop := fun st heap =>
    ∃ currentZ currentD currentInput currentOrigin currentBase ys accepted delivered,
      StrategyBoundary heap r ds currentZ currentD currentInput currentOrigin currentBase ys config ∧
      EndFrontier heap currentD ∧ StreamBuffers heap r ∧ StreamAccounting z currentZ accepted delivered ∧
      currentOrigin + fillEnd currentD = startEnd + accepted ∧
      (∀ i, i < startEnd → currentInput i = input i) ∧ base ≤ currentBase ∧
      (currentZ.avail_in ≠ 0 → currentZ.next_in ≠ .null) ∧
      (st.ret = none ∨ st.ret = some need_more) ∧ (st.ret = none → 0 < currentZ.avail_out.toNat) ∧
      (st.ret = some need_more → currentZ.avail_out = 0) ∧
      (st.brk = true → currentD.lookahead = 0 ∧ currentZ.avail_in = 0) ∧
      currentD.lookahead.toNat + currentZ.avail_in.toNat ≤ d.lookahead.toNat + z.avail_in.toNat ∧
      (st.ret = some need_more →
        currentD.lookahead.toNat + currentZ.avail_in.toNat < d.lookahead.toNat + z.avail_in.toNat)
  let rank : LoopS → Heap → Nat := fun st heap => if st.brk || st.ret.isSome then 0 else
    ((heap.dstates ds).map (fun state => state.lookahead.toNat)).getD 0 +
      ((r.get heap).map (fun stream => stream.avail_in.toNat)).getD 0 + 1
  let Q : LoopS → Heap → Prop := fun st heap => Inv st heap ∧ (st.ret = some need_more ∨ (st.ret = none ∧ st.brk = true))
  have step : ∀ st heap, Inv st heap → ∃ c st1 heap1,
      forever st heap = .ok ((c, st1), heap1) ∧ (c = false → Q st1 heap1) ∧
      (c = true → ∃ st2 heap2, deflate_slow_body (some (.tab ds)) Z_FINISH st1 heap1 = .ok (st2, heap2) ∧
        Inv st2 heap2 ∧ rank st2 heap2 < rank st heap) := by
    intro st heap inv
    have initialInv := inv
    obtain ⟨currentZ, currentD, currentInput, currentOrigin, currentBase, ys, accepted, delivered,
      state, endS, buffersS, accountS, endpointS, agreesS, baseS, validS, retS, outputS, _stopS, _eofS, remainingS, _strictS⟩ := inv
    refine ⟨!(st.brk || st.ret.isSome), st, heap, rfl, ?_, ?_⟩
    · intro stopped
      refine ⟨initialInv, ?_⟩
      rcases retS with running | returned
      · right
        refine ⟨running, ?_⟩
        cases brkEq : st.brk with
        | false => simp [brkEq, running] at stopped
        | true => rfl
      · exact Or.inl returned
    · intro continued
      have running : st.ret = none := by
        rcases retS with running | returned
        · exact running
        · simp [returned] at continued
      have brkS : st.brk = false := by
        cases brkEq : st.brk with
        | false => rfl
        | true => simp [brkEq] at continued
      have pointerS : currentZ.next_out = .ref (.blk ob) (oo + delivered) := by
        rw [accountS.2.2.2.2.2.1, pointer]
        rfl
      obtain ⟨used, produced, next, after, nextZ, result, nextBase, nextYs, nextInput, nextOrigin,
        bodyRun, stateA, endA, buffersA, accountA, agreesA, endpointA, baseA, reasonA, retA, outputA, decrease, breakA⟩ :=
        slow_finish_strategy_step_progress state endS buffersS positive pointerS memory wrap (outputS running) validS st
      have retNext : next.ret = none ∨ next.ret = some need_more := by
        rcases retA with same | returned
        · exact Or.inl (same.trans running)
        · exact Or.inr returned
      have agrees : ∀ i, i < startEnd → nextInput i = input i := by
        intro i before
        exact (agreesA i (by omega)).trans (agreesS i before)
      have stopA : next.ret = some need_more → nextZ.avail_out = 0 := by
        intro returned
        rcases reasonA returned with old | empty
        · rw [running] at old; cases old
        · exact empty
      have eofA : next.brk = true → result.lookahead = 0 ∧ nextZ.avail_in = 0 := by
        intro broke
        rcases breakA broke with old | eof
        · rw [brkS] at old; cases old
        · exact eof
      have remainingA : result.lookahead.toNat + nextZ.avail_in.toNat ≤
          currentD.lookahead.toNat + currentZ.avail_in.toNat := by
        by_cases broke : next.brk = true
        · obtain ⟨lookZero, inputZero⟩ := eofA broke
          simp only [lookZero, inputZero, UInt32.toNat_zero, Nat.zero_add, Nat.zero_le]
        · have less := decrease (Or.inl (Bool.eq_false_iff.mpr broke))
          omega
      have strictA : next.ret = some need_more → result.lookahead.toNat + nextZ.avail_in.toNat <
          d.lookahead.toNat + z.avail_in.toNat := by
        intro returned
        have less := decrease (Or.inr ⟨running, returned⟩)
        omega
      have account := stream_accounting_trans accountS accountA
      have nextInv : Inv next after :=
        ⟨nextZ, result, nextInput, nextOrigin, nextBase, nextYs, accepted + used, delivered + produced,
          stateA, endA, buffersA, account, by omega, agrees, Nat.le_trans baseS baseA,
          input_valid_accounting_output validS accountA, retNext, outputA, stopA, eofA, by omega, strictA⟩
      refine ⟨next, after, bodyRun, nextInv, ?_⟩
      have beforeRank : rank st heap = currentD.lookahead.toNat + currentZ.avail_in.toNat + 1 := by
        simp [rank, running, brkS, state.good.live.hs, state.good.live.hz]
      rw [beforeRank]
      rcases retNext with nextRunning | returned
      · by_cases broke : next.brk = true
        · simp [rank, broke]
        · have nextBrk : next.brk = false := Bool.eq_false_iff.mpr broke
          have afterRank : rank next after = result.lookahead.toNat + nextZ.avail_in.toNat + 1 := by
            simp [rank, nextRunning, nextBrk, stateA.good.live.hs, stateA.good.live.hz]
          rw [afterRank]
          have less := decrease (Or.inl nextBrk)
          omega
      · simp [rank, returned]
  have initial : Inv {} h :=
    ⟨z, d, input, origin, base, xs, 0, 0, boundary, frontier, buffers, stream_accounting_zero z,
      by simp [startEnd], fun _ _ => rfl, Nat.le_refl _, inputValid, Or.inl rfl, fun _ => output,
      (fun impossible => by cases impossible), (fun impossible => by cases impossible),
      Nat.le_refl _, (fun impossible => by cases impossible)⟩
  have bound : rank {} h < fuel := by
    have remaining := remaining_below_fuel boundary.toContentBoundary
    simpa [rank, boundary.good.live.hs, boundary.good.live.hz] using remaining
  obtain ⟨final, after, loop, finalInv, stopped⟩ := while_heap_rank Inv rank Q step initial bound
  obtain ⟨z', result, extended, nextOrigin, base', ys, used, produced, stateA, endA, buffersA, accountA,
    endpointA, agreesA, baseA, _validA, _retA, outputA, stopA, eofA, _remainingA, strictA⟩ := finalInv
  exact ⟨used, produced, final, after, z', result, base', ys, extended, nextOrigin,
    loop, stateA, endA, buffersA, accountA, agreesA, endpointA, baseA, stopped, stopA, eofA, outputA, strictA⟩


end Zlib.Deflate.Engine.Proofs
