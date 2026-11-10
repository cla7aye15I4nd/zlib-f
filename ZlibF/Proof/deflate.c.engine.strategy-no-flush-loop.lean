import ZlibF.Proof.«deflate.c.engine.strategy-refill»
import ZlibF.Proof.«deflate.c.engine.loops»

/-! # The complete NO_FLUSH strategy loop including full block output -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Input-pointer validity is independent of simultaneous output. -/
theorem input_valid_accounting_output {z z' : ZStream} {used produced : Nat}
    (valid : z.avail_in ≠ 0 → z.next_in ≠ .null) (account : StreamAccounting z z' used produced) :
    z'.avail_in ≠ 0 → z'.next_in ≠ .null := by
  intro nonempty
  have oldNonempty : z.avail_in ≠ 0 := by
    intro zero
    have count := account.2.2.1
    rw [zero] at count
    simp only [show (0 : UInt32).toNat = 0 from rfl] at count
    have empty : z'.avail_in.toNat = 0 := by omega
    exact nonempty (UInt32.toNat_inj.mp empty)
  cases pointer : z.next_in with
  | null => exact False.elim (valid oldNonempty pointer)
  | ref ref off =>
    rw [account.2.2.2.2.1, pointer]
    simp only [advance, ne_eq, reduceCtorEq, not_false_eq_true]

set_option maxHeartbeats 3000000 in
/-- `local block_state deflate_slow(deflate_state *s, int flush)`.
A complete actual NO_FLUSH call for the initialized default-memory slow
strategy, including any number of full stored/fixed/dynamic block flushes,
refills, pending insertion and window slides. No input/symbol byte-budget
premise excludes full blocks. The strategy boundary, exact accepted and
delivered counts and logical input endpoint survive on the returned heap.
This is an internal strategy result. Wrapper ownership/frame and complete
emitted-block format history are separate obligations. -/
theorem deflate_slow_no_flush_full {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (buffers : StreamBuffers h r) (positive : 0 < config.level.toInt)
    (pointer : z.next_out = .ref (.blk ob) oo) (memory : config.memory.toNat = 16384)
    (wrap : config.wrap = 1) (output : 0 < z.avail_out.toNat)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ used produced after z' result base' ys extended nextOrigin,
      deflate_slow (some (.tab ds)) Z_NO_FLUSH h = .ok (need_more, after) ∧
      StrategyBoundary after r ds z' result extended nextOrigin base' ys config ∧
      StreamBuffers after r ∧ StreamAccounting z z' used produced ∧
      (∀ i, i < origin + fillEnd d → extended i = input i) ∧
      nextOrigin + fillEnd result = origin + fillEnd d + used ∧ base ≤ base' ∧
      ((z'.avail_in = 0 ∧ result.lookahead.toNat < 262) ∨ z'.avail_out = 0) ∧
      (0 < z'.avail_out.toNat → used = z.avail_in.toNat) := by
  let startEnd := origin + fillEnd d
  let Inv : LoopS → Heap → Prop := fun st heap =>
    ∃ currentZ currentD currentInput currentOrigin currentBase ys accepted delivered,
      StrategyBoundary heap r ds currentZ currentD currentInput currentOrigin currentBase ys config ∧
      StreamBuffers heap r ∧ StreamAccounting z currentZ accepted delivered ∧
      currentOrigin + fillEnd currentD = startEnd + accepted ∧
      (∀ i, i < startEnd → currentInput i = input i) ∧ base ≤ currentBase ∧
      (currentZ.avail_in ≠ 0 → currentZ.next_in ≠ .null) ∧ st.brk = false ∧
      (st.ret = none ∨ st.ret = some need_more) ∧ (st.ret = none → 0 < currentZ.avail_out.toNat) ∧
      (st.ret = some need_more → (currentZ.avail_in = 0 ∧ currentD.lookahead.toNat < 262) ∨ currentZ.avail_out = 0)
  let rank : LoopS → Heap → Nat := fun st heap => if st.ret.isSome then 0 else
    ((heap.dstates ds).map (fun state => state.lookahead.toNat)).getD 0 +
      ((r.get heap).map (fun stream => stream.avail_in.toNat)).getD 0 + 1
  let Q : LoopS → Heap → Prop := fun st heap => Inv st heap ∧ st.ret = some need_more
  have step : ∀ st heap, Inv st heap → ∃ c st1 heap1,
      forever st heap = .ok ((c, st1), heap1) ∧ (c = false → Q st1 heap1) ∧
      (c = true → ∃ st2 heap2, deflate_slow_body (some (.tab ds)) Z_NO_FLUSH st1 heap1 = .ok (st2, heap2) ∧
        Inv st2 heap2 ∧ rank st2 heap2 < rank st heap) := by
    intro st heap inv
    have initialInv := inv
    obtain ⟨currentZ, currentD, currentInput, currentOrigin, currentBase, ys, accepted, delivered,
      state, buffersS, accountS, endpointS, agreesS, baseS, validS, brkS, retS, outputS, _stopS⟩ := inv
    refine ⟨!(st.brk || st.ret.isSome), st, heap, rfl, ?_, ?_⟩
    · intro stopped
      have returned : st.ret = some need_more := by
        rcases retS with running | returned
        · simp [brkS, running] at stopped
        · exact returned
      exact ⟨initialInv, returned⟩
    · intro continued
      have running : st.ret = none := by
        rcases retS with running | returned
        · exact running
        · simp [brkS, returned] at continued
      have pointerS : currentZ.next_out = .ref (.blk ob) (oo + delivered) := by
        rw [accountS.2.2.2.2.2.1, pointer]
        rfl
      obtain ⟨used, produced, next, after, nextZ, result, nextBase, nextYs, nextInput, nextOrigin,
        bodyRun, stateA, buffersA, accountA, agreesA, endpointA, baseA, brkA, retA, outputA, decrease, reasonA⟩ :=
        slow_no_flush_strategy_step state buffersS positive pointerS memory wrap (outputS running) validS st
      have retNext : next.ret = none ∨ next.ret = some need_more := by
        rcases retA with same | returned
        · exact Or.inl (same.trans running)
        · exact Or.inr returned
      have agrees : ∀ i, i < startEnd → nextInput i = input i := by
        intro i before
        exact (agreesA i (by omega)).trans (agreesS i before)
      have stopA : next.ret = some need_more →
          (nextZ.avail_in = 0 ∧ result.lookahead.toNat < 262) ∨ nextZ.avail_out = 0 := by
        intro returned
        rcases reasonA returned with old | stop
        · rw [running] at old; cases old
        · exact stop
      have account := stream_accounting_trans accountS accountA
      have nextInv : Inv next after :=
        ⟨nextZ, result, nextInput, nextOrigin, nextBase, nextYs, accepted + used, delivered + produced,
          stateA, buffersA, account, by omega, agrees, Nat.le_trans baseS baseA,
          input_valid_accounting_output validS accountA, brkA.trans brkS, retNext, outputA, stopA⟩
      refine ⟨next, after, bodyRun, nextInv, ?_⟩
      have beforeRank : rank st heap = currentD.lookahead.toNat + currentZ.avail_in.toNat + 1 := by
        simp [rank, running, state.good.live.hs, state.good.live.hz]
      rw [beforeRank]
      rcases retNext with nextRunning | returned
      · have afterRank : rank next after = result.lookahead.toNat + nextZ.avail_in.toNat + 1 := by
          simp [rank, nextRunning, stateA.good.live.hs, stateA.good.live.hz]
        rw [afterRank]
        have less := decrease nextRunning
        omega
      · simp [rank, returned]
  have initial : Inv {} h :=
    ⟨z, d, input, origin, base, xs, 0, 0, boundary, buffers, stream_accounting_zero z,
      by simp [startEnd], fun _ _ => rfl, Nat.le_refl _, inputValid, rfl, Or.inl rfl, fun _ => output, fun impossible => by cases impossible⟩
  have bound : rank {} h < fuel := by
    have remaining := remaining_below_fuel boundary.toContentBoundary
    simpa [rank, boundary.good.live.hs, boundary.good.live.hz] using remaining
  obtain ⟨final, after, loop, finalInv, returned⟩ := while_heap_rank Inv rank Q step initial bound
  obtain ⟨z', result, extended, nextOrigin, base', ys, used, produced, stateA, buffersA, accountA,
    endpointA, agreesA, baseA, _validA, _brkA, _retA, _outputA, stopA⟩ := finalInv
  refine ⟨used, produced, after, z', result, base', ys, extended, nextOrigin,
    ?_, stateA, buffersA, accountA, agreesA, endpointA, baseA, stopA returned, ?_⟩
  · unfold deflate_slow
    rw [bind_app, loop]
    simp only [returned]
    rfl
  · intro space
    rcases stopA returned with ⟨empty, _⟩ | empty
    · have count := accountA.2.2.1
      rw [empty] at count
      simpa only [show (0 : UInt32).toNat = 0 from rfl, Nat.zero_add] using count
    · rw [empty] at space
      change 0 < 0 at space
      omega

end Zlib.Deflate.Engine.Proofs
