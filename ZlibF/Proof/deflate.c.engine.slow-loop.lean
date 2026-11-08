import ZlibF.Proof.«deflate.c.engine.loop-accounting»

/-! # The actual non-flushing slow loop before block output

The byte budget describes the source path that cannot fill its symbol
buffer. It is not a restriction on the public compressor target.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

set_option maxHeartbeats 2500000 in
/-- `local block_state deflate_slow(deflate_state *s, int flush)`.
A complete Z_NO_FLUSH call when the current block's accepted and remaining
bytes fit its real symbol capacity. Every iteration derives tally room
from its ledger. The source loop returns need_more without block output.
The full-buffer path remains a separate implementation obligation.
-/
theorem deflate_slow_no_flush_before_block {h : Heap} {r : ZStreamRef} {ds origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List Symbol}
    (boundary : ContentBoundary h r ds z d input origin base xs)
    (wrap : d.wrap = 1) (buffers : StreamBuffers h r)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (capacity : 3 * (origin + fillEnd d + z.avail_in.toNat - base + 1) < d.sym_end.toNat) :
    ∃ used after z' result ys extended nextOrigin,
      deflate_slow (some (.tab ds)) Z_NO_FLUSH h = .ok (need_more, after) ∧
      ContentBoundary after r ds z' result extended nextOrigin base ys ∧ StreamBuffers after r ∧
      StreamAccounting z z' used 0 ∧ ByteFrame h after (DeflateOwned ds d) ∧ SlowIterationFrame d result ∧
      (∀ i, i < origin + fillEnd d → extended i = input i) ∧ xs <+: ys ∧
      nextOrigin + fillEnd result = origin + fillEnd d + used ∧
      expandSymbols ys (inputPrefix extended base) =
        inputPrefix extended (nextOrigin + result.strstart.toNat - pendingCredit result) ∧
      ((z'.avail_in = 0 ∧ result.lookahead.toNat < 262) ∨ z'.avail_out = 0) ∧
      (z.avail_out ≠ 0 → used = z.avail_in.toNat) := by
  let startEnd := origin + fillEnd d
  let limit := startEnd + z.avail_in.toNat
  let Inv : LoopS → Heap → Prop := fun st heap =>
    ∃ currentZ currentD currentInput currentOrigin ys accepted,
      ContentBoundary heap r ds currentZ currentD currentInput currentOrigin base ys ∧
      StreamBuffers heap r ∧ StreamAccounting z currentZ accepted 0 ∧
      currentOrigin + fillEnd currentD = startEnd + accepted ∧
      (∀ i, i < startEnd → currentInput i = input i) ∧ xs <+: ys ∧
      SlowIterationFrame d currentD ∧ ByteFrame h heap (DeflateOwned ds d) ∧
      (currentZ.avail_in ≠ 0 → currentZ.next_in ≠ .null) ∧ st.brk = false ∧
      (st.ret = none ∨ st.ret = some need_more) ∧
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
    obtain ⟨currentZ, currentD, currentInput, currentOrigin, ys, accepted, boundaryS, buffersS,
      accountS, endpointS, agreesS, symbolsS, fieldsS, storageS, validS, brkS, retS, stopS⟩ := inv
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
      have potential : currentOrigin + fillEnd currentD + currentZ.avail_in.toNat = limit := by
        have inputCount := accountS.2.2.1
        dsimp only [limit]
        omega
      have endSame : currentD.sym_end = d.sym_end := congrArg (·.sym_end) fieldsS
      have room : currentD.sym_next.toNat + 3 < currentD.sym_end.toNat :=
        content_symbol_room boundaryS (limit := limit) (by omega) (by rw [endSame]; exact capacity)
      have wrapS : currentD.wrap = 1 := (congrArg (·.wrap) fieldsS).trans wrap
      obtain ⟨used, next, after, nextZ, result, nextYs, nextInput, nextOrigin, bodyRun, boundaryA, accountA,
        agreesA, endpointA, symbolsA, _, brkA, progress, buffersA, storageA, fieldsA, retA, reasonA⟩ :=
        slow_no_flush_content_buffers_reason boundaryS room wrapS buffersS validS st
      have retNext : next.ret = none ∨ next.ret = some need_more := by
        rcases retA with same | returned
        · exact Or.inl (same.trans running)
        · exact Or.inr returned
      have owned := iteration_owned_frame fieldsS ds
      rw [owned] at storageA
      have agrees : ∀ i, i < startEnd → nextInput i = input i := by
        intro i before
        exact (agreesA i (by omega)).trans (agreesS i before)
      have symbols : xs <+: nextYs := by
        rcases symbolsA with same | ⟨symbol, appended⟩
        · rw [same]
          exact symbolsS
        · rw [appended]
          exact symbolsS.trans (List.prefix_append ys [symbol])
      have stopA : next.ret = some need_more →
          (nextZ.avail_in = 0 ∧ result.lookahead.toNat < 262) ∨ nextZ.avail_out = 0 := by
        intro returned
        rcases reasonA returned with old | stopped
        · rw [running] at old
          cases old
        · exact stopped
      have nextInv : Inv next after :=
        ⟨nextZ, result, nextInput, nextOrigin, nextYs, accepted + used, boundaryA, buffersA,
          stream_accounting_trans_zero accountS accountA, by omega, agrees, symbols,
          fieldsS.trans fieldsA, storageS.trans storageA, input_valid_accounting validS accountA,
          brkA.trans brkS, retNext, stopA⟩
      refine ⟨next, after, bodyRun, nextInv, ?_⟩
      have beforeRank : rank st heap = currentD.lookahead.toNat + currentZ.avail_in.toNat + 1 := by
        simp [rank, running, boundaryS.good.live.hs, boundaryS.good.live.hz]
      rw [beforeRank]
      rcases retNext with nextRunning | returned
      · have advance : currentOrigin + currentD.strstart.toNat < nextOrigin + result.strstart.toNat := by
          rcases progress with returned | advance
          · rw [nextRunning] at returned
            cases returned
          · exact advance
        have inputCount := accountA.2.2.1
        have afterRank : rank next after = result.lookahead.toNat + nextZ.avail_in.toNat + 1 := by
          simp [rank, nextRunning, boundaryA.good.live.hs, boundaryA.good.live.hz]
        rw [afterRank]
        dsimp only [fillEnd] at endpointA
        omega
      · simp [rank, returned]
  have initial : Inv {} h :=
    ⟨z, d, input, origin, xs, 0, boundary, buffers, stream_accounting_zero z,
      by simp [startEnd], fun _ _ => rfl, ⟨[], by simp⟩, rfl, ByteFrame.refl h _, inputValid, rfl, Or.inl rfl, fun impossible => by cases impossible⟩
  have bound : rank {} h < fuel := by
    have remaining := remaining_below_fuel boundary
    simpa [rank, boundary.good.live.hs, boundary.good.live.hz] using remaining
  obtain ⟨final, after, loop, finalInv, returned⟩ := while_heap_rank Inv rank Q step initial bound
  obtain ⟨z', result, extended, nextOrigin, ys, used, boundaryA, buffersA, accountA,
    endpointA, agreesA, symbolsA, fieldsA, storageA, _, _, _, stopA⟩ := finalInv
  refine ⟨used, after, z', result, ys, extended, nextOrigin, ?_, boundaryA, buffersA, accountA,
    storageA, fieldsA, agreesA, symbolsA, endpointA, boundaryA.expands, stopA returned, ?_⟩
  · unfold deflate_slow
    rw [bind_app, loop]
    simp only [returned]
    rfl
  · intro positive
    have output : z'.avail_out = z.avail_out := UInt32.toNat_inj.mp (by
      have count := accountA.2.2.2.1
      omega)
    rcases stopA returned with ⟨empty, _⟩ | empty
    · have count := accountA.2.2.1
      rw [empty] at count
      simpa using count
    · exact False.elim (positive (output.symm.trans empty))

end Zlib.Deflate.Engine.Proofs
