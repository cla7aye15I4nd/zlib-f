import ZlibF.Proof.«deflate.c.engine.body-counted-size»
import ZlibF.Proof.«deflate.c.engine.body-ready-phase»

/-! # Actual complete slow loops accumulate the full-block byte budget -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false
set_option maxRecDepth 10000

/-- Every counted block in the actual complete loop represents at least
16383 bytes. The cumulative output potential includes published bytes and
all pending bits, so output exhaustion does not lose any cost. This is
the actual loop budget; EOF settlement, the final block and the public
wrapper still have to compose on the returned state. -/
theorem slow_loop_run_counted_size {h after : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List Symbol} {config : EngineConfig}
    {final : LoopS} {flush : Int32}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (window : config.windowBits = 15)
    (strategy : config.strategy = Z_DEFAULT_STRATEGY)
    (publish : PublishReady d) (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (candidate : ShortCandidateQuality d) (floor : StoredSourceFloor d)
    (quality : ∀ s ∈ xs, s.distance ≠ 0 → s.value = 0 → s.distance ≤ 4096)
    (observed : cwhile forever (deflate_slow_body (some (.tab ds)) flush) {} h = .ok (final, after)) :
    ∃ used produced blocks z' result extended nextOrigin nextBase ys,
      StrategyBoundary after r ds z' result extended nextOrigin nextBase ys config ∧ EndFrontier after result ∧
      StreamBuffers after r ∧ StreamAccounting z z' used produced ∧
      nextOrigin + fillEnd result = origin + fillEnd d + used ∧ base ≤ nextBase ∧
      (final.ret = none → PublishReady result) ∧
      ShortCandidateQuality result ∧ StoredSourceFloor result ∧
      (∀ s ∈ ys, s.distance ≠ 0 → s.value = 0 → s.distance ≤ 4096) ∧
      16383 * blocks ≤ nextBase - base ∧
      produced + result.pending.toNat + (result.bi_valid.toInt.toNat + 7) / 8 ≤
        (d.bi_valid.toInt.toNat + 7) / 8 + (nextBase - base) + 5 * blocks := by
  let Inv : LoopS → Heap → Prop := fun st heap =>
    ∃ currentZ currentD currentInput currentOrigin currentBase currentSymbols used produced blocks,
      StrategyBoundary heap r ds currentZ currentD currentInput currentOrigin currentBase currentSymbols config ∧
      EndFrontier heap currentD ∧ StreamBuffers heap r ∧ StreamAccounting z currentZ used produced ∧
      currentOrigin + fillEnd currentD = origin + fillEnd d + used ∧ base ≤ currentBase ∧
      (currentZ.avail_in ≠ 0 → currentZ.next_in ≠ .null) ∧
      (st.ret = none → PublishReady currentD) ∧ ShortCandidateQuality currentD ∧ StoredSourceFloor currentD ∧
      (∀ s ∈ currentSymbols, s.distance ≠ 0 → s.value = 0 → s.distance ≤ 4096) ∧
      16383 * blocks ≤ currentBase - base ∧
      produced + currentD.pending.toNat + (currentD.bi_valid.toInt.toNat + 7) / 8 ≤
        (d.bi_valid.toInt.toNat + 7) / 8 + (currentBase - base) + 5 * blocks
  have step : ∀ st heap, Inv st heap → st.brk = false → st.ret = none →
      ∀ next middle, deflate_slow_body (some (.tab ds)) flush st heap = .ok (next, middle) → Inv next middle := by
    intro st heap inv _notBreak running next middle actual
    obtain ⟨currentZ, currentD, currentInput, currentOrigin, currentBase, currentSymbols, used, produced, blocks,
      state, endS, buffersS, accountS, endpointS, baseS, validS, readyS, candidateS, floorS, qualityS,
      minimumS, costS⟩ := inv
    have pointerS : currentZ.next_out = .ref (.blk ob) (oo + produced) := by
      rw [accountS.2.2.2.2.2.1, pointer]; rfl
    have known : ∃ read amount expected computed nextZ nextD nextInput nextOrigin nextBase nextSymbols,
        deflate_slow_body (some (.tab ds)) flush st heap = .ok (expected, computed) ∧
        StrategyBoundary computed r ds nextZ nextD nextInput nextOrigin nextBase nextSymbols config ∧
        EndFrontier computed nextD ∧ StreamBuffers computed r ∧ StreamAccounting currentZ nextZ read amount ∧
        nextOrigin + fillEnd nextD = currentOrigin + fillEnd currentD + read ∧ currentBase ≤ nextBase ∧
        (expected.ret = none → PublishReady nextD) := by
      by_cases waiting : flush = Z_NO_FLUSH
      · subst flush
        obtain ⟨read, amount, expected, computed, nextZ, nextD, nextBase, nextSymbols, nextInput, nextOrigin,
          run, stateA, endA, buffersA, accountA, _agrees, endpointA, baseA, _breaks, _returns, readyA, _less, _reason⟩ :=
          slow_no_flush_ready_step state endS buffersS positive pointerS memory wrap (readyS running) validS st
        exact ⟨read, amount, expected, computed, nextZ, nextD, nextInput, nextOrigin, nextBase, nextSymbols,
          run, stateA, endA, buffersA, accountA, endpointA, baseA, readyA⟩
      · obtain ⟨read, amount, expected, computed, nextZ, nextD, nextBase, nextSymbols, nextInput, nextOrigin,
          run, stateA, endA, buffersA, accountA, _agrees, endpointA, baseA, _reason, _returns, readyA, _less, _breaks⟩ :=
          slow_finish_ready_step state endS buffersS positive pointerS memory wrap (readyS running) validS st
        refine ⟨read, amount, expected, computed, nextZ, nextD, nextInput, nextOrigin, nextBase, nextSymbols,
          ?_, stateA, endA, buffersA, accountA, endpointA, baseA, readyA⟩
        rw [slow_positive_body_source _ _ waiting _]
        exact run
    obtain ⟨read, amount, expected, computed, nextZ, nextD, nextInput, nextOrigin, nextBase, nextSymbols,
      run, stateA, endA, buffersA, accountA, endpointA, baseA, readyA⟩ := known
    have width : currentD.w_bits = 15 := (congrArg EngineConfig.windowBits state.configuration).trans window
    have windowS : currentD.w_size.toNat = 32768 := by rw [state.good.inv.wsize, width]; rfl
    obtain ⟨k, _one, minimumA, costA⟩ := slow_body_run_counted_size state endS buffersS positive pointerS memory wrap
      strategy windowS (readyS running) validS candidateS floorS qualityS run stateA.toContentBoundary accountA endpointA
    obtain ⟨candidateA, floorA, qualityA⟩ := slow_body_run_size_facts state endS buffersS positive pointerS memory wrap
      windowS (readyS running) validS candidateS floorS qualityS run stateA.good.live.hs stateA.symbols
    have pair := Prod.mk.inj (Except.ok.inj (run.symm.trans actual))
    rw [← pair.1, ← pair.2]
    refine ⟨nextZ, nextD, nextInput, nextOrigin, nextBase, nextSymbols, used + read, produced + amount, blocks + k,
      stateA, endA, buffersA, stream_accounting_trans accountS accountA, by omega, Nat.le_trans baseS baseA,
      input_valid_accounting_output validS accountA, readyA, candidateA, floorA, qualityA, ?_, ?_⟩
    · rw [Nat.mul_add]; omega
    · rw [Nat.mul_add]; omega
  have initial : Inv {} h := by
    refine ⟨z, d, input, origin, base, xs, 0, 0, 0, boundary, frontier, buffers, stream_accounting_zero z,
      by simp, Nat.le_refl _, inputValid, fun _ => publish, candidate, floor, quality, by simp, ?_⟩
    rw [publish.1, UInt64.toNat_zero]; simp
  have post := forever_run_invariant Inv (deflate_slow_body (some (.tab ds)) flush) step initial observed
  obtain ⟨currentZ, currentD, currentInput, currentOrigin, currentBase, currentSymbols, used, produced, blocks,
    state, endS, buffersS, accountS, endpointS, baseS, _validS, readyS, candidateS, floorS, qualityS, minimumS, costS⟩ := post
  exact ⟨used, produced, blocks, currentZ, currentD, currentInput, currentOrigin, currentBase, currentSymbols,
    state, endS, buffersS, accountS, endpointS, baseS, readyS, candidateS, floorS, qualityS, minimumS, costS⟩

end Zlib.Deflate.Engine.Proofs
