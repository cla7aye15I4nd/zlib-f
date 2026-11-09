import ZlibF.Proof.«deflate.c.engine.body-size-history»
import ZlibF.Proof.«deflate.c.engine.body-ready-phase»

/-! # Actual complete slow loops preserve the block-cost history facts -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false
set_option maxRecDepth 10000

/-- Every iteration of the actual loop retains short-match quality on
the current ledger and the negative-source floor. Refill and every full
publication participate in the same induction. The loop run is supplied
by its existing actual termination proof, not by a callee contract.
Whole public-call framing, accepted-input/output cost accumulation and
the utility history remain separate composition steps. -/
theorem slow_loop_run_size_facts {h after : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d result : DeflateState} {input : Nat → UInt8} {xs ys : List Symbol} {config : EngineConfig}
    {final : LoopS} {flush : Int32}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (window : config.windowBits = 15)
    (publish : PublishReady d) (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (candidate : ShortCandidateQuality d) (floor : StoredSourceFloor d)
    (quality : ∀ s ∈ xs, s.distance ≠ 0 → s.value = 0 → s.distance ≤ 4096)
    (observed : cwhile forever (deflate_slow_body (some (.tab ds)) flush) {} h = .ok (final, after))
    (live : after.dstates ds = some result) (symbols : SymbolBoundary after ds result ys) :
    ShortCandidateQuality result ∧ StoredSourceFloor result ∧
      (∀ s ∈ ys, s.distance ≠ 0 → s.value = 0 → s.distance ≤ 4096) := by
  let Inv : LoopS → Heap → Prop := fun st heap =>
    ∃ currentZ currentD currentInput currentOrigin currentBase currentSymbols offset,
      StrategyBoundary heap r ds currentZ currentD currentInput currentOrigin currentBase currentSymbols config ∧
      EndFrontier heap currentD ∧ StreamBuffers heap r ∧ currentZ.next_out = .ref (.blk ob) offset ∧
      (currentZ.avail_in ≠ 0 → currentZ.next_in ≠ .null) ∧
      (st.ret = none → PublishReady currentD) ∧ ShortCandidateQuality currentD ∧ StoredSourceFloor currentD ∧
      (∀ s ∈ currentSymbols, s.distance ≠ 0 → s.value = 0 → s.distance ≤ 4096)
  have step : ∀ st heap, Inv st heap → st.brk = false → st.ret = none →
      ∀ next middle, deflate_slow_body (some (.tab ds)) flush st heap = .ok (next, middle) → Inv next middle := by
    intro st heap inv _notBreak running next middle actual
    obtain ⟨currentZ, currentD, currentInput, currentOrigin, currentBase, currentSymbols, offset,
      state, endS, buffersS, pointerS, validS, readyS, candidateS, floorS, qualityS⟩ := inv
    have known : ∃ used produced expected computed nextZ nextD nextInput nextOrigin nextBase nextSymbols,
        deflate_slow_body (some (.tab ds)) flush st heap = .ok (expected, computed) ∧
        StrategyBoundary computed r ds nextZ nextD nextInput nextOrigin nextBase nextSymbols config ∧
        EndFrontier computed nextD ∧ StreamBuffers computed r ∧ StreamAccounting currentZ nextZ used produced ∧
        (expected.ret = none → PublishReady nextD) := by
      by_cases waiting : flush = Z_NO_FLUSH
      · subst flush
        obtain ⟨used, produced, expected, computed, nextZ, nextD, nextBase, nextSymbols, nextInput, nextOrigin,
          run, stateA, endA, buffersA, accountA, _agrees, _endpoint, _base, _breaks, _returns, readyA, _less, _reason⟩ :=
          slow_no_flush_ready_step state endS buffersS positive pointerS memory wrap (readyS running) validS st
        exact ⟨used, produced, expected, computed, nextZ, nextD, nextInput, nextOrigin, nextBase, nextSymbols,
          run, stateA, endA, buffersA, accountA, readyA⟩
      · obtain ⟨used, produced, expected, computed, nextZ, nextD, nextBase, nextSymbols, nextInput, nextOrigin,
          run, stateA, endA, buffersA, accountA, _agrees, _endpoint, _base, _reason, _returns, readyA, _less, _breaks⟩ :=
          slow_finish_ready_step state endS buffersS positive pointerS memory wrap (readyS running) validS st
        refine ⟨used, produced, expected, computed, nextZ, nextD, nextInput, nextOrigin, nextBase, nextSymbols,
          ?_, stateA, endA, buffersA, accountA, readyA⟩
        rw [slow_positive_body_source _ _ waiting _]
        exact run
    obtain ⟨used, produced, expected, computed, nextZ, nextD, nextInput, nextOrigin, nextBase, nextSymbols,
      run, stateA, endA, buffersA, accountA, readyA⟩ := known
    have width : currentD.w_bits = 15 := (congrArg EngineConfig.windowBits state.configuration).trans window
    have windowS : currentD.w_size.toNat = 32768 := by rw [state.good.inv.wsize, width]; rfl
    obtain ⟨candidateA, floorA, qualityA⟩ := slow_body_run_size_facts state endS buffersS positive pointerS memory wrap
      windowS (readyS running) validS candidateS floorS qualityS run stateA.good.live.hs stateA.symbols
    have pair := Prod.mk.inj (Except.ok.inj (run.symm.trans actual))
    rw [← pair.1, ← pair.2]
    have pointerA : nextZ.next_out = .ref (.blk ob) (offset + produced) := by
      rw [accountA.2.2.2.2.2.1, pointerS]
      rfl
    exact ⟨nextZ, nextD, nextInput, nextOrigin, nextBase, nextSymbols, offset + produced,
      stateA, endA, buffersA, pointerA, input_valid_accounting_output validS accountA,
      readyA, candidateA, floorA, qualityA⟩
  have initial : Inv {} h := ⟨z, d, input, origin, base, xs, oo, boundary, frontier, buffers, pointer,
    inputValid, fun _ => publish, candidate, floor, quality⟩
  have post := forever_run_invariant Inv (deflate_slow_body (some (.tab ds)) flush) step initial observed
  obtain ⟨_currentZ, currentD, _currentInput, _currentOrigin, _currentBase, currentSymbols, _offset,
    state, _end, _buffers, _pointer, _valid, _ready, candidateA, floorA, qualityA⟩ := post
  have stateEq : currentD = result := Option.some.inj (state.good.live.hs.symm.trans live)
  rw [stateEq] at state candidateA floorA
  have symbolsEq : currentSymbols = ys := symbol_boundary_symbols_unique state.symbols symbols
  rw [symbolsEq] at qualityA
  exact ⟨candidateA, floorA, qualityA⟩

end Zlib.Deflate.Engine.Proofs
