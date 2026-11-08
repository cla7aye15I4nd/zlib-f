import ZlibF.Proof.«deflate.c.engine.loop-output-interval»

/-! # Reusing the actual terminating loop for every flushing request -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The translated slow loop distinguishes only NO_FLUSH from the other
requests. The tail and public markers still depend on the precise flag. -/
theorem slow_positive_body_source (s : DeflateStatePtr) (flush : Int32)
    (nonzero : flush ≠ Z_NO_FLUSH) (st : LoopS) :
    deflate_slow_body s flush st = deflate_slow_body s Z_FINISH st := by
  simp only [slow_body_source, beq_eq_false_iff_ne.mpr nonzero,
    show (Z_FINISH == Z_NO_FLUSH) = false from by decide,
    Bool.and_false, Bool.false_eq_true, ite_false]
  rfl

/-- This equality includes every refill, decision, nonfinal block and
early output return, but deliberately stops before the flag-specific tail. -/
theorem slow_positive_loop_source (s : DeflateStatePtr) (flush : Int32)
    (nonzero : flush ≠ Z_NO_FLUSH) (st : LoopS) :
    cwhile forever (deflate_slow_body s flush) st =
      cwhile forever (deflate_slow_body s Z_FINISH) st := by
  have body : deflate_slow_body s flush = deflate_slow_body s Z_FINISH :=
    funext (slow_positive_body_source s flush nonzero)
  rw [body]

/-- Every nonzero flush has the already established terminating loop.
The initialized default-memory boundary supplies actual callee proofs;
no successful run or callee specification is assumed. The flag-specific
EOF tail and the public flush marker are separate obligations. -/
theorem slow_positive_ready_loop {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (flush : Int32) (nonzero : flush ≠ Z_NO_FLUSH) :
    ∃ used produced final after z' result base' ys extended nextOrigin,
      cwhile forever (deflate_slow_body (some (.tab ds)) flush) {} h = .ok (final, after) ∧
      StrategyBoundary after r ds z' result extended nextOrigin base' ys config ∧ EndFrontier after result ∧
      StreamBuffers after r ∧ StreamAccounting z z' used produced ∧
      (∀ i, i < origin + fillEnd d → extended i = input i) ∧
      nextOrigin + fillEnd result = origin + fillEnd d + used ∧ base ≤ base' ∧
      (final.ret = some need_more ∨ (final.ret = none ∧ final.brk = true)) ∧
      (final.ret = some need_more → z'.avail_out = 0) ∧
      (final.brk = true → result.lookahead = 0 ∧ z'.avail_in = 0) ∧
      (final.ret = none → PublishReady result) := by
  rw [slow_positive_loop_source _ flush nonzero]
  exact slow_finish_ready_loop boundary frontier buffers positive pointer memory wrap publish inputValid

/-- The complete actual nonzero-flush loop also has exact counters, caller
output interval, object frame, allocation ledger and public controls.
This still excludes the subsequent flag-specific EOF tail and marker. -/
theorem slow_positive_loop_safety {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (flush : Int32) (nonzero : flush ≠ Z_NO_FLUSH) :
    ∃ used produced final after z' result base' ys extended nextOrigin,
      cwhile forever (deflate_slow_body (some (.tab ds)) flush) {} h = .ok (final, after) ∧
      StrategyBoundary after r ds z' result extended nextOrigin base' ys config ∧ EndFrontier after result ∧
      StreamBuffers after r ∧ StreamAccounting z z' used produced ∧
      (∀ i, i < origin + fillEnd d → extended i = input i) ∧
      nextOrigin + fillEnd result = origin + fillEnd d + used ∧ base ≤ base' ∧
      (final.ret = some need_more ∨ (final.ret = none ∧ final.brk = true)) ∧
      (final.ret = some need_more → z'.avail_out = 0) ∧
      (final.brk = true → result.lookahead = 0 ∧ z'.avail_in = 0) ∧
      (final.ret = none → PublishReady result) ∧
      z'.total_in = z.total_in + UInt64.ofNat used ∧
      z'.total_out = z.total_out + UInt64.ofNat produced ∧
      RawOutputInterval h after ob oo produced ∧
      Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = ob) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧
      after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk ∧ StrategyControls d result := by
  obtain ⟨used, produced, final, after, z', result, base', ys, extended, nextOrigin,
      run, stateA, endA, buffersA, accountA, agreesA, endpointA, baseA, stopped, outputA, eofA, readyA⟩ :=
    slow_positive_ready_loop boundary frontier buffers positive pointer memory wrap publish inputValid flush nonzero
  have finishRun : cwhile forever (deflate_slow_body (some (.tab ds)) Z_FINISH) {} h = .ok (final, after) := by
    rw [slow_positive_loop_source _ flush nonzero] at run
    exact run
  have totals := slow_ordinary_loop_run_counter_effects (Or.inr rfl) boundary frontier buffers positive pointer
    memory wrap publish inputValid finishRun stateA.good.live.hz accountA
  have interval := slow_ordinary_loop_run_output_effect (Or.inr rfl) boundary frontier buffers positive pointer
    memory wrap publish inputValid finishRun stateA.good.live.hz accountA
  have storage := slow_ordinary_loop_run_full_storage (Or.inr rfl) boundary frontier buffers positive pointer
    memory wrap publish inputValid finishRun
  have controls := slow_finish_loop_run_controls boundary frontier buffers positive pointer memory wrap publish
    inputValid finishRun stateA.good.live.hs
  exact ⟨used, produced, final, after, z', result, base', ys, extended, nextOrigin,
    run, stateA, endA, buffersA, accountA, agreesA, endpointA, baseA, stopped, outputA, eofA, readyA,
    totals.1, totals.2, interval, storage.1, storage.2.1, storage.2.2.1, storage.2.2.2.1, storage.2.2.2.2, controls⟩

end Zlib.Deflate.Engine.Proofs
