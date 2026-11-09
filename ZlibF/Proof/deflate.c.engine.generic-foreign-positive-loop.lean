import ZlibF.Proof.«deflate.c.engine.generic-foreign-finish-ready-loop»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-loop-controls»
import ZlibF.Proof.«deflate.c.engine.positive-flush-loop»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Every nonzero flush has the already established terminating loop.
The initialized default-memory boundary supplies actual callee proofs;
no successful run or callee specification is assumed. The flag-specific
EOF tail and the public flush marker are separate obligations. -/
theorem default_foreign_slow_positive_ready_loop {h : Heap} {r : ZStreamRef} {ds owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.dstate_depth owner) oo)
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
  exact default_foreign_slow_finish_ready_loop boundary frontier buffers positive pointer memory wrap publish inputValid


end Zlib.Deflate.Engine.Proofs
