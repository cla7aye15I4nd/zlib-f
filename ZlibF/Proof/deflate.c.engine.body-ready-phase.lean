import ZlibF.Proof.«deflate.c.engine.no-flush-ready-step»
import ZlibF.Proof.«deflate.c.engine.finish-ready-step»
import ZlibF.Proof.«deflate.c.engine.positive-flush-loop»

/-! # Actual body continuation retains publication readiness even at zero output -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Every signed-flush actual body preserves publication readiness when
it continues. Initial and returned output capacities may be zero. This
uses the separately proved actual NO_FLUSH/FINISH execution steps and exact
nonzero-scalar source equality, not a callee contract assumption. -/
theorem slow_body_run_ready_phase {h after : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d result : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    {st next : LoopS} {flush : Int32}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (run : deflate_slow_body (some (.tab ds)) flush st h = .ok (next, after))
    (live : after.dstates ds = some result) : next.ret = none → PublishReady result := by
  have known : ∃ expected other otherD,
      deflate_slow_body (some (.tab ds)) flush st h = .ok (expected, other) ∧
      other.dstates ds = some otherD ∧ (expected.ret = none → PublishReady otherD) := by
    by_cases waiting : flush = Z_NO_FLUSH
    · subst flush
      obtain ⟨_used, _produced, expected, other, _z, otherD, _base, _ys, _input, _origin,
          actual, stateA, _end, _buffers, _account, _agrees, _endpoint, _baseLe, _brk, _ret, readyA, _less, _reason⟩ :=
        slow_no_flush_ready_step boundary frontier buffers positive pointer memory wrap publish inputValid st
      exact ⟨expected, other, otherD, actual, stateA.good.live.hs, readyA⟩
    · obtain ⟨_used, _produced, expected, other, _z, otherD, _base, _ys, _input, _origin,
          actual, stateA, _end, _buffers, _account, _agrees, _endpoint, _baseLe, _reason, _ret, readyA, _less, _brk⟩ :=
        slow_finish_ready_step boundary frontier buffers positive pointer memory wrap publish inputValid st
      refine ⟨expected, other, otherD, ?_, stateA.good.live.hs, readyA⟩
      rw [slow_positive_body_source _ _ waiting _]
      exact actual
  obtain ⟨expected, other, otherD, actual, stateA, readyA⟩ := known
  have pair := Prod.mk.inj (Except.ok.inj (actual.symm.trans run))
  rw [pair.2] at stateA
  have states : otherD = result := Option.some.inj (stateA.symm.trans live)
  simpa only [pair.1, states] using readyA

end Zlib.Deflate.Engine.Proofs
