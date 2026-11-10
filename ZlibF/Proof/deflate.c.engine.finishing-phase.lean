import ZlibF.Proof.«deflate.c.engine.public-finish-pending-entry»

/-! # Actual post-strategy FINISH calls retain the finishing phase -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
set_option autoImplicit false

/-- A scalar publication/retry update retains the finishing phase if an
empty positive-wrapper pending buffer has reset its cursor. -/
theorem FinishingPhase.control {d result : DeflateState} {config : EngineConfig}
    (phase : FinishingPhase d config)
    (fields : result = { d with
      pending := result.pending, pending_out := result.pending_out, last_flush := result.last_flush })
    (cursor : result.wrap = 1 → result.pending = 0 → result.pending_out = result.pending_buf) :
    FinishingPhase result config := by
  refine ⟨?_, ?_, ?_, ?_, ?_, cursor⟩
  · rw [fields]; exact phase.status
  · rw [fields]; exact phase.lookahead
  · rw [fields]; exact phase.bits
  · rw [fields]; exact phase.configuration
  · rw [fields]; exact phase.wrapper

/-- A finishing state skips the header and strategy statements. -/
theorem public_finishing_header_source {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (good : DGood h r ds z d) (phase : FinishingPhase d config) (empty : z.avail_in = 0) :
    publicZlibHeader (some r) (some (.tab ds))
      (publicDataTail (some r) (some (.tab ds)) Z_FINISH) h =
      publicFinishTail (some r) (some (.tab ds)) Z_FINISH h := by
  unfold publicZlibHeader
  simp only [bind_app, pure_app, rdD_eq, good.live.hs, phase.status,
    show (FINISH_STATE == INIT_STATE) = false from rfl, Bool.false_and, Bool.false_eq_true, ite_false]
  exact public_finish_source good.live.hz good.live.hs phase.status empty phase.lookahead

/-- After the final block has drained, execute the real header/data tail.
The positive wrapper queues its trailer exactly once; the negative wrapper
returns STREAM_END without another write. Arbitrary raw capacity includes zero. -/
theorem public_finishing_tail_phase {h : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r) (phase : FinishingPhase d config)
    (pointer : z.next_out = .ref (.blk ob) oo) (empty : z.avail_in = 0) (pending : d.pending = 0) :
    ∃ produced rc after z' result,
      publicZlibHeader (some r) (some (.tab ds))
        (publicDataTail (some r) (some (.tab ds)) Z_FINISH) h = .ok (rc, after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
      (rc = Z_OK ∨ rc = Z_STREAM_END) ∧ FinishingPhase result config ∧
      result.last_flush = d.last_flush ∧ z'.avail_in = 0 ∧
      (rc = Z_STREAM_END → result.wrap = -1 ∧ result.pending = 0) := by
  rcases phase.wrapper with wrap | wrap
  · obtain ⟨other, pb, buf, trees⟩ := good.trees
    have eq : other = d := Option.some.inj (trees.base.dstate.symm.trans good.live.hs)
    subst other
    obtain ⟨produced, after, z', result, _written, _remaining, run, goodA, buffersA, account,
        _sizes, _storage, _amount, _left, wrapA, bitsA, fields, _bytes, _pendingA, _output⟩ :=
      zlib_trailer_publish good trees buffers pointer wrap pending (phase.cursor wrap pending) phase.bits
    have header := public_finishing_header_source good phase empty
    have phaseA : FinishingPhase result config := by
      refine ⟨by rw [fields]; exact phase.status, by rw [fields]; exact phase.lookahead, bitsA, ?_, Or.inr wrapA, ?_⟩
      · rw [wrapA, fields]
        change { engineConfig d with wrap := -1 } = { config with wrap := -1 }
        rw [phase.configuration]
      · intro impossible
        rw [wrapA] at impossible
        cases (show (-1 : Int32) ≠ 1 from by decide) impossible
    refine ⟨produced, if result.pending != 0 then Z_OK else Z_STREAM_END, after, z', result,
      header.trans run, goodA, buffersA, account, ?_, phaseA, by rw [fields], ?_, ?_⟩
    · by_cases queued : result.pending = 0 <;> simp [queued]
    · apply UInt32.toNat_inj.mp
      have count := account.2.2.1
      rw [empty] at count
      change z'.avail_in.toNat + 0 = 0 at count
      exact count
    · intro ended
      refine ⟨wrapA, ?_⟩
      by_cases queued : result.pending = 0
      · exact queued
      · simp [queued, show Z_OK ≠ Z_STREAM_END from by decide] at ended
  · exact ⟨0, Z_STREAM_END, h, z, d,
      public_finished_headers good phase.status empty phase.lookahead wrap,
      good, buffers, stream_accounting_zero z, Or.inr rfl, phase, rfl, empty, fun _ => ⟨wrap, pending⟩⟩

end Zlib.Deflate.Engine.Proofs
