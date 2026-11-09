import ZlibF.Proof.«deflate.c.engine.generic-foreign-partial-data-safety»
import ZlibF.Proof.«deflate.c.engine.public-partial-sync-ready»

/-! # Actual accepted PARTIAL entry preserves the working boundary -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The actual default BUSY PARTIAL call with no old pending bytes covers
all input counts, including empty-input duplicate refusal. It retains the
same caller-independent content/EOF boundary for the next call or rebuffer.
Public output is positive and foreign-depth; earlier entry refusals, old pending and
the initial header remain separate cases of the unchanged Goal.deflate. -/
theorem public_foreign_busy_partial_ready {h : Heap} {r : ZStreamRef} {ds owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : BufferedBoundary h r ds z d input origin base xs config) (buffers : StreamBuffers h r)
    (status : d.status = BUSY_STATE) (level : d.level = 6) (strategy : d.strategy = 0)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (memory : config.memory.toNat = 16384)
    (wrap : config.wrap = 1) (pending : d.pending = 0) (output : 0 < z.avail_out.toNat)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (lower : -2 ≤ d.last_flush.toInt) (upper : d.last_flush.toInt ≤ 5)
    (flush : Int32) (flag : flush = Z_PARTIAL_FLUSH) :
    ∃ used produced rc after z' result extended nextOrigin nextBase ys,
      deflate (some r) flush h = .ok (rc, after) ∧
      BufferedBoundary after r ds z' result extended nextOrigin nextBase ys config ∧
      StreamBuffers after r ∧ StreamAccounting z z' used produced ∧
      (rc = Z_OK ∨ rc = Z_BUF_ERROR) ∧ result.status = BUSY_STATE ∧
      (result.last_flush = flush ∨ result.last_flush = -1) := by
  have flagLo : 0 ≤ flush.toInt := by rw [flag];decide
  have flagHi : flush.toInt ≤ 5 := by rw [flag];decide
  have nonnull : z.next_out ≠ .null := by rw [pointer]; intro impossible; cases impossible
  have positive : z.avail_out ≠ 0 := by intro zero; rw [zero] at output; contradiction
  have state0 := last_flush_buffered_boundary boundary flush
  have buffers0 := last_flush_buffers boundary.good buffers flush
  have publish0 : PublishReady { d with last_flush := flush } :=
    ⟨pending, boundary.empty_cursor pending, boundary.bits⟩
  obtain ⟨current, old, _currentRank, _oldRank, source⟩ := public_busy_valid_entry_choice boundary.good
    status pending nonnull positive inputValid lower upper flush flagLo flagHi
  by_cases duplicate : (z.avail_in == 0 && decide (current ≤ old) && flush != Z_FINISH) = true
  · rw [ite_eq_left duplicate] at source
    obtain ⟨message, refused⟩ := err_return_run state0.good.live.hz Z_BUF_ERROR
    let z' := { z with msg := message }
    have goodA := stream_control_good (z' := z') state0.good rfl boundary.good.live.zalloc boundary.good.live.zfree
    have account : StreamAccounting z z' 0 0 := stream_accounting_zero z
    have buffersA := stream_control_buffers state0.good goodA buffers0 account
    have stateA := stream_control_buffered state0 goodA
    exact ⟨0, 0, Z_BUF_ERROR, _, z', _, input, origin, base, xs, source.trans refused,
      stateA, buffersA, account, Or.inr rfl, status, Or.inl rfl⟩
  · rw [ite_eq_right duplicate] at source
    obtain ⟨used, produced, after, z', result, extended, nextOrigin, nextBase, ys,
        run, stateA, buffersA, accountA, statusA, lastA⟩ :=
      public_foreign_busy_partial_data_safety state0 buffers0 status level strategy pointer memory wrap
        publish0 inputValid flush flag
    exact ⟨used, produced, Z_OK, after, z', result, extended, nextOrigin, nextBase, ys,
      source.trans run, stateA, buffersA, accountA, Or.inl rfl, statusA, lastA⟩

end Zlib.Deflate.Engine.Proofs
