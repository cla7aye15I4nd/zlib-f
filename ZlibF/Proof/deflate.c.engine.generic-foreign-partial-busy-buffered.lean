import ZlibF.Proof.«deflate.c.engine.generic-foreign-partial-busy-ready»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-public-pending-buffered»
import ZlibF.Proof.«deflate.c.engine.public-partial-sync-buffered»

/-! # Complete BUSY PARTIAL calls include old pending publication -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Every actual default BUSY PARTIAL call with positive foreign-depth output retains
the initialized working boundary, for all input counts and old pending
sizes. Publication may exhaust output or continue directly into the actual
strategy; the original duplicate check is never repeated after a drain.
The initial header, entry refusals and encoded history remain separate. -/
theorem public_foreign_busy_partial_buffered {h : Heap} {r : ZStreamRef} {ds owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : BufferedBoundary h r ds z d input origin base xs config) (buffers : StreamBuffers h r)
    (status : d.status = BUSY_STATE) (level : d.level = 6) (strategy : d.strategy = 0)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (memory : config.memory.toNat = 16384)
    (wrap : config.wrap = 1) (output : 0 < z.avail_out.toNat)
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
  by_cases queued : d.pending = 0
  · exact public_foreign_busy_partial_ready boundary buffers status level strategy pointer memory wrap queued output
      inputValid lower upper flush flag
  · have nonnull : z.next_out ≠ .null := by rw [pointer]; intro impossible; cases impossible
    have positive : z.avail_out ≠ 0 := by intro zero; rw [zero] at output; contradiction
    obtain ⟨before, pending⟩ := good_pending_bits boundary.good
    by_cases enough : z.avail_out.toNat ≤ d.pending.toNat
    · obtain ⟨_pb, after, z', result, _written, _remaining, _base, run, stateA, buffersA, account,
          _sizes, _storage, _outA, last, _count, _bits, fields, _bytes, _pendingA, _bitsA,_preciseA⟩ :=
        public_pending_buffered_exhausted_foreign flush boundary buffers pointer inputValid flagLo flagHi
          (by intro finished; rw [status] at finished; cases (show BUSY_STATE ≠ FINISH_STATE from by decide) finished)
          output enough pending
      refine ⟨0, z.avail_out.toNat, Z_OK, after, z', result, input, origin, base, xs,
        run, stateA, buffersA, account, Or.inl rfl, ?_, Or.inr last⟩
      rw [fields]; exact status
    · have state0 := last_flush_buffered_boundary boundary flush
      have buffers0 := last_flush_buffers boundary.good buffers flush
      have pending0 := last_flush_pending_bits boundary.good pending flush
      obtain ⟨_pb, produced, middle, zm, dm, _written, _remaining, _base, flushRun, stateM, buffersM,
          accountM, _sizesM, _storageM, amount, _pendingCount, fields, readyM, _bytesM, _pendingM, _bitsM,_preciseM⟩ :=
        flush_pending_buffered_foreign_boundary state0 buffers0 pointer pending0
      have statusM : dm.status = BUSY_STATE := by rw [fields]; exact status
      have levelM : dm.level = 6 := by rw [fields]; exact level
      have strategyM : dm.strategy = 0 := by rw [fields]; exact strategy
      have left : 0 < zm.avail_out.toNat := by
        have balance := accountM.2.2.2.1
        change produced = min d.pending.toNat z.avail_out.toNat at amount
        rw [Nat.min_eq_left (by omega)] at amount
        omega
      have pointerM : zm.next_out = .ref (.dstate_depth owner) (oo + produced) := by
        rw [accountM.2.2.2.2.2.1, pointer]; rfl
      obtain ⟨used, laterProduced, after, z', result, extended, nextOrigin, nextBase, ys,
          tailRun, stateA, buffersA, accountA, statusA, lastA⟩ :=
        public_foreign_busy_partial_data_safety stateM buffersM statusM levelM strategyM
          pointerM memory wrap (readyM left) (input_valid_accounting_output inputValid accountM) flush flag
      have entry := public_pending_valid_continue boundary.good stateM.good status nonnull positive inputValid queued
        flush flagLo flagHi flushRun
        (by intro zero; rw [zero] at left; contradiction)
        (by intro impossible; rw [statusM] at impossible; cases (show BUSY_STATE ≠ FINISH_STATE from by decide) impossible)
      have lastM : dm.last_flush = flush := by rw [fields]
      rw [lastM] at lastA
      refine ⟨used, produced + laterProduced, Z_OK, after, z', result, extended, nextOrigin, nextBase, ys,
        entry.trans ((public_busy_header_skip_next stateM.good statusM _).trans tailRun),
        stateA, buffersA, ?_, Or.inl rfl, statusA, lastA⟩
      simpa only [Nat.zero_add] using stream_accounting_trans accountM accountA

end Zlib.Deflate.Engine.Proofs
