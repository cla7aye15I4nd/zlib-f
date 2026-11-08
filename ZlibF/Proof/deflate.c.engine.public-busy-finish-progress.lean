import ZlibF.Proof.«deflate.c.engine.public-data-finish-progress»
import ZlibF.Proof.«deflate.c.engine.public-busy-finish-phase»

/-! # The complete BUSY FINISH entry has progress at every positive capacity -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec ZlibF.Spec.Public Zlib.Deflate.Proofs
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Each real BUSY FINISH either enters the finishing phase, strictly
reduces unread input plus lookahead, or only publishes old pending bytes
and strictly reduces their count. Zero-output refusals are outside this
progress premise and remain in the general safety theorem. -/
theorem public_default_busy_finish_progress {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : BufferedBoundary h r ds z d input origin base xs config) (buffers : StreamBuffers h r)
    (status : d.status = BUSY_STATE) (level : d.level = 6) (strategy : d.strategy = 0)
    (pointer : z.next_out = .ref (.blk ob) oo) (memory : config.memory.toNat = 16384)
    (wrap : config.wrap = 1) (output : 0 < z.avail_out.toNat)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (lower : -2 ≤ d.last_flush.toInt) (upper : d.last_flush.toInt ≤ 5) :
    ∃ used produced rc after z' result,
      deflate (some r) Z_FINISH h = .ok (rc, after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' used produced ∧
      (rc = Z_OK ∨ rc = Z_STREAM_END) ∧ result.bi_valid.toInt < 8 ∧
      PublicFinishPhase after r ds z' result config ∧ (result.last_flush = -1 ∨ result.last_flush = Z_FINISH) ∧
      (rc = Z_STREAM_END → result.status = FINISH_STATE ∧ result.wrap = -1 ∧
        z'.avail_in = 0 ∧ result.lookahead = 0 ∧ result.pending = 0 ∧ result.bi_valid.toInt = 0) ∧
      (result.status = BUSY_STATE →
        result.lookahead.toNat + z'.avail_in.toNat < d.lookahead.toNat + z.avail_in.toNat ∨
        (result.lookahead.toNat + z'.avail_in.toNat = d.lookahead.toNat + z.avail_in.toNat ∧
          result.pending.toNat < d.pending.toNat)) ∧
      (result.status = FINISH_STATE → z'.avail_in = 0) := by
  have nonnull : z.next_out ≠ .null := by rw [pointer]; intro impossible; cases impossible
  have positive : z.avail_out ≠ 0 := by intro zero; rw [zero] at output; contradiction
  have boundary0 := last_flush_buffered_boundary boundary Z_FINISH
  have buffers0 := last_flush_buffers boundary.good buffers Z_FINISH
  by_cases queued : d.pending = 0
  · have ready : PublishReady { d with last_flush := Z_FINISH } :=
      ⟨queued, boundary.empty_cursor queued, boundary.bits⟩
    obtain ⟨used, produced, rc, after, z', result, run, goodA, buffersA, account, allowed, bits, phase, last, ended, strict, emptyA⟩ :=
      public_busy_slow_finish_progress boundary0 buffers0 status level strategy pointer memory wrap ready output inputValid
    have entry := public_busy_finish_entry boundary.good status queued nonnull positive inputValid lower upper
    exact ⟨used, produced, rc, after, z', result, entry.trans run, goodA, buffersA, account, allowed, bits, phase, last, ended, fun busy => Or.inl (strict busy), emptyA⟩
  · obtain ⟨before, pending⟩ := good_pending_bits boundary.good
    by_cases enough : z.avail_out.toNat ≤ d.pending.toNat
    · obtain ⟨_pb, after, z', result, _written, _remaining, _base, run, stateA, buffersA, account, _sizes, _storage,
          _outA, last, pendingCount, bits, fields, _bytes, _pendingA, _bitsA⟩ :=
        public_pending_buffered_exhausted Z_FINISH boundary buffers pointer inputValid (by decide) (by decide)
          (fun _ => rfl) output enough pending
      refine ⟨0, z.avail_out.toNat, Z_OK, after, z', result, run, stateA.good, buffersA, account, Or.inl rfl, bits,
        Or.inl ⟨input, origin, base, xs, stateA, ?_⟩, Or.inl last, ?_, ?_, ?_⟩
      · rw [fields]; exact status
      · intro impossible
        cases (show Z_OK ≠ Z_STREAM_END from by decide) impossible
      · intro _
        right
        have look : result.lookahead = d.lookahead := by rw [fields]
        have inputCount := account.2.2.1
        constructor
        · rw [look]
          omega
        · omega
      · intro impossible
        have sameStatus : result.status = BUSY_STATE := by rw [fields]; exact status
        cases (by decide : BUSY_STATE ≠ FINISH_STATE) (sameStatus.symm.trans impossible)
    · have pending0 := last_flush_pending_bits boundary.good pending Z_FINISH
      obtain ⟨_pb, produced, middle, zm, dm, _written, _remaining, _base, flushRun, stateM, buffersM,
          accountM, _sizesM, _storageM, amount, _pendingCount, fields, readyM, _bytesM, _pendingM, _bitsM⟩ :=
        flush_pending_buffered_boundary boundary0 buffers0 pointer pending0
      have statusM : dm.status = BUSY_STATE := by rw [fields]; exact status
      have levelM : dm.level = 6 := by rw [fields]; exact level
      have strategyM : dm.strategy = 0 := by rw [fields]; exact strategy
      have left : 0 < zm.avail_out.toNat := by
        have balance := accountM.2.2.2.1
        change produced = min d.pending.toNat z.avail_out.toNat at amount
        rw [Nat.min_eq_left (by omega)] at amount
        omega
      have pointerM : zm.next_out = .ref (.blk ob) (oo + produced) := by
        rw [accountM.2.2.2.2.2.1, pointer]; rfl
      obtain ⟨used, laterProduced, rc, after, z', result, tailRun, goodA, buffersA, accountA, allowed, bits, phase, last, ended, strict, emptyA⟩ :=
        public_busy_slow_finish_progress stateM buffersM statusM levelM strategyM pointerM memory wrap (readyM left) left
          (input_valid_accounting_output inputValid accountM)
      have entry := public_pending_finish_continue boundary.good stateM.good nonnull positive inputValid queued flushRun
        (by intro zero; rw [zero] at left; contradiction) (by
          intro impossible; rw [statusM] at impossible; cases (show BUSY_STATE ≠ FINISH_STATE from by decide) impossible)
      have lastM : dm.last_flush = Z_FINISH := by rw [fields]
      rw [lastM] at last
      refine ⟨used, produced + laterProduced, rc, after, z', result,
        entry.trans ((public_busy_header_skip stateM.good statusM).trans tailRun), goodA, buffersA, ?_,
        allowed, bits, phase, last, ended, ?_, emptyA⟩
      · simpa only [Nat.zero_add] using stream_accounting_trans accountM accountA
      · intro busy
        left
        have decrease := strict busy
        have look : dm.lookahead = d.lookahead := by rw [fields]
        have inputCount := accountM.2.2.1
        rw [look] at decrease
        omega

end Zlib.Deflate.Engine.Proofs
