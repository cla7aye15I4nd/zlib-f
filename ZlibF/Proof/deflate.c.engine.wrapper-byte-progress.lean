import ZlibF.Proof.«deflate.c.engine.ready-byte-progress»

/-! # Public byte progress including header and pending drains -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- `int ZEXPORT deflate(z_streamp strm, int flush)` (BUSY NO_FLUSH).
Old pending bytes either exhaust output or precede the actual data tail.
With nonempty input, every accepted call consumes or emits a byte. -/
theorem public_default_busy_no_flush_byte_progress {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List ZlibF.Math.DeflateSymbols.Symbol} {config : EngineConfig}
    (boundary : BufferedBoundary h r ds z d input origin base xs config) (buffers : StreamBuffers h r)
    (status : d.status = BUSY_STATE) (level : d.level = 6) (strategy : d.strategy = 0)
    (pointer : z.next_out = .ref (.blk ob) oo) (output : 0 < z.avail_out.toNat)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1)
    (valid : z.avail_in ≠ 0 → z.next_in ≠ .null) (resume : d.pending ≠ 0 ∨ z.avail_in ≠ 0 ∨ d.last_flush = -1 ∨ d.last_flush = -2)
    (lower : -2 ≤ d.last_flush.toInt) (upper : d.last_flush.toInt ≤ 5) :
    ∃ used produced after z' result nextInput nextOrigin nextBase ys,
      deflate (some r) Z_NO_FLUSH h = .ok (Z_OK, after) ∧
      BufferedBoundary after r ds z' result nextInput nextOrigin nextBase ys config ∧ StreamBuffers after r ∧
      StreamAccounting z z' used produced ∧ result.status = BUSY_STATE ∧
      (result.last_flush = -1 ∨ result.last_flush = Z_NO_FLUSH) ∧
      (z.avail_in ≠ 0 → used ≠ 0 ∨ produced ≠ 0) := by
  have nonnull : z.next_out ≠ .null := by rw [pointer]; intro impossible; cases impossible
  have positive : z.avail_out ≠ 0 := by intro zero; rw [zero] at output; contradiction
  have boundary0 := last_flush_buffered_boundary boundary Z_NO_FLUSH
  have buffers0 := last_flush_buffers boundary.good buffers Z_NO_FLUSH
  by_cases queued : d.pending = 0
  · have ready : PublishReady { d with last_flush := Z_NO_FLUSH } := ⟨queued, boundary.empty_cursor queued, boundary.bits⟩
    obtain ⟨used, produced, after, z', result, nextInput, nextOrigin, nextBase, ys, run, stateA, buffersA, accountA, statusA, lastA, progress⟩ :=
      public_busy_slow_no_flush_byte_progress boundary0 buffers0 status level strategy pointer memory wrap ready valid output
    have resumed : z.avail_in ≠ 0 ∨ d.last_flush = -1 ∨ d.last_flush = -2 := by
      rcases resume with impossible | input | retry | initial
      · exact False.elim (impossible queued)
      · exact Or.inl input
      · exact Or.inr (Or.inl retry)
      · exact Or.inr (Or.inr initial)
    have entry := public_busy_no_flush_resuming_entry boundary.good status queued nonnull positive valid lower upper resumed
    exact ⟨used, produced, after, z', result, nextInput, nextOrigin, nextBase, ys, entry.trans run,
      stateA, buffersA, accountA, statusA, lastA, progress⟩
  · obtain ⟨before, pending⟩ := good_pending_bits boundary.good
    by_cases enough : z.avail_out.toNat ≤ d.pending.toNat
    · obtain ⟨_pb, after, z', result, _written, _remaining, _base, run, stateA, buffersA, accountA, _sizes, _storage,
          _outA, lastA, _count, _bits, fields, _bytes, _pendingA, _bitsA⟩ :=
        public_pending_buffered_exhausted Z_NO_FLUSH boundary buffers pointer valid (by decide) (by decide)
          (by intro impossible; rw [status] at impossible; cases (show BUSY_STATE ≠ FINISH_STATE from by decide) impossible)
          output enough pending
      refine ⟨0, z.avail_out.toNat, after, z', result, input, origin, base, xs, run, stateA, buffersA, accountA, ?_, Or.inl lastA, fun _ => Or.inr (by omega)⟩
      rw [fields]; exact status
    · have pending0 := last_flush_pending_bits boundary.good pending Z_NO_FLUSH
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
      obtain ⟨used, laterProduced, after, z', result, nextInput, nextOrigin, nextBase, ys,
          run, stateA, buffersA, accountA, statusA, lastA⟩ :=
        public_busy_slow_no_flush_buffered stateM buffersM statusM levelM strategyM pointerM memory wrap (readyM left)
          (input_valid_accounting_output valid accountM)
      have entry := public_pending_no_flush_continue boundary.good stateM.good status nonnull positive valid queued flushRun
        (by intro zero; rw [zero] at left; contradiction) (by
          intro impossible; rw [statusM] at impossible; cases (show BUSY_STATE ≠ FINISH_STATE from by decide) impossible)
      have lastM : dm.last_flush = Z_NO_FLUSH := by rw [fields]
      rw [lastM] at lastA
      refine ⟨used, produced + laterProduced, after, z', result, nextInput, nextOrigin, nextBase, ys,
        entry.trans ((public_busy_no_flush_header_skip stateM.good statusM).trans run), stateA, buffersA, ?_, statusA, lastA, ?_⟩
      · simpa only [Nat.zero_add] using stream_accounting_trans accountM accountA
      · intro _
        right
        have nonzero : d.pending.toNat ≠ 0 := fun zero => queued (UInt64.toNat_inj.mp zero)
        have moved : 0 < produced := by
          rw [amount]
          exact Nat.lt_min.mpr ⟨by change 0 < d.pending.toNat; omega, output⟩
        omega


/-- `int ZEXPORT deflate(z_streamp strm, int flush)` (BUSY FINISH).
Positive output makes progress through old pending bytes, the real
strategy exit, or the one-time zlib trailer. -/
theorem public_default_busy_finish_byte_progress {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
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
      (rc = Z_OK → 0 < produced) ∧
      (result.status = FINISH_STATE → z'.avail_in = 0) := by
  have nonnull : z.next_out ≠ .null := by rw [pointer]; intro impossible; cases impossible
  have positive : z.avail_out ≠ 0 := by intro zero; rw [zero] at output; contradiction
  have boundary0 := last_flush_buffered_boundary boundary Z_FINISH
  have buffers0 := last_flush_buffers boundary.good buffers Z_FINISH
  by_cases queued : d.pending = 0
  · have ready : PublishReady { d with last_flush := Z_FINISH } :=
      ⟨queued, boundary.empty_cursor queued, boundary.bits⟩
    obtain ⟨used, produced, rc, after, z', result, run, goodA, buffersA, account, allowed, bits, phase, last, ended, strict, emptyA⟩ :=
      public_busy_slow_finish_byte_progress boundary0 buffers0 status level strategy pointer memory wrap ready output inputValid
    have entry := public_busy_finish_entry boundary.good status queued nonnull positive inputValid lower upper
    exact ⟨used, produced, rc, after, z', result, entry.trans run, goodA, buffersA, account, allowed, bits, phase, last, ended, strict, emptyA⟩
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
      · exact fun _ => output
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
        public_busy_slow_finish_byte_progress stateM buffersM statusM levelM strategyM pointerM memory wrap (readyM left) left
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
      · intro _
        have nonzero : d.pending.toNat ≠ 0 := fun zero => queued (UInt64.toNat_inj.mp zero)
        have moved : 0 < produced := by
          rw [amount]
          exact Nat.lt_min.mpr ⟨by change 0 < d.pending.toNat; omega, output⟩
        omega


/-- `int ZEXPORT deflate(z_streamp strm, int flush)` (initial NO_FLUSH).
The actual wrapper header emits at least one byte at every positive
capacity, including a one-byte split header. -/
theorem public_default_first_no_flush_byte_progress {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {config : EngineConfig}
    (initial : EngineStart h r ds z d) (level : d.level = 6)
    (boundary : BufferedBoundary h r ds z d input origin base [] config) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (positive : 0 < z.avail_out.toNat)
    (memory : config.memory.toNat = 16384) (valid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ used produced after z' result nextInput nextOrigin nextBase ys,
      deflate (some r) Z_NO_FLUSH h = .ok (Z_OK, after) ∧
      BufferedBoundary after r ds z' result nextInput nextOrigin nextBase ys config ∧ StreamBuffers after r ∧
      StreamAccounting z z' used produced ∧ result.status = BUSY_STATE ∧
      (result.last_flush = -1 ∨ result.last_flush = Z_NO_FLUSH) ∧ 0 < produced := by
  obtain ⟨output, outGet, outRw, outBound, outside⟩ := caller_raw_output initial.good buffers pointer
  obtain ⟨oldD, pb, buf, trees⟩ := initial.good.trees
  have sameD : oldD = d := Option.some.inj (trees.base.dstate.symm.trans initial.good.live.hs)
  subst oldD
  have separate : ob ≠ pb := by
    intro same
    subst ob
    exact outside (Or.inr (Or.inr (Or.inr (Or.inr trees.base.pbuf))))
  have room : 2 ≤ buf.size := by have size := trees.base.size; have lo := trees.base.lit_lo; omega
  by_cases one : z.avail_out.toNat = 1
  · have oneWord : z.avail_out = 1 := UInt32.toNat_inj.mp one
    obtain ⟨after, z', result, finishRun, stateA, buffersA, accountA, _outA, _pendingA, statusA, lastA⟩ :=
      first_finish_one_buffered initial level boundary buffers pointer oneWord valid
    have noFlushRun := first_no_flush_one_source initial level trees.base.pbuf trees.base.bytes room trees.base.rw
      pointer outGet outRw separate outBound oneWord valid
    have same := first_finish_one_source initial level trees.base.pbuf trees.base.bytes room trees.base.rw
      pointer outGet outRw separate outBound oneWord valid
    have run : deflate (some r) Z_NO_FLUSH h = .ok (Z_OK, after) := noFlushRun.trans (same.symm.trans finishRun)
    exact ⟨0, 1, after, z', result, input, origin, base, [], run, stateA, buffersA, accountA, statusA, Or.inl lastA, by decide⟩
  · have outputRoom : 2 ≤ z.avail_out.toNat := by omega
    have first := public_default_header_complete initial level trees.base.pbuf trees.base.bytes room trees.base.rw
      pointer outGet outRw separate outBound outputRoom valid
    have contentH := header_complete_content (oo := oo) boundary.toContentBoundary trees.base.pbuf trees.base.bytes outGet outside
    have stateH : BufferedBoundary (headerCompleteHeap h r ds pb ob oo z d buf output) r ds
        (headerCompleteStream z ob oo) (headerCompleteState d) input origin base [] config :=
      ⟨contentH, boundary.configuration, ⟨boundary.clear.bl, boundary.clear.opt, boundary.clear.fixed⟩,
        boundary.bits, boundary.strict,
        header_complete_chains boundary.good trees.base.pbuf boundary.end_frontier outside,
        fun _ => initial.pendingOut⟩
    have buffersH := header_complete_buffers initial.good buffers trees.base.bytes outGet separate pointer outputRoom
    have accountH := header_complete_accounting pointer outputRoom
    have wrapConfig : config.wrap = 1 := (congrArg EngineConfig.wrap boundary.configuration).symm.trans initial.wrap
    have readyH : PublishReady (headerCompleteState d) := ⟨initial.pending, initial.pendingOut, boundary.bits⟩
    have pointerH : (headerCompleteStream z ob oo).next_out = .ref (.blk ob) (oo + 2) := rfl
    obtain ⟨used, produced, after, z', result, nextInput, nextOrigin, nextBase, ys, run, stateA, buffersA, accountA, statusA, lastA⟩ :=
      public_busy_slow_no_flush_buffered stateH buffersH rfl level initial.strategy pointerH memory wrapConfig readyH valid
    refine ⟨used, 2 + produced, after, z', result, nextInput, nextOrigin, nextBase, ys,
      first.trans run, stateA, buffersA, ?_, statusA, lastA, by omega⟩
    simpa only [Nat.zero_add] using stream_accounting_trans accountH accountA

end Zlib.Deflate.Engine.Proofs
