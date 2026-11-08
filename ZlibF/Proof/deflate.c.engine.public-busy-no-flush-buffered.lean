import ZlibF.Proof.«deflate.c.engine.public-no-flush-buffered»
import ZlibF.Proof.«deflate.c.engine.public-finish-pending-entry»

/-! # Complete accepted BUSY NO_FLUSH calls retain the working boundary -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- A positive-output BUSY entry with new input records NO_FLUSH and
reaches the data path. The legal last-flush range makes the actual rank
evaluation total; the new input bypasses duplicate-request refusal. -/
theorem public_busy_no_flush_entry {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (status : d.status = BUSY_STATE) (pending : d.pending = 0)
    (out : z.next_out ≠ .null) (positive : z.avail_out ≠ 0)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (lower : -2 ≤ d.last_flush.toInt) (upper : d.last_flush.toInt ≤ 5) (nonempty : z.avail_in ≠ 0) :
    deflate (some r) Z_NO_FLUSH h =
      publicDataTail (some r) (some (.tab ds)) Z_NO_FLUSH
        (setD h ds { d with last_flush := Z_NO_FLUSH }) := by
  have good0 := last_flush_good good Z_NO_FLUSH
  have header : publicZlibHeader (some r) (some (.tab ds))
      (publicDataTail (some r) (some (.tab ds)) Z_NO_FLUSH)
      (setD h ds { d with last_flush := Z_NO_FLUSH }) =
      publicDataTail (some r) (some (.tab ds)) Z_NO_FLUSH (setD h ds { d with last_flush := Z_NO_FLUSH }) := by
    unfold publicZlibHeader
    simp only [bind_app, pure_app, rdD_eq, setD_dstates_same, status,
      show (BUSY_STATE == INIT_STATE) = false from rfl, Bool.false_and, Bool.false_eq_true, ite_false]
  have inputs : (z.avail_in != 0 && z.next_in == .null) = false := by
    by_cases empty : z.avail_in = 0
    · simp [empty]
    · simp [inputValid empty]
  obtain ⟨rank, ranked⟩ := rank_legal_last_flush d.last_flush lower upper
  have checked := stateCheck_live good.live
  have rankFinish : RANK Z_NO_FLUSH = pure 0 := by rfl
  rw [public_deflate_source]
  simp only [bind_app, pure_app, checked, show ((0 : Int32) != 0) = false from rfl,
    show (Z_NO_FLUSH > Z_BLOCK) = False from by decide, show (Z_NO_FLUSH < 0) = False from by decide,
    decide_false, Bool.false_or, Bool.false_eq_true, ite_false,
    zrd_eq, good.live.hz, good.live.zst, castDeflateState,
    ldZStream_ok good.live.hz, ldDeflateState_tab good.live.hs,
    show (z.next_out == .null) = false from beq_eq_false_iff_ne.mpr out,
    inputs, Bool.or_false, status, show (BUSY_STATE == FINISH_STATE) = false from rfl, Bool.false_and,
    show (z.avail_out == 0) = false from beq_eq_false_iff_ne.mpr positive,
    wrD_eq, good.live.hs, pending,
    show (z.avail_in == 0) = false from beq_eq_false_iff_ne.mpr nonempty, Bool.false_and, show ((0 : UInt64) != 0) = false from rfl,
    BEq.rfl, rankFinish, ranked, show (Z_NO_FLUSH != Z_NO_FLUSH) = false from rfl,
    Bool.and_false, rdD_eq, setD_dstates_same, ZStreamRef.get_setD]
  simpa only [status, pending] using header


/-- The accepted entry uses the actual pending run, then reaches the
header/data tail when caller output remains. No callee contract is assumed. -/
theorem public_pending_no_flush_continue {h middle : Heap} {r : ZStreamRef} {ds : Nat}
    {z zm : ZStream} {d result : DeflateState}
    (good : DGood h r ds z d) (goodM : DGood middle r ds zm result) (status : d.status = BUSY_STATE)
    (out : z.next_out ≠ .null) (positive : z.avail_out ≠ 0)
    (input : z.avail_in ≠ 0 → z.next_in ≠ .null) (pending : d.pending ≠ 0)
    (run : flush_pending (some r) (setD h ds { d with last_flush := Z_NO_FLUSH }) = .ok ((), middle))
    (remaining : zm.avail_out ≠ 0) (finishedInput : result.status = FINISH_STATE → zm.avail_in = 0) :
    deflate (some r) Z_NO_FLUSH h =
      publicZlibHeader (some r) (some (.tab ds))
        (publicDataTail (some r) (some (.tab ds)) Z_NO_FLUSH) middle := by
  have inputs : (z.avail_in != 0 && z.next_in == .null) = false := by
    by_cases empty : z.avail_in = 0
    · simp [empty]
    · simp [input empty]
  have finishInput : (result.status == FINISH_STATE && zm.avail_in != 0) = false := by
    by_cases status : result.status = FINISH_STATE
    · simp [status, finishedInput status]
    · simp [status]
  have checked := stateCheck_live good.live
  rw [public_deflate_source]
  simp only [bind_app, pure_app, checked, show ((0 : Int32) != 0) = false from rfl,
    show (Z_NO_FLUSH > Z_BLOCK) = False from by decide, show (Z_NO_FLUSH < 0) = False from by decide,
    decide_false, Bool.false_or, Bool.false_eq_true, ite_false,
    zrd_eq, good.live.hz, good.live.zst, castDeflateState,
    ldZStream_ok good.live.hz, ldDeflateState_tab good.live.hs,
    show (z.next_out == .null) = false from beq_eq_false_iff_ne.mpr out,
    inputs, show (d.status == FINISH_STATE) = false from by rw [status]; rfl,
    show (Z_NO_FLUSH != Z_FINISH) = true from rfl, Bool.false_and, Bool.and_false, Bool.or_false,
    show (z.avail_out == 0) = false from beq_eq_false_iff_ne.mpr positive,
    wrD_eq, good.live.hs, show (d.pending != 0) = true from bne_iff_ne.mpr pending,
    ite_true, run, goodM.live.hz,
    show (zm.avail_out == 0) = false from beq_eq_false_iff_ne.mpr remaining,
    rdD_eq, goodM.live.hs, finishInput]

/-- BUSY states skip the zlib header statements on every continuation. -/
theorem public_busy_no_flush_header_skip {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (status : d.status = BUSY_STATE) :
    publicZlibHeader (some r) (some (.tab ds))
      (publicDataTail (some r) (some (.tab ds)) Z_NO_FLUSH) h =
      publicDataTail (some r) (some (.tab ds)) Z_NO_FLUSH h := by
  unfold publicZlibHeader
  simp only [bind_app, pure_app, rdD_eq, good.live.hs, status,
    show (BUSY_STATE == INIT_STATE) = false from rfl, Bool.false_and, Bool.false_eq_true, ite_false]

/-- A complete actual BUSY NO_FLUSH call with new input returns the same
working boundary, including existing pending output and every positive
raw capacity. Empty-input duplicate requests have their separate refusal. -/
theorem public_default_busy_no_flush_buffered {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List ZlibF.Math.DeflateSymbols.Symbol} {config : EngineConfig}
    (boundary : BufferedBoundary h r ds z d input origin base xs config) (buffers : StreamBuffers h r)
    (status : d.status = BUSY_STATE) (level : d.level = 6) (strategy : d.strategy = 0)
    (pointer : z.next_out = .ref (.blk ob) oo) (output : 0 < z.avail_out.toNat)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1)
    (valid : z.avail_in ≠ 0 → z.next_in ≠ .null) (nonempty : z.avail_in ≠ 0)
    (lower : -2 ≤ d.last_flush.toInt) (upper : d.last_flush.toInt ≤ 5) :
    ∃ used produced after z' result nextInput nextOrigin nextBase ys,
      deflate (some r) Z_NO_FLUSH h = .ok (Z_OK, after) ∧
      BufferedBoundary after r ds z' result nextInput nextOrigin nextBase ys config ∧ StreamBuffers after r ∧
      StreamAccounting z z' used produced ∧ result.status = BUSY_STATE ∧
      (result.last_flush = -1 ∨ result.last_flush = Z_NO_FLUSH) := by
  have nonnull : z.next_out ≠ .null := by rw [pointer]; intro impossible; cases impossible
  have positive : z.avail_out ≠ 0 := by intro zero; rw [zero] at output; contradiction
  have boundary0 := last_flush_buffered_boundary boundary Z_NO_FLUSH
  have buffers0 := last_flush_buffers boundary.good buffers Z_NO_FLUSH
  by_cases queued : d.pending = 0
  · have ready : PublishReady { d with last_flush := Z_NO_FLUSH } := ⟨queued, boundary.empty_cursor queued, boundary.bits⟩
    obtain ⟨used, produced, after, z', result, nextInput, nextOrigin, nextBase, ys, run, stateA, buffersA, accountA, statusA, lastA⟩ :=
      public_busy_slow_no_flush_buffered boundary0 buffers0 status level strategy pointer memory wrap ready valid
    have entry := public_busy_no_flush_entry boundary.good status queued nonnull positive valid lower upper nonempty
    exact ⟨used, produced, after, z', result, nextInput, nextOrigin, nextBase, ys, entry.trans run,
      stateA, buffersA, accountA, statusA, lastA⟩
  · obtain ⟨before, pending⟩ := good_pending_bits boundary.good
    by_cases enough : z.avail_out.toNat ≤ d.pending.toNat
    · obtain ⟨_pb, after, z', result, _written, _remaining, _base, run, stateA, buffersA, accountA, _sizes, _storage,
          _outA, lastA, _count, _bits, fields, _bytes, _pendingA, _bitsA⟩ :=
        public_pending_buffered_exhausted Z_NO_FLUSH boundary buffers pointer valid (by decide) (by decide)
          (by intro impossible; rw [status] at impossible; cases (show BUSY_STATE ≠ FINISH_STATE from by decide) impossible)
          output enough pending
      refine ⟨0, z.avail_out.toNat, after, z', result, input, origin, base, xs, run, stateA, buffersA, accountA, ?_, Or.inl lastA⟩
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
        entry.trans ((public_busy_no_flush_header_skip stateM.good statusM).trans run), stateA, buffersA, ?_, statusA, lastA⟩
      simpa only [Nat.zero_add] using stream_accounting_trans accountM accountA

end Zlib.Deflate.Engine.Proofs
