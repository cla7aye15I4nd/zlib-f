import ZlibF.Proof.«deflate.c.engine.public-finish-size»
import ZlibF.Proof.«deflate.c.engine.public-busy-finish-phase»

/-! # Complete actual BUSY FINISH calls retain their counted cost phase -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false
set_option maxRecDepth 10000

/-- Size metadata includes the already encoded bytes waiting at the
public entry. The actual call below constructs one of these two phases. -/
def PublicFinishSizeResult (after : Heap) (r : ZStreamRef) (ds : Nat)
    (z' : ZStream) (result : DeflateState) (config : EngineConfig)
    (before : DeflateState) (origin base used produced : Nat) : Prop :=
  (∃ input' origin' base' ys blocks,
    BufferedBoundary after r ds z' result input' origin' base' ys config ∧ result.status = BUSY_STATE ∧
    origin' + fillEnd result = origin + fillEnd before + used ∧ base ≤ base' ∧
    ShortCandidateQuality result ∧ StoredSourceFloor result ∧
    (∀ s ∈ ys, s.distance ≠ 0 → s.value = 0 → s.distance ≤ 4096) ∧
    16383 * blocks ≤ base' - base ∧
    produced + result.pending.toNat + (result.bi_valid.toInt.toNat + 7) / 8 ≤
      before.pending.toNat + (before.bi_valid.toInt.toNat + 7) / 8 + (base' - base) + 5 * blocks) ∨
  (FinishingPhase result config ∧ z'.avail_in = 0 ∧ ∃ blocks delta finalBytes,
    16383 * blocks ≤ delta ∧ delta + finalBytes ≤ origin + fillEnd before + used - base ∧
    produced + result.pending.toNat + (if result.wrap = 1 then 4 else 0) ≤
      before.pending.toNat + (before.bi_valid.toInt.toNat + 7) / 8 + delta + finalBytes + 5 * blocks + 9)

private theorem finish_result_after_drain {after : Heap} {r : ZStreamRef} {ds origin base used amount drained : Nat}
    {z' : ZStream} {result before entry : DeflateState} {config : EngineConfig}
    (endpoint : fillEnd entry = fillEnd before) (bits : entry.bi_valid = before.bi_valid)
    (drain : drained ≤ before.pending.toNat)
    (known : PreparedFinishSizeResult after r ds z' result config entry origin base used amount) :
    PublicFinishSizeResult after r ds z' result config before origin base used (drained + amount) := by
  rcases known with ⟨input', origin', base', ys, blocks, state, status, endA, baseA, candidate, floor, quality, minimum, cost⟩ |
    ⟨phase, empty, blocks, delta, finalBytes, minimum, mass, cost⟩
  · rw [endpoint] at endA
    rw [bits] at cost
    exact Or.inl ⟨input', origin', base', ys, blocks, state, status, endA, baseA, candidate, floor, quality, minimum, by omega⟩
  · rw [endpoint] at mass
    rw [bits] at cost
    exact Or.inr ⟨phase, empty, blocks, delta, finalBytes, minimum, mass, by omega⟩

/-- Complete accepted BUSY FINISH includes real pending drain and the
prepared strategy/EOF/trailer suffix. Working returns keep an exact
prefix cost; finishing returns spend the final overhead exactly once. -/
theorem public_default_busy_finish_counted_size {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : BufferedBoundary h r ds z d input origin base xs config) (buffers : StreamBuffers h r)
    (status : d.status = BUSY_STATE) (level : d.level = 6) (strategy : d.strategy = 0)
    (pointer : z.next_out = .ref (.blk ob) oo) (memory : config.memory.toNat = 16384)
    (wrap : config.wrap = 1) (window : config.windowBits = 15) (output : 0 < z.avail_out.toNat)
    (valid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (lower : -2 ≤ d.last_flush.toInt) (upper : d.last_flush.toInt ≤ 5)
    (candidate : ShortCandidateQuality d) (floor : StoredSourceFloor d)
    (quality : ∀ s ∈ xs, s.distance ≠ 0 → s.value = 0 → s.distance ≤ 4096) :
    ∃ used produced rc after z' result,
      deflate (some r) Z_FINISH h = .ok (rc, after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' used produced ∧
      (rc = Z_OK ∨ rc = Z_STREAM_END) ∧
      PublicFinishSizeResult after r ds z' result config d origin base used produced := by
  have nonnull : z.next_out ≠ .null := by rw [pointer]; intro impossible; cases impossible
  have positive : z.avail_out ≠ 0 := by intro zero; rw [zero] at output; contradiction
  have boundary0 := last_flush_buffered_boundary boundary Z_FINISH
  have buffers0 := last_flush_buffers boundary.good buffers Z_FINISH
  by_cases queued : d.pending = 0
  · have ready : PublishReady { d with last_flush := Z_FINISH } := ⟨queued, boundary.empty_cursor queued, boundary.bits⟩
    obtain ⟨used, produced, rc, after, z', result, run, goodA, buffersA, accountA, allowed,
      _bitsA, phaseA, _lastA, _endedA⟩ :=
      public_busy_slow_finish_counted_size boundary0 buffers0 status level strategy pointer memory wrap ready window
        candidate floor quality valid
    have entry := public_busy_finish_entry boundary.good status queued nonnull positive valid lower upper
    have cost := finish_result_after_drain (before := d) rfl rfl (drained := 0) (by omega) phaseA
    exact ⟨used, produced, rc, after, z', result, entry.trans run, goodA, buffersA, accountA, allowed, by simpa using cost⟩
  · obtain ⟨before, pending⟩ := good_pending_bits boundary.good
    by_cases enough : z.avail_out.toNat ≤ d.pending.toNat
    · obtain ⟨_pb, after, z', result, _written, _remaining, _base, run, stateA, buffersA, accountA, _sizes, _storage,
        _outA, _lastA, countA, _bitsA, fields, _bytes, _pendingA, _wire⟩ :=
        public_pending_buffered_exhausted Z_FINISH boundary buffers pointer valid (by decide) (by decide)
          (fun _ => rfl) output enough pending
      refine ⟨0, z.avail_out.toNat, Z_OK, after, z', result, run, stateA.good, buffersA, accountA, Or.inl rfl, ?_⟩
      apply Or.inl
      refine ⟨input, origin, base, xs, 0, stateA, ?_, ?_, Nat.le_refl _, ?_, ?_, quality, by simp, ?_⟩
      · rw [fields]; exact status
      · rw [fields]; simp [fillEnd]
      · rw [fields]; exact candidate
      · rw [fields]; exact floor
      · have bits : result.bi_valid = d.bi_valid := by rw [fields]
        rw [bits]
        simp only [Nat.sub_self, Nat.add_zero, Nat.mul_zero]
        omega
    · have pending0 := last_flush_pending_bits boundary.good pending Z_FINISH
      obtain ⟨_pb, drained, middle, zm, dm, _written, _remaining, _base, flushRun, stateM, buffersM,
        accountM, _sizesM, _storageM, amount, _pendingCount, fields, readyM, _bytesM, _pendingM, _wire⟩ :=
        flush_pending_buffered_boundary boundary0 buffers0 pointer pending0
      have statusM : dm.status = BUSY_STATE := by rw [fields]; exact status
      have levelM : dm.level = 6 := by rw [fields]; exact level
      have strategyM : dm.strategy = 0 := by rw [fields]; exact strategy
      have drainedEq : drained = d.pending.toNat := by
        change drained = min d.pending.toNat z.avail_out.toNat at amount
        rw [Nat.min_eq_left (by omega)] at amount
        exact amount
      have left : 0 < zm.avail_out.toNat := by have balance := accountM.2.2.2.1; omega
      have pointerM : zm.next_out = .ref (.blk ob) (oo + drained) := by rw [accountM.2.2.2.2.2.1, pointer]; rfl
      have candidateM : ShortCandidateQuality dm := by rw [fields]; exact candidate
      have floorM : StoredSourceFloor dm := by rw [fields]; exact floor
      obtain ⟨used, amountA, rc, after, z', result, run, goodA, buffersA, accountA, allowed,
        _bitsA, phaseA, _lastA, _endedA⟩ :=
        public_busy_slow_finish_counted_size stateM buffersM statusM levelM strategyM pointerM memory wrap (readyM left)
          window candidateM floorM quality (input_valid_accounting_output valid accountM)
      have entry := public_pending_finish_continue boundary.good stateM.good nonnull positive valid queued flushRun
        (by intro zero; rw [zero] at left; contradiction) (by
          intro impossible; rw [statusM] at impossible; cases (show BUSY_STATE ≠ FINISH_STATE from by decide) impossible)
      have endM : fillEnd dm = fillEnd d := by rw [fields]; rfl
      have bitsM : dm.bi_valid = d.bi_valid := by rw [fields]
      have cost := finish_result_after_drain endM bitsM (Nat.le_of_eq drainedEq) phaseA
      refine ⟨used, drained + amountA, rc, after, z', result,
        entry.trans ((public_busy_header_skip stateM.good statusM).trans run), goodA, buffersA, ?_, allowed, cost⟩
      simpa only [Nat.zero_add] using stream_accounting_trans accountM accountA

end Zlib.Deflate.Engine.Proofs
