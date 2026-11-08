import ZlibF.Proof.«deflate.c.engine.public-no-flush-encoding»
import ZlibF.Proof.«deflate.c.engine.raw-prefix-ready»

/-! # Public data dispatch retains raw encoding when the header uses all output -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The actual prepared BUSY NO_FLUSH data path retains independent raw
encoding, exact final-heap output, both input-history frontiers and the
public retry/status controls. It includes the actual inactive dispatch.
The public entry/header/pending guards are composed separately. -/
theorem public_busy_no_flush_data_ready_raw_prefix {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    {published : List UInt8}
    (boundary : BufferedBoundary h r ds z d input origin base xs config) (buffers : StreamBuffers h r)
    (status : d.status = BUSY_STATE) (level : d.level = 6) (strategy : d.strategy = 0)
    (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (encoding : RawPrefix h d input base published) :
    ∃ used after z' result extended nextOrigin base' ys written,
      publicDataTail (some r) (some (.tab ds)) Z_NO_FLUSH h = .ok (Z_OK, after) ∧
      BufferedBoundary after r ds z' result extended nextOrigin base' ys config ∧ StreamBuffers after r ∧
      StreamAccounting z z' used written.length ∧ Bytes after z.next_out written.length written ∧
      (∀ i, i < origin + fillEnd d → extended i = input i) ∧
      nextOrigin + fillEnd result = origin + fillEnd d + used ∧ base ≤ base' ∧
      result.status = BUSY_STATE ∧ (result.last_flush = -1 ∨ result.last_flush = d.last_flush) ∧
      RawPrefix after result extended base' (published ++ written) := by
  by_cases active : z.avail_in ≠ 0 ∨ d.lookahead ≠ 0
  · have positive : 0 < config.level.toInt := by
      have eq := congrArg EngineConfig.level boundary.configuration
      change d.level = config.level at eq
      rw [← eq, level]
      decide
    obtain ⟨used, middle, zm, dm, nextInput, nextOrigin, nextBase, ys, written,
      strategyRun, strategyM, endM, buffersM, accountM, bytesM, agreesM, endpointM, baseM, encodingM⟩ :=
      deflate_slow_no_flush_ready_raw_prefix (boundary.strategy publish) boundary.end_frontier buffers positive pointer memory wrap publish inputValid encoding
    obtain ⟨_used, _produced, other, _z, otherD, _base, _ys, _input, _origin,
        otherRun, otherBoundary, controlsM, _buffers, _account, _agrees, _endpoint, _baseLe, _stopped, _consumed⟩ :=
      deflate_slow_no_flush_buffered_ready boundary buffers positive pointer memory wrap publish inputValid
    have heapEq : other = middle := (Prod.mk.inj (Except.ok.inj (otherRun.symm.trans strategyRun))).2
    rw [heapEq] at otherBoundary
    have stateEq : otherD = dm := Option.some.inj (otherBoundary.good.live.hs.symm.trans strategyM.good.live.hs)
    rw [stateEq] at controlsM
    have stateM := strategyM.buffered endM controlsM.empty_cursor
    have source : publicDataTail (some r) (some (.tab ds)) Z_NO_FLUSH h =
        publicStrategyReturn (some r) (some (.tab ds)) Z_NO_FLUSH need_more middle := by
      rw [public_busy_no_flush_slow_source boundary.good.live.hz boundary.good.live.hs status level strategy active]
      simp only [bind_app, strategyRun]
    have returned := public_need_more_return stateM.good.live.hz stateM.good.live.hs Z_NO_FLUSH
    by_cases empty : zm.avail_out = 0
    · simp only [empty, BEq.rfl, ite_true] at returned
      have bytesF : Bytes (setD middle ds { dm with last_flush := -1 }) z.next_out written.length written := by
        rw [pointer] at bytesM ⊢
        exact raw_output_bytes_setD bytesM
      exact ⟨used, _, zm, _, nextInput, nextOrigin, nextBase, ys, written,
        source.trans returned, last_flush_buffered_boundary stateM (-1), last_flush_buffers stateM.good buffersM (-1),
        accountM, bytesF, agreesM, endpointM, baseM, controlsM.status.trans status, Or.inl rfl,
        encodingM.last_flush stateM.good (-1)⟩
    · simp only [beq_eq_false_iff_ne.mpr empty, Bool.false_eq_true, ite_false] at returned
      exact ⟨used, middle, zm, dm, nextInput, nextOrigin, nextBase, ys, written,
        source.trans returned, stateM, buffersM, accountM, bytesM, agreesM, endpointM,
        baseM, controlsM.status.trans status, Or.inr controlsM.last_flush, encodingM⟩
  · have inputEmpty : z.avail_in = 0 := by
      by_cases empty : z.avail_in = 0
      · exact empty
      · exact False.elim (active (Or.inl empty))
    have lookEmpty : d.lookahead = 0 := by
      by_cases empty : d.lookahead = 0
      · exact empty
      · exact False.elim (active (Or.inr empty))
    have noBytes : Bytes h z.next_out 0 [] := by
      obtain ⟨array, get, _writable, bound, _owned⟩ := caller_raw_output boundary.good buffers pointer
      exact Or.inr ⟨.blk ob, oo, array, pointer, get, by omega, by simp⟩
    refine ⟨0, h, z, d, input, origin, base, xs, [], public_default_empty_data boundary.good status inputEmpty lookEmpty,
      boundary, buffers, stream_accounting_zero z, noBytes, fun _ _ => rfl,
      by omega, Nat.le_refl _, status, Or.inr rfl, ?_⟩
    simpa only [List.append_nil] using encoding

end Zlib.Deflate.Engine.Proofs
