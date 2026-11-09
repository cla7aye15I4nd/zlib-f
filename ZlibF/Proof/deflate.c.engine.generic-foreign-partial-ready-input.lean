import ZlibF.Proof.«deflate.c.engine.generic-foreign-partial-data-input»
import ZlibF.Proof.«deflate.c.engine.public-nonfinal-ready-encoding»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Every PARTIAL BUSY request with no old pending bytes retains
raw encoding and Adler for exactly the consumed original caller input.
The actual rank/duplicate check is executed, including empty-input BUF_ERROR
refusal. No resumption/rank condition or callee contract is assumed.
Null/zero-output refusals, old pending and the initial header are separate. -/
theorem public_foreign_busy_partial_ready_raw_prefix_input {h : Heap} {r : ZStreamRef} {ds owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    {published : List UInt8}
    (boundary : BufferedBoundary h r ds z d input origin base xs config) (buffers : StreamBuffers h r)
    (status : d.status = BUSY_STATE) (level : d.level = 6) (strategy : d.strategy = 0)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (memory : config.memory.toNat = 16384)
    (wrap : config.wrap = 1) (pending : d.pending = 0) (output : 0 < z.avail_out.toNat)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (lower : -2 ≤ d.last_flush.toInt) (upper : d.last_flush.toInt ≤ 5)
    {actualInput : List UInt8} (snapshot : Bytes h z.next_in z.avail_in.toNat actualInput)
    (checksum : z.adler = (ZlibF.Spec.adler32 (inputPrefix input (origin + fillEnd d))).toUInt64)
    (encoding : RawPrefix h d input base published) :
    ∃ used rc after z' result extended nextOrigin nextBase ys written,
      deflate (some r) Z_PARTIAL_FLUSH h = .ok (rc, after) ∧
      BufferedBoundary after r ds z' result extended nextOrigin nextBase ys config ∧
      StreamBuffers after r ∧ StreamAccounting z z' used written.length ∧ Bytes after z.next_out written.length written ∧
      (∀ i, i < origin + fillEnd d → extended i = input i) ∧
      nextOrigin + fillEnd result = origin + fillEnd d + used ∧ base ≤ nextBase ∧
      (rc = Z_OK ∨ rc = Z_BUF_ERROR) ∧ result.status = BUSY_STATE ∧
      (result.last_flush = Z_PARTIAL_FLUSH ∨ result.last_flush = -1) ∧
      RawPrefix after result extended nextBase (published ++ written) ∧
      z'.adler = (ZlibF.Spec.adler32 (inputPrefix extended (nextOrigin + fillEnd result))).toUInt64 ∧
      inputPrefix extended (nextOrigin + fillEnd result) =
        inputPrefix input (origin + fillEnd d) ++ actualInput.take used := by
  have flagLo : 0 ≤ Z_PARTIAL_FLUSH.toInt := by decide
  have flagHi : Z_PARTIAL_FLUSH.toInt ≤ 5 := by decide
  have nonnull : z.next_out ≠ .null := by rw [pointer]; intro eq; cases eq
  have positive : z.avail_out ≠ 0 := by intro zero; rw [zero] at output; cases output
  have state0 := last_flush_buffered_boundary boundary Z_PARTIAL_FLUSH
  have buffers0 := last_flush_buffers boundary.good buffers Z_PARTIAL_FLUSH
  have publish0 : PublishReady { d with last_flush := Z_PARTIAL_FLUSH } := ⟨pending, boundary.empty_cursor pending, boundary.bits⟩
  have encoding0 := encoding.last_flush boundary.good Z_PARTIAL_FLUSH
  have snapshot0 := caller_bytes_setD_depth (result := {d with last_flush := Z_PARTIAL_FLUSH}) boundary.good.live.hs rfl snapshot
  obtain ⟨current, old, _currentRank, _oldRank, source⟩ := public_busy_valid_entry_choice boundary.good
    status pending nonnull positive inputValid lower upper Z_PARTIAL_FLUSH flagLo flagHi
  by_cases duplicate : (z.avail_in == 0 && decide (current ≤ old) && Z_PARTIAL_FLUSH != Z_FINISH) = true
  · rw [ite_eq_left duplicate] at source
    obtain ⟨message, refused⟩ := err_return_run state0.good.live.hz Z_BUF_ERROR
    let z' := {z with msg := message}
    have goodA := stream_control_good (z' := z') state0.good rfl boundary.good.live.zalloc boundary.good.live.zfree
    have accountA : StreamAccounting z z' 0 0 := stream_accounting_zero z
    have buffersA := stream_control_buffers state0.good goodA buffers0 accountA
    have stateA := stream_control_buffered state0 goodA
    refine ⟨0, Z_BUF_ERROR, _, z', {d with last_flush := Z_PARTIAL_FLUSH}, input, origin, base, xs, [],
      source.trans refused, stateA, buffersA, accountA, caller_output_zero_slice (z := z') goodA buffersA,
      fun _ _ => rfl, by rfl, Nat.le_refl _, Or.inr rfl, status, Or.inl rfl, ?_, checksum, ?_⟩
    · simpa only [List.append_nil] using encoding0.put_stream r z'
    · simp only [List.take_zero, List.append_nil, fillEnd]
  · rw [ite_eq_right duplicate] at source
    obtain ⟨used, after, z', result, extended, nextOrigin, nextBase, ys, written,
        run, stateA, buffersA, accountA, bytesA, agreesA, endpointA, baseA,
        statusA, lastA, encodingA, checksumA, inputLedgerA,_intervalA⟩ :=
      public_foreign_busy_partial_data_raw_prefix_input_interval (state0.strategy publish0) state0.end_frontier buffers0 status level strategy pointer memory wrap publish0
        inputValid snapshot0 checksum encoding0
    exact ⟨used, Z_OK, after, z', result, extended, nextOrigin, nextBase, ys, written,
      source.trans run, stateA, buffersA, accountA, bytesA, agreesA, endpointA, baseA, Or.inl rfl,
      statusA, lastA, encodingA, checksumA, inputLedgerA⟩

end Zlib.Deflate.Engine.Proofs
