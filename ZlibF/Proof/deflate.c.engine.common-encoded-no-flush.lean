import ZlibF.Proof.«deflate.c.engine.common-encoded-refusals»
import ZlibF.Proof.«deflate.c.engine.common-header-resume-input»
import ZlibF.Proof.«deflate.c.engine.common-busy-no-flush-input»

/-! # All positive ordinary requests advance the observed encoding state -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Every positive raw-output NO_FLUSH request with a valid input pointer
preserves the same cumulative observed encoding. This includes split
headers, working compression, duplicate refusal and wrong-flush
refusal after the final block. No resumption condition is assumed. -/
theorem CommonEncodingState.no_flush_positive_result {h : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig} {accepted observed actualInput : List UInt8}
    (state : CommonEncodingState h r ds z d config accepted observed) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (output : 0 < z.avail_out.toNat)
    (valid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (snapshot : Bytes h z.next_in z.avail_in.toNat actualInput) :
    ∃ used rc after z' result written,
      deflate (some r) Z_NO_FLUSH h = .ok (rc, after) ∧
      CommonEncodingState after r ds z' result config
        (accepted ++ actualInput.take used) (observed ++ written) ∧
      StreamBuffers after r ∧ StreamAccounting z z' used written.length ∧
      Bytes after z.next_out written.length written ∧ rc ≠ Z_STREAM_END := by
  have raw : z.next_out = .null ∨ ∃ ob oo, z.next_out = .ref (.blk ob) oo := Or.inr ⟨ob, oo, pointer⟩
  have out : z.next_out ≠ .null := by rw [pointer]; intro eq; cases eq
  have positive : z.avail_out ≠ 0 := by intro eq; rw [eq] at output; cases output
  have options := state.protocol.configuration
  rcases state.phase with ⟨emptyInput, headerOutput, input, boundary, status, encoding⟩ |
      ⟨input, origin, base, xs, published, outputEq, boundary, status, encoding, inputEq⟩ |
      ⟨published, outputEq, phase, encoding⟩
  · subst accepted observed
    have low : 4 ≤ d.level.toInt := by
      have eq : d.level = config.level := congrArg EngineConfig.level boundary.configuration
      rw [eq]; exact options.level_low
    have high : d.level.toInt ≤ 9 := by
      have eq : d.level = config.level := congrArg EngineConfig.level boundary.configuration
      rw [eq]; exact options.level_high
    have strategy : d.strategy = 0 := (congrArg EngineConfig.strategy boundary.configuration).trans options.strategy
    have empty : inputPrefix input (0 + fillEnd d) = [] := by
      obtain ⟨_remaining, _pending, _wire, _bits, start, look⟩ := encoding
      simp only [fillEnd, start, look, UInt32.toNat_zero, Nat.add_zero, inputPrefix, List.range_zero, List.map_nil]
    have checksum : z.adler = (ZlibF.Spec.adler32 (inputPrefix input (0 + fillEnd d))).toUInt64 := by
      rw [empty]; exact state.checksum
    obtain ⟨used, after, z', result, nextInput, nextOrigin, nextBase, ys, written,
        run, stateA, buffersA, accountA, bytesA, _agrees, _endpoint, statusA, _last,
        encodingA, checksumA, inputA⟩ :=
      public_common_header_pending_no_flush_encoding_input boundary buffers pointer valid status low high strategy
        options.memory options.wrap output snapshot checksum encoding
    rw [empty, List.nil_append] at inputA
    have protocolA := common_request_protocol_of_run state.protocol buffers raw (Or.inl rfl) run stateA.good
    have length : ([(levelHeaderWord config.level &&& 0xff).toUInt8] ++ written : List UInt8).length = 1 + written.length := by
      simp only [List.length_append, List.length_cons, List.length_nil]
    refine ⟨used, Z_OK, after, z', result, [(levelHeaderWord config.level &&& 0xff).toUInt8] ++ written, run, ⟨protocolA, ?_, ?_⟩, buffersA, ?_, ?_, by decide⟩
    · rw [inputA] at checksumA; exact checksumA
    · refine Or.inr (Or.inl ⟨nextInput, nextOrigin, nextBase, ys, written, ?_,
        stateA, statusA, encodingA, inputA⟩)
      have msb : (levelHeaderWord config.level >>> 8).toUInt8 = 120 := by
        rcases level_header_word_cases config.level with eq | eq | eq | eq <;> rw [eq] <;> rfl
      simp only [levelHeaderPrefix, msb, List.cons_append, List.nil_append]
    · rw [length]; exact accountA
    · rw [length]; exact bytesA
  · have low : 4 ≤ d.level.toInt := by
      have eq : d.level = config.level := congrArg EngineConfig.level boundary.configuration
      rw [eq]; exact options.level_low
    have high : d.level.toInt ≤ 9 := by
      have eq : d.level = config.level := congrArg EngineConfig.level boundary.configuration
      rw [eq]; exact options.level_high
    have strategy : d.strategy = 0 := (congrArg EngineConfig.strategy boundary.configuration).trans options.strategy
    have checksum : z.adler = (ZlibF.Spec.adler32 (inputPrefix input (origin + fillEnd d))).toUInt64 := by
      rw [inputEq]; exact state.checksum
    by_cases resume : d.pending ≠ 0 ∨ z.avail_in ≠ 0 ∨ d.last_flush = -1 ∨ d.last_flush = -2
    · obtain ⟨used, after, z', result, nextInput, nextOrigin, nextBase, ys, written,
          run, stateA, buffersA, accountA, bytesA, _agrees, _endpoint, _base,
          statusA, _last, encodingA, checksumA, inputA⟩ :=
        public_common_slow_no_flush_accepted_raw_prefix_input boundary buffers status low high strategy pointer output
          options.memory options.wrap valid state.protocol.lower state.protocol.upper resume snapshot checksum encoding
      rw [inputEq] at inputA
      have protocolA := common_request_protocol_of_run state.protocol buffers raw (Or.inl rfl) run stateA.good
      refine ⟨used, Z_OK, after, z', result, written, run, ⟨protocolA, ?_, ?_⟩, buffersA, accountA, bytesA, by decide⟩
      · rw [inputA] at checksumA; exact checksumA
      · exact Or.inr (Or.inl ⟨nextInput, nextOrigin, nextBase, ys, published ++ written,
          by rw [outputEq, List.append_assoc], stateA, statusA, encodingA, inputA⟩)
    · have pending : d.pending = 0 := by
        by_cases zero : d.pending = 0
        · exact zero
        · exact False.elim (resume (Or.inl zero))
      have inputEmpty : z.avail_in = 0 := by
        by_cases zero : z.avail_in = 0
        · exact zero
        · exact False.elim (resume (Or.inr (Or.inl zero)))
      have lower : 0 ≤ d.last_flush.toInt := by
        have lower := state.protocol.lower
        have notOne : d.last_flush.toInt ≠ -1 := fun eq => resume (Or.inr (Or.inr (Or.inl (Int32.toInt_inj.mp eq))))
        have notTwo : d.last_flush.toInt ≠ -2 := fun eq => resume (Or.inr (Or.inr (Or.inr (Int32.toInt_inj.mp eq))))
        omega
      have state0 := last_flush_buffered_boundary boundary Z_NO_FLUSH
      have buffers0 := last_flush_buffers boundary.good buffers Z_NO_FLUSH
      obtain ⟨message, errorRun⟩ := err_return_run state0.good.live.hz Z_BUF_ERROR
      have source := public_busy_no_flush_duplicate_source boundary.good status inputEmpty pending out positive lower state.protocol.upper
      have run := source.trans errorRun
      have goodA := stream_control_good (z' := {z with msg := message}) state0.good rfl state0.good.live.zalloc state0.good.live.zfree
      have stateA := stream_control_buffered state0 goodA
      have accountA : StreamAccounting z {z with msg := message} 0 0 := stream_accounting_zero z
      have buffersA := stream_control_buffers state0.good goodA buffers0 accountA
      have protocolA := common_request_protocol_of_run state.protocol buffers raw (Or.inl rfl) run goodA
      have encodingA := (encoding.last_flush boundary.good Z_NO_FLUSH).put_stream r {z with msg := message}
      have nextState : CommonEncodingState _ r ds {z with msg := message} {d with last_flush := Z_NO_FLUSH}
          config accepted observed := ⟨protocolA, state.checksum,
        Or.inr (Or.inl ⟨input, origin, base, xs, published, outputEq, stateA, status, encodingA, inputEq⟩)⟩
      refine ⟨0, Z_BUF_ERROR, _, _, {d with last_flush := Z_NO_FLUSH}, [], run, ?_, buffersA, accountA, ?_, by decide⟩
      · simpa only [List.take_zero, List.append_nil] using nextState
      · exact caller_output_zero_slice (z := {z with msg := message}) goodA buffersA
  · obtain ⟨after, z', run, stateA, buffersA, accountA, bytesA⟩ :=
      state.error_source buffers Z_NO_FLUSH Z_STREAM_ERROR
        (public_stream_guard_refusal state.protocol.good Z_NO_FLUSH (by decide) (by decide)
          (Or.inr (Or.inr ⟨phase.status, by decide⟩)))
    refine ⟨0, Z_STREAM_ERROR, after, z', d, [], run, ?_, buffersA, accountA, bytesA, by decide⟩
    simpa only [List.take_zero, List.append_nil] using stateA

/-- Encoding preservation without retaining the separate non-END result. -/
theorem CommonEncodingState.no_flush_positive {h : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig} {accepted observed actualInput : List UInt8}
    (state : CommonEncodingState h r ds z d config accepted observed) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (output : 0 < z.avail_out.toNat)
    (valid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (snapshot : Bytes h z.next_in z.avail_in.toNat actualInput) :
    ∃ used rc after z' result written,
      deflate (some r) Z_NO_FLUSH h = .ok (rc, after) ∧
      CommonEncodingState after r ds z' result config
        (accepted ++ actualInput.take used) (observed ++ written) ∧
      StreamBuffers after r ∧ StreamAccounting z z' used written.length ∧
      Bytes after z.next_out written.length written := by
  obtain ⟨used, rc, after, z', result, written, run, stateA, buffersA, accountA, bytesA, _notEnd⟩ :=
    state.no_flush_positive_result buffers pointer output valid snapshot
  exact ⟨used, rc, after, z', result, written, run, stateA, buffersA, accountA, bytesA⟩

end Zlib.Deflate.Engine.Proofs
