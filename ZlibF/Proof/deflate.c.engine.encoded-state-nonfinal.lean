import ZlibF.Proof.«deflate.c.engine.encoded-state-refusals»
import ZlibF.Proof.«deflate.c.engine.public-first-nonfinal-input»
import ZlibF.Proof.«deflate.c.engine.public-header-nonfinal-input»
import ZlibF.Proof.«deflate.c.engine.public-nonfinal-accepted-encoding»

/-! # Every positive nonfinal request advances the observed encoding state -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Every valid non-FINISH request with positive raw output and a valid
input pointer retains the same observed encoding invariant. Initial and
split headers, all working flags, duplicates and finished-state refusals
are included. Exact consumed original input and output extend the log;
no successful-call or resumption condition is assumed. -/
theorem DefaultEncodingState.nonfinal_positive_result {h : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig} {accepted observed actualInput : List UInt8}
    (state : DefaultEncodingState h r ds z d config accepted observed) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (output : 0 < z.avail_out.toNat)
    (valid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (flush : Int32) (flag : flush = Z_NO_FLUSH ∨ flush = Z_PARTIAL_FLUSH ∨ flush = Z_SYNC_FLUSH ∨
      flush = Z_FULL_FLUSH ∨ flush = Z_BLOCK)
    (snapshot : Bytes h z.next_in z.avail_in.toNat actualInput) :
    ∃ used rc after z' result written,
      deflate (some r) flush h = .ok (rc, after) ∧
      DefaultEncodingState after r ds z' result config
        (accepted ++ actualInput.take used) (observed ++ written) ∧
      StreamBuffers after r ∧ StreamAccounting z z' used written.length ∧
      Bytes after z.next_out written.length written ∧ rc ≠ Z_STREAM_END := by
  have raw : z.next_out = .null ∨ ∃ ob oo, z.next_out = .ref (.blk ob) oo := Or.inr ⟨ob, oo, pointer⟩
  have out : z.next_out ≠ .null := by rw [pointer]; intro eq; cases eq
  have positive : z.avail_out ≠ 0 := by intro eq; rw [eq] at output; cases output
  have flagLo : 0 ≤ flush.toInt := by rcases flag with rfl | rfl | rfl | rfl | rfl <;> decide
  have flagHi : flush.toInt ≤ 5 := by rcases flag with rfl | rfl | rfl | rfl | rfl <;> decide
  have nonfinal : flush ≠ Z_FINISH := by rcases flag with rfl | rfl | rfl | rfl | rfl <;> decide
  have options := state.protocol.configuration
  rcases state.phase with ⟨emptyInput, emptyOutput, input, start, boundary⟩ |
      ⟨emptyInput, headerOutput, input, boundary, status, encoding⟩ |
      ⟨input, origin, base, xs, published, outputEq, boundary, status, encoding, inputEq⟩ |
      ⟨published, outputEq, phase, encoding⟩
  · subst accepted observed
    have level : d.level = 6 := (congrArg EngineConfig.level boundary.configuration).trans options.level
    obtain ⟨used, after, z', result, nextInput, nextOrigin, nextBase, ys, written,
        run, stateA, buffersA, accountA, bytesA, _agrees, _endpoint, statusA, _last,
        checksumA, inputA, phasesA⟩ :=
      public_first_nonfinal_encoding_input start level boundary buffers pointer output options.memory valid flush flag snapshot
    have protocolA := default_request_protocol_of_run state.protocol buffers raw run stateA.good
    refine ⟨used, Z_OK, after, z', result, written, run, ⟨protocolA, ?_, ?_⟩, buffersA, accountA, bytesA, by decide⟩
    · rw [inputA] at checksumA; exact checksumA
    · rcases phasesA with ⟨zeroUsed, writtenEq, originEq, baseEq, symbolsEq, headerA⟩ |
          ⟨rawWritten, writtenEq, encodingA⟩
      · subst nextOrigin nextBase ys
        exact Or.inr (Or.inl ⟨by rw [zeroUsed]; rfl, writtenEq, nextInput, stateA, statusA, headerA⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨nextInput, nextOrigin, nextBase, ys, rawWritten, writtenEq,
          stateA, statusA, encodingA, inputA⟩))
  · subst accepted observed
    have level : d.level = 6 := (congrArg EngineConfig.level boundary.configuration).trans options.level
    have strategy : d.strategy = 0 := (congrArg EngineConfig.strategy boundary.configuration).trans options.strategy
    have empty : inputPrefix input (0 + fillEnd d) = [] := by
      obtain ⟨_remaining, _pending, _wire, _bits, start, look⟩ := encoding
      simp only [fillEnd, start, look, UInt32.toNat_zero, Nat.add_zero, inputPrefix, List.range_zero, List.map_nil]
    have checksum : z.adler = (ZlibF.Spec.adler32 (inputPrefix input (0 + fillEnd d))).toUInt64 := by
      rw [empty]; exact state.checksum
    obtain ⟨used, after, z', result, nextInput, nextOrigin, nextBase, ys, written,
        run, stateA, buffersA, accountA, bytesA, _agrees, _endpoint, statusA, _last,
        encodingA, checksumA, inputA⟩ :=
      public_header_pending_nonfinal_encoding_input boundary buffers pointer valid status level strategy
        options.memory options.wrap output flush flag snapshot checksum encoding
    rw [empty, List.nil_append] at inputA
    have protocolA := default_request_protocol_of_run state.protocol buffers raw run stateA.good
    have length : ([156] ++ written : List UInt8).length = 1 + written.length := by
      simp only [List.length_append, List.length_cons, List.length_nil]
    refine ⟨used, Z_OK, after, z', result, [156] ++ written, run, ⟨protocolA, ?_, ?_⟩, buffersA, ?_, ?_, by decide⟩
    · rw [inputA] at checksumA; exact checksumA
    · exact Or.inr (Or.inr (Or.inl ⟨nextInput, nextOrigin, nextBase, ys, written, rfl,
        stateA, statusA, encodingA, inputA⟩))
    · rw [length]; exact accountA
    · rw [length]; exact bytesA
  · have level : d.level = 6 := (congrArg EngineConfig.level boundary.configuration).trans options.level
    have strategy : d.strategy = 0 := (congrArg EngineConfig.strategy boundary.configuration).trans options.strategy
    have checksum : z.adler = (ZlibF.Spec.adler32 (inputPrefix input (origin + fillEnd d))).toUInt64 := by
      rw [inputEq]; exact state.checksum
    obtain ⟨used, rc, after, z', result, nextInput, nextOrigin, nextBase, ys, written,
        run, stateA, buffersA, accountA, bytesA, _agrees, _endpoint, _base, codes,
        statusA, _last, encodingA, checksumA, inputA⟩ :=
      public_busy_nonfinal_accepted_raw_prefix_input boundary buffers status level strategy pointer output
        options.memory options.wrap valid state.protocol.lower state.protocol.upper flush flag snapshot checksum encoding
    rw [inputEq] at inputA
    have protocolA := default_request_protocol_of_run state.protocol buffers raw run stateA.good
    refine ⟨used, rc, after, z', result, written, run, ⟨protocolA, ?_, ?_⟩, buffersA, accountA, bytesA, ?_⟩
    · rw [inputA] at checksumA; exact checksumA
    · exact Or.inr (Or.inr (Or.inl ⟨nextInput, nextOrigin, nextBase, ys, published ++ written,
        by rw [outputEq, List.append_assoc], stateA, statusA, encodingA, inputA⟩))
    · intro ended
      rcases codes with ok | buffer
      · exact False.elim ((by decide : Z_OK ≠ Z_STREAM_END) (ok.symm.trans ended))
      · exact False.elim ((by decide : Z_BUF_ERROR ≠ Z_STREAM_END) (buffer.symm.trans ended))
  · obtain ⟨after, z', run, stateA, buffersA, accountA, bytesA⟩ :=
      state.error_source buffers flush Z_STREAM_ERROR
        (public_stream_guard_refusal state.protocol.good flush flagLo flagHi
          (Or.inr (Or.inr ⟨phase.status, nonfinal⟩)))
    refine ⟨0, Z_STREAM_ERROR, after, z', d, [], run, ?_, buffersA, accountA, bytesA, by decide⟩
    simpa only [List.take_zero, List.append_nil] using stateA

end Zlib.Deflate.Engine.Proofs
