import ZlibF.Proof.«deflate.c.engine.common-encoded-refusals»
import ZlibF.Proof.«deflate.c.engine.common-header-finish-encoding»
import ZlibF.Proof.«deflate.c.engine.common-finish-accepted-representation»
import ZlibF.Proof.«deflate.c.engine.common-finished-default-bridge»

/-! # Actual accepted FINISH calls advance the observed encoding invariant -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Every accepted actual FINISH call advances the same initialized
encoding invariant by its consumed original input and exact emitted bytes.
All positive raw output capacities and all three post-header protocol phases are
included. New input after FINISH_STATE has its separate refusal path. -/
theorem CommonEncodingState.finish_accepted {h : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig} {accepted observed actualInput : List UInt8}
    (state : CommonEncodingState h r ds z d config accepted observed) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (output : 0 < z.avail_out.toNat)
    (valid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (allowed : d.status = FINISH_STATE → z.avail_in = 0)
    (snapshot : Bytes h z.next_in z.avail_in.toNat actualInput) :
    ∃ used rc after z' result written,
      deflate (some r) Z_FINISH h = .ok (rc, after) ∧
      CommonEncodingState after r ds z' result config
        (accepted ++ actualInput.take used) (observed ++ written) ∧
      StreamBuffers after r ∧ StreamAccounting z z' used written.length ∧
      Bytes after z.next_out written.length written := by
  have raw : z.next_out = .null ∨ ∃ ob oo, z.next_out = .ref (.blk ob) oo := Or.inr ⟨ob, oo, pointer⟩
  have options := state.protocol.configuration
  rcases state.phase with ⟨emptyInput, headerOutput, input, boundary, status, encoding⟩ |
      ⟨input, origin, base, xs, published, outputEq, boundary, status, encoding, inputEq⟩ |
      ⟨published, outputEq, phase, encoding⟩
  · subst accepted observed
    have levelEq : d.level = config.level := congrArg EngineConfig.level boundary.configuration
    have low : 4 ≤ d.level.toInt := by rw [levelEq]; exact options.level_low
    have high : d.level.toInt ≤ 9 := by rw [levelEq]; exact options.level_high
    have strategy : d.strategy = 0 := (congrArg EngineConfig.strategy boundary.configuration).trans options.strategy
    obtain ⟨used, rc, after, z', result, rawWritten, nextAccepted, acceptedEq, run, goodA, buffersA,
        accountA, bytesA, checksumA, phasesA, _endedA⟩ :=
      public_common_header_finish_encoding boundary buffers pointer valid status low high strategy options.memory options.wrap
        output snapshot state.checksum encoding
    subst nextAccepted
    have protocolA := common_request_protocol_of_run state.protocol buffers raw (Or.inr rfl) run goodA
    have length : ([(levelHeaderWord config.level &&& 0xff).toUInt8] ++ rawWritten : List UInt8).length = 1 + rawWritten.length := by
      simp only [List.length_append, List.length_cons, List.length_nil]
    have headerEq : [120] ++ ([(levelHeaderWord config.level &&& 0xff).toUInt8] ++ rawWritten) =
        levelHeaderPrefix config.level ++ rawWritten := by
      have msb : (levelHeaderWord config.level >>> 8).toUInt8 = 120 := by
        rcases level_header_word_cases config.level with eq | eq | eq | eq <;> rw [eq] <;> rfl
      simp only [levelHeaderPrefix, msb, List.cons_append, List.nil_append]
    refine ⟨used, rc, after, z', result, [(levelHeaderWord config.level &&& 0xff).toUInt8] ++ rawWritten, run, ⟨protocolA, checksumA, ?_⟩, buffersA, ?_, ?_⟩
    · rcases phasesA with ⟨nextInput, nextOrigin, nextBase, ys, stateA, statusA, encodingA, nextInputEq⟩ |
          ⟨phaseA, encodingA⟩
      · exact Or.inr (Or.inl ⟨nextInput, nextOrigin, nextBase, ys, rawWritten, headerEq,
          stateA, statusA, encodingA, nextInputEq⟩)
      · exact Or.inr (Or.inr ⟨rawWritten, headerEq, phaseA, encodingA⟩)
    · rw [length]; exact accountA
    · rw [length]; exact bytesA
  · have levelEq : d.level = config.level := congrArg EngineConfig.level boundary.configuration
    have low : 4 ≤ d.level.toInt := by rw [levelEq]; exact options.level_low
    have high : d.level.toInt ≤ 9 := by rw [levelEq]; exact options.level_high
    have strategy : d.strategy = 0 := (congrArg EngineConfig.strategy boundary.configuration).trans options.strategy
    have checksum : z.adler = (ZlibF.Spec.adler32 (inputPrefix input (origin + fillEnd d))).toUInt64 := by
      rw [inputEq]
      exact state.checksum
    obtain ⟨used, rc, after, z', result, written, nextAccepted, acceptedEq, run, goodA, buffersA,
        accountA, bytesA, checksumA, phasesA, _endedA⟩ :=
      public_common_slow_finish_accepted_completed_encoding boundary buffers status low high strategy pointer options.memory
        options.wrap output state.protocol.lower state.protocol.upper valid snapshot checksum encoding
    rw [inputEq] at acceptedEq
    subst nextAccepted
    have protocolA := common_request_protocol_of_run state.protocol buffers raw (Or.inr rfl) run goodA
    have observedEq : observed ++ written = levelHeaderPrefix config.level ++ (published ++ written) := by
      rw [outputEq, List.append_assoc]
    refine ⟨used, rc, after, z', result, written, run, ⟨protocolA, checksumA, ?_⟩, buffersA, accountA, bytesA⟩
    rcases phasesA with ⟨nextInput, nextOrigin, nextBase, ys, stateA, statusA, encodingA, nextInputEq⟩ |
        ⟨phaseA, encodingA⟩
    · exact Or.inr (Or.inl ⟨nextInput, nextOrigin, nextBase, ys, published ++ written, observedEq,
        stateA, statusA, encodingA, nextInputEq⟩)
    · exact Or.inr (Or.inr ⟨published ++ written, observedEq, phaseA, encodingA⟩)
  · obtain ⟨rc, after, z', result, written, run, goodA, buffersA, accountA, bytesA, phaseA, encodingA, checksumA, _endedA⟩ :=
      public_common_finishing_encoding state.protocol.good buffers phase pointer (allowed phase.status) output
        state.protocol.lower state.protocol.upper state.checksum encoding
    have protocolA := common_request_protocol_of_run state.protocol buffers raw (Or.inr rfl) run goodA
    have observedEq : observed ++ written = levelHeaderPrefix config.level ++ (published ++ written) := by
      rw [outputEq, List.append_assoc]
    have stateA : CommonEncodingState after r ds z' result config accepted (observed ++ written) :=
      ⟨protocolA, checksumA, Or.inr (Or.inr ⟨published ++ written, observedEq, phaseA, encodingA⟩)⟩
    refine ⟨0, rc, after, z', result, written, run, ?_, buffersA, accountA, bytesA⟩
    simpa only [List.take_zero, List.append_nil] using stateA

end Zlib.Deflate.Engine.Proofs
