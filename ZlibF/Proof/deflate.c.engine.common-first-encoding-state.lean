import ZlibF.Proof.«deflate.c.engine.common-first-input»
import ZlibF.Proof.«deflate.c.engine.common-encoded-state»

/-! # Every positive first NO_FLUSH capacity establishes common encoding -/
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Every positive first raw-output NO_FLUSH call establishes the same
post-header cumulative encoding invariant. Capacity one leaves a header
byte; capacities two and above reach actual compression, including zero
remaining public output after the header. -/
theorem public_common_first_no_flush_encoding_state {h : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {config : EngineConfig}
    {actualInput : List UInt8}
    (initial : EngineStart h r ds z d)
    (boundary : BufferedBoundary h r ds z d input 0 0 [] config)
    (configuration : CommonSlowFinishConfig config) (reachable : StreamReachable .deflate h r)
    (buffers : StreamBuffers h r) (pointer : z.next_out = .ref (.blk ob) oo)
    (output : 0 < z.avail_out.toNat) (valid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (snapshot : Bytes h z.next_in z.avail_in.toNat actualInput) :
    ∃ used after z' result written,
      deflate (some r) Z_NO_FLUSH h = .ok (Z_OK, after) ∧
      CommonEncodingState after r ds z' result config (actualInput.take used) written ∧
      StreamBuffers after r ∧ StreamAccounting z z' used written.length ∧
      Bytes after z.next_out written.length written := by
  have levelEq : d.level = config.level := congrArg EngineConfig.level boundary.configuration
  have low : 4 ≤ d.level.toInt := by rw [levelEq]; exact configuration.level_low
  have high : d.level.toInt ≤ 9 := by rw [levelEq]; exact configuration.level_high
  obtain ⟨used, after, z', result, nextInput, nextOrigin, nextBase, ys, written,
      run, stateA, buffersA, accountA, bytesA, _agrees, _endpoint, statusA, lastA,
      checksumA, inputA, phasesA⟩ := public_common_first_no_flush_encoding_input initial low high
        boundary buffers pointer output configuration.memory valid snapshot
  have noHeader : d.gzhead = none := (congrArg EngineConfig.header boundary.configuration).trans configuration.header
  have reachableA : StreamReachable .deflate after r := by
    apply StreamReachable.step (call := .deflate (some r) Z_NO_FLUSH) (value := Z_OK) reachable
    · exact ⟨rfl, rfl⟩
    · exact ⟨buffers, default_finish_active_header boundary.good noHeader⟩
    · simpa only [Call.execute, heapCall, run]
  have lower : -2 ≤ result.last_flush.toInt := by rcases lastA with eq | eq <;> rw [eq] <;> decide
  have upper : result.last_flush.toInt ≤ 5 := by rcases lastA with eq | eq <;> rw [eq] <;> decide
  have protocolA : CommonSlowFinishBoundary after r ds z' result config :=
    ⟨stateA.good, reachableA, configuration,
      Or.inl ⟨nextInput, nextOrigin, nextBase, ys, stateA, statusA⟩, lower, upper⟩
  refine ⟨used, after, z', result, written, run, ⟨protocolA, ?_, ?_⟩, buffersA, accountA, bytesA⟩
  · rw [inputA] at checksumA; exact checksumA
  · rcases phasesA with ⟨zero, writtenEq, originEq, baseEq, symbolsEq, headerA⟩ |
        ⟨rawWritten, writtenEq, encodingA⟩
    · subst nextOrigin nextBase ys
      exact Or.inl ⟨by rw [zero]; rfl, writtenEq, nextInput, stateA, statusA, headerA⟩
    · exact Or.inr (Or.inl ⟨nextInput, nextOrigin, nextBase, ys, rawWritten, writtenEq,
        stateA, statusA, encodingA, inputA⟩)

end Zlib.Deflate.Engine.Proofs
