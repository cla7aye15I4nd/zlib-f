import ZlibF.Proof.«deflate.c.engine.common-first-finish-encoding»
import ZlibF.Proof.«deflate.c.engine.common-first-finish-phase»
import ZlibF.Proof.«deflate.c.engine.common-encoded-state»

/-! # Every positive first FINISH capacity establishes common observed encoding -/
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Every positive-capacity actual first FINISH call establishes the
same cumulative encoding invariant and public protocol. Header splitting,
working compression and completed trailer publication use the same actual
run, caller snapshot and emitted bytes. -/
theorem public_common_first_finish_encoding_state {h : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {config : EngineConfig}
    {actualInput : List UInt8}
    (initial : EngineStart h r ds z d)
    (boundary : BufferedBoundary h r ds z d input 0 0 [] config)
    (configuration : CommonSlowFinishConfig config) (reachable : StreamReachable .deflate h r)
    (buffers : StreamBuffers h r) (pointer : z.next_out = .ref (.blk ob) oo)
    (output : 0 < z.avail_out.toNat) (valid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (snapshot : Bytes h z.next_in z.avail_in.toNat actualInput) :
    ∃ used rc after z' result written,
      deflate (some r) Z_FINISH h = .ok (rc, after) ∧
      CommonEncodingState after r ds z' result config (actualInput.take used) written ∧
      StreamBuffers after r ∧ StreamAccounting z z' used written.length ∧
      Bytes after z.next_out written.length written ∧
      (rc = Z_OK ∨ rc = Z_STREAM_END) ∧
      (rc = Z_STREAM_END → ZlibF.Spec.Zlib.Valid (actualInput.take used) written) := by
  have levelEq : d.level = config.level := congrArg EngineConfig.level boundary.configuration
  have low : 4 ≤ d.level.toInt := by rw [levelEq]; exact configuration.level_low
  have high : d.level.toInt ≤ 9 := by rw [levelEq]; exact configuration.level_high
  obtain ⟨used, rc, after, z', result, written, accepted, acceptedEq, run, goodA,
      buffersA, accountA, bytesA, checksumA, phasesA, ended⟩ :=
    public_common_first_finish_encoding_input initial low high boundary buffers pointer output configuration.memory
      valid snapshot
  subst accepted
  obtain ⟨_usedP, _producedP, rcP, heapP, zp, dp, runP, goodP, _buffersP, _accountP,
      allowedP, _bitsP, physicalP, lastP, _endedP⟩ := public_common_first_finish_phase initial low high boundary
        buffers pointer output configuration.memory valid
  obtain ⟨codes, heaps⟩ := Prod.mk.inj (Except.ok.inj (runP.symm.trans run))
  subst rcP heapP
  have streams : zp = z' := Option.some.inj (goodP.live.hz.symm.trans goodA.live.hz)
  have states : dp = result := Option.some.inj (goodP.live.hs.symm.trans goodA.live.hs)
  subst zp dp
  have noHeader : d.gzhead = none := (congrArg EngineConfig.header boundary.configuration).trans configuration.header
  have reachableA : StreamReachable .deflate after r := by
    apply StreamReachable.step (call := .deflate (some r) Z_FINISH) (value := rc) reachable
    · exact ⟨rfl, rfl⟩
    · exact ⟨buffers, default_finish_active_header boundary.good noHeader⟩
    · simpa only [Call.execute, heapCall, run]
  have lower : -2 ≤ result.last_flush.toInt := by rcases lastP with eq | eq <;> rw [eq] <;> decide
  have upper : result.last_flush.toInt ≤ 5 := by rcases lastP with eq | eq <;> rw [eq] <;> decide
  have protocolA : CommonSlowFinishBoundary after r ds z' result config :=
    ⟨goodA, reachableA, configuration, physicalP, lower, upper⟩
  refine ⟨used, rc, after, z', result, written, run, ⟨protocolA, checksumA, ?_⟩,
    buffersA, accountA, bytesA, allowedP, ended⟩
  rcases phasesA with ⟨zero, writtenEq, stateA, statusA, headerA⟩ |
      ⟨rawWritten, writtenEq, working⟩
  · exact Or.inl ⟨by rw [zero]; rfl, writtenEq, input, stateA, statusA, headerA⟩
  · rcases working with ⟨nextInput, nextOrigin, nextBase, ys, stateA, statusA, encodingA, inputA⟩ |
        ⟨phaseA, encodingA⟩
    · exact Or.inr (Or.inl ⟨nextInput, nextOrigin, nextBase, ys, rawWritten, writtenEq,
        stateA, statusA, encodingA, inputA⟩)
    · exact Or.inr (Or.inr ⟨rawWritten, writtenEq, phaseA, encodingA⟩)

end Zlib.Deflate.Engine.Proofs
