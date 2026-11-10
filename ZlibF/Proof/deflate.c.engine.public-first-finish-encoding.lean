import ZlibF.Proof.«deflate.c.engine.public-first-finish-complete-encoding»
import ZlibF.Proof.«deflate.c.engine.public-first-finish-one-encoding»

/-! # Every positive first FINISH capacity encodes its consumed original input -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Every actual first default FINISH call with positive raw output
capacity establishes the split-header, working or completed encoding
alternative for exactly its consumed original caller input. Actual init
fields supply the encoding seed and checksum. A STREAM_END call produces
an independently valid complete zlib stream on its final heap. -/
theorem public_first_finish_encoding_input {h : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {config : EngineConfig} {actualInput : List UInt8}
    (initial : EngineStart h r ds z d) (level : d.level = 6)
    (boundary : BufferedBoundary h r ds z d input 0 0 [] config) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (output : 0 < z.avail_out.toNat)
    (memory : config.memory.toNat = 16384) (valid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (snapshot : Bytes h z.next_in z.avail_in.toNat actualInput) :
    ∃ used rc after z' result written accepted,
      accepted = actualInput.take used ∧ deflate (some r) Z_FINISH h = .ok (rc, after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' used written.length ∧
      Bytes after z.next_out written.length written ∧ z'.adler = (ZlibF.Spec.adler32 accepted).toUInt64 ∧
      ((used = 0 ∧ written = [120] ∧
          BufferedBoundary after r ds z' result input 0 0 [] config ∧ result.status = BUSY_STATE ∧
          HeaderPending after result [120]) ∨
       (∃ rawWritten, written = [120,156] ++ rawWritten ∧
         ((∃ nextInput nextOrigin nextBase ys,
             BufferedBoundary after r ds z' result nextInput nextOrigin nextBase ys config ∧ result.status = BUSY_STATE ∧
             RawPrefix after result nextInput nextBase rawWritten ∧
             inputPrefix nextInput (nextOrigin + fillEnd result) = accepted) ∨
          (FinishingPhase result config ∧ FinishedEncoding after result accepted rawWritten)))) ∧
      (rc = Z_STREAM_END → ZlibF.Spec.Zlib.Valid accepted written) := by
  by_cases one : z.avail_out.toNat = 1
  · obtain ⟨after, z', result, run, stateA, buffersA, accountA, bytesA,
        _outA, statusA, _lastA, encodingA, checksumA⟩ :=
      public_first_finish_one_byte_encoding_adler initial level boundary buffers pointer (UInt32.toNat_inj.mp one) valid
    have originalEncoding := encodingA
    obtain ⟨_remaining, _pendingA, _headerA, _bitsA, startA, lookA⟩ := encodingA
    have prefixNil : inputPrefix input (0 + fillEnd result) = [] := by
      simp only [fillEnd, startA, lookA, UInt32.toNat_zero, Nat.add_zero, inputPrefix, List.range_zero, List.map_nil]
    refine ⟨0, Z_OK, after, z', result, [120], [], by simp, run, stateA.good, buffersA,
      accountA, bytesA, ?_, Or.inl ⟨rfl, rfl, stateA, statusA, originalEncoding⟩, ?_⟩
    · simpa only [prefixNil] using checksumA
    · intro impossible
      cases (show Z_OK ≠ Z_STREAM_END from by decide) impossible
  · obtain ⟨used, rc, after, z', result, rawWritten, accepted, acceptedA, run,
        goodA, buffersA, accountA, bytesA, checksumA, phasesA, endedA⟩ :=
      public_first_finish_complete_encoding initial level boundary buffers pointer (by omega) memory valid snapshot
    have length : ([120,156] ++ rawWritten : List UInt8).length = 2 + rawWritten.length := by
      simp only [List.length_append, List.length_cons, List.length_nil]
    refine ⟨used, rc, after, z', result, [120,156] ++ rawWritten, accepted, acceptedA, run,
      goodA, buffersA, ?_, ?_, checksumA, Or.inr ⟨rawWritten, rfl, phasesA⟩, endedA⟩
    · rw [length]; exact accountA
    · rw [length]; exact bytesA

end Zlib.Deflate.Engine.Proofs
