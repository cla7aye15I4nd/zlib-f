import ZlibF.Proof.«deflate.c.engine.generic-foreign-header-finish-continue-input»

/-! # Every positive split-header FINISH continuation retains exact encoding -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Every actual positive-output FINISH request after a one-byte header
completes the remaining header byte and retains the correlated working or
completed representation. The accepted input is precisely the consumed
original caller snapshot. Header exhaustion consumes no input. -/
theorem public_foreign_header_finish_encoding {h : Heap} {r : ZStreamRef} {ds owner oo : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {config : EngineConfig} {actualInput : List UInt8}
    (boundary : BufferedBoundary h r ds z d input 0 0 [] config) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (valid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (status : d.status = BUSY_STATE) (level : d.level = 6) (strategy : d.strategy = 0)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (output : 0 < z.avail_out.toNat)
    (snapshot : Bytes h z.next_in z.avail_in.toNat actualInput)
    (checksum : z.adler = (ZlibF.Spec.adler32 []).toUInt64) (encoding : HeaderPending h d [120]) :
    ∃ used rc after z' result rawWritten accepted,
      accepted = actualInput.take used ∧ deflate (some r) Z_FINISH h = .ok (rc, after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' used (1 + rawWritten.length) ∧
      Bytes after z.next_out (1 + rawWritten.length) ([156] ++ rawWritten) ∧
      z'.adler = (ZlibF.Spec.adler32 accepted).toUInt64 ∧
      ((∃ nextInput nextOrigin nextBase ys,
          BufferedBoundary after r ds z' result nextInput nextOrigin nextBase ys config ∧ result.status = BUSY_STATE ∧
          RawPrefix after result nextInput nextBase rawWritten ∧
          inputPrefix nextInput (nextOrigin + fillEnd result) = accepted) ∨
       (FinishingPhase result config ∧ FinishedEncoding after result accepted rawWritten)) ∧
      (rc = Z_STREAM_END → ZlibF.Spec.Zlib.Valid accepted ([120,156] ++ rawWritten)) := by
  by_cases one : z.avail_out.toNat = 1
  · have originalEncoding := encoding
    obtain ⟨_remaining, _pending, _headerEq, _bits, start, look⟩ := originalEncoding
    have prefixNil : inputPrefix input (0 + fillEnd d) = [] := by
      simp only [fillEnd, start, look, UInt32.toNat_zero, Nat.add_zero, inputPrefix, List.range_zero, List.map_nil]
    have checksum0 : z.adler = (ZlibF.Spec.adler32 (inputPrefix input (0 + fillEnd d))).toUInt64 := by
      simpa only [prefixNil] using checksum
    obtain ⟨after, z', result, run, stateA, buffersA, accountA, bytesA,
        _outA, statusA, _lastA, _pendingA, encodingA, checksumA,endA⟩ :=
      public_foreign_header_pending_one_output_encoding_adler Z_FINISH boundary buffers pointer valid status
        (UInt32.toNat_inj.mp one) (by decide) (by decide) checksum0 encoding
    have prefixNilA : inputPrefix input (0 + fillEnd result) = [] := by rw [endA]; exact prefixNil
    refine ⟨0, Z_OK, after, z', result, [], [], by simp, run, stateA.good, buffersA,
      accountA, bytesA, ?_, Or.inl ⟨input, 0, 0, [], stateA, statusA, encodingA, prefixNilA⟩, ?_⟩
    · simpa only [prefixNilA] using checksumA
    · intro impossible
      cases (show Z_OK ≠ Z_STREAM_END from by decide) impossible
  · exact public_foreign_header_finish_continue_encoding boundary buffers pointer valid status level strategy memory wrap
      (by omega) snapshot checksum encoding

end Zlib.Deflate.Engine.Proofs
