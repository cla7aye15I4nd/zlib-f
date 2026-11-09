import ZlibF.Proof.«deflate.c.engine.generic-foreign-header-no-flush-continue-input»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols ZlibF.Math.DeflateEncoding
set_option autoImplicit false

/-- The next accepted positive-output NO_FLUSH request after a one-byte
split header always emits 156 followed by its actual raw output. This
covers immediate output exhaustion and continuation into compression. -/
theorem public_foreign_header_pending_no_flush_encoding_input {h : Heap} {r : ZStreamRef} {ds owner oo origin : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : BufferedBoundary h r ds z d input origin 0 [] config) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (status : d.status = BUSY_STATE) (level : d.level = 6) (strategy : d.strategy = 0)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1)
    (output : 0 < z.avail_out.toNat)
    {actualInput : List UInt8} (snapshot : Bytes h z.next_in z.avail_in.toNat actualInput)
    (checksum : z.adler = (ZlibF.Spec.adler32 (inputPrefix input (origin + fillEnd d))).toUInt64)
    (encoding : HeaderPending h d [120]) :
    ∃ used after z' result nextInput nextOrigin nextBase ys rawWritten,
      deflate (some r) Z_NO_FLUSH h = .ok (Z_OK, after) ∧
      BufferedBoundary after r ds z' result nextInput nextOrigin nextBase ys config ∧ StreamBuffers after r ∧
      StreamAccounting z z' used (1 + rawWritten.length) ∧
      Bytes after z.next_out (1 + rawWritten.length) ([156] ++ rawWritten) ∧
      (∀ i, i < origin + fillEnd d → nextInput i = input i) ∧
      nextOrigin + fillEnd result = origin + fillEnd d + used ∧
      result.status = BUSY_STATE ∧ (result.last_flush = -1 ∨ result.last_flush = Z_NO_FLUSH) ∧
      RawPrefix after result nextInput nextBase rawWritten ∧
      z'.adler = (ZlibF.Spec.adler32 (inputPrefix nextInput (nextOrigin + fillEnd result))).toUInt64 ∧
      inputPrefix nextInput (nextOrigin + fillEnd result) =
        inputPrefix input (origin + fillEnd d) ++ actualInput.take used := by
  by_cases one : z.avail_out.toNat = 1
  · obtain ⟨after, z', result, run, stateA, buffersA, accountA, bytesA,
        _outA, statusA, lastA, _pendingA, encodingA, checksumA,endA⟩ :=
      public_foreign_header_pending_one_output_encoding_adler Z_NO_FLUSH boundary buffers pointer inputValid status
        (UInt32.toNat_inj.mp one) (by decide) (by decide) checksum encoding
    refine ⟨0, after, z', result, input, origin, 0, [], [], run, stateA, buffersA,
      accountA, bytesA, fun _ _ => rfl, ?_, statusA, Or.inl lastA, encodingA, checksumA, by simp only [endA, List.take_zero, List.append_nil]⟩
    rw [endA, Nat.add_zero]
  · exact public_foreign_header_pending_no_flush_continue_encoding_input boundary buffers pointer inputValid
      status level strategy memory wrap (by omega) snapshot checksum encoding

end Zlib.Deflate.Engine.Proofs
