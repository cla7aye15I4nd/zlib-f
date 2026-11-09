import ZlibF.Proof.«deflate.c.engine.generic-foreign-partial-first-one-input»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-partial-first-complete-input»

/-! # Every positive first nonfinal call encodes its consumed original input -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateEncoding ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The actual first default PARTIAL request at every positive foreign-depth caller
capacity returns exact wrapper bytes and either HeaderPending or RawPrefix. Its accepted logical input equals the consumed original caller prefix.
The empty raw history is established from actual initialization fields;
no encoding invariant or C callee contract is assumed. Zero output refusal
and later public phases have their separate entry results. -/
theorem public_foreign_first_partial_encoding_input {h : Heap} {r : ZStreamRef} {ds owner oo : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {config : EngineConfig}
    (initial : EngineStart h r ds z d) (level : d.level = 6)
    (boundary : BufferedBoundary h r ds z d input 0 0 [] config) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (output : 0 < z.avail_out.toNat)
    (memory : config.memory.toNat = 16384) (valid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    {actualInput : List UInt8} (snapshot : Bytes h z.next_in z.avail_in.toNat actualInput) :
    ∃ used after z' result nextInput nextOrigin nextBase ys written,
      deflate (some r) Z_PARTIAL_FLUSH h = .ok (Z_OK, after) ∧
      BufferedBoundary after r ds z' result nextInput nextOrigin nextBase ys config ∧ StreamBuffers after r ∧
      StreamAccounting z z' used written.length ∧ Bytes after z.next_out written.length written ∧
      (∀ i, i < fillEnd d → nextInput i = input i) ∧
      nextOrigin + fillEnd result = fillEnd d + used ∧
      result.status = BUSY_STATE ∧ (result.last_flush = Z_PARTIAL_FLUSH ∨ result.last_flush = -1) ∧
      z'.adler = (ZlibF.Spec.adler32 (inputPrefix nextInput (nextOrigin + fillEnd result))).toUInt64 ∧
      inputPrefix nextInput (nextOrigin + fillEnd result) = actualInput.take used ∧
      ((used = 0 ∧ written = [120] ∧ nextOrigin = 0 ∧ nextBase = 0 ∧ ys = [] ∧ HeaderPending after result [120]) ∨
       (∃ rawWritten, written = [120,156] ++ rawWritten ∧ RawPrefix after result nextInput nextBase rawWritten)) := by
  have flagLo : 0 ≤ Z_PARTIAL_FLUSH.toInt := by decide
  have flagHi : Z_PARTIAL_FLUSH.toInt ≤ 5 := by decide
  by_cases one : z.avail_out.toNat = 1
  · have oneWord : z.avail_out = 1 := UInt32.toNat_inj.mp one
    obtain ⟨after, z', result, run, stateA, buffersA, accountA, bytesA, _outA, statusA, lastA, encodingA, checksumA⟩ :=
      public_foreign_first_partial_one_byte_encoding_adler initial level boundary buffers pointer oneWord valid
    have phaseA := encodingA
    obtain ⟨remaining, _pending, _headerEq, _bits, startA, lookA⟩ := encodingA
    refine ⟨0, after, z', result, input, 0, 0, [], [120], run, stateA, buffersA,
      accountA, bytesA, fun _ _ => rfl, ?_, statusA, Or.inr lastA, checksumA, ?_,
      Or.inl ⟨rfl, rfl, rfl, rfl, rfl, phaseA⟩⟩
    · simp only [fillEnd, startA, lookA, initial.start, initial.lookahead,
        UInt32.toNat_zero, Nat.add_zero]
    · simp only [fillEnd, startA, lookA, UInt32.toNat_zero, Nat.add_zero,
        inputPrefix, List.range_zero, List.map_nil, List.take_zero]
  · have room : 2 ≤ z.avail_out.toNat := by omega
    obtain ⟨used, after, z', result, nextInput, nextOrigin, nextBase, ys, rawWritten,
        run, stateA, buffersA, accountA, bytesA, agreesA, endpointA, _baseA, statusA, lastA, encodingA, checksumA, inputLedgerA⟩ :=
      public_foreign_first_partial_complete_header_encoding_input initial level boundary buffers pointer room memory valid snapshot
    have length : ([120,156] ++ rawWritten : List UInt8).length = 2 + rawWritten.length := by
      simp only [List.length_append, List.length_cons, List.length_nil]
    refine ⟨used, after, z', result, nextInput, nextOrigin, nextBase, ys, [120,156] ++ rawWritten,
      run, stateA, buffersA, ?_, ?_, ?_, ?_, statusA, lastA, checksumA, inputLedgerA, Or.inr ⟨rawWritten, rfl, encodingA⟩⟩
    · rw [length]; exact accountA
    · rw [length]; exact bytesA
    · simpa only [Nat.zero_add] using agreesA
    · simpa only [Nat.zero_add] using endpointA

end Zlib.Deflate.Engine.Proofs
