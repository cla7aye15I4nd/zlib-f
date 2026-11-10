import ZlibF.Proof.«deflate.c.engine.public-first-valid-one-encoding»
import ZlibF.Proof.«deflate.c.engine.public-first-nonfinal-complete-input»
import ZlibF.Proof.«deflate.c.engine.public-first-one-byte-checksum»
import ZlibF.Proof.«deflate.c.engine.public-first-complete-input»

/-! # Every positive first nonfinal call encodes its consumed original input -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateEncoding ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The actual first default non-FINISH request at every positive raw caller
capacity returns exact wrapper bytes and either HeaderPending or RawPrefix. Its accepted logical input equals the consumed original caller prefix.
The empty raw history is established from actual initialization fields;
no encoding invariant or C callee contract is assumed. Zero output refusal
and later public phases have their separate entry results. -/
theorem public_first_nonfinal_encoding_input {h : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {config : EngineConfig}
    (initial : EngineStart h r ds z d) (level : d.level = 6)
    (boundary : BufferedBoundary h r ds z d input 0 0 [] config) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (output : 0 < z.avail_out.toNat)
    (memory : config.memory.toNat = 16384) (valid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (flush : Int32) (flag : flush = Z_NO_FLUSH ∨ flush = Z_PARTIAL_FLUSH ∨ flush = Z_SYNC_FLUSH ∨
      flush = Z_FULL_FLUSH ∨ flush = Z_BLOCK)
    {actualInput : List UInt8} (snapshot : Bytes h z.next_in z.avail_in.toNat actualInput) :
    ∃ used after z' result nextInput nextOrigin nextBase ys written,
      deflate (some r) flush h = .ok (Z_OK, after) ∧
      BufferedBoundary after r ds z' result nextInput nextOrigin nextBase ys config ∧ StreamBuffers after r ∧
      StreamAccounting z z' used written.length ∧ Bytes after z.next_out written.length written ∧
      (∀ i, i < fillEnd d → nextInput i = input i) ∧
      nextOrigin + fillEnd result = fillEnd d + used ∧
      result.status = BUSY_STATE ∧ (result.last_flush = flush ∨ result.last_flush = -1) ∧
      z'.adler = (ZlibF.Spec.adler32 (inputPrefix nextInput (nextOrigin + fillEnd result))).toUInt64 ∧
      inputPrefix nextInput (nextOrigin + fillEnd result) = actualInput.take used ∧
      ((used = 0 ∧ written = [120] ∧ nextOrigin = 0 ∧ nextBase = 0 ∧ ys = [] ∧ HeaderPending after result [120]) ∨
       (∃ rawWritten, written = [120,156] ++ rawWritten ∧ RawPrefix after result nextInput nextBase rawWritten)) := by
  have flagLo : 0 ≤ flush.toInt := by rcases flag with rfl | rfl | rfl | rfl | rfl <;> decide
  have flagHi : flush.toInt ≤ 5 := by rcases flag with rfl | rfl | rfl | rfl | rfl <;> decide
  by_cases one : z.avail_out.toNat = 1
  · have oneWord : z.avail_out = 1 := UInt32.toNat_inj.mp one
    obtain ⟨after, z', result, run, stateA, buffersA, accountA, bytesA, _outA, statusA, lastA, encodingA, checksumA⟩ :=
      public_first_valid_one_byte_encoding_adler initial level boundary buffers pointer oneWord valid flush flagLo flagHi
    have phaseA := encodingA
    obtain ⟨remaining, _pending, _headerEq, _bits, startA, lookA⟩ := encodingA
    refine ⟨0, after, z', result, input, 0, 0, [], [120], run, stateA, buffersA,
      accountA, bytesA, fun _ _ => rfl, ?_, statusA, Or.inr lastA, checksumA, ?_,
      Or.inl ⟨rfl, rfl, rfl, rfl, rfl, phaseA⟩⟩
    · simp only [fillEnd, startA, lookA, initial.start, initial.lookahead,
        UInt32.toNat_zero, Nat.add_zero, Nat.zero_add]
    · simp only [fillEnd, startA, lookA, UInt32.toNat_zero, Nat.add_zero, Nat.zero_add,
        inputPrefix, List.range_zero, List.map_nil, List.take_zero]
  · have room : 2 ≤ z.avail_out.toNat := by omega
    obtain ⟨before, pending⟩ := good_pending_bits initial.good
    have empty := pending_bits_empty pending (by rw [initial.pending]; rfl) (by rw [initial.bits]; rfl)
    have encoding : RawPrefix h d input 0 [] := by
      rw [empty] at pending
      refine ⟨[], [], pending, rfl, ?_⟩
      simpa only [inputPrefix, List.range_zero, List.map_nil] using block_prefix_empty ([] : List UInt8) [] 0
    obtain ⟨used, after, z', result, nextInput, nextOrigin, nextBase, ys, rawWritten,
        run, stateA, buffersA, accountA, bytesA, agreesA, endpointA, _baseA, statusA, lastA, encodingA, checksumA, inputLedgerA⟩ :=
      public_first_nonfinal_complete_header_encoding_input initial level boundary buffers pointer room memory valid flush flag snapshot encoding
    have length : ([120,156] ++ rawWritten : List UInt8).length = 2 + rawWritten.length := by
      simp only [List.length_append, List.length_cons, List.length_nil]
    refine ⟨used, after, z', result, nextInput, nextOrigin, nextBase, ys, [120,156] ++ rawWritten,
      run, stateA, buffersA, ?_, ?_, ?_, ?_, statusA, lastA, checksumA, inputLedgerA, Or.inr ⟨rawWritten, rfl, encodingA⟩⟩
    · rw [length]; exact accountA
    · rw [length]; exact bytesA
    · simpa only [Nat.zero_add] using agreesA
    · simpa only [Nat.zero_add] using endpointA

end Zlib.Deflate.Engine.Proofs
