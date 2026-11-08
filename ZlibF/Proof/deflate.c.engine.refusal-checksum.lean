import ZlibF.Proof.«deflate.c.engine.public-header-resume-checksum»
import ZlibF.Proof.«deflate.c.engine.public-entry-refusals»

/-! # Actual early refusals retain encoded input and checksum meaning -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Updating a stream record does not change the private pending bit view. -/
theorem pending_bits_put_stream {h : Heap} {d : DeflateState} {bits : List Bool}
    (pending : PendingBits h d bits) (r : ZStreamRef) (z' : ZStream) :
    PendingBits (r.put h z') d bits := by
  obtain ⟨bytes, data, value⟩ := pending
  refine ⟨bytes, ?_, value⟩
  rcases data with null | ⟨ref, offset, array, pointer, get, bound, slice⟩
  · exact Or.inl null
  · exact Or.inr ⟨ref, offset, array, pointer, (byte_get_stream_put h r z' ref).trans get, bound, slice⟩

/-- A stream-only message store retains the raw encoded prefix. -/
theorem RawPrefix.put_stream {h : Heap} {d : DeflateState} {input : Nat → UInt8}
    {base : Nat} {published : List UInt8} (encoding : RawPrefix h d input base published)
    (r : ZStreamRef) (z' : ZStream) : RawPrefix (r.put h z') d input base published := by
  obtain ⟨remaining, encoded, pending, wire, meaning⟩ := encoding
  exact ⟨remaining, encoded, pending_bits_put_stream pending r z', wire, meaning⟩

/-- A stream-only message store retains pending initial header bytes. -/
theorem HeaderPending.put_stream {h : Heap} {d : DeflateState} {published : List UInt8}
    (encoding : HeaderPending h d published) (r : ZStreamRef) (z' : ZStream) :
    HeaderPending (r.put h z') d published := by
  obtain ⟨remaining, pending, wire, bits, start, look⟩ := encoding
  exact ⟨remaining, pending_bits_put_stream pending r z', wire, bits, start, look⟩

/-- A stream-only scalar store with the same checksum preserves the
source-established initial engine state, including its hash frontier. -/
theorem EngineStart.put_stream {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z z' : ZStream} {d : DeflateState} (initial : EngineStart h r ds z d)
    (goodA : DGood (r.put h z') r ds z' d) (adler : z'.adler = z.adler) :
    EngineStart (r.put h z') r ds z' d := by
  have chains : HeapChains (r.put h z') d 0 := control_heap_chains initial.chains (fun _ _ => by simp only [ZStreamRef.put_bytes])
    (by simp only [ZStreamRef.put_words]) rfl
  exact { initial with good := goodA, chains := chains, adler := adler.trans initial.adler }

/-- Every admitted caller output has the exact zero-length slice. -/
theorem caller_output_zero_slice {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} (good : DGood h r ds z d) (buffers : StreamBuffers h r) :
    Bytes h z.next_out 0 [] := by
  obtain ⟨other, get, _input, output, _separate⟩ := buffers
  have same : other = z := Option.some.inj (get.symm.trans good.live.hz)
  subst other
  rcases output with null | ⟨⟨bytes, data⟩, _writable, _outside⟩
  · exact Or.inl ⟨null, rfl, rfl⟩
  · rcases data with null | ⟨ref, offset, array, pointer, get, bound, _slice⟩
    · exact Or.inl ⟨null.1, rfl, rfl⟩
    · exact Or.inr ⟨ref, offset, array, pointer, get, by omega, by simp⟩

/-- The actual static-message error callee preserves raw/header encoding,
checksum and initialized content, and writes no caller bytes. Its real
execution is proved here; the caller assumes no callee specification. -/
theorem err_return_encoding_checksum {h : Heap} {r : ZStreamRef} {ds origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List Symbol}
    {config : EngineConfig} {published : List UInt8} (err : Int32)
    (boundary : BufferedBoundary h r ds z d input origin base xs config) (buffers : StreamBuffers h r)
    (encoding : RawPrefix h d input base published ∨ HeaderPending h d published)
    (checksum : z.adler = (ZlibF.Spec.adler32 (inputPrefix input (origin + fillEnd d))).toUInt64) :
    ∃ message,
      let z' := { z with msg := message }
      let after := r.put h z'
      ERR_RETURN (some r) err h = .ok (err, after) ∧
      BufferedBoundary after r ds z' d input origin base xs config ∧ StreamBuffers after r ∧
      StreamAccounting z z' 0 0 ∧ Bytes after z.next_out 0 [] ∧
      (RawPrefix after d input base published ∨ HeaderPending after d published) ∧
      z'.adler = (ZlibF.Spec.adler32 (inputPrefix input (origin + fillEnd d))).toUInt64 ∧
      (EngineStart h r ds z d → EngineStart after r ds z' d) := by
  obtain ⟨message, run⟩ := err_return_run boundary.good.live.hz err
  let z' := { z with msg := message }
  have goodA := stream_control_good (z' := z') boundary.good rfl boundary.good.live.zalloc boundary.good.live.zfree
  have account : StreamAccounting z z' 0 0 := stream_accounting_zero z
  have stateA := stream_control_buffered boundary goodA
  have buffersA := stream_control_buffers boundary.good goodA buffers account
  refine ⟨message, run, stateA, buffersA, account, caller_output_zero_slice (z := z') goodA buffersA, ?_, checksum, ?_⟩
  · rcases encoding with raw | header
    · exact Or.inl (raw.put_stream r z')
    · exact Or.inr (header.put_stream r z')
  · intro initial
    exact initial.put_stream goodA rfl

/-- All actual early stream/zero-output refusals preserve the same
encoding and accepted-input checksum, including the initial header phase.
The public source guards select the real static-message callee. -/
theorem public_entry_refusals_encoding_checksum {h : Heap} {r : ZStreamRef} {ds origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List Symbol}
    {config : EngineConfig} {published : List UInt8} (flush : Int32)
    (boundary : BufferedBoundary h r ds z d input origin base xs config) (buffers : StreamBuffers h r)
    (flagLo : 0 ≤ flush.toInt) (flagHi : flush.toInt ≤ Z_BLOCK.toInt)
    (refused : z.next_out = .null ∨ (z.avail_in ≠ 0 ∧ z.next_in = .null) ∨
      (d.status = FINISH_STATE ∧ flush ≠ Z_FINISH) ∨ z.avail_out = 0)
    (encoding : RawPrefix h d input base published ∨ HeaderPending h d published)
    (checksum : z.adler = (ZlibF.Spec.adler32 (inputPrefix input (origin + fillEnd d))).toUInt64) :
    ∃ err after z', (err = Z_STREAM_ERROR ∨ err = Z_BUF_ERROR) ∧
      deflate (some r) flush h = .ok (err, after) ∧
      BufferedBoundary after r ds z' d input origin base xs config ∧ StreamBuffers after r ∧
      StreamAccounting z z' 0 0 ∧ Bytes after z.next_out 0 [] ∧
      (RawPrefix after d input base published ∨ HeaderPending after d published) ∧
      z'.adler = (ZlibF.Spec.adler32 (inputPrefix input (origin + fillEnd d))).toUInt64 ∧
      (EngineStart h r ds z d → EngineStart after r ds z' d) := by
  by_cases bad : z.next_out = .null ∨ (z.avail_in ≠ 0 ∧ z.next_in = .null) ∨
      (d.status = FINISH_STATE ∧ flush ≠ Z_FINISH)
  · obtain ⟨message, run, stateA, buffersA, accountA, bytesA, encodingA, checksumA, initialA⟩ :=
      err_return_encoding_checksum Z_STREAM_ERROR boundary buffers encoding checksum
    exact ⟨Z_STREAM_ERROR, _, _, Or.inl rfl,
      (public_stream_guard_refusal boundary.good flush flagLo flagHi bad).trans run,
      stateA, buffersA, accountA, bytesA, encodingA, checksumA, initialA⟩
  · have out : z.next_out ≠ .null := fun eq => bad (Or.inl eq)
    have valid : z.avail_in ≠ 0 → z.next_in ≠ .null := fun count eq => bad (Or.inr (Or.inl ⟨count, eq⟩))
    have finish : d.status = FINISH_STATE → flush = Z_FINISH := by
      intro status
      by_cases same : flush = Z_FINISH
      · exact same
      · exact False.elim (bad (Or.inr (Or.inr ⟨status, same⟩)))
    have empty : z.avail_out = 0 := by
      rcases refused with wrong | wrong | wrong | empty
      · exact False.elim (out wrong)
      · exact False.elim (valid wrong.1 wrong.2)
      · exact False.elim (wrong.2 (finish wrong.1))
      · exact empty
    obtain ⟨message, run, stateA, buffersA, accountA, bytesA, encodingA, checksumA, initialA⟩ :=
      err_return_encoding_checksum Z_BUF_ERROR boundary buffers encoding checksum
    exact ⟨Z_BUF_ERROR, _, _, Or.inr rfl,
      (public_zero_output_refusal boundary.good flush flagLo flagHi out valid finish empty).trans run,
      stateA, buffersA, accountA, bytesA, encodingA, checksumA, initialA⟩

/-- Actual duplicate NO_FLUSH refusal records last_flush = 0 and retains
the encoded input and checksum without consuming or producing any byte. -/
theorem public_duplicate_encoding_checksum {h : Heap} {r : ZStreamRef} {ds origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List Symbol}
    {config : EngineConfig} {published : List UInt8}
    (boundary : BufferedBoundary h r ds z d input origin base xs config) (buffers : StreamBuffers h r)
    (status : d.status = BUSY_STATE) (inputEmpty : z.avail_in = 0) (pending : d.pending = 0)
    (out : z.next_out ≠ .null) (positive : z.avail_out ≠ 0)
    (lower : 0 ≤ d.last_flush.toInt) (upper : d.last_flush.toInt ≤ 5)
    (encoding : RawPrefix h d input base published ∨ HeaderPending h d published)
    (checksum : z.adler = (ZlibF.Spec.adler32 (inputPrefix input (origin + fillEnd d))).toUInt64) :
    ∃ after z',
      let result := { d with last_flush := Z_NO_FLUSH }
      deflate (some r) Z_NO_FLUSH h = .ok (Z_BUF_ERROR, after) ∧
      BufferedBoundary after r ds z' result input origin base xs config ∧ StreamBuffers after r ∧
      StreamAccounting z z' 0 0 ∧ Bytes after z.next_out 0 [] ∧
      (RawPrefix after result input base published ∨ HeaderPending after result published) ∧
      z'.adler = (ZlibF.Spec.adler32 (inputPrefix input (origin + fillEnd result))).toUInt64 := by
  have state0 := last_flush_buffered_boundary boundary Z_NO_FLUSH
  have buffers0 := last_flush_buffers boundary.good buffers Z_NO_FLUSH
  have encoding0 : RawPrefix (setD h ds { d with last_flush := Z_NO_FLUSH })
      { d with last_flush := Z_NO_FLUSH } input base published ∨
      HeaderPending (setD h ds { d with last_flush := Z_NO_FLUSH }) { d with last_flush := Z_NO_FLUSH } published := by
    rcases encoding with raw | header
    · exact Or.inl (raw.last_flush boundary.good Z_NO_FLUSH)
    · exact Or.inr (header.last_flush boundary.good Z_NO_FLUSH)
  obtain ⟨message, errorRun, stateA, buffersA, accountA, bytesA, encodingA, checksumA, _initialA⟩ :=
    err_return_encoding_checksum Z_BUF_ERROR state0 buffers0 encoding0 checksum
  have source := public_busy_no_flush_duplicate_source boundary.good status inputEmpty pending out positive lower upper
  exact ⟨_, _, source.trans errorRun, stateA, buffersA, accountA, bytesA, encodingA, checksumA⟩

/-- Every invalid signed flush scalar leaves even the stream message
unchanged, so encoding, checksum and zero-byte accounting are retained. -/
theorem public_invalid_flush_encoding_checksum {h : Heap} {r : ZStreamRef} {ds origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List Symbol}
    {config : EngineConfig} {published : List UInt8} (flush : Int32)
    (boundary : BufferedBoundary h r ds z d input origin base xs config) (buffers : StreamBuffers h r)
    (bad : flush > Z_BLOCK ∨ flush < 0)
    (encoding : RawPrefix h d input base published ∨ HeaderPending h d published)
    (checksum : z.adler = (ZlibF.Spec.adler32 (inputPrefix input (origin + fillEnd d))).toUInt64) :
    deflate (some r) flush h = .ok (Z_STREAM_ERROR, h) ∧
      BufferedBoundary h r ds z d input origin base xs config ∧ StreamBuffers h r ∧
      StreamAccounting z z 0 0 ∧ Bytes h z.next_out 0 [] ∧
      (RawPrefix h d input base published ∨ HeaderPending h d published) ∧
      z.adler = (ZlibF.Spec.adler32 (inputPrefix input (origin + fillEnd d))).toUInt64 := by
  exact ⟨public_bad_flush_refusal boundary.good flush bad, boundary, buffers, stream_accounting_zero z,
    caller_output_zero_slice boundary.good buffers, encoding, checksum⟩

end Zlib.Deflate.Engine.Proofs
