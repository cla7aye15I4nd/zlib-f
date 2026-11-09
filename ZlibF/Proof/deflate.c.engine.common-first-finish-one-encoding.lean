import ZlibF.Proof.«deflate.c.engine.common-first-one-byte-checksum»

/-! # One-byte first FINISH output retains exact common-level header encoding -/
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Only the first one-byte header path is shared between these flags.
Both actual calls stop before data dispatch and retain the same checksum. -/
theorem public_common_first_finish_one_byte_encoding_adler {h : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {config : EngineConfig}
    (initial : EngineStart h r ds z d)
    (boundary : BufferedBoundary h r ds z d input 0 0 [] config) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (one : z.avail_out = 1)
    (valid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ after z' result,
      deflate (some r) Z_FINISH h = .ok (Z_OK, after) ∧
      BufferedBoundary after r ds z' result input 0 0 [] config ∧ StreamBuffers after r ∧
      StreamAccounting z z' 0 1 ∧ Bytes after z.next_out 1 [120] ∧
      z'.avail_out = 0 ∧ result.status = BUSY_STATE ∧ result.last_flush = -1 ∧
      CommonHeaderPending after result config.level [120] ∧
      z'.adler = (ZlibF.Spec.adler32 (ZlibF.Math.DeflateSymbols.inputPrefix input (0 + fillEnd result))).toUInt64 := by
  obtain ⟨after, z', result, run, stateA, buffersA, accountA, bytesA, outputA, statusA, lastA, encodingA, checksumA⟩ :=
    public_common_first_no_flush_one_byte_encoding_adler initial boundary buffers pointer one valid
  have actual := (first_common_valid_one_eq_finish initial buffers pointer one valid Z_NO_FLUSH
    (by decide) (by decide)).symm.trans run
  exact ⟨after, z', result, actual, stateA, buffersA, accountA, bytesA, outputA, statusA, lastA, encodingA, checksumA⟩

end Zlib.Deflate.Engine.Proofs
