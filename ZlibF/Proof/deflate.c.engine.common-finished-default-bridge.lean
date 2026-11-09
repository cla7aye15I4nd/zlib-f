import ZlibF.Proof.«deflate.c.engine.common-finished-encoding»
import ZlibF.Proof.«deflate.c.engine.public-finished-encoding»

/-! # Completed raw bodies retain meaning across dictionary-free headers -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- This changes only a mathematical wrapper prefix. It does not claim
that different compression levels execute alike or emit equal bodies. -/
theorem CommonFinishedEncoding.to_default {h : Heap} {d : DeflateState} {level : Int32}
    {accepted published : List UInt8} (encoding : CommonFinishedEncoding h d level accepted published) :
    FinishedEncoding h d accepted published := by
  obtain ⟨tailBytes, data, meaning⟩ := encoding.data
  refine ⟨encoding.bits, tailBytes, data, ?_⟩
  rcases meaning with raw | ⟨wrap, valid⟩
  · exact Or.inl raw
  · refine Or.inr ⟨wrap, ?_⟩
    exact ZlibF.Math.DeflateEncoding.zlib_valid_replace_plain_header valid
      (level_header_format level).2 (by decide +kernel) (by decide +kernel)

/-- The level-specific prefix supplies independent header validity and
FDICT zero for the same exact encoded body and checksum. -/
theorem FinishedEncoding.common {h : Heap} {d : DeflateState}
    {accepted published : List UInt8} (encoding : FinishedEncoding h d accepted published) (level : Int32) :
    CommonFinishedEncoding h d level accepted published := by
  obtain ⟨tailBytes, data, meaning⟩ := encoding.data
  refine ⟨encoding.bits, tailBytes, data, ?_⟩
  rcases meaning with raw | ⟨wrap, valid⟩
  · exact Or.inl raw
  · exact Or.inr ⟨wrap, level_header_rewrap level valid⟩

/-- Reuse the already proved level-independent actual finishing execution;
only its mathematical wrapper prefix is exchanged before and after. -/
theorem public_common_finishing_encoding {h : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig} {accepted published : List UInt8}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r) (phase : FinishingPhase d config)
    (pointer : z.next_out = .ref (.blk ob) oo) (empty : z.avail_in = 0)
    (output : 0 < z.avail_out.toNat) (lower : -2 ≤ d.last_flush.toInt) (upper : d.last_flush.toInt ≤ 5)
    (checksum : z.adler = (ZlibF.Spec.adler32 accepted).toUInt64)
    (encoding : CommonFinishedEncoding h d config.level accepted published) :
    ∃ rc after z' result written,
      deflate (some r) Z_FINISH h = .ok (rc, after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 written.length ∧
      Bytes after z.next_out written.length written ∧ FinishingPhase result config ∧
      CommonFinishedEncoding after result config.level accepted (published ++ written) ∧
      z'.adler = (ZlibF.Spec.adler32 accepted).toUInt64 ∧
      (rc = Z_STREAM_END → ZlibF.Spec.Zlib.Valid accepted (levelHeaderPrefix config.level ++ published ++ written)) := by
  obtain ⟨rc, after, z', result, written, run, goodA, buffersA, accountA, bytesA, phaseA,
      encodingA, checksumA, ended⟩ := public_default_finishing_encoding good buffers phase pointer empty output
        lower upper checksum encoding.to_default
  exact ⟨rc, after, z', result, written, run, goodA, buffersA, accountA, bytesA, phaseA,
    encodingA.common config.level, checksumA, fun done => level_header_rewrap config.level (ended done)⟩

end Zlib.Deflate.Engine.Proofs
