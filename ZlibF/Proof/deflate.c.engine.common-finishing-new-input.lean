import ZlibF.Proof.«deflate.c.engine.common-finished-default-bridge»
import ZlibF.Proof.«deflate.c.engine.finishing-new-input-encoding»

/-! # Finished common-level streams retain meaning when new input is refused -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- This actual level-independent path may drain pending output before
refusing new input. No fresh input is consumed in either return branch. -/
theorem public_common_finishing_new_input_encoding {h : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig} {accepted published : List UInt8}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r) (phase : FinishingPhase d config)
    (pointer : z.next_out = .ref (.blk ob) oo) (valid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (nonempty : z.avail_in ≠ 0) (output : 0 < z.avail_out.toNat)
    (lower : -2 ≤ d.last_flush.toInt) (upper : d.last_flush.toInt ≤ 5)
    (checksum : z.adler = (ZlibF.Spec.adler32 accepted).toUInt64)
    (encoding : CommonFinishedEncoding h d config.level accepted published) :
    ∃ rc after z' result written,
      deflate (some r) Z_FINISH h = .ok (rc, after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 written.length ∧
      Bytes after z.next_out written.length written ∧ FinishingPhase result config ∧
      CommonFinishedEncoding after result config.level accepted (published ++ written) ∧
      z'.adler = (ZlibF.Spec.adler32 accepted).toUInt64 ∧ (rc = Z_OK ∨ rc = Z_BUF_ERROR) := by
  obtain ⟨rc, after, z', result, written, run, goodA, buffersA, accountA, bytesA, phaseA,
      encodingA, checksumA, codes⟩ := public_finishing_new_input_encoding good buffers phase pointer valid
        nonempty output lower upper checksum encoding.to_default
  exact ⟨rc, after, z', result, written, run, goodA, buffersA, accountA, bytesA, phaseA,
    encodingA.common config.level, checksumA, codes⟩

end Zlib.Deflate.Engine.Proofs
