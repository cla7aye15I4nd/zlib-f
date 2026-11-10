import ZlibF.Proof.«deflate.c.engine.block-request-contract»
import ZlibF.Proof.«deflate.c.engine.ordinary-request-contract»

/-! # Uniform public request contracts for ordinary and BLOCK requests -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Every initialized default NO_FLUSH/FINISH/BLOCK request has the same
public safety/control contract, with exact counters, byte slice, BufferFrame
and no allocation changes. Null/raw output and all refusal cases are
included. Other valid flags, advanced APIs and encoded correctness are open. -/
theorem DefaultFinishBoundary.request_contract_with_block {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (boundary : DefaultFinishBoundary h r ds z d config) (flush : Int32)
    (flag : flush = Z_NO_FLUSH ∨ flush = Z_FINISH ∨ flush = Z_BLOCK) (buffers : StreamBuffers h r)
    (raw : z.next_out = .null ∨ ∃ ob oo, z.next_out = .ref (.blk ob) oo) :
    ∃ used written rc after z' result,
      C.run (deflate (some r) flush) h = .ok (rc, after) ∧
      DefaultFinishBoundary after r ds z' result config ∧ StreamBuffers after r ∧
      DGood after r ds z' result ∧ StreamAccounting z z' used written.length ∧
      Bytes after z.next_out written.length written ∧
      z'.total_in = z.total_in + UInt64.ofNat used ∧ z'.total_out = z.total_out + UInt64.ofNat written.length ∧
      (rc = Z_OK ∨ rc = Z_STREAM_END ∨ rc = Z_STREAM_ERROR ∨ rc = Z_BUF_ERROR) ∧
      (rc = Z_STREAM_ERROR ↔ flush.toInt < 0 ∨ 5 < flush.toInt ∨ z.next_out = .null ∨
        (z.next_in = .null ∧ z.avail_in ≠ 0) ∨ (d.status = FINISH_STATE ∧ flush ≠ Z_FINISH)) ∧
      (flush.toInt < 0 ∨ 5 < flush.toInt → rc = Z_STREAM_ERROR ∧ after = h) ∧
      (rc = Z_STREAM_END → flush = Z_FINISH ∧ result.status = FINISH_STATE ∧
        z'.avail_in = 0 ∧ result.pending = 0 ∧ result.bi_valid = 0) ∧
      Shape h after ∧ BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out, written.length⟩] ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  rcases flag with noFlush | finish | block
  · exact boundary.ordinary_request_contract flush (Or.inl noFlush) buffers raw
  · exact boundary.ordinary_request_contract flush (Or.inr finish) buffers raw
  · subst flush
    exact boundary.block_request_contract buffers raw

/-- The same scoped contract also proves every invalid signed flush is
refused on the unchanged heap. It does not enlarge the history constructors. -/
theorem DefaultFinishBoundary.scalar_request_contract_with_block {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (boundary : DefaultFinishBoundary h r ds z d config) (flush : Int32)
    (flag : (flush = Z_NO_FLUSH ∨ flush = Z_FINISH ∨ flush = Z_BLOCK) ∨ (flush.toInt < 0 ∨ 5 < flush.toInt)) (buffers : StreamBuffers h r)
    (raw : z.next_out = .null ∨ ∃ ob oo, z.next_out = .ref (.blk ob) oo) :
    ∃ used written rc after z' result,
      C.run (deflate (some r) flush) h = .ok (rc, after) ∧
      DefaultFinishBoundary after r ds z' result config ∧ StreamBuffers after r ∧
      DGood after r ds z' result ∧ StreamAccounting z z' used written.length ∧
      Bytes after z.next_out written.length written ∧
      z'.total_in = z.total_in + UInt64.ofNat used ∧ z'.total_out = z.total_out + UInt64.ofNat written.length ∧
      (rc = Z_OK ∨ rc = Z_STREAM_END ∨ rc = Z_STREAM_ERROR ∨ rc = Z_BUF_ERROR) ∧
      (rc = Z_STREAM_ERROR ↔ flush.toInt < 0 ∨ 5 < flush.toInt ∨ z.next_out = .null ∨
        (z.next_in = .null ∧ z.avail_in ≠ 0) ∨ (d.status = FINISH_STATE ∧ flush ≠ Z_FINISH)) ∧
      (flush.toInt < 0 ∨ 5 < flush.toInt → rc = Z_STREAM_ERROR ∧ after = h) ∧
      (rc = Z_STREAM_END → flush = Z_FINISH ∧ result.status = FINISH_STATE ∧
        z'.avail_in = 0 ∧ result.pending = 0 ∧ result.bi_valid = 0) ∧
      Shape h after ∧ BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out, written.length⟩] ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  rcases flag with supported | invalid
  · exact boundary.request_contract_with_block flush supported buffers raw
  · exact boundary.ordinary_or_invalid_request_contract flush (Or.inr invalid) buffers raw

end Zlib.Deflate.Engine.Proofs
