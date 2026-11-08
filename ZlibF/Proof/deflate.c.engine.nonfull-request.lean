import ZlibF.Proof.«deflate.c.engine.partial-sync-protocol»
import ZlibF.Proof.«deflate.c.engine.ordinary-block-history»

/-! # Every default request except FULL preserves the same actual initialized boundary -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- The same initialized protocol supports NO_FLUSH, PARTIAL, SYNC,
FINISH and BLOCK. Each translated request returns, preserves the boundary
and public reachability, and accounts for consumed and delivered bytes.
The full public domain, FULL reset and encoded history remain separate. -/
theorem DefaultFinishBoundary.nonfull_request {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (boundary : DefaultFinishBoundary h r ds z d config) (buffers : StreamBuffers h r)
    (raw : z.next_out = .null ∨ ∃ ob oo, z.next_out = .ref (.blk ob) oo)
    (flush : Int32)
    (flag : flush = Z_NO_FLUSH ∨ flush = Z_PARTIAL_FLUSH ∨ flush = Z_SYNC_FLUSH ∨
      flush = Z_FINISH ∨ flush = Z_BLOCK) :
    ∃ used produced rc after z' result,
      deflate (some r) flush h = .ok (rc, after) ∧
      DefaultFinishBoundary after r ds z' result config ∧ StreamBuffers after r ∧
      StreamAccounting z z' used produced ∧
      (rc = Z_OK ∨ rc = Z_STREAM_END ∨ rc = Z_STREAM_ERROR ∨ rc = Z_BUF_ERROR) := by
  rcases flag with noflush | partialFlag | sync | finish | block
  · exact boundary.request_with_block flush (Or.inl noflush) buffers raw
  · obtain ⟨used, produced, rc, after, z', result, run, stateA, buffersA, account, allowed⟩ :=
      boundary.partial_sync_total buffers raw flush (Or.inl partialFlag)
    exact ⟨used, produced, rc, after, z', result, run, stateA, buffersA, account,
      allowed.elim Or.inl (fun err => Or.inr (Or.inr err))⟩
  · obtain ⟨used, produced, rc, after, z', result, run, stateA, buffersA, account, allowed⟩ :=
      boundary.partial_sync_total buffers raw flush (Or.inr sync)
    exact ⟨used, produced, rc, after, z', result, run, stateA, buffersA, account,
      allowed.elim Or.inl (fun err => Or.inr (Or.inr err))⟩
  · exact boundary.request_with_block flush (Or.inr (Or.inl finish)) buffers raw
  · exact boundary.request_with_block flush (Or.inr (Or.inr block)) buffers raw

end Zlib.Deflate.Engine.Proofs
