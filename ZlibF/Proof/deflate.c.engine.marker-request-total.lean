import ZlibF.Proof.«deflate.c.engine.all-scalar-history»

/-! # All actual marker request return classes retain the initialized boundary -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Each active PARTIAL/SYNC/FULL request returns OK or BUF_ERROR while
retaining the same initialized protocol and caller accounting. -/
theorem DefaultFinishBoundary.marker_active {h : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (boundary : DefaultFinishBoundary h r ds z d config) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (output : 0 < z.avail_out.toNat)
    (valid : z.avail_in ≠ 0 → z.next_in ≠ .null) (active : d.status ≠ FINISH_STATE)
    (flush : Int32) (flag : flush = Z_PARTIAL_FLUSH ∨ flush = Z_SYNC_FLUSH ∨ flush = Z_FULL_FLUSH) :
    ∃ used produced rc after z' result,
      deflate (some r) flush h = .ok (rc, after) ∧
      DefaultFinishBoundary after r ds z' result config ∧ StreamBuffers after r ∧
      StreamAccounting z z' used produced ∧ (rc = Z_OK ∨ rc = Z_BUF_ERROR) := by
  rcases flag with partialFlag | sync | full
  · exact boundary.partial_sync_active buffers pointer output valid active flush (Or.inl partialFlag)
  · exact boundary.partial_sync_active buffers pointer output valid active flush (Or.inr sync)
  · subst flush
    exact boundary.full_active buffers pointer output valid active

/-- Every marker request includes pointer/capacity/phase refusals and
returns without STREAM_END, on the same initialized boundary. -/
theorem DefaultFinishBoundary.marker_total {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (boundary : DefaultFinishBoundary h r ds z d config) (buffers : StreamBuffers h r)
    (raw : z.next_out = .null ∨ ∃ ob oo, z.next_out = .ref (.blk ob) oo)
    (flush : Int32) (flag : flush = Z_PARTIAL_FLUSH ∨ flush = Z_SYNC_FLUSH ∨ flush = Z_FULL_FLUSH) :
    ∃ used produced rc after z' result,
      deflate (some r) flush h = .ok (rc, after) ∧
      DefaultFinishBoundary after r ds z' result config ∧ StreamBuffers after r ∧
      StreamAccounting z z' used produced ∧ (rc = Z_OK ∨ rc = Z_STREAM_ERROR ∨ rc = Z_BUF_ERROR) := by
  rcases flag with partialFlag | sync | full
  · exact boundary.partial_sync_total buffers raw flush (Or.inl partialFlag)
  · exact boundary.partial_sync_total buffers raw flush (Or.inr sync)
  · subst flush
    exact boundary.full_total buffers raw

end Zlib.Deflate.Engine.Proofs
