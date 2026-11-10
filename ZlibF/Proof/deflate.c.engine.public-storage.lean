import ZlibF.Proof.«deflate.c.engine.ordinary-call-full-storage»
import ZlibF.Proof.«deflate.c.engine.public-busy-counters»
/-! # Full object and allocation frames for both public data paths -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- A private state store composes with an already established full frame. -/
theorem full_storage_state_trans {h g : Heap} {ds : Nat} {d : DeflateState} {changed : Nat → Prop}
    (shape : Shape h g) (frame : Frame h g changed) (alloc : g.nalloc = h.nalloc)
    (next : g.nextBlk = h.nextBlk) (get : g.dstates ds = some d)
    (inside : changed ds) (result : DeflateState) :
    Shape h (setD g ds result) ∧ Frame h (setD g ds result) changed ∧
      LiveChange h (setD g ds result) (fun _ => False) (fun _ => False) ∧
      (setD g ds result).nalloc = h.nalloc ∧ (setD g ds result).nextBlk = h.nextBlk := by
  have store := state_store_full_storage get result
  have shapeA := shape.trans store.1
  have frameA := full_frame_trans_shape frame
    (full_frame_weaken store.2.1 (fun b same => by subst b; exact inside)) shape
  exact ⟨shapeA, frameA, full_shape_live_change shapeA, alloc, next⟩

/-- The complete actual trailer keeps its private/output object frame and exact allocation ledger. -/
theorem zlib_trailer_run_full_storage {h after : Heap} {r : ZStreamRef} {ds pb ob oo : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {rc : Int32}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (wrap : d.wrap = 1)
    (pending : d.pending = 0) (cursor : d.pending_out = d.pending_buf) (bits : d.bi_valid.toInt = 0)
    (run : publicFinishTail (some r) (some (.tab ds)) Z_FINISH h = .ok (rc, after)) :
    Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = ob) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  obtain ⟨_produced, other, _z', _result, _written, _remaining, tested, _goodA, _buffersA, _account,
      _sizes, storage, _rest⟩ := zlib_trailer_publish good trees buffers pointer wrap pending cursor bits
  have eq := (Prod.mk.inj (Except.ok.inj (tested.symm.trans run))).2
  rw [← eq]
  exact ⟨storage.shape, storage.private_frame trees.base.pbuf, full_shape_live_change storage.shape,
    storage.nalloc, storage.nextBlk⟩

end Zlib.Deflate.Engine.Proofs
