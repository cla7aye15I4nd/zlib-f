import ZlibF.Proof.«deflate.c.engine.generic-foreign-default-macro»
import ZlibF.Proof.«deflate.c.engine.generic-wrapper-frames»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-pending-buffered-boundary»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-pending-scalars»
import ZlibF.Proof.«deflate.c.engine.generic-output-append»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-buffer-frame-restore»
import ZlibF.Proof.«deflate.c.engine.empty-output-prepared»
import ZlibF.Proof.«deflate.c.engine.full-marker-endpoint»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- A real pending-only private storage footprint excludes the caller owner. -/
theorem marker_pending_private_frame {h after : Heap} {r : ZStreamRef} {ds pb : Nat} {d : DeflateState}
    (storage : OutputStorage h after r ds pb pb) (pending : d.pending_buf=.ref (.blk pb) 0) :
    Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) := by
  apply full_frame_weaken storage.frame
  intro b changed
  rcases changed with root|state|same|same
  · exact Or.inl root
  · exact Or.inr (Or.inl state)
  · subst b;exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr pending))))
  · subst b;exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr pending))))

/-- The stronger pending-only storage relation also admits the caller output key. -/
theorem marker_pending_storage_output {h after : Heap} {r : ZStreamRef} {ds pb owner : Nat}
    (storage : OutputStorage h after r ds pb pb) : OutputStorage h after r ds pb owner := by
  refine ⟨storage.shape,storage.nalloc,storage.nextBlk,full_frame_weaken storage.frame ?_⟩
  intro b changed
  rcases changed with root|state|same|same
  · exact Or.inl root
  · exact Or.inr (Or.inl state)
  · exact Or.inr (Or.inr (Or.inl same))
  · exact Or.inr (Or.inr (Or.inl same))

/-- A genuine private prefix has a precise empty caller-output frame. -/
theorem marker_private_buffer_frame {h after : Heap} {r : ZStreamRef} {ds owner oo : Nat}
    {z : ZStream} {d : DeflateState} (good : DGood h r ds z d) (buffers : StreamBuffers h r)
    (pointer : z.next_out=.ref (.dstate_depth owner) oo)
    (privateFrame : Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b)) (shape : Shape h after) :
    BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,0⟩] := by
  obtain ⟨foreign,get,_⟩ := caller_foreign_output good buffers pointer
  rw [pointer]
  exact foreign_buffer_frame_of_fields (full_frame_weaken privateFrame (fun _ yes=>Or.inl yes))
    shape good.uniq get (ForeignOwnerFields.of_private_frame good buffers pointer privateFrame)
    (ForeignOwnerReadonly.of_private_frame good buffers pointer privateFrame)
    (ByteOutputInterval.of_same (private_frame_foreign_output_same good buffers pointer privateFrame))

end Zlib.Deflate.Engine.Proofs
