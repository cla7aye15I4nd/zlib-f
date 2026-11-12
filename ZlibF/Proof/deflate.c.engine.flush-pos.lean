import ZlibF.Proof.«deflate.c.engine.generic-foreign-private-arrays»
import ZlibF.Proof.«deflate.c.engine.pos-heap»

/-! # Block flushes keep the positional chains

`flush_frames_pchains` and `foreign_flush_frames_pchains` are `flush_frames_chains` and
`foreign_flush_frames_chains` for `PHeapChains`: a flush keeps the window, `prev` and `head` arrays.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

theorem flush_frames_pchains {h after : Heap} {r : ZStreamRef} {ds pb ob oo top stop : Nat}
    {z : ZStream} {d result : DeflateState}
    (storage : OutputStorage h after r ds pb ob)
    (good : DGood h r ds z d) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo)
    (pendingPtr : d.pending_buf = .ref (.blk pb) 0)
    (frame : FlushWorkFrame { d with block_start := d.strstart.toUInt64.toInt64 } result)
    (chains : PHeapChains h d top stop) : PHeapChains after result top stop := by
  obtain ⟨w, p0, q0, b, blocks⟩ := good.inv.blocks
  obtain ⟨wa, get, _⟩ := blocks.wa
  obtain ⟨p, q, pa, qa, prev, head, getPrev, getHead, chain⟩ := chains
  obtain ⟨_, prevA, headA⟩ := storage.private_arrays good buffers pointer blocks.win get prev getPrev head getHead pendingPtr
  refine ⟨p, q, pa, qa, ?_, ?_, prevA, headA, ?_⟩
  · rw [frame]; exact prev
  · rw [frame]; exact head
  · rw [frame]; exact chain

theorem foreign_flush_frames_pchains {h after : Heap} {r : ZStreamRef} {ds pb owner oo top stop : Nat}
    {z : ZStream} {d result : DeflateState}
    (storage : OutputStorage h after r ds pb owner)
    (good : DGood h r ds z d) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo)
    (pendingPtr : d.pending_buf = .ref (.blk pb) 0)
    (frame : FlushWorkFrame { d with block_start := d.strstart.toUInt64.toInt64 } result)
    (chains : PHeapChains h d top stop) : PHeapChains after result top stop := by
  obtain ⟨w, p0, q0, b, blocks⟩ := good.inv.blocks
  obtain ⟨wa, get, _⟩ := blocks.wa
  obtain ⟨p, q, pa, qa, prev, head, getPrev, getHead, chain⟩ := chains
  obtain ⟨_, prevA, headA⟩ :=
    storage.foreign_private_arrays good buffers pointer blocks.win get prev getPrev head getHead pendingPtr
  refine ⟨p, q, pa, qa, ?_, ?_, prevA, headA, ?_⟩
  · rw [frame]; exact prev
  · rw [frame]; exact head
  · rw [frame]; exact chain

end Zlib.Deflate.Engine.Proofs
