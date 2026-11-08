import ZlibF.Proof.«deflate.c.engine.public-data-full-storage»
import ZlibF.Proof.«deflate.c.engine.public-first-counters»

/-! # Full heap frames for the actual default header -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The header's two byte-array writes and its record writes have their full object frame. -/
theorem header_write_storage {h : Heap} {r : ZStreamRef} {ds pb ob : Nat}
    {z : ZStream} {d : DeflateState} {buf output : Array UInt8}
    (good : DGood h r ds z d) (get : h.bytes pb = some buf) (outGet : h.bytes ob = some output)
    (separate : ob ≠ pb) (nextBuf nextOutput : Array UInt8) (nextZ : ZStream) (nextD : DeflateState) :
    OutputStorage h (setD (r.put
      (Zlib.Trees.Proofs.Out.setB (Zlib.Trees.Proofs.Out.setB h pb nextBuf) ob nextOutput) nextZ) ds nextD) r ds pb ob := by
  let first := Zlib.Trees.Proofs.Out.setB h pb nextBuf
  let second := Zlib.Trees.Proofs.Out.setB first ob nextOutput
  let stream := r.put second nextZ
  have shapeB : Shape h first := shape_setB get nextBuf
  have getO : first.bytes ob = some output := by
    simpa only [first, Zlib.Trees.Proofs.Out.setB, upd_ne _ _ _ _ separate] using outGet
  have shapeO : Shape first second := shape_setB getO nextOutput
  have getZ : r.get second = some z := by
    simpa only [second, first, Zlib.Trees.Proofs.Out.setB, stream_get_bytes] using good.live.hz
  have shapeZ := shape_put getZ nextZ
  have getD : stream.dstates ds = some d := by
    simpa only [stream, second, first, Zlib.Trees.Proofs.Out.setB, ZStreamRef.put_dstates] using good.live.hs
  have shapeD := shape_setD getD nextD
  let changed := fun b => StreamRoot r b ∨ b = ds ∨ b = pb ∨ b = ob
  have frameB : Frame h first changed := full_frame_weaken (byte_store_full_frame h pb nextBuf)
    (fun _ same => Or.inr (Or.inr (Or.inl same)))
  have frameO : Frame first second changed := full_frame_weaken (byte_store_full_frame first ob nextOutput)
    (fun _ same => Or.inr (Or.inr (Or.inr same)))
  have frameZ : Frame second stream changed := full_frame_weaken (stream_store_full_frame second r nextZ)
    (fun _ root => Or.inl root)
  have frameD : Frame stream (setD stream ds nextD) changed := full_frame_weaken (state_store_full_frame stream ds nextD)
    (fun _ same => Or.inr (Or.inl same))
  have shapeBO := shapeB.trans shapeO
  have shapeBOZ := shapeBO.trans shapeZ
  refine ⟨shapeBOZ.trans shapeD, ?_, ?_, ?_⟩
  · simp only [Zlib.Trees.Proofs.Out.setB, setD_nalloc, ZStreamRef.put_nalloc]
  · simp only [Zlib.Trees.Proofs.Out.setB, setD_nextBlk, ZStreamRef.put_nextBlk]
  · exact full_frame_trans_shape (full_frame_trans_shape (full_frame_trans_shape frameB frameO shapeB)
      frameZ shapeBO) frameD shapeBOZ

/-- The complete two-byte header retains its full storage frame. -/
theorem header_complete_full_storage {h : Heap} {r : ZStreamRef} {ds pb ob oo : Nat}
    {z : ZStream} {d : DeflateState} {buf output : Array UInt8}
    (good : DGood h r ds z d) (get : h.bytes pb = some buf) (outGet : h.bytes ob = some output)
    (separate : ob ≠ pb) :
    OutputStorage h (headerCompleteHeap h r ds pb ob oo z d buf output) r ds pb ob :=
  header_write_storage good get outGet separate _ _ _ _

/-- Splitting the header after one byte retains the same complete storage frame. -/
theorem header_one_full_storage {h : Heap} {r : ZStreamRef} {ds pb ob oo : Nat}
    {z : ZStream} {d : DeflateState} {buf output : Array UInt8}
    (good : DGood h r ds z d) (get : h.bytes pb = some buf) (outGet : h.bytes ob = some output)
    (separate : ob ≠ pb) :
    OutputStorage h (headerOneHeap h r ds pb ob oo z d buf output) r ds pb ob :=
  header_write_storage good get outGet separate _ _ _ _

/-- Both real ordinary first calls with one output byte have exact object/allocation frames. -/
theorem first_ordinary_one_run_full_storage {h after : Heap} {r : ZStreamRef}
    {ds ob oo : Nat} {z : ZStream} {d : DeflateState} {flush rc : Int32}
    (flag : flush = Z_NO_FLUSH ∨ flush = Z_FINISH)
    (initial : EngineStart h r ds z d) (level : d.level = 6) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (one : z.avail_out = 1)
    (valid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (run : deflate (some r) flush h = .ok (rc, after)) :
    Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = ob) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  obtain ⟨output, outGet, outRw, outBound, outside⟩ := caller_raw_output initial.good buffers pointer
  obtain ⟨oldD, pb, buf, trees⟩ := initial.good.trees
  have sameD : oldD = d := Option.some.inj (trees.base.dstate.symm.trans initial.good.live.hs)
  subst oldD
  have separate : ob ≠ pb := by
    intro same
    subst ob
    exact outside (Or.inr (Or.inr (Or.inr (Or.inr trees.base.pbuf))))
  have room : 2 ≤ buf.size := by have size := trees.base.size; have lo := trees.base.lit_lo; omega
  have actual : deflate (some r) flush h = .ok (Z_OK, headerOneHeap h r ds pb ob oo z d buf output) := by
    rcases flag with rfl | rfl
    · exact first_no_flush_one_source initial level trees.base.pbuf trees.base.bytes room trees.base.rw
        pointer outGet outRw separate outBound one valid
    · exact first_finish_one_source initial level trees.base.pbuf trees.base.bytes room trees.base.rw
        pointer outGet outRw separate outBound one valid
  have same := (Prod.mk.inj (Except.ok.inj (actual.symm.trans run))).2
  rw [← same]
  have storage := header_one_full_storage (oo := oo) initial.good trees.base.bytes outGet separate
  exact ⟨storage.shape, storage.private_frame trees.base.pbuf, full_shape_live_change storage.shape,
    storage.nalloc, storage.nextBlk⟩

end Zlib.Deflate.Engine.Proofs
