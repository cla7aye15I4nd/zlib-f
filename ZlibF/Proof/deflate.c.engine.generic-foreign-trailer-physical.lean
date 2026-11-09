import ZlibF.Proof.«deflate.c.engine.generic-foreign-zlib-trailer»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-pending-storage»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-buffer-frame-adjacent»
import ZlibF.Proof.«deflate.c.engine.public-storage»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
set_option autoImplicit false

/-- The real private trailer stores, foreign pending publication and wrapper transition
retain the actual heap shape and exact object/allocation ledger. -/
theorem foreign_zlib_trailer_run_full_storage {h after : Heap} {r : ZStreamRef} {ds pb owner oo : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {rc : Int32}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (wrap : d.wrap = 1)
    (pending : d.pending = 0) (cursor : d.pending_out = d.pending_buf) (bits : d.bi_valid.toInt = 0)
    (run : publicFinishTail (some r) (some (.tab ds)) Z_FINISH h = .ok (rc, after)) :
    Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = owner) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  obtain ⟨write,goodE,treesE,buffersE,_sizesE,storageE,_values⟩ :=
    zlib_trailer_write (ob:=pb) good trees buffers pending cursor
  obtain ⟨produced,middle,z',result,_written,_remaining,flush,goodM,_buffersM,account,_sizesM,
      _amount,_left,fields,_bytesM,_pendingM,_outputM,_frameM⟩ :=
    flush_pending_low_foreign_caller_bits_frame goodE treesE buffersE
      (by change d.bi_valid.toInt<8;omega) cursor pointer
  have storageM := low_foreign_pending_run_storage goodE buffersE treesE.base.pbuf pointer
    (by change d.bi_valid.toInt<8;omega) flush
  have frameE := full_private_frame_add_output (ob:=owner) (storageE.pending_private_frame trees.base.pbuf)
  have frameM := storageM.private_frame treesE.base.pbuf
  have wrapM : result.wrap=1 := by rw [fields];exact wrap
  let final := setD middle ds {result with wrap := -1}
  have tested : publicFinishTail (some r) (some (.tab ds)) Z_FINISH h =
      .ok ((if result.pending != 0 then Z_OK else Z_STREAM_END),final) := by
    have getW : rd (some (.tab ds)) (·.wrap) h=.ok (1,h) := by simp only [rdD_eq,good.live.hs,wrap]
    have getWM : rd (some (.tab ds)) (·.wrap) middle=.ok (1,middle) := by simp only [rdD_eq,goodM.live.hs,wrapM]
    have negative : ineg (1:Int32)=pure (-1) := by rfl
    unfold publicFinishTail
    simp only [bind_app,pure_app,show (Z_FINISH != Z_FINISH)=false from rfl,
      Bool.false_eq_true,ite_false,getW,show ¬(1:Int32)≤0 from by decide,
      show ((1:Int32)==2)=false from rfl,write,flush,getWM,
      show (1:Int32)>0 from by decide,ite_true,negative,wrD_eq,goodM.live.hs]
    simp only [rdD_eq,setD_dstates_same]
    rfl
  have physical := full_storage_state_trans (storageE.shape.trans storageM.shape)
    (full_frame_trans_shape frameE frameM storageE.shape) (storageM.nalloc.trans storageE.nalloc)
    (storageM.nextBlk.trans storageE.nextBlk) goodM.live.hs (Or.inr (Or.inl (Or.inl rfl))) {result with wrap := -1}
  have heaps := (Prod.mk.inj (Except.ok.inj (tested.symm.trans run))).2
  exact heaps ▸ physical

end Zlib.Deflate.Engine.Proofs
