import ZlibF.Proof.«deflate.c.engine.generic-header-source»
import ZlibF.Proof.«deflate.c.engine.common-first-header»
import ZlibF.Proof.«deflate.c.engine.trailer-state»
import ZlibF.Proof.«deflate.c.engine.stream-control»
import ZlibF.Proof.«deflate.c.engine.flush-exact-output-frame»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt BitsDiff)
set_option autoImplicit false

/-- The actual source header's private ready heap retains every legal caller
view. No raw-output assumption enters before pending publication. -/
theorem generic_zlib_header_ready_engine {h : Heap} {r : ZStreamRef} {ds pb : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (pending : d.pending = 0) (cursor : d.pending_out = d.pending_buf) :
    let next := levelHeaderBytes d.level buf
    let result := levelHeaderState d
    let stream := {z with adler := 1}
    let after := levelHeaderReady h r ds pb z d buf
    DGood after r ds stream result ∧ TreesInvAt after ds result pb next ∧ StreamBuffers after r ∧
      ByteSizes h after ∧ OutputStorage h after r ds pb pb ∧
      StreamAccounting z stream 0 0 ∧
      Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [] ∧
      next.toList.take 2 = levelHeaderPrefix d.level := by
  let next := levelHeaderBytes d.level buf
  let emitted : DeflateState := {d with pending := 2}
  let first := setD (Zlib.Trees.Proofs.Out.setB h pb next) ds emitted
  let stream : ZStream := {z with adler := 1}
  let result := levelHeaderState d
  let after := levelHeaderReady h r ds pb z d buf
  have room : 2 ≤ buf.size := by have size := trees.base.size; have lo := trees.base.lit_lo; omega
  have size : next.size = buf.size := by simp [next, levelHeaderBytes]
  have fields : BitsDiff d emitted := ⟨2, d.bi_buf, d.bi_valid, d.bi_used, rfl⟩
  obtain ⟨goodA, buffersA⟩ := common_header_ready_good_buffers good trees buffers cursor
  have treesA : TreesInvAt after ds result pb next := by
    refine ⟨⟨by simp [after, levelHeaderReady, result, next], trees.base.wf, (by simpa [after, levelHeaderReady] using trees.base.static), trees.base.pbuf,
      by simp [after, levelHeaderReady, result, next], (by simpa [after, levelHeaderReady] using trees.base.rw), size.trans trees.base.size,
      trees.base.psize.trans size.symm, trees.base.sym, trees.base.lit_lo,
      trees.base.lit_hi, trees.base.sym_end, ?_⟩,
      ⟨trees.run.ldyn, trees.run.lstat, trees.run.ddyn, trees.run.dstat,
       trees.run.bldyn, trees.run.blstat, trees.run.bi_lo, trees.run.bi_hi,
       trees.run.bi_buf, trees.run.sym_next_le, trees.run.sym_next_mod⟩⟩
    change 2 ≤ d.pending_buf_size.toNat
    rw [trees.base.psize]
    exact room
  have sizesE := output_bits_sizes good trees.base.bytes size fields
  have sizesZ := stream_control_sizes first r stream
  have stateZ : (r.put first stream).dstates ds = some emitted := by simp only [first, ZStreamRef.put_dstates, setD_dstates_same]
  have sizesD := block_record_sizes (result := result) stateZ rfl
  have sizesA : ByteSizes h after := by
    simpa only [after, levelHeaderReady, first, ZStreamRef.put_setD, setD_setD,
      Zlib.Trees.Proofs.Out.setB] using (sizesE.trans sizesZ).trans sizesD
  have account : StreamAccounting z stream 0 0 := by
    exact stream_accounting_zero z
  let stated := setD (Zlib.Trees.Proofs.Out.setB h pb next) ds result
  have stored : OutputStorage h stated r ds pb pb := output_bits_storage good.live.hs trees.base.bytes
  have getZ : r.get stated = some z := by simpa only [stated, ZStreamRef.get_setD,
    Zlib.Trees.Proofs.Out.setB, stream_get_bytes] using good.live.hz
  have storageZ : OutputStorage stated (r.put stated stream) r ds pb pb :=
    ⟨shape_put getZ stream, by simp only [ZStreamRef.put_nalloc], by simp only [ZStreamRef.put_nextBlk],
      full_frame_weaken (stream_store_full_frame stated r stream) (fun _ root => Or.inl root)⟩
  have storage : OutputStorage h after r ds pb pb := by
    simpa only [after, levelHeaderReady, stated, ZStreamRef.put_setD,
      Zlib.Trees.Proofs.Out.setB] using stored.trans storageZ
  have frame := storage.pending_private_frame trees.base.pbuf
  have precise : BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [] := by
    refine ⟨frame, ?_⟩
    intro region member
    simp at member
  refine ⟨goodA, treesA, buffersA, sizesA, storage, account, frame, precise, ?_⟩
  apply List.ext_getElem
  · simp [levelHeaderBytes, levelHeaderPrefix, Nat.min_eq_left room]
  · intro i hi hj
    have range : i < 2 := by simpa [levelHeaderPrefix] using hj
    have cases : i = 0 ∨ i = 1 := by omega
    rcases cases with rfl | rfl <;> simp [next, levelHeaderBytes, levelHeaderPrefix, room, Array.set!_eq_setIfInBounds]

end Zlib.Deflate.Engine.Proofs
#print axioms Zlib.Deflate.Engine.Proofs.generic_zlib_header_ready_engine
