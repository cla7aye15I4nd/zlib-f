import ZlibF.Proof.«deflate.c.engine.generic-foreign-caller-publication»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-pending-storage»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-pending-scalars»
import ZlibF.Proof.«deflate.c.engine.flush-exact-output-frame»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt BitsDiff)
set_option autoImplicit false

/-- A genuine private stage may precede foreign output without widening the foreign owner footprint. -/
theorem foreign_buffer_frame_precompose {h prepared after : Heap} {owner off n : Nat} {changed : Nat → Prop}
    (privateFrame : Frame h prepared changed) (shape : Shape h prepared)
    (outputView : Space.get prepared (BRef.dstate_depth owner) = Space.get h (BRef.dstate_depth owner))
    (frame : BufferFrame prepared after changed [⟨.ref (.dstate_depth owner) off,n⟩]) :
    BufferFrame h after changed [⟨.ref (.dstate_depth owner) off,n⟩] := by
  have restores : restoreRegions h after [⟨.ref (.dstate_depth owner) off,n⟩] =
      restoreRegions prepared after [⟨.ref (.dstate_depth owner) off,n⟩] := by
    simp only [restoreRegions,List.foldl_cons,List.foldl_nil,outputView]
  refine ⟨?_,?_⟩
  · rw [restores]
    exact full_frame_trans_shape privateFrame frame.1 shape
  · intro region mem ref i a pointer get
    simp only [List.mem_singleton] at mem
    subst region
    obtain ⟨sameRef,sameOff⟩ := Ptr.ref.inj pointer
    subst ref i
    exact frame.2 ⟨.ref (.dstate_depth owner) off,n⟩ (by simp) _ _ _ rfl (outputView.trans get)

/-- Complete actual pending publication to a legal foreign byte view.
All legal bit counts and all output capacities are included. The base pending cursor
and real pending bit-room condition are the publishing-phase preconditions. -/
theorem flush_pending_foreign_bits_frame {h : Heap} {r : ZStreamRef} {ds pb owner oo : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (pointer : z.next_out = .ref (.dstate_depth owner) oo)
    (cursor : d.pending_out = d.pending_buf)
    (room : 8*d.pending.toNat+d.bi_valid.toInt.toNat ≤ 8*buf.size) :
    ∃ produced after z' result written remaining,
      flush_pending (some r) h = .ok ((),after) ∧ DGood after r ds z' result ∧ StreamBuffers after r ∧
      StreamAccounting z z' 0 produced ∧ ByteSizes h after ∧ OutputStorage h after r ds pb owner ∧
      produced = min (d.pending.toNat+d.bi_valid.toInt.toNat/8) z.avail_out.toNat ∧
      result.pending.toNat+produced = d.pending.toNat+d.bi_valid.toInt.toNat/8 ∧
      result.bi_valid.toInt < 8 ∧ result.bi_valid.toInt.toNat = d.bi_valid.toInt.toNat%8 ∧
      result = {d with
        pending := result.pending, pending_out := result.pending_out,
        bi_buf := result.bi_buf, bi_valid := result.bi_valid, bi_used := result.bi_used} ∧
      Bytes after z.next_out produced written ∧ PendingBits after result remaining ∧
      ZlibF.Spec.bytesToBits written++remaining = Zlib.Trees.Proofs.Out.outBits buf d ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ b=ds ∨ b=pb) [⟨z.next_out,produced⟩] := by
  obtain ⟨next,prepared,_bitRun,goodP,treesP,bitStream,low,size,diff,pendingCount,validCount,sameRun⟩ :=
    flush_pending_prepare good trees cursor room
  let ready := setD (Zlib.Trees.Proofs.Out.setB h pb next) ds prepared
  have cursorP : prepared.pending_out=prepared.pending_buf := by
    obtain ⟨_,_,_,_,equal⟩ := diff
    rw [equal]
    exact cursor
  have buffersP := output_bits_buffers good buffers cursor trees.base.bytes size diff treesP
  obtain ⟨produced,after,z',result,written,remaining,run,goodA,buffersA,account,sizesA,count,remainingCount,
    fields,bytes,pendingBits,bits,frameA⟩ :=
    flush_pending_low_foreign_caller_bits_frame goodP treesP buffersP low cursorP pointer
  have storageA := low_foreign_pending_run_storage goodP buffersP treesP.base.pbuf pointer low run
  have sizesP := output_bits_sizes good trees.base.bytes size diff
  have storageP := output_bits_storage (r:=r) (ob:=owner) (result:=prepared) (next:=next) good.live.hs trees.base.bytes
  have storagePrivate := output_bits_storage (r:=r) (ob:=pb) (result:=prepared) (next:=next) good.live.hs trees.base.bytes
  have privateFrame : Frame h ready (fun b => StreamRoot r b ∨ b=ds ∨ b=pb) := by
    apply full_frame_weaken storagePrivate.frame
    intro b changed
    rcases changed with root|same|same|same
    · exact Or.inl root
    · exact Or.inr (Or.inl same)
    · exact Or.inr (Or.inr same)
    · exact Or.inr (Or.inr same)
  have outputView : Space.get ready (BRef.dstate_depth owner) = Space.get h (BRef.dstate_depth owner) := by
    obtain ⟨_,_,_,_,equal⟩ := diff
    change Space.get (setD (Zlib.Trees.Proofs.Out.setB h pb next) ds prepared) (BRef.dstate_depth owner) = _
    rw [byte_view_setD_depth (h:=Zlib.Trees.Proofs.Out.setB h pb next) (d:=d) (result:=prepared) good.live.hs (by rw [equal])]
    rfl
  have frameBig : BufferFrame ready after (fun b => StreamRoot r b ∨ b=ds ∨ b=pb)
      [⟨.ref (.dstate_depth owner) oo,produced⟩] := by
    rw [pointer] at frameA
    exact ⟨full_frame_weaken frameA.1 (fun b h => h.elim Or.inl (fun e => Or.inr (Or.inl e))),frameA.2⟩
  have frame := foreign_buffer_frame_precompose privateFrame storageP.shape outputView frameBig
  have resultFields : result = {d with
      pending := result.pending, pending_out := result.pending_out,
      bi_buf := result.bi_buf, bi_valid := result.bi_valid, bi_used := result.bi_used} := by
    obtain ⟨_,_,_,_,equal⟩ := diff
    rw [fields,equal]
  have validSame : result.bi_valid=prepared.bi_valid := congrArg (·.bi_valid) fields
  refine ⟨produced,after,z',result,written,remaining,sameRun.trans run,goodA,buffersA,account,
    sizesP.trans sizesA,storageP.trans storageA,?_,by omega,?_,?_,resultFields,bytes,pendingBits,bits.trans bitStream,?_⟩
  · rw [pendingCount] at count
    exact count
  · rw [validSame]
    exact low
  · rw [validSame]
    exact validCount
  · simpa only [pointer] using frame

end Zlib.Deflate.Engine.Proofs
