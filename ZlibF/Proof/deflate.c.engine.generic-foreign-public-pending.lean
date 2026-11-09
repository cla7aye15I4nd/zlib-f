import ZlibF.Proof.«deflate.c.engine.generic-foreign-pending-cursor»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-private-frame»
import ZlibF.Proof.«deflate.c.engine.full-storage»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Proofs.DefaultInit
set_option autoImplicit false

/-- Moving the pre-state across a private depth-preserving record update does not change
which caller output bytes the frame permits. -/
theorem foreign_buffer_frame_before_last_flush {h after : Heap} {r : ZStreamRef} {ds owner oo n : Nat}
    {d : DeflateState} (state : h.dstates ds = some d) (flush : Int32)
    (frame : BufferFrame (setD h ds {d with last_flush := flush}) after
      (fun x => StreamRoot r x ∨ x = ds) [⟨.ref (.dstate_depth owner) oo,n⟩]) :
    BufferFrame h after (fun x => StreamRoot r x ∨ x = ds) [⟨.ref (.dstate_depth owner) oo,n⟩] := by
  let h0 := setD h ds { d with last_flush := flush }
  have view := byte_view_setD_depth (result := {d with last_flush := flush}) state rfl
  have restores : restoreRegions h after [⟨.ref (.dstate_depth owner) oo,n⟩] =
      restoreRegions h0 after [⟨.ref (.dstate_depth owner) oo,n⟩] := by
    simp only [restoreRegions,List.foldl_cons,List.foldl_nil,h0,view]
  refine ⟨?_,?_⟩
  · rw [restores]
    exact full_frame_trans_shape
      (full_frame_weaken (state_store_full_frame h ds {d with last_flush := flush}) (fun _ same => Or.inr same))
      frame.1 (shape_setD state _)
  · intro region mem ref off a pointer get
    exact frame.2 region mem ref off a pointer ((view ref).trans get)

/-- The actual public entry publishes to an arbitrary legal foreign depth view.
This is the resumed-pending early-return path, for every accepted flush flag,
positive output exhausted by pending data, and fewer than eight residual bits.
There is no raw-output, base-cursor or foreign-separation premise. -/
theorem public_pending_exhausted_foreign {h : Heap} {r : ZStreamRef} {ds owner oo : Nat}
    {z : ZStream} {d : DeflateState} {before : List Bool} (flush : Int32)
    (good : DGood h r ds z d) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo)
    (input : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (flagLo : 0 ≤ flush.toInt) (flagHi : flush.toInt ≤ Z_BLOCK.toInt)
    (status : d.status = FINISH_STATE → flush = Z_FINISH) (positive : 0 < z.avail_out.toNat)
    (enough : z.avail_out.toNat ≤ d.pending.toNat) (low : d.bi_valid.toInt < 8)
    (pending : PendingBits h d before) :
    ∃ after z' result written remaining,
      deflate (some r) flush h = .ok (Z_OK,after) ∧ DGood after r ds z' result ∧ StreamBuffers after r ∧
      StreamAccounting z z' 0 z.avail_out.toNat ∧ ByteSizes h after ∧
      z'.avail_out = 0 ∧ result.last_flush = -1 ∧
      result.pending.toNat + z.avail_out.toNat = d.pending.toNat ∧ result.bi_valid.toInt < 8 ∧
      result = {d with pending := result.pending,pending_out := result.pending_out,last_flush := -1} ∧
      Bytes after z.next_out z.avail_out.toNat written ∧ PendingBits after result remaining ∧
      ZlibF.Spec.bytesToBits written ++ remaining = before ∧
      BufferFrame h after (fun x => StreamRoot r x ∨ x = ds) [⟨z.next_out,z.avail_out.toNat⟩] := by
  let d0 := {d with last_flush := flush}
  let h0 := setD h ds d0
  have good0 := last_flush_good good flush
  have buffers0 := last_flush_buffers good buffers flush
  have pending0 := last_flush_pending_bits good pending flush
  obtain ⟨foreign,outGet,outBound,different,_,_⟩ := caller_foreign_output good0 buffers0 pointer
  obtain ⟨w,p,q,pb,blocks⟩ := good0.inv.blocks
  obtain ⟨buf,get,size⟩ := blocks.ba
  obtain ⟨po,cursor,bound⟩ := blocks.pout
  have sourceBound : po + d0.pending.toNat ≤ buf.size := by rw [size,← blocks.psize]; exact bound
  let n := pendingLen d0.pending z.avail_out
  have count : n.toNat = z.avail_out.toNat := by
    rw [pendingLen_value]
    exact Nat.min_eq_right enough
  have nonzero : n ≠ 0 := by intro empty; rw [empty] at count; change 0 = _ at count; omega
  let middle := foreignPendingCopyHeap h0 r ds pb po owner oo z d0 buf foreign n
  let z' := pendingStream z (.ref (.dstate_depth owner) (oo+n.toNat)) n
  let result := pendingState d0 (.ref (.blk pb) (po+n.toNat)) n
  have run : flush_pending (some r) h0 = .ok ((),middle) :=
    flush_pending_low_foreign good0.live.hz good0.live.zst good0.live.hs low pointer cursor
      outGet get (Ne.symm different) outBound sourceBound nonzero
  have goodM : DGood middle r ds z' result :=
    foreign_pending_copy_good good0 blocks.pbuf cursor outGet (Ne.symm different)
  have account0 : StreamAccounting z z' 0 n.toNat := foreign_pending_copy_accounting pointer
  have account : StreamAccounting z z' 0 z.avail_out.toNat := by simpa only [count] using account0
  have sizesM := foreign_pending_copy_sizes (r := r) (z := z) (pb := pb) (po := po)
    (pending := buf) (oo := oo) n good0.live.hs outGet (Ne.symm different)
  have owned : ∀ b,StreamOwned middle r b ↔ StreamOwned h0 r b := by
    intro b
    rw [stream_owned_deflate goodM,stream_owned_deflate good0]
    rfl
  have buffersM := stream_buffers_sizes good0.live.hz goodM.live.hz buffers0 sizesM owned account0
  obtain ⟨written,remaining,bytes,pendingM,bits⟩ :=
    foreign_pending_copy_cursor_bits (r := r) (ds := ds) blocks.pbuf cursor get sourceBound pending0 pointer different outBound
  let final := setD middle ds {result with last_flush := -1}
  have goodF := last_flush_good goodM (-1)
  have buffersF := last_flush_buffers goodM buffersM (-1)
  have pendingF := last_flush_pending_bits goodM pendingM (-1)
  have sizes := ((last_flush_sizes good.live.hs flush).trans sizesM).trans (last_flush_sizes goodM.live.hs (-1))
  have outputZero : z'.avail_out = 0 := UInt32.toNat_inj.mp (by
    have balance := account.2.2.2.1
    change z'.avail_out.toNat = 0
    omega)
  have dataF : Bytes final z.next_out z.avail_out.toNat written := by
    rw [← count]
    have kept := byte_view_setD_depth (d := result) (result := {result with last_flush := -1}) goodM.live.hs rfl
    rcases bytes with null | ⟨ref,off,array,ptr,read,bound,value⟩
    · exact Or.inl null
    · exact Or.inr ⟨ref,off,array,ptr,(kept ref).trans read,bound,value⟩
  have frame0 : BufferFrame h0 final (fun x => StreamRoot r x ∨ x = ds)
      [⟨.ref (.dstate_depth owner) oo,n.toNat⟩] := by
    simpa only [final,middle,foreignPendingCopyHeap,setD_setD] using
      foreign_output_private_buffer_frame (stream := z') (result := {result with last_flush := -1})
        (po := po) (pending := buf) n outGet different (by omega)
  have frame := foreign_buffer_frame_before_last_flush good.live.hs flush frame0
  dsimp only [h0,d0] at run
  have publicRun : deflate (some r) flush h = .ok (Z_OK,final) := by
    have checked := stateCheck_live good.live
    have inputs : (z.avail_in != 0 && z.next_in == .null) = false := by
      by_cases empty : z.avail_in = 0
      · simp [empty]
      · simp [input empty]
    have outNonzero : z.avail_out ≠ 0 := by intro zero; rw [zero] at positive; contradiction
    have pendingNonzero : d.pending ≠ 0 := by intro zero; rw [zero] at enough; change z.avail_out.toNat ≤ 0 at enough; omega
    have flagUpper : ¬ flush > Z_BLOCK := by
      change ¬ Z_BLOCK < flush
      rw [Int32.lt_iff_toInt_lt]
      omega
    have flagLower : ¬ flush < 0 := by
      rw [Int32.lt_iff_toInt_lt]
      change ¬ flush.toInt < 0
      omega
    have finishAllowed : (d.status == FINISH_STATE && flush != Z_FINISH) = false := by
      by_cases finished : d.status = FINISH_STATE
      · simp [finished,status finished]
      · simp [finished]
    rw [public_deflate_source]
    simp only [bind_app,pure_app,checked,show ((0 : Int32) != 0) = false from rfl,
      flagUpper,flagLower,decide_false,Bool.false_or,Bool.false_eq_true,ite_false,
      zrd_eq,good.live.hz,good.live.zst,castDeflateState,ldZStream_ok good.live.hz,
      ldDeflateState_tab good.live.hs,inputs,
      show (z.next_out == .null) = false from by rw [pointer];rfl,
      finishAllowed,show (z.avail_out == 0) = false from beq_eq_false_iff_ne.mpr outNonzero,
      wrD_eq,good.live.hs,show (d.pending != 0) = true from bne_iff_ne.mpr pendingNonzero,
      ite_true,run,goodM.live.hz,outputZero,BEq.rfl,goodM.live.hs]
    rfl
  refine ⟨final,z',{result with last_flush := -1},written,remaining,publicRun,goodF,buffersF,
    account,sizes,outputZero,rfl,?_,low,rfl,dataF,pendingF,bits,?_⟩
  · rw [← count]
    exact (pending_copy_counts d.pending z.avail_out).1
  · simpa only [pointer,count] using frame

end Zlib.Deflate.Engine.Proofs
