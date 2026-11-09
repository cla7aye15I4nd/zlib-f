import ZlibF.Proof.«deflate.c.engine.generic-foreign-header-buffered»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-zlib-header»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-pending-storage»
import ZlibF.Proof.«deflate.c.engine.public-storage»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
set_option autoImplicit false

/-- The actual header preparation, buffered foreign publication and optional
retry store jointly retain buffered content, exact bytes and physical effects.
The full-header source keeps the arbitrary continuation unchanged. -/
theorem foreign_zlib_header_buffered_joint_next_physical {h : Heap} {r : ZStreamRef} {ds pb owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : BufferedBoundary h r ds z d input origin base [] config) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo)
    (status : d.status = INIT_STATE) (wrap : d.wrap = 1) (strategy : d.strategy = 0)
    (window : d.w_bits = 15) (start : d.strstart = 0) (pending : d.pending = 0)
    (cursor : d.pending_out = d.pending_buf) (bits : d.bi_valid.toInt = 0) (next : M Int32) :
    ∃ produced after z' result written remaining,
      publicZlibHeader (some r) (some (.tab ds)) next h =
        (if result.pending != 0 then .ok (Z_OK,after) else next after) ∧
      BufferedBoundary after r ds z' result input origin base [] config ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
      ByteSizes h after ∧ produced = min 2 z.avail_out.toNat ∧ result.pending.toNat + produced = 2 ∧
      result.status = BUSY_STATE ∧ result.bi_valid.toInt = 0 ∧
      result.last_flush = (if result.pending != 0 then -1 else d.last_flush) ∧
      result = {d with pending := result.pending, pending_out := result.pending_out, status := BUSY_STATE, last_flush := result.last_flush} ∧
      Bytes after z.next_out produced written ∧ PendingBits after result remaining ∧
      ZlibF.Spec.bytesToBits written ++ remaining = ZlibF.Spec.bytesToBits (levelHeaderPrefix d.level) ∧
      z'.adler = 1 ∧ z'.total_in = z.total_in ∧ z'.total_out = z.total_out + UInt64.ofNat produced ∧
      after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,produced⟩] ∧
      Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b=owner) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc=h.nalloc ∧ after.nextBlk=h.nextBlk := by
  have good := boundary.good
  let ready := levelHeaderReady h r ds pb z d buf
  let queued := levelHeaderState d
  let reset : ZStream := {z with adler := 1}
  let queuedBytes := levelHeaderBytes d.level buf
  obtain ⟨goodE,treesE,buffersE,sizesE,storageE,accountE,privateFrame,_preciseE,values⟩ :=
    generic_zlib_header_ready_engine good trees buffers pending cursor
  obtain ⟨stateE, _buffersE⟩ := foreign_header_ready_buffered boundary trees buffers pending cursor
  have pendingE := pending_bits_base treesE cursor
  obtain ⟨_pb,produced,middle,z',result,written,remaining,_base,flush,stateM,buffersM,accountM,sizesM,
      _storageM,amount,left,fields,_publishM,bytesM,pendingM,outputM,frameM⟩ :=
    flush_pending_buffered_foreign_boundary stateE buffersE pointer pendingE
  have goodM := stateM.good
  obtain ⟨adlerM,inputM,outputCountM,allocM,frontierM⟩ :=
    flush_pending_low_foreign_run_scalar_effects goodE buffersE pointer
      (by change d.bi_valid.toInt < 8; omega) flush goodM.live.hz accountM
  have storageM := low_foreign_pending_run_storage goodE buffersE treesE.base.pbuf pointer
    (by change d.bi_valid.toInt<8;omega) flush
  have storageEW : OutputStorage h ready r ds pb owner := by
    refine ⟨storageE.shape,storageE.nalloc,storageE.nextBlk,full_frame_weaken storageE.frame ?_⟩
    intro b changed
    rcases changed with root|state|pending|output
    · exact Or.inl root
    · exact Or.inr (Or.inl state)
    · exact Or.inr (Or.inr (Or.inl pending))
    · exact Or.inr (Or.inr (Or.inl output))
  have storageAll := storageEW.trans storageM
  have account : StreamAccounting z z' 0 produced := by
    simpa only [Nat.zero_add] using stream_accounting_trans accountE accountM
  have room : 2 ≤ queuedBytes.size := by
    have size : queuedBytes.size = buf.size := by simp [queuedBytes,levelHeaderBytes]
    have extent := trees.base.size; have lo := trees.base.lit_lo
    omega
  have word : Zlib.Trees.Proofs.Out.outBits queuedBytes queued = ZlibF.Spec.bytesToBits (levelHeaderPrefix d.level) := by
    unfold Zlib.Trees.Proofs.Out.outBits
    change Zlib.Trees.Proofs.Out.bytesBits queuedBytes 2 ++ Zlib.Trees.Proofs.Out.natBits d.bi_buf.toNat d.bi_valid.toInt.toNat = _
    rw [bytes_bits_format queuedBytes 2 room]
    change ZlibF.Spec.bytesToBits (queuedBytes.toList.take 2) ++ Zlib.Trees.Proofs.Out.natBits d.bi_buf.toNat d.bi_valid.toInt.toNat = _
    rw [values,bits]
    rfl
  have wire := outputM.trans word
  have frameM' : BufferFrame ready middle (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,produced⟩] := by
    refine ⟨full_frame_weaken frameM.1 ?_,frameM.2⟩
    intro b changed
    exact changed.elim Or.inl (fun same => Or.inr (Or.inl same))
  have initialFrame : BufferFrame h middle (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,produced⟩] := by
    rw [pointer] at frameM' ⊢
    exact generic_wrapper_foreign_private_prefix privateFrame
      (generic_zlib_header_ready_foreign_view good.live.hs) frameM'
  obtain ⟨beforeForeign,beforeGet,_beforeBound,different,_old,_notRoot⟩ := caller_foreign_output good buffers pointer
  have pointerM : z'.next_out = .ref (.dstate_depth owner) (oo + produced) := by
    rw [account.2.2.2.2.2.1,pointer]
    rfl
  obtain ⟨middleForeign,middleGet,_middleBound,_different,_oldM,_rootM⟩ := caller_foreign_output goodM buffersM pointerM
  let marked := if result.pending != 0 then {result with last_flush := -1} else result
  let after := if result.pending != 0 then setD middle ds {result with last_flush := -1} else middle
  have finalized : BufferedBoundary after r ds z' marked input origin base [] config ∧ DGood after r ds z' marked ∧ StreamBuffers after r ∧ ByteSizes middle after ∧
      Bytes after z.next_out produced written ∧ PendingBits after marked remaining ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,produced⟩] := by
    by_cases waiting : (result.pending != 0) = true
    · simp only [after,marked,waiting,ite_true]
      have goodF := last_flush_good goodM (-1)
      have sizesF := block_record_sizes (result := {result with last_flush := -1}) goodM.live.hs rfl
      have buffersF := stream_buffers_sizes goodM.live.hz goodF.live.hz buffersM sizesF
        (stream_owned_keys goodM goodF rfl rfl rfl rfl) (stream_accounting_zero z')
      have bytesF := generic_wrapper_setD_bytes (result := {result with last_flush := -1}) goodM.live.hs rfl bytesM
      have pendingF := generic_wrapper_setD_pending_bits (result := {result with last_flush := -1})
        goodM.live.hs rfl rfl rfl rfl rfl pendingM
      have frameF : BufferFrame h (setD middle ds {result with last_flush := -1})
          (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,produced⟩] := by
        rw [pointer] at initialFrame ⊢
        exact generic_wrapper_foreign_setD_frame goodM.live.hs beforeGet middleGet different (Or.inr (Or.inl rfl)) rfl initialFrame
      exact ⟨last_flush_buffered_boundary stateM (-1),goodF,buffersF,sizesF,bytesF,pendingF,frameF⟩
    · simp only [after,marked,waiting,ite_false]
      exact ⟨stateM,goodM,buffersM,⟨fun _ _ get => ⟨_,get,rfl⟩,fun _ => rfl⟩,bytesM,pendingM,initialFrame⟩
  obtain ⟨stateF,goodF,buffersF,sizesF,bytesF,pendingF,frameF⟩ := finalized
  have pendingF' : marked.pending = result.pending := by dsimp only [marked]; split <;> rfl
  have bitsF : marked.bi_valid.toInt = 0 := by
    have same : marked.bi_valid = result.bi_valid := by dsimp only [marked]; split <;> rfl
    rw [same,fields]
    exact bits
  have statusF : marked.status = BUSY_STATE := by
    have same : marked.status = result.status := by dsimp only [marked]; split <;> rfl
    rw [same,fields]
    rfl
  have lastF : marked.last_flush = (if marked.pending != 0 then -1 else d.last_flush) := by
    rw [pendingF']
    by_cases waiting : (result.pending != 0) = true
    · simp only [marked,waiting,ite_true]
    · simp only [marked,waiting,ite_false]
      rw [fields]
      rfl
  have fieldsF : marked = {d with pending := marked.pending,pending_out := marked.pending_out,status := BUSY_STATE,last_flush := marked.last_flush} := by
    by_cases waiting : (result.pending != 0) = true
    · simp only [marked,waiting,ite_true]
      rw [fields] <;> rfl
    · simp only [marked,waiting,ite_false]
      rw [fields] <;> rfl
  have headerRoom : 2 ≤ buf.size := by have extent := trees.base.size; have lo := trees.base.lit_lo; omega
  have prepared := generic_zlib_header_prepare_source good.live.hz good.live.hs status wrap strategy window start pending
    trees.base.pbuf trees.base.bytes headerRoom trees.base.rw next
  have run : publicZlibHeader (some r) (some (.tab ds)) next h =
      (if marked.pending != 0 then .ok (Z_OK,after) else next after) := by
    rw [prepared,pendingF']
    by_cases waiting : (result.pending != 0) = true
    · simp only [bind_app,flush,rdD_eq,goodM.live.hs,waiting,ite_true,wrD_eq,pure_app,after]
    · simp only [bind_app,flush,rdD_eq,goodM.live.hs,waiting,ite_false,pure_app,after] <;> rfl
  have physical : Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b=owner) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc=h.nalloc ∧ after.nextBlk=h.nextBlk := by
    by_cases waiting : (result.pending != 0)=true
    · simp only [after,waiting,ite_true]
      exact full_storage_state_trans storageAll.shape (storageAll.private_frame trees.base.pbuf)
        storageAll.nalloc storageAll.nextBlk goodM.live.hs (Or.inr (Or.inl (Or.inl rfl))) {result with last_flush:= -1}
    · simp only [after,waiting,ite_false]
      exact ⟨storageAll.shape,storageAll.private_frame trees.base.pbuf,full_shape_live_change storageAll.shape,storageAll.nalloc,storageAll.nextBlk⟩
  refine ⟨produced,after,z',marked,written,remaining,run,stateF,goodF,buffersF,account,
    (sizesE.trans sizesM).trans sizesF,amount,?_,statusF,bitsF,lastF,fieldsF,bytesF,pendingF,wire,adlerM,inputM,outputCountM,?_,?_,frameF,physical⟩
  · rw [pendingF']; exact left
  · by_cases waiting : (result.pending != 0) = true <;> simp only [after,waiting,ite_true,ite_false,setD_nalloc]
    · exact allocM.trans storageE.nalloc
    · exact allocM.trans storageE.nalloc
  · by_cases waiting : (result.pending != 0) = true <;> simp only [after,waiting,ite_true,ite_false,setD_nextBlk]
    · exact frontierM.trans storageE.nextBlk
    · exact frontierM.trans storageE.nextBlk

end Zlib.Deflate.Engine.Proofs
