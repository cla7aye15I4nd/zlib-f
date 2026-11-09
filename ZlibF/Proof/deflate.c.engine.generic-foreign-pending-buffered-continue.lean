import ZlibF.Proof.«deflate.c.engine.generic-foreign-public-pending-buffered»
import ZlibF.Proof.«deflate.c.engine.public-busy-no-flush-buffered»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- A queued ordinary BUSY call drains pending output and reaches the exact
real data continuation when capacity remains. It adds no callee contract,
owner separation, initialization or output-budget premise. -/
theorem public_pending_buffered_continue_foreign {h : Heap} {r : ZStreamRef} {ds owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List Symbol} {config : EngineConfig} {before : List Bool}
    (boundary : BufferedBoundary h r ds z d input origin base xs config) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (valid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (status : d.status = BUSY_STATE) (queued : d.pending ≠ 0) (room : d.pending.toNat < z.avail_out.toNat)
    (flush : Int32) (flag : flush = Z_NO_FLUSH ∨ flush = Z_FINISH) (pending : PendingBits h d before) :
    ∃ pb produced middle zm dm written remaining,
      d.pending_buf = .ref (.blk pb) 0 ∧
      flush_pending (some r) (setD h ds {d with last_flush := flush}) = .ok ((),middle) ∧
      deflate (some r) flush h = publicDataTail (some r) (some (.tab ds)) flush middle ∧
      BufferedBoundary middle r ds zm dm input origin base xs config ∧ StreamBuffers middle r ∧
      StreamAccounting z zm 0 produced ∧ ByteSizes h middle ∧ OutputStorage h middle r ds pb owner ∧
      produced = d.pending.toNat ∧ 0 < zm.avail_out.toNat ∧ PublishReady dm ∧
      dm.status = BUSY_STATE ∧ dm.last_flush = flush ∧
      dm = {d with pending := dm.pending,pending_out := dm.pending_out,last_flush := flush} ∧
      Bytes middle z.next_out produced written ∧ PendingBits middle dm remaining ∧
      ZlibF.Spec.bytesToBits written ++ remaining = before ∧
      BufferFrame h middle (fun x => StreamRoot r x ∨ x = ds) [⟨z.next_out,produced⟩] := by
  let d0 := {d with last_flush := flush}
  let h0 := setD h ds d0
  have boundary0 := last_flush_buffered_boundary boundary flush
  have buffers0 := last_flush_buffers boundary.good buffers flush
  have pending0 := last_flush_pending_bits boundary.good pending flush
  obtain ⟨pb,produced,middle,zm,dm,written,remaining,basePtr,flushRun,stateM,buffersM,accountM,
      sizesM,storageM,amount,_left,fields,readyM,bytesM,pendingM,bitsM,frameM⟩ :=
    flush_pending_buffered_foreign_boundary boundary0 buffers0 pointer pending0
  have amountM : produced = d.pending.toNat := by
    rw [amount]
    exact Nat.min_eq_left (by change d.pending.toNat ≤ z.avail_out.toNat;omega)
  have left : 0 < zm.avail_out.toNat := by
    have balance := accountM.2.2.2.1
    omega
  have statusM : dm.status = BUSY_STATE := by rw [fields];exact status
  have lastM : dm.last_flush = flush := by rw [fields]
  have fieldsM : dm = {d with pending := dm.pending,pending_out := dm.pending_out,last_flush := flush} := by
    simpa only [d0] using fields
  have nonnull : z.next_out ≠ .null := by rw [pointer];intro impossible;cases impossible
  have positive : z.avail_out ≠ 0 := by intro zero;rw [zero] at room;change d.pending.toNat < 0 at room;omega
  have remainingOutput : zm.avail_out ≠ 0 := by intro zero;rw [zero] at left;contradiction
  have finishedInput : dm.status = FINISH_STATE → zm.avail_in = 0 := by
    intro finished
    rw [statusM] at finished
    cases (show BUSY_STATE ≠ FINISH_STATE from by decide) finished
  have entry : deflate (some r) flush h = publicDataTail (some r) (some (.tab ds)) flush middle := by
    rcases flag with rfl | rfl
    · exact (public_pending_no_flush_continue boundary.good stateM.good status nonnull positive valid queued flushRun
        remainingOutput finishedInput).trans (public_busy_no_flush_header_skip stateM.good statusM)
    · exact (public_pending_finish_continue boundary.good stateM.good nonnull positive valid queued flushRun
        remainingOutput finishedInput).trans (public_busy_header_skip stateM.good statusM)
  obtain ⟨w,p,q,b,blocks⟩ := boundary.good.inv.blocks
  have baseD : d.pending_buf = .ref (.blk pb) 0 := basePtr
  have key : b = pb := by simpa only [baseD,Ptr.ref.injEq,BRef.blk.injEq,and_true] using blocks.pbuf.symm
  subst b
  obtain ⟨buf,get,_size⟩ := blocks.ba
  have storage := (last_flush_storage (ob := owner) boundary.good get flush).trans storageM
  have sizes := (last_flush_sizes boundary.good.live.hs flush).trans sizesM
  have precise : BufferFrame h middle (fun x => StreamRoot r x ∨ x = ds) [⟨z.next_out,produced⟩] := by
    rw [pointer] at frameM ⊢
    exact foreign_buffer_frame_before_last_flush boundary.good.live.hs flush frameM
  exact ⟨pb,produced,middle,zm,dm,written,remaining,baseD,flushRun,entry,stateM,buffersM,
    accountM,sizes,storage,amountM,left,readyM left,statusM,lastM,fieldsM,bytesM,pendingM,bitsM,precise⟩

end Zlib.Deflate.Engine.Proofs
#print axioms Zlib.Deflate.Engine.Proofs.public_pending_buffered_continue_foreign
