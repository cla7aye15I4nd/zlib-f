import ZlibF.Proof.«deflate.c.engine.generic-foreign-marker-private»
import ZlibF.Proof.«deflate.c.engine.marker-raw-prefix»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
open Zlib.Trees.Proofs.Out (TreesInvAt outBits storedHeaderBits)
set_option autoImplicit false

/-- Actual SYNC marker generation and foreign publication retain exact wire,
content, checksum, wrapping totals and the complete caller byte frame. Every
capacity is admitted; marker room is derived from the initialized tree extent. -/
theorem foreign_empty_sync_publish {h : Heap} {r : ZStreamRef} {ds pb owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : BufferedBoundary h r ds z d input origin base [] config)
    (buffers : StreamBuffers h r) (trees : TreesInvAt h ds d pb buf)
    (pointer : z.next_out=.ref (.dstate_depth owner) oo) (publish : PublishReady d) :
    ∃ produced after z' result written remaining,
      (do Zlib.Trees.«_tr_stored_block» (some (.tab ds)) .null 0 0
          flush_pending (some r)) h=.ok ((),after) ∧
      BufferedBoundary after r ds z' result input origin base [] config ∧ StreamBuffers after r ∧
      StreamAccounting z z' 0 produced ∧ ByteSizes h after ∧ OutputStorage h after r ds pb owner ∧
      ConfigFrame d result ∧ result.status=d.status ∧ result.last_flush=d.last_flush ∧
      (0<z'.avail_out.toNat → PublishReady result) ∧
      Bytes after z.next_out produced written ∧ PendingBits after result remaining ∧
      ZlibF.Spec.bytesToBits written++remaining=outBits buf d++storedHeaderBits d 0 false ∧
      z'.adler=z.adler ∧ z'.total_in=z.total_in ∧ z'.total_out=z.total_out+UInt64.ofNat produced ∧
      fillEnd result=fillEnd d ∧ result.match_available=d.match_available ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,produced⟩] := by
  have room : d.pending.toNat+6≤buf.size := by
    have extent:=trees.base.size
    have lower:=trees.base.lit_lo
    rw [publish.1]
    change 0+6≤_
    omega
  obtain ⟨next,middle,markerRun,treesM,outputM,sizeM,_aligned,pendingM,fieldsM⟩ :=
    Zlib.Trees.Proofs.Out.stored_zero_null_emit trees (by have low:=publish.2.2;omega) room
  have bitRoom : 8*middle.pending.toNat+middle.bi_valid.toInt.toNat≤8*next.size := by
    have upper:=treesM.run.bi_hi
    have lower:=treesM.run.bi_lo
    have extent:=trees.base.size
    have minimum:=trees.base.lit_lo
    rw [sizeM]
    rw [publish.1] at pendingM
    change middle.pending.toNat≤6 at pendingM
    omega
  obtain ⟨preparedHeap,prepared,sourceP,stateP,buffersP,sizesP,storageP,bitsP,fieldsP⟩ :=
    prepare_empty_bit_output (ob:=pb) boundary buffers trees publish.2.1 sizeM fieldsM treesM bitRoom
  obtain ⟨pb',produced,after,z',result,written,remaining,pbufP,run,stateA,buffersA,account,
      sizes,storage,_amount,_left,controls,ready,bytes,pending,bits,precise⟩ :=
    flush_pending_buffered_foreign_boundary stateP buffersP pointer bitsP
  have effects:=flush_pending_low_foreign_run_scalar_effects stateP.good buffersP pointer stateP.bits
    run stateA.good.live.hz account
  have pbEq : pb'=pb := by
    obtain ⟨_,_,_,_,equal⟩ := fieldsP
    rw [equal] at pbufP
    simpa only [trees.base.pbuf,Ptr.ref.injEq,BRef.blk.injEq,and_true] using pbufP.symm
  subst pb'
  have frameA : ConfigFrame prepared result := by rw [controls];rfl
  have controlsA : result.status=d.status ∧ result.last_flush=d.last_flush := by
    obtain ⟨_,_,_,_,equal⟩ := fieldsP
    rw [controls,equal]
    exact ⟨rfl,rfl⟩
  have endpointA : fillEnd result=fillEnd d := by
    obtain ⟨_,_,_,_,equal⟩ := fieldsP
    rw [controls,equal]
    rfl
  have availableA : result.match_available=d.match_available := by
    obtain ⟨_,_,_,_,equal⟩ := fieldsP
    rw [controls,equal]
  have privateFrame:=marker_pending_private_frame storageP trees.base.pbuf
  have sameView:=private_frame_foreign_output_same boundary.good buffers pointer privateFrame
  have preciseA : BufferFrame preparedHeap after (fun b => StreamRoot r b ∨ DeflateOwned ds d b)
      [⟨z.next_out,produced⟩] := by
    refine ⟨full_frame_weaken precise.1 ?_,precise.2⟩
    intro b changed
    exact changed.elim Or.inl (fun state=>Or.inr (Or.inl state))
  have fullFrame : BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b)
      [⟨z.next_out,produced⟩] := by
    rw [pointer] at preciseA ⊢
    exact generic_wrapper_foreign_private_prefix privateFrame sameView preciseA
  refine ⟨produced,after,z',result,written,remaining,?_,stateA,buffersA,account,
    sizesP.trans sizes,(marker_pending_storage_output storageP).trans storage,(ConfigFrame.bits fieldsP).trans frameA,
    controlsA.1,controlsA.2,ready,bytes,pending,bits.trans outputM,effects.1,effects.2.1,effects.2.2.1,
    endpointA,availableA,fullFrame⟩
  have actualMarker : Zlib.Trees.«_tr_stored_block» (some (.tab ds)) .null 0 0 h=
      .ok ((),setD (Zlib.Trees.Proofs.Out.setB h pb next) ds middle) := markerRun
  rw [bind_app,actualMarker]
  exact sourceP.trans run

end Zlib.Deflate.Engine.Proofs
