import ZlibF.Proof.«deflate.c.engine.generic-foreign-marker-private»
import ZlibF.Proof.«deflate.c.engine.partial-sync-marker-endpoint»
import ZlibF.Proof.«trees.c.align»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
open Zlib.Trees.Proofs.Out (TreesInvAt BitsDiff outBits natBits)
set_option autoImplicit false

/-- Actual PARTIAL marker alignment and foreign pending publication share one initialized
execution. The bit budget follows from the real tree buffer; caller capacity may be zero. -/
theorem empty_foreign_partial_publish {h : Heap} {r : ZStreamRef} {ds pb owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : BufferedBoundary h r ds z d input origin base [] config)
    (buffers : StreamBuffers h r) (trees : TreesInvAt h ds d pb buf)
    (pointer : z.next_out=.ref (.dstate_depth owner) oo) (publish : PublishReady d) :
    ∃ produced after z' result written remaining,
      (do Zlib.Trees.«_tr_align» (some (.tab ds)); flush_pending (some r)) h=.ok ((),after) ∧
      BufferedBoundary after r ds z' result input origin base [] config ∧ StreamBuffers after r ∧
      StreamAccounting z z' 0 produced ∧ ByteSizes h after ∧ OutputStorage h after r ds pb owner ∧
      ConfigFrame d result ∧ result.status=d.status ∧ result.last_flush=d.last_flush ∧
      (0<z'.avail_out.toNat → PublishReady result) ∧
      Bytes after z.next_out produced written ∧ PendingBits after result remaining ∧
      ZlibF.Spec.bytesToBits written++remaining=outBits buf d++(natBits 2 3++(natBits 0 7++[])) ∧
      z'.adler=z.adler ∧ z'.total_in=z.total_in ∧ z'.total_out=z.total_out+UInt64.ofNat produced ∧
      fillEnd result=fillEnd d ∧ result.match_available=d.match_available ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,produced⟩] := by
  have room : 8≤buf.size := by have extent:=trees.base.size;have lower:=trees.base.lit_lo;omega
  obtain ⟨next,middle,alignRun,treesM,outputM,sizeM,_frame,_lower,pendingM,fieldsM⟩ :=
    Zlib.Trees.Proofs.Out.tr_align_emit trees (by
      have zero:=publish.1;have low:=publish.2.2;have lower:=trees.run.bi_lo
      rw [zero];change 8*0+_+10≤_;omega)
  have markerRun : Zlib.Trees.«_tr_align» (some (.tab ds)) h=
      .ok ((),setD (Zlib.Trees.Proofs.Out.setB h pb next) ds middle) := by
    simpa only [Zlib.Trees.Proofs.Out.setD,setD] using alignRun
  have pendingBound : middle.pending.toNat≤6 := by rw [publish.1] at pendingM;exact pendingM
  have bitRoom : 8*middle.pending.toNat+middle.bi_valid.toInt.toNat≤8*next.size := by
    have upper:=treesM.run.bi_hi;have lower:=treesM.run.bi_lo
    rw [sizeM];omega
  obtain ⟨preparedHeap,prepared,sourceP,stateP,buffersP,sizesP,storageP,bitsP,fieldsP⟩ :=
    prepare_empty_bit_output (ob:=pb) boundary buffers trees publish.2.1 sizeM fieldsM treesM bitRoom
  obtain ⟨pb',produced,after,z',result,written,remaining,pbufP,run,stateA,buffersA,account,
      sizes,storage,_amount,_left,controls,ready,bytes,pending,bits,precise⟩ :=
    flush_pending_buffered_foreign_boundary stateP buffersP pointer bitsP
  obtain ⟨adlerA,inputA,outputA,_allocA,_nextA⟩ := flush_pending_low_foreign_run_scalar_effects
    stateP.good buffersP pointer stateP.bits run stateA.good.live.hz account
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
  have privatePrefix := marker_pending_private_frame storageP trees.base.pbuf
  have outputView := private_frame_foreign_output_same boundary.good buffers pointer privatePrefix
  have preciseWide : BufferFrame preparedHeap after (fun b => StreamRoot r b ∨ DeflateOwned ds d b)
      [⟨z.next_out,produced⟩] :=
    ⟨full_frame_weaken precise.1 (fun _ yes => yes.elim Or.inl (fun same => Or.inr (Or.inl same))),precise.2⟩
  have preciseAll : BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,produced⟩] := by
    rw [pointer] at preciseWide ⊢
    exact generic_wrapper_foreign_private_prefix privatePrefix outputView preciseWide
  refine ⟨produced,after,z',result,written,remaining,?_,stateA,buffersA,account,
    sizesP.trans sizes,(marker_pending_storage_output storageP).trans storage,(ConfigFrame.bits fieldsP).trans frameA,
    controlsA.1,controlsA.2,ready,bytes,pending,bits.trans outputM,adlerA,inputA,outputA,endpointA,availableA,preciseAll⟩
  simp only [bind_app,markerRun]
  exact sourceP.trans run

end Zlib.Deflate.Engine.Proofs
