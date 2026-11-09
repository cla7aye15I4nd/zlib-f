import ZlibF.Proof.«deflate.c.engine.generic-foreign-nonfinish-marker-data-physical»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-partial-data-safety»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-marker-data-safety»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-no-flush-data-environment»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Every accepted prepared non-FINISH flag executes its actual complete data tail,
preserves the initialized buffered protocol, has exact wrapping totals and the full
object/allocation/caller byte frame. Internal zero capacity is included. -/
theorem public_foreign_busy_nonfinish_data_full_storage_execution {h : Heap} {r : ZStreamRef} {ds owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : BufferedBoundary h r ds z d input origin base xs config) (buffers : StreamBuffers h r)
    (status : d.status=BUSY_STATE) (level : d.level=6) (strategy : d.strategy=0)
    (pointer : z.next_out=.ref (.dstate_depth owner) oo) (memory : config.memory.toNat=16384)
    (wrap : config.wrap=1) (publish : PublishReady d) (valid : z.avail_in≠0 → z.next_in≠.null)
    (flush : Int32) (flag : flush=Z_NO_FLUSH ∨ flush=Z_PARTIAL_FLUSH ∨ flush=Z_SYNC_FLUSH ∨ flush=Z_FULL_FLUSH ∨ flush=Z_BLOCK) :
    ∃ used produced after z' result nextInput nextOrigin nextBase ys,
      publicDataTail (some r) (some (.tab ds)) flush h=.ok (Z_OK,after) ∧
      BufferedBoundary after r ds z' result nextInput nextOrigin nextBase ys config ∧ StreamBuffers after r ∧
      StreamAccounting z z' used produced ∧ result.status=BUSY_STATE ∧
      (result.last_flush=d.last_flush ∨ result.last_flush= -1) ∧
      z'.total_in=z.total_in+UInt64.ofNat used ∧ z'.total_out=z.total_out+UInt64.ofNat produced ∧
      Shape h after ∧ Frame h after (fun b=>StreamRoot r b ∨ DeflateOwned ds d b ∨ b=owner) ∧
      LiveChange h after (fun _=>False) (fun _=>False) ∧ after.nalloc=h.nalloc ∧ after.nextBlk=h.nextBlk ∧
      BufferFrame h after (fun b=>StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,produced⟩] := by
  have safety : ∃ used produced after z' result nextInput nextOrigin nextBase ys,
      publicDataTail (some r) (some (.tab ds)) flush h=.ok (Z_OK,after) ∧
      BufferedBoundary after r ds z' result nextInput nextOrigin nextBase ys config ∧ StreamBuffers after r ∧
      StreamAccounting z z' used produced ∧ result.status=BUSY_STATE ∧
      (result.last_flush=d.last_flush ∨ result.last_flush= -1) := by
    rcases flag with nf|par|other
    · subst flush
      obtain ⟨used,produced,after,z',result,nextInput,nextOrigin,nextBase,ys,actual,stateA,buffersA,accountA,statusA,lastA,_static⟩ :=
        public_foreign_busy_no_flush_data_static_execution boundary buffers status level strategy pointer memory wrap publish valid
      exact ⟨used,produced,after,z',result,nextInput,nextOrigin,nextBase,ys,actual,stateA,buffersA,accountA,statusA,lastA.symm⟩
    · subst flush
      exact public_foreign_busy_partial_data_safety boundary buffers status level strategy pointer memory wrap publish valid Z_PARTIAL_FLUSH rfl
    · exact public_foreign_busy_sync_full_block_data_safety boundary buffers status level strategy pointer memory wrap publish valid flush other
  obtain ⟨used,produced,after,z',result,nextInput,nextOrigin,nextBase,ys,run,stateA,buffersA,accountA,statusA,lastA⟩ := safety
  have physics : ∃ read written other otherZ otherD,
      publicDataTail (some r) (some (.tab ds)) flush h=.ok (Z_OK,other) ∧
      DGood other r ds otherZ otherD ∧ StreamAccounting z otherZ read written ∧
      otherZ.total_in=z.total_in+UInt64.ofNat read ∧ otherZ.total_out=z.total_out+UInt64.ofNat written ∧
      Shape h other ∧ Frame h other (fun b=>StreamRoot r b ∨ DeflateOwned ds d b ∨ b=owner) ∧
      LiveChange h other (fun _=>False) (fun _=>False) ∧ other.nalloc=h.nalloc ∧ other.nextBlk=h.nextBlk ∧
      BufferFrame h other (fun b=>StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,written⟩] := by
    rcases flag with nf|marker
    · subst flush
      exact public_foreign_busy_no_flush_physical_execution boundary buffers status level strategy pointer memory wrap publish valid
    · exact public_foreign_busy_marker_data_physical_execution boundary buffers status level strategy pointer memory wrap publish valid flush marker
  obtain ⟨read,written,other,otherZ,otherD,actual,goodA,accountB,inputA,outputA,shape,frame,live,alloc,next,precise⟩ := physics
  have heaps := (Prod.mk.inj (Except.ok.inj (actual.symm.trans run))).2
  subst other
  have streams : otherZ=z' := Option.some.inj (goodA.live.hz.symm.trans stateA.good.live.hz)
  subst otherZ
  have counts := stream_accounting_counts_unique accountB accountA
  rw [counts.1] at inputA
  rw [counts.2] at outputA precise
  exact ⟨used,produced,after,z',result,nextInput,nextOrigin,nextBase,ys,run,stateA,buffersA,accountA,statusA,lastA,
    inputA,outputA,shape,frame,live,alloc,next,precise⟩
end Zlib.Deflate.Engine.Proofs
