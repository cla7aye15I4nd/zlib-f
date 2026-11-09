import ZlibF.Proof.«deflate.c.engine.generic-foreign-sync-data-safety»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-full-data-safety»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-block-data-safety»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Actual SYNC2/FULL3/BLOCK5 data dispatch preserves the original initialized
working protocol at every prepared output capacity. No RawPrefix, input snapshot,
checksum history or callee execution/effect premise is required. -/
theorem public_foreign_busy_sync_full_block_data_safety {h : Heap} {r : ZStreamRef} {ds owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : BufferedBoundary h r ds z d input origin base xs config) (buffers : StreamBuffers h r)
    (status : d.status=BUSY_STATE) (level : d.level=6) (strategy : d.strategy=0)
    (pointer : z.next_out=.ref (.dstate_depth owner) oo) (memory : config.memory.toNat=16384)
    (wrap : config.wrap=1) (publish : PublishReady d) (inputValid : z.avail_in≠0 → z.next_in≠.null)
    (flush : Int32) (flag : flush=Z_SYNC_FLUSH ∨ flush=Z_FULL_FLUSH ∨ flush=Z_BLOCK) :
    ∃ used produced after z' result extended nextOrigin nextBase ys,
      publicDataTail (some r) (some (.tab ds)) flush h=.ok (Z_OK,after) ∧
      BufferedBoundary after r ds z' result extended nextOrigin nextBase ys config ∧ StreamBuffers after r ∧
      StreamAccounting z z' used produced ∧ result.status=BUSY_STATE ∧
      (result.last_flush=d.last_flush ∨ result.last_flush= -1) := by
  rcases flag with rfl|rfl|rfl
  · exact public_foreign_busy_slow_sync_phase (boundary.strategy publish) boundary.end_frontier buffers
      status level strategy pointer memory wrap publish inputValid
  · exact public_foreign_busy_slow_full_phase (boundary.strategy publish) boundary.end_frontier buffers
      status level strategy pointer memory wrap publish inputValid
  · obtain ⟨used,produced,after,z',result,nextBase,ys,extended,nextOrigin,run,stateA,endA,buffersA,accountA,
        _agreesA,_endpointA,_baseA,statusA,lastA,cursorA⟩ :=
      public_foreign_busy_slow_block_phase (boundary.strategy publish) boundary.end_frontier buffers
        status level strategy pointer memory wrap publish inputValid
    exact ⟨used,produced,after,z',result,extended,nextOrigin,nextBase,ys,run,
      stateA.buffered endA cursorA,buffersA,accountA,statusA,lastA⟩
end Zlib.Deflate.Engine.Proofs
