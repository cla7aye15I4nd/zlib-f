import ZlibF.Proof.«deflate.c.engine.generic-foreign-sync-joint-raw»
import ZlibF.Proof.«deflate.c.engine.partial-sync-return»
import ZlibF.Proof.«deflate.c.engine.public-no-flush-encoding»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
open Zlib.Trees.Proofs.Out (TreesInvAt)
set_option autoImplicit false

/-- The actual SYNC block-done dispatch includes its real empty stored marker, foreign
publication and conditional retry store. All prepared caller capacities are admitted. -/
theorem public_strategy_foreign_sync_done_raw_encoding {h : Heap} {r : ZStreamRef} {ds pb owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {input : Nat → UInt8} {config : EngineConfig}
    {published : List UInt8}
    (boundary : BufferedBoundary h r ds z d input origin base [] config)
    (buffers : StreamBuffers h r) (trees : TreesInvAt h ds d pb buf)
    (pointer : z.next_out=.ref (.dstate_depth owner) oo) (publish : PublishReady d)
    (encoding : RawPrefix h d input base published) :
    ∃ produced after z' result written,
      publicStrategyReturn (some r) (some (.tab ds)) Z_SYNC_FLUSH block_done h=.ok (Z_OK,after) ∧
      BufferedBoundary after r ds z' result input origin base [] config ∧ StreamBuffers after r ∧
      StreamAccounting z z' 0 produced ∧ Bytes after z.next_out produced written ∧
      RawPrefix after result input base (published++written) ∧ ConfigFrame d result ∧
      result.status=d.status ∧ (result.last_flush=d.last_flush ∨ result.last_flush= -1) ∧
      z'.adler=z.adler ∧ fillEnd result=fillEnd d ∧ result.match_available=d.match_available ∧
      ByteOutputInterval h after (.dstate_depth owner) oo produced ∧
      z'.total_in=z.total_in ∧ z'.total_out=z.total_out+UInt64.ofNat produced ∧
      ByteSizes h after ∧ OutputStorage h after r ds pb owner ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,produced⟩] ∧
      (0<z'.avail_out.toNat → PublishReady result) := by
  obtain ⟨produced,middle,z',result,written,run,stateA,buffersA,accountA,bytesA,encodingA,
      configA,statusA,lastA,readyA,adlerA,endpointA,availableA,inputA,outputA,sizes,storage,precise⟩ :=
    foreign_sync_marker_joint_raw_prefix boundary buffers trees pointer publish encoding
  have source : publicStrategyReturn (some r) (some (.tab ds)) Z_SYNC_FLUSH block_done h=
      (if z'.avail_out==0 then .ok (Z_OK,setD middle ds {result with last_flush:= -1}) else .ok (Z_OK,middle)) := by
    have cut := public_strategy_partial_sync_source (some r) (some (.tab ds)) Z_SYNC_FLUSH (Or.inr rfl)
    simp only [show (Z_SYNC_FLUSH==Z_PARTIAL_FLUSH)=false from rfl,Bool.false_eq_true,ite_false] at cut
    rw [cut,bind_app,run]
    simp only [bind_app,zrd_eq,stateA.good.live.hz]
    split <;> simp only [wrD_eq,stateA.good.live.hs,bind_app,pure_app]
  by_cases exhausted : (z'.avail_out==0)=true
  · have bytesF := caller_bytes_setD_depth (result:={result with last_flush:= -1}) stateA.good.live.hs rfl bytesA
    have stateF := last_flush_buffered_boundary stateA (-1)
    obtain ⟨oldD,pba,ba,treesA⟩ := stateA.good.trees
    have sameD : oldD=result := Option.some.inj (treesA.base.dstate.symm.trans stateA.good.live.hs)
    subst oldD
    have pbEq : pba=pb := by
      have pendingA : result.pending_buf=d.pending_buf := congrArg EngineConfig.pending configA
      simpa only [pendingA,trees.base.pbuf,Ptr.ref.injEq,BRef.blk.injEq,and_true] using treesA.base.pbuf.symm
    subst pba
    obtain ⟨foreign,beforeGet,_bound,different,_old,_notRoot⟩ := caller_foreign_output boundary.good buffers pointer
    have pointerM : z'.next_out=.ref (.dstate_depth owner) (oo+produced) := by
      rw [accountA.2.2.2.2.2.1,pointer]
      rfl
    obtain ⟨middleForeign,middleGet,_⟩ := caller_foreign_output stateA.good buffersA pointerM
    have preciseF : BufferFrame h (setD middle ds {result with last_flush:= -1})
        (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,produced⟩] := by
      rw [pointer] at precise ⊢
      exact generic_wrapper_foreign_setD_frame stateA.good.live.hs beforeGet middleGet different (Or.inr (Or.inl rfl)) rfl precise
    have intervalF : ByteOutputInterval h (setD middle ds {result with last_flush:= -1}) (.dstate_depth owner) oo produced := by
      rw [pointer] at preciseF
      exact ByteOutputInterval.of_buffer_frame preciseF
    refine ⟨produced,_,z',_,written,by simpa only [exhausted,ite_true] using source,
      stateF,last_flush_buffers stateA.good buffersA (-1),accountA,bytesF,
      encodingA.last_flush stateA.good (-1),configA.trans (by rfl),statusA,Or.inr rfl,
      adlerA,endpointA,availableA,intervalF,inputA,outputA,sizes.trans (last_flush_sizes stateA.good.live.hs (-1)),
      storage.trans (last_flush_storage (ob:=owner) stateA.good treesA.base.bytes (-1)),preciseF,?_⟩
    intro output
    have empty : z'.avail_out=0 := beq_iff_eq.mp exhausted
    rw [empty] at output
    contradiction
  · have interval : ByteOutputInterval h middle (.dstate_depth owner) oo produced := by
      rw [pointer] at precise
      exact ByteOutputInterval.of_buffer_frame precise
    exact ⟨produced,middle,z',result,written,by simpa only [exhausted,Bool.false_eq_true,ite_false] using source,
      stateA,buffersA,accountA,bytesA,encodingA,configA,statusA,Or.inl lastA,adlerA,endpointA,
      availableA,interval,inputA,outputA,sizes,storage,precise,readyA⟩

end Zlib.Deflate.Engine.Proofs
