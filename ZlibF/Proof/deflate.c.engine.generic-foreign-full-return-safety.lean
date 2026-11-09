import ZlibF.Proof.«deflate.c.engine.generic-foreign-full-marker»
import ZlibF.Proof.«deflate.c.engine.full-flush-return»
import ZlibF.Proof.«deflate.c.engine.public-no-flush-encoding»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
open Zlib.Trees.Proofs.Out (TreesInvAt)
set_option autoImplicit false

/-- The actual FULL block-done dispatch includes its real stored marker, hash/position reset, foreign
publication and conditional retry store. All prepared caller capacities are admitted. No independent encoding or checksum history is required. -/
theorem public_strategy_foreign_full_done {h : Heap} {r : ZStreamRef} {ds pb owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : BufferedBoundary h r ds z d input origin base [] config)
    (buffers : StreamBuffers h r) (trees : TreesInvAt h ds d pb buf)
    (pointer : z.next_out=.ref (.dstate_depth owner) oo) (publish : PublishReady d)
    (look : d.lookahead=0) (available : d.match_available=0)
    :
    ∃ produced after z' result written remaining,
      publicStrategyReturn (some r) (some (.tab ds)) Z_FULL_FLUSH block_done h=.ok (Z_OK,after) ∧
      BufferedBoundary after r ds z' result input base base [] config ∧ StreamBuffers after r ∧
      StreamAccounting z z' 0 produced ∧ Bytes after z.next_out produced written ∧
      PendingBits after result remaining ∧
      ZlibF.Spec.bytesToBits written++remaining=Zlib.Trees.Proofs.Out.outBits buf d++Zlib.Trees.Proofs.Out.storedHeaderBits d 0 false ∧
      ConfigFrame d result ∧
      result.status=d.status ∧ (result.last_flush=d.last_flush ∨ result.last_flush= -1) ∧
      z'.adler=z.adler ∧ fillEnd result=0 ∧ result.match_available=0 ∧ base+fillEnd result=origin+fillEnd d ∧
      ByteOutputInterval h after (.dstate_depth owner) oo produced ∧
      z'.total_in=z.total_in ∧ z'.total_out=z.total_out+UInt64.ofNat produced ∧
      ByteSizes h after ∧ Shape h after ∧ after.nalloc=h.nalloc ∧ after.nextBlk=h.nextBlk ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,produced⟩] ∧
      (0<z'.avail_out.toNat → PublishReady result) := by
  obtain ⟨produced,middle,z',result,written,remaining,run,stateA,buffersA,accountA,
      configA,statusA,lastA,bytesA,pendingA,wireA,adlerA,endpointA,availableA,inputA,outputA,readyA,sizes,shape,alloc,next,precise⟩ :=
    foreign_empty_full_marker_publish boundary buffers trees pointer publish look available
  have source : publicStrategyReturn (some r) (some (.tab ds)) Z_FULL_FLUSH block_done h=
      (if z'.avail_out==0 then .ok (Z_OK,setD middle ds {result with last_flush:= -1}) else .ok (Z_OK,middle)) := by
    rw [public_strategy_full_source,bind_app,run]
    simp only [bind_app,zrd_eq,stateA.good.live.hz]
    split <;> simp only [wrD_eq,stateA.good.live.hs,bind_app,pure_app]
  have endpointOld : base=origin+fillEnd d := by
    have accounted:=boundary.accounted
    have position : base=origin+d.strstart.toNat := by
      simpa only [represented,pendingCredit,available,ite_true,Nat.add_zero] using accounted
    simpa only [fillEnd,look,UInt32.toNat_zero,Nat.add_zero] using position
  have endpointGlobal : base+fillEnd result=origin+fillEnd d := by
    rw [endpointA,Nat.add_zero]
    exact endpointOld
  by_cases exhausted : (z'.avail_out==0)=true
  · have bytesF := caller_bytes_setD_depth (result:={result with last_flush:= -1}) stateA.good.live.hs rfl bytesA
    have stateF := last_flush_buffered_boundary stateA (-1)
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
    refine ⟨produced,_,z',_,written,remaining,by simpa only [exhausted,ite_true] using source,
      stateF,last_flush_buffers stateA.good buffersA (-1),accountA,bytesF,
      last_flush_pending_bits stateA.good pendingA (-1),wireA,configA.trans (by rfl),statusA,Or.inr rfl,
      adlerA,endpointA,availableA,endpointGlobal,intervalF,inputA,outputA,sizes.trans (last_flush_sizes stateA.good.live.hs (-1)),
      shape.trans (shape_setD stateA.good.live.hs {result with last_flush:= -1}),alloc,next,preciseF,?_⟩
    intro output
    have empty : z'.avail_out=0 := beq_iff_eq.mp exhausted
    rw [empty] at output
    contradiction
  · have interval : ByteOutputInterval h middle (.dstate_depth owner) oo produced := by
      rw [pointer] at precise
      exact ByteOutputInterval.of_buffer_frame precise
    exact ⟨produced,middle,z',result,written,remaining,by simpa only [exhausted,Bool.false_eq_true,ite_false] using source,
      stateA,buffersA,accountA,bytesA,pendingA,wireA,configA,statusA,Or.inl lastA,adlerA,endpointA,
      availableA,endpointGlobal,interval,inputA,outputA,sizes,shape,alloc,next,precise,readyA⟩

end Zlib.Deflate.Engine.Proofs
