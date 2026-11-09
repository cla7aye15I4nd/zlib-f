import ZlibF.Proof.«deflate.c.engine.generic-foreign-nonfinish-strategy-physical»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-partial-return-safety»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-sync-return-safety»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-full-return-safety»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-finish-scalar-frame»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Actual block-done marker returns retain exact totals and complete caller/object effects. -/
theorem foreign_nonfinish_marker_return_physical_execution {h : Heap} {r : ZStreamRef} {ds pb owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {config : EngineConfig} {buf : Array UInt8}
    (boundary : BufferedBoundary h r ds z d input origin base [] config) (buffers : StreamBuffers h r)
    (trees : TreesInvAt h ds d pb buf) (pointer : z.next_out=.ref (.dstate_depth owner) oo)
    (publish : PublishReady d) (look : d.lookahead=0) (available : d.match_available=0)
    (flush : Int32) (flag : flush=Z_PARTIAL_FLUSH ∨ flush=Z_SYNC_FLUSH ∨ flush=Z_FULL_FLUSH ∨ flush=Z_BLOCK) :
    ∃ produced after z' result,
      publicStrategyReturn (some r) (some (.tab ds)) flush block_done h=.ok (Z_OK,after) ∧
      DGood after r ds z' result ∧ StreamAccounting z z' 0 produced ∧
      z'.total_in=z.total_in ∧ z'.total_out=z.total_out+UInt64.ofNat produced ∧
      Shape h after ∧ Frame h after (fun b=>StreamRoot r b ∨ DeflateOwned ds d b ∨ b=owner) ∧
      LiveChange h after (fun _=>False) (fun _=>False) ∧ after.nalloc=h.nalloc ∧ after.nextBlk=h.nextBlk ∧
      BufferFrame h after (fun b=>StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,produced⟩] := by
  rcases flag with rfl|rfl|rfl|rfl
  · obtain ⟨amount,after,z',result,_written,run,stateA,_buffersA,accountA,_bytes,_config,_status,_last,
        _adler,_end,_available,_interval,inputA,outputA,_sizes,storage,precise,_ready⟩ :=
      public_strategy_foreign_partial_done boundary buffers trees pointer publish
    exact ⟨amount,after,z',result,run,stateA.good,accountA,inputA,outputA,
      storage.shape,storage.private_frame trees.base.pbuf,full_shape_live_change storage.shape,storage.nalloc,storage.nextBlk,precise⟩
  · obtain ⟨amount,after,z',result,_written,_remaining,run,stateA,_buffersA,accountA,_bytes,_pending,_wire,
        _config,_status,_last,_adler,_end,_available,_interval,inputA,outputA,_sizes,storage,precise,_ready⟩ :=
      public_strategy_foreign_sync_done boundary buffers trees pointer publish
    exact ⟨amount,after,z',result,run,stateA.good,accountA,inputA,outputA,
      storage.shape,storage.private_frame trees.base.pbuf,full_shape_live_change storage.shape,storage.nalloc,storage.nextBlk,precise⟩
  · obtain ⟨amount,after,z',result,_written,_remaining,run,stateA,_buffersA,accountA,_bytes,_pending,_wire,
        _config,_status,_last,_adler,_end,_available,_endpoint,_interval,inputA,outputA,_sizes,shape,alloc,next,precise,_ready⟩ :=
      public_strategy_foreign_full_done boundary buffers trees pointer publish look available
    obtain ⟨foreign,get,_⟩ := caller_foreign_output boundary.good buffers pointer
    have framed := precise
    rw [pointer] at framed
    have coarse := (foreign_buffer_frame_owner_facts get (caller_foreign_owner_outside boundary.good buffers pointer) framed).2.2
    have frame : Frame h after (fun b=>StreamRoot r b ∨ DeflateOwned ds d b ∨ b=owner) :=
      full_frame_weaken coarse (fun _ yes=>yes.elim (fun inner=>inner.elim Or.inl (fun owned=>Or.inr (Or.inl owned))) (fun same=>Or.inr (Or.inr same)))
    exact ⟨amount,after,z',result,run,stateA.good,accountA,inputA,outputA,shape,frame,full_shape_live_change shape,alloc,next,precise⟩
  · have actual := public_strategy_block_done_ready boundary.good publish
    by_cases empty : (z.avail_out==0)=true
    · simp only [empty,ite_true] at actual
      have shape := shape_setD boundary.good.live.hs {d with last_flush:= -1}
      have privateFrame : Frame h (setD h ds {d with last_flush:= -1}) (fun b=>StreamRoot r b ∨ DeflateOwned ds d b) :=
        full_frame_weaken (state_store_full_frame h ds _) (fun _ same=>Or.inr (Or.inl same))
      exact ⟨0,_,z,_,actual,last_flush_good boundary.good (-1),stream_accounting_zero z,rfl,by simp,
        shape,full_private_frame_add_output privateFrame,full_shape_live_change shape,rfl,rfl,
        marker_private_buffer_frame boundary.good buffers pointer privateFrame shape⟩
    · simp only [empty,Bool.false_eq_true,ite_false] at actual
      exact ⟨0,h,z,d,actual,boundary.good,stream_accounting_zero z,rfl,by simp,
        Shape.refl h,(full_storage_refl h _).2.1,full_shape_live_change (Shape.refl h),rfl,rfl,
        marker_private_buffer_frame boundary.good buffers pointer (full_storage_refl h _).2.1 (Shape.refl h)⟩
end Zlib.Deflate.Engine.Proofs
