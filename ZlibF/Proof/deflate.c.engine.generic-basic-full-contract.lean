import ZlibF.Proof.«deflate.c.engine.generic-all-scalar-effects»
import ZlibF.Proof.«deflate.c.engine.generic-request-next-content»
import ZlibF.Proof.«deflate.c.engine.generic-request-encoding-state»
import ZlibF.Proof.«deflate.c.engine.generic-stream-end-control»
import ZlibF.Proof.«deflate.c.engine.generic-return-code-controls»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Complete same-execution basic deflate contract, for every signed flush and
all legal public caller output views. The caller supplies the original initialized
encoding state and public buffers only; the actual history producer derives that
state. A readable input snapshot is derived when present. NULL positive-input
refusals have zero accepted/emitted bytes and need no false snapshot.
All return controls, exact original consumed bytes, independent END validity,
wrapping totals, full caller frame and allocation effects describe the same run. -/
theorem DefaultEncodingState.generic_basic_full_request {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig} {accepted observed : List UInt8}
    (state : DefaultEncodingState h r ds z d config accepted observed) (buffers : StreamBuffers h r)
    (flush : Int32) :
    ∃ used rc after z' result written consumed,
      deflate (some r) flush h=.ok (rc,after) ∧
      DefaultEncodingState after r ds z' result config (accepted++consumed) (observed++written) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧
      StreamAccounting z z' used written.length ∧ Bytes after z.next_out written.length written ∧
      consumed.length=used ∧
      ((∃ original,Bytes h z.next_in z.avail_in.toNat original ∧ consumed=original.take used) ∨
        (z.avail_in≠0 ∧ z.next_in=.null ∧ used=0 ∧ consumed=[] ∧ written=[] ∧ rc=Z_STREAM_ERROR)) ∧
      z'.adler=(ZlibF.Spec.adler32 (accepted++consumed)).toUInt64 ∧
      z'.total_in=z.total_in+UInt64.ofNat used ∧ z'.total_out=z.total_out+UInt64.ofNat written.length ∧
      (rc=Z_OK ∨ rc=Z_STREAM_END ∨ rc=Z_STREAM_ERROR ∨ rc=Z_BUF_ERROR) ∧
      (rc=Z_STREAM_ERROR ↔ flush.toInt<0 ∨ 5<flush.toInt ∨ z.next_out=.null ∨
        (z.next_in=.null ∧ z.avail_in≠0) ∨ (d.status=FINISH_STATE ∧ flush≠Z_FINISH)) ∧
      (flush.toInt<0 ∨ 5<flush.toInt → rc=Z_STREAM_ERROR ∧ after=h) ∧
      (rc=Z_STREAM_END → flush=Z_FINISH ∧ result.status=FINISH_STATE ∧
        z'.avail_in=0 ∧ result.pending=0 ∧ result.bi_valid=0) ∧
      (rc=Z_STREAM_END → ZlibF.Spec.Zlib.Valid (accepted++consumed) (observed++written)) ∧
      Shape h after ∧ BufferFrame h after (fun b=>StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,written.length⟩] ∧
      LiveChange h after (fun _=>False) (fun _=>False) ∧ after.nalloc=h.nalloc ∧ after.nextBlk=h.nextBlk := by
  obtain ⟨used,rc,after,z',result,written,consumed,run,stateA,buffersA,account,bytesA,length,ledger,validity⟩ :=
    state.generic_scalar_request_content_without_snapshot buffers flush
  have effects := state.protocol.generic_all_scalar_run_effects buffers run stateA.protocol.good.live.hz account
  have codes : rc=Z_OK ∨ rc=Z_STREAM_END ∨ rc=Z_STREAM_ERROR ∨ rc=Z_BUF_ERROR := by
    obtain ⟨_used,_produced,ret,_heap,_z,_d,actual,_state,_buffers,_account,codes⟩ :=
      state.protocol.generic_all_scalar_request buffers flush
    have code := (Prod.mk.inj (Except.ok.inj (actual.symm.trans run))).1
    rw [←code]
    exact codes
  have errorControl := state.protocol.generic_stream_error_run_iff buffers run
  have badControl := state.protocol.generic_bad_scalar_run_control run
  have terminal : rc=Z_STREAM_END → flush=Z_FINISH ∧ result.status=FINISH_STATE ∧
      z'.avail_in=0 ∧ result.pending=0 ∧ result.bi_valid=0 := by
    intro ended
    have actual : deflate (some r) flush h=.ok (Z_STREAM_END,after) := by rw [←ended];exact run
    exact state.protocol.generic_stream_end_run_control buffers actual stateA.protocol.good
  exact ⟨used,rc,after,z',result,written,consumed,run,stateA,stateA.protocol.good,buffersA,account,
    bytesA,length,ledger,stateA.checksum,effects.1,effects.2.1,codes,errorControl,badControl,terminal,
    validity,effects.2.2⟩

end Zlib.Deflate.Engine.Proofs
