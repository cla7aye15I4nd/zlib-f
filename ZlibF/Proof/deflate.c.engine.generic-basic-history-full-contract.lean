import ZlibF.Proof.«deflate.c.engine.generic-basic-full-contract»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Every actual basic default history establishes the original strong encoding
state and default allocator identities, then every next signed public deflate
call has one complete same-execution safety/content/controls/resource contract.
History and next-call inputs impose no readable snapshot, output representation,
positive capacity, custom-header, invariant or called-function assumption.
Advanced APIs are outside this basic init/caller/deflate epoch. -/
theorem GenericDefaultRequestTrace.full_next_request_contract {h : Heap} {r : ZStreamRef}
    (history : GenericDefaultRequestTrace r h) :
    ∃ ds z d config accepted observed,
      DefaultEncodingState h r ds z d config accepted observed ∧ DefAlloc z ∧
      ∀ flush,StreamBuffers h r →
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
  obtain ⟨ds,z,d,config,accepted,observed,state⟩ := history.encoding_state
  obtain ⟨allocated,getAllocated,allocators⟩ := history.allocators
  have same : allocated=z := Option.some.inj (getAllocated.symm.trans state.protocol.good.live.hz)
  subst allocated
  exact ⟨ds,z,d,config,accepted,observed,state,allocators,
    fun flush buffers=>state.generic_basic_full_request buffers flush⟩
end Zlib.Deflate.Engine.Proofs
