import ZlibF.Proof.«deflate.c.engine.generic-request-encoding-state»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Every signed basic call has exact accepted/published byte meaning without
requiring a readable snapshot from the caller. Public buffers derive either the
actual snapshot and its consumed prefix, or the real NULL-input refusal with
zero input/output. All conclusions describe the same actual library execution. -/
theorem DefaultEncodingState.generic_scalar_request_content_without_snapshot {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig} {accepted observed : List UInt8}
    (state : DefaultEncodingState h r ds z d config accepted observed) (buffers : StreamBuffers h r)
    (flush : Int32) :
    ∃ used rc after z' result written consumed,
      deflate (some r) flush h=.ok (rc,after) ∧
      DefaultEncodingState after r ds z' result config (accepted++consumed) (observed++written) ∧
      StreamBuffers after r ∧ StreamAccounting z z' used written.length ∧
      Bytes after z.next_out written.length written ∧ consumed.length=used ∧
      ((∃ original,Bytes h z.next_in z.avail_in.toNat original ∧ consumed=original.take used) ∨
        (z.avail_in≠0 ∧ z.next_in=.null ∧ used=0 ∧ consumed=[] ∧ written=[] ∧ rc=Z_STREAM_ERROR)) ∧
      (rc=Z_STREAM_END → ZlibF.Spec.Zlib.Valid (accepted++consumed) (observed++written)) := by
  rcases caller_input_snapshot_or_invalid buffers state.protocol.good.live.hz with ⟨original,snapshot⟩|invalid
  · obtain ⟨used,rc,after,z',result,written,run,stateA,buffersA,account,bytesA,validity⟩ :=
      state.generic_scalar_encoding_request buffers flush snapshot
    have length : (original.take used).length=used := by
      have full := caller_bytes_length snapshot
      have bound := account.1
      simp only [List.length_take]
      omega
    exact ⟨used,rc,after,z',result,written,original.take used,run,stateA,buffersA,account,bytesA,length,
      Or.inl ⟨original,snapshot,rfl⟩,validity⟩
  · obtain ⟨after,z',run,stateA,buffersA,account,bytesA⟩ := state.unreadable_input_refusal buffers invalid flush
    refine ⟨0,Z_STREAM_ERROR,after,z',d,[],[],run,?_,buffersA,account,bytesA,rfl,
      Or.inr ⟨invalid.1,invalid.2,rfl,rfl,rfl,rfl⟩,?_⟩
    · simpa only [List.append_nil] using stateA
    · intro impossible
      exact False.elim ((by decide : Z_STREAM_ERROR≠Z_STREAM_END) impossible)

end Zlib.Deflate.Engine.Proofs
