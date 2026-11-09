import ZlibF.Proof.«deflate.c.engine.generic-foreign-all-scalar-encoding»
import ZlibF.Proof.«deflate.c.engine.encoding-all-scalar-history»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false
/-- Every signed request and every legal public caller output view advances the
same original exact initialized encoding invariant. No outputtype/flag restriction
or called-function specification premise is supplied by the caller. -/
theorem DefaultEncodingState.generic_scalar_encoding_request {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig} {accepted observed actualInput : List UInt8}
    (state : DefaultEncodingState h r ds z d config accepted observed) (buffers : StreamBuffers h r)
    (flush : Int32)
    (snapshot : Bytes h z.next_in z.avail_in.toNat actualInput) :
    ∃ used rc after z' result written,
      deflate (some r) flush h=.ok (rc,after) ∧
      DefaultEncodingState after r ds z' result config
        (accepted++actualInput.take used) (observed++written) ∧
      StreamBuffers after r ∧ StreamAccounting z z' used written.length ∧
      Bytes after z.next_out written.length written ∧
      (rc=Z_STREAM_END → ZlibF.Spec.Zlib.Valid (accepted++actualInput.take used) (observed++written)) := by
  rcases caller_output_storage_cases state.protocol.good buffers with null|raw|⟨owner,oo,pointer⟩
  · exact state.scalar_encoding_request buffers (Or.inl null) flush snapshot
  · exact state.scalar_encoding_request buffers (Or.inr raw) flush snapshot
  · exact state.foreign_all_scalar_encoding_request buffers pointer flush snapshot

/-- Every actual signed observed event advances its exact accepted/emitted log.
Run determinism identifies the same final heap, code, counts and output byte list. -/
theorem DefaultEncodingState.generic_scalar_observed {h after : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    {accepted observed actualInput actualOutput : List UInt8} {flush rc : Int32} {used : Nat}
    (state : DefaultEncodingState h r ds z d config accepted observed)
    (step : DataStep .deflate h after r flush rc actualInput actualOutput used) :
    ∃ z' result, DefaultEncodingState after r ds z' result config
      (accepted++actualInput.take used) (observed++actualOutput) ∧
      (rc=Z_STREAM_END → ZlibF.Spec.Zlib.Valid (accepted++actualInput.take used) (observed++actualOutput)) := by
  have originalStep:=step
  obtain ⟨oldZ,_nextZ,oldGet,_nextGet,buffers,_header,snapshot,_usedEq,_bytes,_run⟩:=originalStep
  have streams : oldZ=z:=Option.some.inj (oldGet.symm.trans state.protocol.good.live.hz)
  subst oldZ
  obtain ⟨acceptedCount,ret,computed,z',result,written,run,stateA,_buffersA,accountA,bytesA,endedA⟩:=
    state.generic_scalar_encoding_request buffers flush snapshot
  obtain ⟨heaps,code,counts,writtenEq⟩:=data_step_identify_actual step state.protocol.good.live.hz run
    stateA.protocol.good.live.hz accountA bytesA
  rw [heaps,code,counts,writtenEq]
  exact ⟨z',result,stateA,endedA⟩

end Zlib.Deflate.Engine.Proofs
