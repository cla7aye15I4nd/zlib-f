import ZlibF.Proof.«deflate.c.engine.generic-finish-continuation-encoding»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Every genuine basic call history admits a finite actual FINISH continuation
once the remaining source is readable and obeys the original FINISH input protocol.
Past calls need no snapshots; real unreadable-input refusals preserve accepted and
emitted lists. Those lists and the initialized J are derived from actual history.
The continuation really returns END and its final cumulative output independently
encodes the derived accepted bytes followed by exactly the remaining source.
No output bound, raw restriction on past history or callee-contract premise appears. -/
theorem GenericDefaultRequestTrace.completes {h : Heap} {r : ZStreamRef}
    {z : ZStream} {input : List UInt8} (history : GenericDefaultRequestTrace r h)
    (get : r.get h=some z) (buffers : StreamBuffers h r)
    (snapshot : Bytes h z.next_in z.avail_in.toNat input)
    (protocol : ∀ ds d,z.state=some (.deflate ds) → h.dstates ds=some d →
      d.status=FINISH_STATE → input=[]) :
    ∃ ds d config accepted observed after finalLog z' result,
      DefaultEncodingState h r ds z d config accepted observed ∧
      DeflateCore.FinishContinuation r accepted input h
        {input:=accepted,output:=observed} after finalLog ∧
      GenericDefaultRequestTrace r after ∧ finalLog.input=accepted++input ∧
      finalLog.result=Z_STREAM_END ∧
      DefaultEncodingState after r ds z' result config finalLog.input finalLog.output ∧
      ZlibF.Spec.Zlib.Valid (accepted++input) finalLog.output := by
  obtain ⟨ds,current,d,config,accepted,observed,state⟩ := history.encoding_state
  have same : current=z := Option.some.inj (state.protocol.good.live.hz.symm.trans get)
  subst current
  obtain ⟨allocated,getAllocated,allocators⟩ := history.allocators
  have same : allocated=z := Option.some.inj (getAllocated.symm.trans get)
  subst allocated
  have inputProtocol : d.status=FINISH_STATE → z.avail_in=0 := by
    intro status
    have empty := protocol ds d state.protocol.good.live.zst state.protocol.good.live.hs status
    have length := caller_bytes_length snapshot
    rw [empty] at length
    exact UInt32.toNat_inj.mp length.symm
  let initial : DataLog := {input:=accepted,output:=observed}
  obtain ⟨after,finalLog,continuation,content,ended⟩ :=
    ZlibF.Spec.Public.Proofs.DeflateCore.complete_source_environment (log:=initial)
      state.protocol history.globals allocators buffers snapshot inputProtocol
  have traceA := GenericDefaultRequestTrace.append_finish continuation history
  have seedValidity : initial.result=Z_STREAM_END → ZlibF.Spec.Zlib.Valid initial.input initial.output := by
    intro impossible
    exact False.elim ((by decide : Z_OK≠Z_STREAM_END) impossible)
  obtain ⟨z',result,stateA,validityA⟩ :=
    DefaultEncodingState.follow_finish_continuation continuation z d state seedValidity
  exact ⟨ds,d,config,accepted,observed,after,finalLog,z',result,state,continuation,
    traceA,content,ended,stateA,content ▸ validityA ended⟩
end Zlib.Deflate.Engine.Proofs
