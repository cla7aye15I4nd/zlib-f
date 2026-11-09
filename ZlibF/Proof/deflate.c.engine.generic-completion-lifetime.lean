import ZlibF.Proof.«deflate.c.engine.generic-continuation-end-status»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- A finite real FINISH continuation completes and then End returns OK, releasing
exactly the original five successful-default-init objects. Past requests may have
any signed flag and need no readable snapshots. The remaining input uses the
original public FINISH protocol. No END or final status is assumed. -/
theorem GenericDefaultRequestTrace.completes_with_original_birth_cleanup
    {h : Heap} {r : ZStreamRef} {z : ZStream} {input : List UInt8}
    (history : GenericDefaultRequestTrace r h) (get : r.get h=some z)
    (buffers : StreamBuffers h r) (snapshot : Bytes h z.next_in z.avail_in.toNat input)
    (protocol : ∀ ds d,z.state=some (.deflate ds) → h.dstates ds=some d →
      d.status=FINISH_STATE → input=[]) :
    ∃ ds d config accepted observed after finalLog z' result before initialized version ended,
      DefaultEncodingState h r ds z d config accepted observed ∧
      DeflateCore.FinishContinuation r accepted input h
        {input:=accepted,output:=observed} after finalLog ∧
      GenericDefaultRequestTrace r after ∧ finalLog.input=accepted++input ∧
      finalLog.result=Z_STREAM_END ∧
      DefaultEncodingState after r ds z' result config finalLog.input finalLog.output ∧
      ZlibF.Spec.Zlib.Valid (accepted++input) finalLog.output ∧ result.status=FINISH_STATE ∧
      InitDomain before r version ∧
      C.run (deflateInit_ (some r) Z_DEFAULT_COMPRESSION version 112) before=.ok (Z_OK,initialized) ∧
      ds=before.nextBlk ∧ initialized.nalloc=before.nalloc+5 ∧
      DeflateInitial before initialized r (ZlibF.Spec.Public.Proofs.DeflateInit.settings 6) ∧
      (∀ b, DeflateOwned ds result b ↔ before.nextBlk≤b ∧ b<before.nextBlk+5) ∧
      (∀ b, before.nextBlk≤b → b<before.nextBlk+5 → after.live b ∧ ¬ before.live b) ∧
      C.run (deflateEnd (some r)) after=.ok (Z_OK,ended) ∧
      r.get ended=some {z' with state:=none} ∧
      LiveChange after ended (fun _=>False) (fun b=>before.nextBlk≤b ∧ b<before.nextBlk+5) ∧
      (∀ b, ended.live b ↔ after.live b ∧ ¬ (before.nextBlk≤b ∧ b<before.nextBlk+5)) ∧
      (∀ b, before.nextBlk≤b → b<before.nextBlk+5 → ¬ ended.live b) ∧
      (∀ b, ¬ (before.nextBlk≤b ∧ b<before.nextBlk+5) → (ended.live b ↔ after.live b)) ∧
      Frame after ended (fun b=>StreamRoot r b ∨ (before.nextBlk≤b ∧ b<before.nextBlk+5)) ∧
      ended.nalloc=after.nalloc ∧ ended.nextBlk=after.nextBlk := by
  obtain ⟨ds,d,config,accepted,observed,after,finalLog,z',result,state,continuation,
    historyA,content,done,stateA,validity⟩:=history.completes get buffers snapshot protocol
  have seedTerminal : ({input:=accepted,output:=observed} : DataLog).result=Z_STREAM_END → d.status=FINISH_STATE := by
    intro impossible
    exact False.elim ((by decide : Z_OK≠Z_STREAM_END) impossible)
  obtain ⟨terminalZ,terminalD,terminalState,terminal⟩ :=
    DefaultFinishBoundary.follow_finish_continuation_end_status continuation z d state.protocol seedTerminal
  have terminalStreams : terminalZ=z' :=
    Option.some.inj (terminalState.good.live.hz.symm.trans stateA.protocol.good.live.hz)
  have terminalStates : terminalD=result :=
    Option.some.inj (terminalState.good.live.hs.symm.trans stateA.protocol.good.live.hs)
  subst terminalZ terminalD
  have status : result.status=FINISH_STATE:=terminal done
  obtain ⟨before,initialized,version,birthDs,birthZ,birthD,birthConfig,ended,domain,initRun,key,count,initial,
    birthState,owned,fresh,cleanup,getEnd,live,exactLive,freed,others,frame,nalloc,next⟩:=historyA.birth_cleanup
  have streams : birthZ=z' := Option.some.inj (birthState.good.live.hz.symm.trans stateA.protocol.good.live.hz)
  subst birthZ
  have keys : birthDs=ds := by
    injection birthState.good.live.zst.symm.trans stateA.protocol.good.live.zst with tagged
    injection tagged
  rw [keys] at birthState owned key
  have states : birthD=result := Option.some.inj (birthState.good.live.hs.symm.trans stateA.protocol.good.live.hs)
  subst birthD
  have notBusy : result.status≠BUSY_STATE := by rw [status];decide
  rw [ite_eq_right notBusy] at cleanup
  exact ⟨ds,d,config,accepted,observed,after,finalLog,z',result,before,initialized,version,ended,
    state,continuation,historyA,content,done,stateA,validity,status,domain,initRun,key,count,initial,
    owned,fresh,cleanup,getEnd,live,exactLive,freed,others,frame,nalloc,next⟩
end Zlib.Deflate.Engine.Proofs
