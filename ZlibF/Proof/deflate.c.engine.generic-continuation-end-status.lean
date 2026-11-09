import ZlibF.Proof.«deflate.c.engine.generic-basic-request-completes»
import ZlibF.Proof.«deflate.c.engine.generic-completed-birth-cleanup»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Actual FINISH observations derive their terminal state. Rebuffering preserves
private status, while it may replace input fields; no final input-count equation
is preserved across arbitrary caller edits. -/
theorem DefaultFinishBoundary.follow_finish_continuation_end_status
    {r : ZStreamRef} {ds : Nat} {config : EngineConfig}
    {accepted source : List UInt8} {h after : Heap} {log finalLog : DataLog}
    (continuation : DeflateCore.FinishContinuation r accepted source h log after finalLog) :
    ∀ z d, DefaultFinishBoundary h r ds z d config →
      (log.result=Z_STREAM_END → d.status=FINISH_STATE) →
      ∃ z' result,DefaultFinishBoundary after r ds z' result config ∧
        (finalLog.result=Z_STREAM_END → result.status=FINISH_STATE) := by
  induction continuation with
  | refl => intro z d state terminal;exact ⟨z,d,state,terminal⟩
  | caller _ edit ih =>
      intro z d state terminal
      obtain ⟨zm,dm,stateM,terminalM⟩:=ih z d state terminal
      obtain ⟨zg,_getG,stateG⟩:=stateM.rebuffer edit
      exact ⟨zg,dm,stateG,terminalM⟩
  | step _ _get _pointer _positive _protocol _remaining observed ih =>
      intro z d state terminal
      obtain ⟨zm,dm,stateM,_terminalM⟩:=ih z d state terminal
      obtain ⟨_z,_z',_get,_get',buffers,_header,_snapshot,_used,_bytes,actual⟩:=observed
      obtain ⟨_consumed,_produced,rc,computed,returned,result,run,stateA,_buffers,_account,_codes⟩:=
        stateM.generic_all_scalar_request buffers Z_FINISH
      obtain ⟨code,heap⟩:=Prod.mk.inj (Except.ok.inj (run.symm.trans actual))
      subst rc computed
      refine ⟨returned,result,stateA,?_⟩
      intro ended
      have endedCode:=ended
      dsimp only [DeflateCore.advanceLog] at endedCode
      have actualEnd:=endedCode ▸ actual
      exact (stateM.generic_stream_end_run_control buffers actualEnd stateA.good).2.1
end Zlib.Deflate.Engine.Proofs
