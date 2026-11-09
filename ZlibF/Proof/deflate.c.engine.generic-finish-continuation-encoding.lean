import ZlibF.Proof.«deflate.c.engine.generic-request-encoding-state»
import ZlibF.Proof.«deflate.c.engine.generic-all-scalar-static»
import ZlibF.Proof.«deflate.c.engine.generic-finish-complete-environment»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- A real finite FINISH continuation preserves the exact seed encoding state
and its cumulative byte log, regardless of the representation of past outputs. -/
theorem DefaultEncodingState.follow_finish_continuation {r : ZStreamRef} {ds : Nat} {config : EngineConfig}
    {accepted source : List UInt8} {h after : Heap} {log finalLog : DataLog}
    (continuation : DeflateCore.FinishContinuation r accepted source h log after finalLog) :
    ∀ z d, DefaultEncodingState h r ds z d config log.input log.output →
      (log.result=Z_STREAM_END → ZlibF.Spec.Zlib.Valid log.input log.output) →
      ∃ z' result,DefaultEncodingState after r ds z' result config finalLog.input finalLog.output ∧
        (finalLog.result=Z_STREAM_END → ZlibF.Spec.Zlib.Valid finalLog.input finalLog.output) := by
  induction continuation with
  | refl => intro z d state validity; exact ⟨z,d,state,validity⟩
  | caller _ edit ih =>
      intro z d state validity
      obtain ⟨zm,dm,stateM,validityM⟩ := ih z d state validity
      obtain ⟨zg,_getG,stateG⟩ := stateM.rebuffer edit
      exact ⟨zg,dm,stateG,validityM⟩
  | step _ get _pointer _positive _protocol _remaining observed ih =>
      intro z d state validity
      obtain ⟨zm,dm,stateM,_validityM⟩ := ih z d state validity
      have same := Option.some.inj (stateM.protocol.good.live.hz.symm.trans get)
      subst zm
      exact stateM.generic_scalar_observed observed

/-- A continuation appends actual events to the unrestricted observed history. -/
theorem GenericDefaultDataTrace.append_finish {r : ZStreamRef} {accepted source : List UInt8}
    {h after : Heap} {log finalLog : DataLog}
    (continuation : DeflateCore.FinishContinuation r accepted source h log after finalLog) :
    GenericDefaultDataTrace r h log → GenericDefaultDataTrace r after finalLog := by
  induction continuation with
  | refl => intro history;exact history
  | caller _ edit ih => intro history;exact .caller (ih history) edit
  | step _ get _pointer _positive _protocol _remaining observed ih =>
      intro history;exact .step (ih history) get observed

/-- A continuation appends actual events to the no-snapshot basic history. -/
theorem GenericDefaultRequestTrace.append_finish {r : ZStreamRef} {accepted source : List UInt8}
    {h after : Heap} {log finalLog : DataLog}
    (continuation : DeflateCore.FinishContinuation r accepted source h log after finalLog) :
    GenericDefaultRequestTrace r h → GenericDefaultRequestTrace r after := by
  induction continuation with
  | refl => intro history;exact history
  | caller _ edit ih => intro history;exact .caller (ih history) edit
  | step _ _get _pointer _positive _protocol _remaining observed ih =>
      intro history
      obtain ⟨_z,_z',_get,_get',buffers,_header,_snapshot,_used,_bytes,run⟩ := observed
      exact .step (ih history) buffers run
end Zlib.Deflate.Engine.Proofs
