import ZlibF.Proof.«inflate.c.whole-epoch-source-spine-v4»
import ZlibF.Proof.«inflate.c.whole-epoch-final-acceptance»

namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- The two added entry phases cannot pretend to be DONE; only the
unchanged finished source certificate supplies successful meaning. -/
theorem SourcePhase4.finished_of_done {log : DataLog} {s : InflateState} {wire : List Bool}
    (phase : SourcePhase4 log s wire) (done : s.mode = DONE) : Nonempty (Finished log) := by
  cases phase with
  | legacy previous => exact previous.finished_of_done done
  | rawStored _ mode _ _ _ _ =>
    exact False.elim ((by decide : STORED ≠ DONE) (mode.symm.trans done))
  | uncheckedMatch mode _ =>
    exact False.elim ((by decide : MATCH ≠ DONE) (mode.symm.trans done))
  | memory _ _ _ frame =>
    have wrong : MEM = DONE := (congrArg InflateState.mode frame).symm.trans done
    exact False.elim ((by decide : MEM ≠ DONE) wrong)

/-- The additive candidate's actual DONE case has the same exact
configured-window output relation as the already checked final projection. -/
theorem AtPublic4.default_accepted_of_done
    {h : Heap} {r : ZStreamRef} {log : DataLog} (before : AtPublic4 h r log)
    (done : before.point.state.mode = DONE) :
    Api.Layer.InflateAccepted .zlib 15 log.dictionary log.input log.output := by
  obtain ⟨finished⟩ := before.phase.finished_of_done done
  exact finished.default_accepted

/-- Actual protocol END still determines DONE. Candidate preservation for
arbitrary calls remains separate, rather than becoming a caller premise. -/
theorem AtPublic4.default_accepted_of_protocol_end
    {h : Heap} {r : ZStreamRef} {log : DataLog} {pending : Bool}
    (before : AtPublic4 h r log)
    (trace : InflateProtocolTrace 15 r h log pending)
    (scope : ProtocolWindow.PlatformScope trace) (ended : log.result = Z_STREAM_END) :
    Api.Layer.InflateAccepted .zlib 15 log.dictionary log.input log.output := by
  apply before.default_accepted_of_done
  exact ProtocolWindow.protocol_result_end_mode trace scope
    before.point.zs before.point.z before.point.state before.point.good ended

#print axioms SourcePhase4.finished_of_done
#print axioms AtPublic4.default_accepted_of_done
#print axioms AtPublic4.default_accepted_of_protocol_end
end Zlib.Inflate.Proofs.WholeEpoch
