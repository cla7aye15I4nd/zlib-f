import ZlibF.Proof.«inflate.c.whole-epoch-public-record-frame-v4»
import ZlibF.Proof.«inflate.c.whole-epoch-source-routes»
namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- The constructed record transport retains the actual CODE alphabet,
so the ordinary/nonzero route is unchanged rather than chosen again. -/
theorem PublicRecordTransport.revised_routed
    {s target : InflateState} {log : DataLog} {wire : List Bool}
    (phase : SourcePhase4 log s wire)
    (keep : (s.mode = DICT ∨ s.mode = MEM) → target.check = s.check) :
    (revised phase keep).Routed ↔ phase.Routed := by
  cases phase
  case memory prior nonmem frame previous => cases frame; exact Iff.rfl
  case legacy previous =>
    cases previous
    case memory prior nonmem frame previous => cases frame; exact Iff.rfl
    all_goals exact Iff.rfl
  all_goals exact Iff.rfl

/-- The same source-constructed witness transports materialization,
saved-state admission and alphabet routing across exact bookkeeping. -/
theorem SourcePhase4.public_record_frame_routed
    {s after : InflateState} {log : DataLog} {wire : List Bool} {h heap : Heap}
    (phase : SourcePhase4 log s wire) (tables : phase.Materialized h)
    (frame : PublicRecordFrame s after)
    (keep : (s.mode = DICT ∨ s.mode = MEM) → after.check = s.check)
    (views : ∀ ref : CodeRef, (Space.get heap ref : Option (Array Code)) = Space.get h ref) :
    ∃ next : SourcePhase4 log after wire, next.Materialized heap ∧
      (next.Saved ↔ phase.Saved) ∧ (next.Routed ↔ phase.Routed) := by
  have result : ∃ next : SourcePhase4 log (publicRefresh s after) wire,
      next.Materialized heap ∧ (next.Saved ↔ phase.Saved) ∧ (next.Routed ↔ phase.Routed) :=
    ⟨PublicRecordTransport.revised phase keep,
      PublicRecordTransport.revised_materialized phase keep tables views,
      PublicRecordTransport.revised_saved phase keep,
      PublicRecordTransport.revised_routed phase keep⟩
  exact frame.symm ▸ result

#print axioms PublicRecordTransport.revised_routed
#print axioms SourcePhase4.public_record_frame_routed
end Zlib.Inflate.Proofs.WholeEpoch
