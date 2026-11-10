import ZlibF.Proof.«inflate.c.whole-epoch-dispatch-interface-v4»
import ZlibF.Proof.«inflate.c.whole-epoch-check-observed-mode-v1»

namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- Actual CHECK cannot be a raw STORED, unchecked MATCH or MEM source
stage. Recover its existing completed-block trailer without guessing it. -/
theorem SourcePhase4.legacy_of_check
    {log : DataLog} {s : InflateState} {wire : List Bool}
    (phase : SourcePhase4 log s wire) (mode : s.mode = CHECK) :
    ∃ previous : SourcePhase log s wire, phase = .legacy previous := by
  cases phase with
  | legacy previous => exact ⟨previous, rfl⟩
  | _ => simp_all [STORED, MATCH, MEM, CHECK]

/-- Exhaustive actual CHECK preservation in the additive invariant.
Waiting, accepted END and rejected BAD retain exact original executions;
their observed modes justify the inactive CODE parser-inverse transport. -/
theorem EpochCallCut4.check_dispatch
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (before : EpochCallCut4 c entryHeap h r zs entryZ z s l base raw)
    (mode : s.mode = CHECK) : Nonempty (DispatchResult4 before) := by
  obtain ⟨previous, phaseEq⟩ := before.phase.legacy_of_check mode
  have tables : previous.Materialized h := by
    have materialized := before.materialized
    rw [phaseEq] at materialized
    exact materialized.1
  let old := before.facts.with_legacy previous tables
  obtain ⟨result⟩ := old.check_dispatch mode
  cases result with
  | progress after stream state regs actual next =>
    have noCodes := old.check_observed_not_codelens mode actual next.framed.cut.env.hs
    have reversible := next.framed.cut.phase.reversible_of_not_codes noCodes
    exact ⟨.progress after stream state regs actual (next.upgrade reversible)⟩
  | stopped after stream state regs exit actual next =>
    have noCodes := old.check_observed_not_codelens mode actual next.terminal.env.hs
    have reversible := next.terminal.phase.reversible_of_not_codes noCodes
    exact ⟨.stopped after stream state regs exit actual (next.upgrade reversible)⟩

#print axioms SourcePhase4.legacy_of_check
#print axioms EpochCallCut4.check_dispatch
end Zlib.Inflate.Proofs.WholeEpoch
