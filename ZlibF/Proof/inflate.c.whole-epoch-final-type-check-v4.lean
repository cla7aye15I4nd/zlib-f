import ZlibF.Proof.«inflate.c.whole-epoch-final-type-check»
import ZlibF.Proof.«inflate.c.whole-epoch-terminal-dispatch-v4»

namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- New raw STORED, unchecked MATCH and MEM snapshots cannot occur at a
TYPE/TYPEDO control cut. The original source witness is retained exactly. -/
theorem SourcePhase4.legacy_of_type
    {log : DataLog} {s : InflateState} {wire : List Bool}
    (phase : SourcePhase4 log s wire) (mode : s.mode = TYPE ∨ s.mode = TYPEDO) :
    ∃ previous : SourcePhase log s wire, phase = .legacy previous := by
  cases phase with
  | legacy previous => exact ⟨previous, rfl⟩
  | _ => simp_all [STORED, MATCH, MEM, TYPE, TYPEDO]

/-- Lift the checked real final alignment into the additive interface.
Actual source equality proves the new state is CHECK, so the CODE parser
inverse is inactive; no legacy phase is fabricated for new cases. -/
theorem EpochCallCut4.final_type_to_check
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (before : EpochCallCut4 c entryHeap h r zs entryZ z s l base raw)
    (mode : s.mode = TYPE ∨ s.mode = TYPEDO) (last : s.last ≠ 0)
    (flush : s.mode = TYPE → c.flush ≠ Z_BLOCK ∧ c.flush ≠ Z_TREES) :
    Nonempty (DispatchResult4 before) := by
  obtain ⟨previous, phaseEq⟩ := before.phase.legacy_of_type mode
  have tables : previous.Materialized h := by
    have materialized := before.materialized
    rw [phaseEq] at materialized
    exact materialized.1
  let old := before.facts.with_legacy previous tables
  have expected : runX (inflate_dispatch c) l h =
      .ok ((.ok (), bytebits l), setI h zs {s with mode := CHECK}) := by
    rw [inflate_dispatch_block_type before.facts.env l mode]
    rcases mode with selected | selected
    · rw [ite_eq_left selected, inflate_TYPE_go c l h (flush selected)]
      exact inflate_TYPEDO_last before.facts.env l last
    · have different : s.mode ≠ TYPE := by rw [selected]; decide
      rw [ite_eq_right different]
      exact inflate_TYPEDO_last before.facts.env l last
  obtain ⟨result⟩ := old.final_type_to_check mode last flush
  cases result with
  | progress after stream state regs actual next =>
    have pair := Except.ok.inj (expected.symm.trans actual)
    cases pair
    have stateEq : state = {s with mode := CHECK} := by
      apply Option.some.inj
      rw [← next.framed.cut.env.hs, setI_istates_same]
    have noCodes : (leaveState state (bytebits l)).mode ≠ CODELENS := by
      rw [stateEq]
      change CHECK ≠ CODELENS
      decide
    have reversible := next.framed.cut.phase.reversible_of_not_codes noCodes
    exact ⟨.progress _ stream state (bytebits l) actual (next.upgrade reversible)⟩
  | stopped after stream state regs exit actual _ =>
    rw [expected] at actual
    cases actual

/-- Complete actual final-block TYPE/TYPEDO routing for every flush in
the additive source invariant. This remains one finite dispatcher family. -/
theorem EpochCallCut4.final_tag_dispatch
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (before : EpochCallCut4 c entryHeap h r zs entryZ z s l base raw)
    (mode : s.mode = TYPE ∨ s.mode = TYPEDO) (last : s.last ≠ 0) :
    Nonempty (DispatchResult4 before) := by
  by_cases pause : s.mode = TYPE ∧ (c.flush = Z_BLOCK ∨ c.flush = Z_TREES)
  · exact before.type_flush_pause pause.1 pause.2
  · apply before.final_type_to_check mode last
    intro selected
    constructor
    · intro block
      exact pause ⟨selected, Or.inl block⟩
    · intro trees
      exact pause ⟨selected, Or.inr trees⟩

#print axioms SourcePhase4.legacy_of_type
#print axioms EpochCallCut4.final_type_to_check
#print axioms EpochCallCut4.final_tag_dispatch
end Zlib.Inflate.Proofs.WholeEpoch
