import ZlibF.Proof.«inflate.c.whole-epoch-source-routes»
import ZlibF.Proof.«inflate.c.whole-epoch-check-dispatch-v4»
import ZlibF.Proof.«inflate.c.whole-epoch-final-type-check-v4»

namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- Actual CHECK results retain the existing exact post-mode observer. -/
theorem EpochCallCut4.check_observed_not_codelens
    {c : Ctx} {entryHeap h after : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s state : InflateState} {l regs : IL} {base : DataLog} {raw : List UInt8}
    {outcome : Except Ex Unit}
    (before : EpochCallCut4 c entryHeap h r zs entryZ z s l base raw) (mode : s.mode = CHECK)
    (actual : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after))
    (stored : after.istates zs = some state) : state.mode ≠ CODELENS := by
  obtain ⟨previous, phaseEq⟩ := before.phase.legacy_of_check mode
  have attached := before.materialized
  rw [phaseEq] at attached
  let old := before.facts.with_legacy previous attached.1
  exact old.check_observed_not_codelens mode actual stored

/-- Terminal dispatcher execution changes no heap state, irrespective of
which ret-only register convention that terminal uses. -/
theorem EpochCallCut4.terminal_observed_not_codelens
    {c : Ctx} {entryHeap h after : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s state : InflateState} {l regs : IL} {base : DataLog} {raw : List UInt8}
    {outcome : Except Ex Unit}
    (before : EpochCallCut4 c entryHeap h r zs entryZ z s l base raw)
    (mode : s.mode = DONE ∨ s.mode = BAD ∨ s.mode = MEM)
    (actual : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after))
    (stored : after.istates zs = some state) : state.mode ≠ CODELENS := by
  have terminal : TerminalMode s.mode := by
    rcases mode with done | bad | memory
    · exact Or.inl done
    · exact Or.inr (Or.inl bad)
    · exact Or.inr (Or.inr (Or.inl memory))
  have expected := inflate_dispatch_terminal_run before.facts.env l terminal
  have same := xrun_state_eq expected actual before.facts.env.hs stored
  rw [← same]
  rcases mode with selected | selected | selected <;> rw [selected] <;> decide

/-- The real final-block selector either pauses unchanged at TYPE or
normalizes padding into CHECK; neither outcome can construct CODELENS. -/
theorem EpochCallCut4.final_tag_observed_not_codelens
    {c : Ctx} {entryHeap h after : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s state : InflateState} {l regs : IL} {base : DataLog} {raw : List UInt8}
    {outcome : Except Ex Unit}
    (before : EpochCallCut4 c entryHeap h r zs entryZ z s l base raw)
    (mode : s.mode = TYPE ∨ s.mode = TYPEDO) (last : s.last ≠ 0)
    (actual : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after))
    (stored : after.istates zs = some state) : state.mode ≠ CODELENS := by
  by_cases pause : s.mode = TYPE ∧ (c.flush = Z_BLOCK ∨ c.flush = Z_TREES)
  · have expected : runX (inflate_dispatch c) l h = .ok ((.error Ex.leave, l), h) := by
      rw [inflate_dispatch_block_type before.facts.env l (Or.inl pause.1), ite_eq_left pause.1]
      exact inflate_TYPE_leave c l h pause.2
    have same := xrun_state_eq expected actual before.facts.env.hs stored
    rw [← same, pause.1]
    decide
  · have flush : s.mode = TYPE → c.flush ≠ Z_BLOCK ∧ c.flush ≠ Z_TREES := by
      intro selected
      exact ⟨fun block => pause ⟨selected, Or.inl block⟩,
        fun trees => pause ⟨selected, Or.inr trees⟩⟩
    have expected : runX (inflate_dispatch c) l h =
        .ok ((.ok (), bytebits l), setI h zs {s with mode := CHECK}) := by
      rw [inflate_dispatch_block_type before.facts.env l mode]
      rcases mode with selected | selected
      · rw [ite_eq_left selected, inflate_TYPE_go c l h (flush selected)]
        exact inflate_TYPEDO_last before.facts.env l last
      · rw [ite_eq_right (by rw [selected]; decide : s.mode ≠ TYPE)]
        exact inflate_TYPEDO_last before.facts.env l last
    have same := xrun_state_eq expected actual (by rw [setI_istates_same]) stored
    rw [← same]
    change CHECK ≠ CODELENS
    decide

/-- CHECK supplies its own routed successor from actual post-modes. -/
theorem SourceCallCut.check_dispatch
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (before : SourceCallCut c entryHeap h r zs entryZ z s l base raw)
    (mode : s.mode = CHECK) : Nonempty (SourceDispatch before) := by
  obtain ⟨result⟩ := before.core.check_dispatch mode
  refine ⟨⟨result, ?_⟩⟩
  cases result with
  | progress _ _ _ _ actual next =>
    have observed := before.core.check_observed_not_codelens mode actual next.facts.env.hs
    exact next.phase.routed_of_not_codes observed
  | stopped _ _ _ _ _ actual next =>
    have observed := before.core.check_observed_not_codelens mode actual next.facts.env.hs
    exact next.phase.routed_of_not_codes observed

/-- DONE/BAD/MEM retain routing under their actual distinct exits. -/
theorem SourceCallCut.terminal_dispatch
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (before : SourceCallCut c entryHeap h r zs entryZ z s l base raw)
    (mode : s.mode = DONE ∨ s.mode = BAD ∨ s.mode = MEM) :
    Nonempty (SourceDispatch before) := by
  obtain ⟨result⟩ := before.core.terminal_dispatch mode
  refine ⟨⟨result, ?_⟩⟩
  cases result with
  | progress _ _ _ _ actual next =>
    have observed := before.core.terminal_observed_not_codelens mode actual next.facts.env.hs
    exact next.phase.routed_of_not_codes observed
  | stopped _ _ _ _ _ actual next =>
    have observed := before.core.terminal_observed_not_codelens mode actual next.facts.env.hs
    exact next.phase.routed_of_not_codes observed

/-- Every final TYPE/TYPEDO flush branch produces a routed real result. -/
theorem SourceCallCut.final_tag_dispatch
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (before : SourceCallCut c entryHeap h r zs entryZ z s l base raw)
    (mode : s.mode = TYPE ∨ s.mode = TYPEDO) (last : s.last ≠ 0) :
    Nonempty (SourceDispatch before) := by
  obtain ⟨result⟩ := before.core.final_tag_dispatch mode last
  refine ⟨⟨result, ?_⟩⟩
  cases result with
  | progress _ _ _ _ actual next =>
    have observed := before.core.final_tag_observed_not_codelens mode last actual next.facts.env.hs
    exact next.phase.routed_of_not_codes observed
  | stopped _ _ _ _ _ actual next =>
    have observed := before.core.final_tag_observed_not_codelens mode last actual next.facts.env.hs
    exact next.phase.routed_of_not_codes observed

#print axioms EpochCallCut4.check_observed_not_codelens
#print axioms EpochCallCut4.terminal_observed_not_codelens
#print axioms EpochCallCut4.final_tag_observed_not_codelens
#print axioms SourceCallCut.check_dispatch
#print axioms SourceCallCut.terminal_dispatch
#print axioms SourceCallCut.final_tag_dispatch
end Zlib.Inflate.Proofs.WholeEpoch
