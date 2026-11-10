import ZlibF.Proof.«inflate.c.whole-stored-header-dispatch»
import ZlibF.Proof.«inflate.c.whole-epoch-dispatch-interface-v4»

namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- A real stored dispatcher cannot enter CODELENS. This is an actual
callee theorem applied to the observed source trip, not a phase oracle. -/
theorem stored_exit_mode_of_run
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s state : InflateState}
    {l regs : IL} {bs : List UInt8} {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (origin : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = STORED ∨ s.mode = COPY_ ∨ s.mode = COPY)
    (actual : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after))
    (get : after.istates zs = some state) : StoredExitMode state.mode := by
  obtain ⟨value, current, heap, stream, next, run, invariant, modes⟩ :=
    inflate_dispatch_stored_state E origin.toDefaultStateJ buffers mode
  have same := Except.ok.inj (actual.symm.trans run)
  cases same
  have states : next = state := Option.some.inj (invariant.good.live.hs.symm.trans get)
  subst next
  exact modes

/-- Lift already checked stored results through the additive v4 interface.
The inverse parser clause is genuinely inactive in every actual exit mode. -/
def stored_result_upgrade
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (before : EpochCallCut4 c entryHeap h r zs entryZ z s l base raw)
    (old : EpochCallCut c entryHeap h r zs entryZ z s l base raw)
    (mode : s.mode = STORED ∨ s.mode = COPY_ ∨ s.mode = COPY)
    (result : DispatchResult old) : DispatchResult4 before := by
  cases result with
  | progress after stream state regs actual next =>
    have modes := stored_exit_mode_of_run old.framed.cut.env old.framed.cut.origin old.framed.cut.buffers
      mode actual next.framed.cut.origin.good.live.hs
    have notCodes : (leaveState state regs).mode ≠ CODELENS := by
      change state.mode ≠ CODELENS
      rcases modes with m | m | m | m | m <;> rw [m] <;> decide
    exact .progress after stream state regs actual (next.upgrade (next.framed.cut.phase.reversible_of_not_codes notCodes))
  | stopped after stream state regs exit actual next =>
    have modes := stored_exit_mode_of_run old.framed.cut.env old.framed.cut.origin old.framed.cut.buffers
      mode actual next.terminal.origin.good.live.hs
    have notCodes : (leaveState state regs).mode ≠ CODELENS := by
      change state.mode ≠ CODELENS
      rcases modes with m | m | m | m | m <;> rw [m] <;> decide
    exact .stopped after stream state regs exit actual (next.upgrade (next.terminal.phase.reversible_of_not_codes notCodes))

/-- v4 COPY/COPY_ uses its actual legacy stored source, never rawStored
or unchecked MATCH, and invokes the closed whole-dispatch producer. -/
theorem EpochCallCut4.copy_dispatch
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (before : EpochCallCut4 c entryHeap h r zs entryZ z s l base raw)
    (mode : s.mode = COPY_ ∨ s.mode = COPY) : Nonempty (DispatchResult4 before) := by
  cases selected : before.phase
  case legacy phase =>
    have materialized := before.materialized
    rw [selected] at materialized
    let old := before.facts.with_legacy phase materialized.1
    obtain ⟨result⟩ := old.copy_dispatch mode
    exact ⟨stored_result_upgrade before old (Or.inr mode) result⟩
  all_goals
    clear selected
    exfalso
    rcases mode with mode | mode <;>
      simp_all [leaveState, STORED, COPY_, COPY, MATCH, MEM]

/-- An aligned legacy stored phase lifts through the same checked full
STORED producer. The distinct rawStored case is handled by actual BYTEBITS. -/
theorem EpochCallCut4.legacy_stored_dispatch
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (before : EpochCallCut4 c entryHeap h r zs entryZ z s l base raw)
    (phase : SourcePhase (sourceLog (callLog base raw before.facts.used before.facts.emitted))
      (leaveState s l) before.facts.word)
    (selected : before.phase = .legacy phase) (mode : s.mode = STORED) : Nonempty (DispatchResult4 before) := by
  have materialized := before.materialized
  rw [selected] at materialized
  let old := before.facts.with_legacy phase materialized.1
  obtain ⟨result⟩ := old.stored_dispatch mode
  exact ⟨stored_result_upgrade before old (Or.inl mode) result⟩

#print axioms stored_exit_mode_of_run
#print axioms stored_result_upgrade
#print axioms EpochCallCut4.copy_dispatch
#print axioms EpochCallCut4.legacy_stored_dispatch
end Zlib.Inflate.Proofs.WholeEpoch
