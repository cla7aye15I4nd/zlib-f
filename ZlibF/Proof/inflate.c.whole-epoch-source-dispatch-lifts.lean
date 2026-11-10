import ZlibF.Proof.«inflate.c.whole-epoch-source-routes»
import ZlibF.Proof.«inflate.c.whole-epoch-replace-initial-v4»
import ZlibF.Proof.«inflate.c.fast-view-dispatch-rank»
namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- An actual data dispatcher cannot create a dynamic-header phase. The
same-run source mode classifier justifies routing for every produced
normal or terminal revised data result, including unchecked MATCH. -/
theorem DispatchResult4.routed_of_data
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat}
    {entryZ z : ZStream} {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    {before : EpochCallCut4 c entryHeap h r zs entryZ z s l base raw}
    (result : DispatchResult4 before) (mode : DataTableMode s.mode) : result.Routed := by
  have notCodes : ∀ outcome regs after state,
      runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) →
      after.istates zs = some state → state.mode ≠ CODELENS := by
    intro outcome regs after state actual get
    obtain ⟨outcome0, regs0, after0, stream, state0, used, made, _bound, source, current, modes, _rest⟩ :=
      inflate_dispatch_data_view_state_rank before.facts.env before.facts.origin.toDefaultStateJ before.facts.buffers mode
    have pair := Except.ok.inj (actual.symm.trans source)
    cases pair
    have same : state0 = state := Option.some.inj (current.good.live.hs.symm.trans get)
    rw [same] at modes
    rcases modes with data | selected | selected
    · rcases data with selected | selected | selected | selected | selected | selected | selected <;>
        rw [selected] <;> decide
    · rw [selected]; decide
    · rw [selected]; decide
  cases result with
  | progress after stream state regs actual next =>
    have excluded : state.mode ≠ CODELENS := notCodes _ _ _ state actual next.facts.env.hs
    exact next.phase.routed_of_not_codes excluded
  | stopped after stream state regs exit actual next =>
    have excluded : state.mode ≠ CODELENS := notCodes _ _ _ state actual next.facts.env.hs
    exact next.phase.routed_of_not_codes excluded

/-- A proved inline-prefix equality changes no produced next source
witness. Routing therefore transfers with the exact same actual result. -/
theorem DispatchResult4.replace_initial_routed
    {c : Ctx} {entryHeap h nextHeap : Heap} {r : ZStreamRef} {zs : Nat}
    {entryZ z nextZ : ZStream} {s nextState : InflateState} {l nextRegs : IL}
    {base : DataLog} {raw : List UInt8}
    {before : EpochCallCut4 c entryHeap h r zs entryZ z s l base raw}
    {next : EpochCallCut4 c entryHeap nextHeap r zs entryZ nextZ nextState nextRegs base raw}
    (result : DispatchResult4 next) (routed : result.Routed)
    (same : runX (inflate_dispatch c) l h = runX (inflate_dispatch c) nextRegs nextHeap) :
    ∃ produced : DispatchResult4 before, produced.Routed := by
  cases result with
  | progress after stream state regs actual final =>
    exact ⟨.progress after stream state regs (same.trans actual) final, routed⟩
  | stopped after stream state regs exit actual final =>
    exact ⟨.stopped after stream state regs exit (same.trans actual) final, routed⟩

#print axioms DispatchResult4.routed_of_data
#print axioms DispatchResult4.replace_initial_routed
end Zlib.Inflate.Proofs.WholeEpoch
