import ZlibF.Proof.«inflate.c.whole-stored-v4-dispatch»
import ZlibF.Proof.«inflate.c.whole-epoch-source-routes»

namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- Every destination of the actual stored dispatcher lies outside
CODELENS, including its real waits, rejection and inline copy paths. -/
theorem DispatchResult4.stored_routed
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat}
    {entryZ z : ZStream} {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (before : EpochCallCut4 c entryHeap h r zs entryZ z s l base raw)
    (mode : s.mode = STORED ∨ s.mode = COPY_ ∨ s.mode = COPY)
    (result : DispatchResult4 before) : result.Routed := by
  cases result with
  | progress after stream state regs actual next =>
    have modes := stored_exit_mode_of_run before.facts.env before.facts.origin before.facts.buffers
      mode actual next.facts.origin.good.live.hs
    apply next.phase.routed_of_not_codes
    change state.mode ≠ CODELENS
    rcases modes with m | m | m | m | m <;> rw [m] <;> decide
  | stopped after stream state regs exit actual next =>
    have modes := stored_exit_mode_of_run before.facts.env before.facts.origin before.facts.buffers
      mode actual next.facts.origin.good.live.hs
    apply next.phase.routed_of_not_codes
    change state.mode ≠ CODELENS
    rcases modes with m | m | m | m | m <;> rw [m] <;> decide

/-- The closed STORED producer also constructs routing from its actual
source execution. No returned mode or routing fact is a premise. -/
theorem EpochCallCut4.stored_dispatch_routed
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat}
    {entryZ z : ZStream} {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (before : EpochCallCut4 c entryHeap h r zs entryZ z s l base raw)
    (mode : s.mode = STORED) : ∃ result : DispatchResult4 before, result.Routed := by
  obtain ⟨result⟩ := before.stored_dispatch mode
  exact ⟨result, result.stored_routed before (Or.inl mode)⟩

/-- COPY and COPY_ produce routing together with the full physical and
semantic result already proved for their literal source execution. -/
theorem EpochCallCut4.copy_dispatch_routed
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat}
    {entryZ z : ZStream} {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (before : EpochCallCut4 c entryHeap h r zs entryZ z s l base raw)
    (mode : s.mode = COPY_ ∨ s.mode = COPY) : ∃ result : DispatchResult4 before, result.Routed := by
  obtain ⟨result⟩ := before.copy_dispatch mode
  exact ⟨result, result.stored_routed before (Or.inr mode)⟩

/-- Source envelope adapter for the actual STORED branch. -/
theorem SourceCallCut.stored_dispatch
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat}
    {entryZ z : ZStream} {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (before : SourceCallCut c entryHeap h r zs entryZ z s l base raw)
    (mode : s.mode = STORED) : Nonempty (SourceDispatch before) := by
  obtain ⟨result, routed⟩ := before.core.stored_dispatch_routed mode
  exact ⟨⟨result, routed⟩⟩

/-- Source envelope adapter for the actual COPY_ or COPY branch. -/
theorem SourceCallCut.copy_dispatch
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat}
    {entryZ z : ZStream} {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (before : SourceCallCut c entryHeap h r zs entryZ z s l base raw)
    (mode : s.mode = COPY_ ∨ s.mode = COPY) : Nonempty (SourceDispatch before) := by
  obtain ⟨result, routed⟩ := before.core.copy_dispatch_routed mode
  exact ⟨⟨result, routed⟩⟩

#print axioms DispatchResult4.stored_routed
#print axioms EpochCallCut4.stored_dispatch_routed
#print axioms EpochCallCut4.copy_dispatch_routed
#print axioms SourceCallCut.stored_dispatch
#print axioms SourceCallCut.copy_dispatch
end Zlib.Inflate.Proofs.WholeEpoch
