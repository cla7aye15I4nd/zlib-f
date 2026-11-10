import ZlibF.Proof.«inflate.c.whole-epoch-wrapper-routes-v1»
import ZlibF.Proof.«inflate.c.whole-epoch-source-dispatch-lifts»
import ZlibF.Proof.«inflate.c.nonfinal-type-total-v1»

namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.WholeWrapper
set_option autoImplicit false

/-- The real installed-DICT source prefix establishes a routed TYPE entry
with last=0 and the identical first dispatcher execution. -/
theorem SourceCallCut.dictionary_ready_type_prefix
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (before : SourceCallCut c entryHeap h r zs entryZ z s l base raw)
    (mode : s.mode = DICT) (present : s.havedict ≠ 0) :
    ∃ _next : SourceCallCut c entryHeap (readyDictHeap h r zs z s) r zs entryZ
        {z with adler := 1} {s with check := 1, mode := TYPE} l base raw,
      runX (inflate_dispatch c) l h = runX (inflate_dispatch c) l (readyDictHeap h r zs z s) ∧
      ({s with check := 1, mode := TYPE} : InflateState).last = 0 := by
  obtain ⟨next, actual, last⟩ := before.core.dictionary_ready_type_prefix mode present
  exact ⟨⟨next, next.phase.routed_of_not_codes (by change TYPE ≠ CODELENS; decide)⟩, actual, last⟩

#print axioms SourceCallCut.dictionary_ready_type_prefix
/-- Full DICT dispatch includes the actual installed-dictionary TYPE
fallthrough. The resulting actual step/terminal transfers through that
literal source prefix, rather than inventing a return at TYPE. -/
theorem EpochCallCut4.dictionary_dispatch
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (before : EpochCallCut4 c entryHeap h r zs entryZ z s l base raw)
    (mode : s.mode = DICT) : Nonempty (DispatchResult4 before) := by
  by_cases missing : s.havedict = 0
  · exact before.dictionary_missing mode missing
  · obtain ⟨next, same, last⟩ := before.dictionary_ready_type_prefix mode missing
    obtain ⟨result⟩ := next.nonfinal_tag_dispatch (Or.inl rfl) last
    exact result.replace_initial same

/-- Actual TYPE/TYPEDO cannot create CODELENS. Routing of the same produced
result follows from source mode classification, independently of any
selected block kind or desired successor phase. -/
theorem DispatchResult4.wrapper_type_routed
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    {before : EpochCallCut4 c entryHeap h r zs entryZ z s l base raw}
    (result : DispatchResult4 before) (mode : s.mode = TYPE ∨ s.mode = TYPEDO) : result.Routed := by
  have noCodes : ∀ outcome regs after state,
      runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) →
      after.istates zs = some state → state.mode ≠ CODELENS := by
    intro outcome regs after state actual stored
    obtain ⟨exit0, regs0, after0, stream0, state0, used, _bound, source, current, modes, _rest⟩ :=
      inflate_dispatch_type_state_rank before.facts.env before.facts.origin.toDefaultStateJ
        before.facts.buffers mode before.facts.bits
    have same := xrun_state_eq source actual current.good.live.hs stored
    rw [← same]
    rcases modes with selected | selected | selected | selected | selected | selected | selected <;>
      rw [selected] <;> decide
  cases result with
  | progress after stream state regs actual next =>
    exact next.phase.routed_of_not_codes (noCodes _ _ _ state actual next.facts.env.hs)
  | stopped after stream state regs exit actual next =>
    exact next.phase.routed_of_not_codes (noCodes _ _ _ state actual next.facts.env.hs)

/-- Full routed DICT family. Missing dictionary returns directly; an
installed dictionary uses the real nonfinal TYPE dispatch in the same
trip, including all flush pauses and all four tag values. -/
theorem SourceCallCut.dictionary_dispatch
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (before : SourceCallCut c entryHeap h r zs entryZ z s l base raw)
    (mode : s.mode = DICT) : Nonempty (SourceDispatch before) := by
  by_cases missing : s.havedict = 0
  · exact before.dictionary_missing mode missing
  · obtain ⟨next, same, last⟩ := before.dictionary_ready_type_prefix mode missing
    obtain ⟨result⟩ := next.core.nonfinal_tag_dispatch (Or.inl rfl) last
    obtain ⟨produced, routed⟩ := result.replace_initial_routed (result.wrapper_type_routed (Or.inl rfl)) same
    exact ⟨⟨produced, routed⟩⟩

/-- The complete HEAD/DICTID/DICT source mode family constructs the actual
v4 dispatcher result without accepted-header, selected identifier, valid
input, desired run or guessed post-phase premises. -/
theorem EpochCallCut4.wrapper_dispatch
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (before : EpochCallCut4 c entryHeap h r zs entryZ z s l base raw)
    (mode : s.mode = HEAD ∨ s.mode = DICTID ∨ s.mode = DICT) : Nonempty (DispatchResult4 before) := by
  rcases mode with mode | mode | mode
  · exact before.head_dispatch mode
  · exact before.dictid_dispatch mode
  · exact before.dictionary_dispatch mode

/-- Routed complete wrapper family for the shared full-mode source fold. -/
theorem SourceCallCut.wrapper_dispatch
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (before : SourceCallCut c entryHeap h r zs entryZ z s l base raw)
    (mode : s.mode = HEAD ∨ s.mode = DICTID ∨ s.mode = DICT) : Nonempty (SourceDispatch before) := by
  rcases mode with mode | mode | mode
  · exact before.head_dispatch mode
  · exact before.dictid_dispatch mode
  · exact before.dictionary_dispatch mode

#print axioms EpochCallCut4.dictionary_dispatch
#print axioms DispatchResult4.wrapper_type_routed
#print axioms SourceCallCut.dictionary_dispatch
#print axioms EpochCallCut4.wrapper_dispatch
#print axioms SourceCallCut.wrapper_dispatch

end Zlib.Inflate.Proofs.WholeEpoch
