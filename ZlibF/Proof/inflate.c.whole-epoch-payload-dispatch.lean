import ZlibF.Proof.«inflate.c.whole-epoch-source-dispatch-lifts»
import ZlibF.Proof.«inflate.c.whole-epoch-fast-dispatch-v4»
import ZlibF.Proof.«inflate.c.whole-slow-payload-dispatch-v4»
import ZlibF.Proof.«inflate.c.whole-epoch-len-start-v4»
namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- Complete actual payload dispatch: the real fast guard is selected
internally; all seven modes, parsed unchecked MATCH and partly emitted
MATCH produce the same source envelope. LEN_ is an inline store, never
an invented extra outer-loop iteration. -/
theorem SourceCallCut.payload_dispatch
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat}
    {entryZ z : ZStream} {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (before : SourceCallCut c entryHeap h r zs entryZ z s l base raw)
    (mode : DataTableMode s.mode) : Nonempty (SourceDispatch before) := by
  by_cases branch : (s.mode = LEN_ ∨ s.mode = LEN) ∧
      (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true
  · rcases branch.1 with start | length
    · obtain ⟨next, same⟩ := before.core.normalize_len_start start
      obtain ⟨boundary, _selectedMode, last, selected⟩ := next.phase.ready_of_length (Or.inr rfl)
      obtain ⟨result⟩ := next.fast_dispatch boundary last rfl selected branch.2
      have routed := result.routed_of_data (Or.inr (Or.inl rfl))
      obtain ⟨produced, routed⟩ := result.replace_initial_routed (before := before.core) routed same
      exact ⟨⟨produced, routed⟩⟩
    · obtain ⟨boundary, _selectedMode, last, selected⟩ := before.core.phase.ready_of_length (Or.inr length)
      obtain ⟨result⟩ := before.core.fast_dispatch boundary last length selected branch.2
      exact ⟨⟨result, result.routed_of_data mode⟩⟩
  · have slow : s.mode = LEN_ ∨ s.mode = LEN →
        ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true := by
      intro selected fast
      exact branch ⟨selected, fast⟩
    obtain ⟨result⟩ := before.core.slow_payload_dispatch mode slow
    exact ⟨⟨result, result.routed_of_data mode⟩⟩

#print axioms SourceCallCut.payload_dispatch
end Zlib.Inflate.Proofs.WholeEpoch
