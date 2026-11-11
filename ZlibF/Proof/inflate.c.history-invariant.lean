import ZlibF.Proof.«inflate.c.invariant»
import ZlibF.Proof.«inflate.c.default-history-calls»

/-!
# inflate.c: caller edits and stream operations preserve the general invariant

Each lemma covers one actual return of a public operation from any state
with `InflateInv`, in every configuration.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- A caller rebuffer keeps the decoder state and its owned memory. -/
theorem rebuffer_invariant {h after : Heap} {r : ZStreamRef} {i : Nat} {z : ZStream}
    {s : InflateState} (current : InflateInv h r i z s) (edit : Rebuffer h after r) :
    ∃ z', InflateInv after r i z' s := by
  obtain ⟨stream, fields, good⟩ := rebuffer_inflate_good current.good edit
  have tables := (rebuffer_dataTableInvariant current.good edit current.tables).2
  refine ⟨stream, ⟨good, ?_, tables, current.pending, current.lengths, current.headerLengths,
    current.held, current.config, current.modes, current.phase, current.origin, edit.2.2.1⟩⟩
  rw [fields]
  exact current.alloc

/-- Preservation by one actual return of a stream operation. -/
def InflatePreserves (r : ZStreamRef) (call : Call) : Prop :=
  ∀ (h after : Heap) (i : Nat) (z : ZStream) (s : InflateState) (value : call.Result),
    InflateInv h r i z s → StreamArguments h r call →
    call.execute default h = .ok ((value, default), after) →
    ∃ z' s', InflateInv after r i z' s'

theorem inflateSyncPoint_preserves (r : ZStreamRef) :
    InflatePreserves r (.inflateSyncPoint (some r)) := by
  intro h after i z s value current _ actual
  have run := inflateSyncPoint_spec current.good.live
  have same := Except.ok.inj ((heapCall_of_actual_run run default).symm.trans actual)
  cases same
  exact ⟨z, s, current⟩

theorem inflateMark_preserves (r : ZStreamRef) : InflatePreserves r (.inflateMark (some r)) := by
  intro h after i z s value current _ actual
  obtain ⟨mark, run, _⟩ := inflateMark_spec current.good.live
  have same := Except.ok.inj ((heapCall_of_actual_run run default).symm.trans actual)
  cases same
  exact ⟨z, s, current⟩

theorem inflateCodesUsed_preserves (r : ZStreamRef) :
    InflatePreserves r (.inflateCodesUsed (some r)) := by
  intro h after i z s value current _ actual
  obtain ⟨offset, _, _, run⟩ := inflateCodesUsed_spec current.good
  have same := Except.ok.inj ((heapCall_of_actual_run run default).symm.trans actual)
  cases same
  exact ⟨z, s, current⟩

/-- The default build refuses undermining and keeps `sane = 1`. -/
theorem inflateUndermine_preserves (r : ZStreamRef) (subvert : Int32) :
    InflatePreserves r (.inflateUndermine (some r) subvert) := by
  intro h after i z s value current _ actual
  obtain ⟨written, run, heap, _⟩ := inflateUndermine_safe current.good subvert
  have state : { s with sane := 1 } = s := by rw [← current.pending.sane]
  have unchanged : written = h := by rw [heap, state, tcSetI_same current.good.live.hs]
  subst unchanged
  have same := Except.ok.inj ((heapCall_of_actual_run run default).symm.trans actual)
  cases same
  exact ⟨z, s, current⟩

#print axioms rebuffer_invariant
#print axioms inflateSyncPoint_preserves
#print axioms inflateMark_preserves
#print axioms inflateCodesUsed_preserves
#print axioms inflateUndermine_preserves

end Zlib.Inflate.Proofs
