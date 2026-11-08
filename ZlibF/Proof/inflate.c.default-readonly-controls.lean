import ZlibF.Proof.«inflate.c.dictionary-query-default»
import ZlibF.Proof.«inflate.c.misc»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual synchronization-point query returns its source condition and
leaves the complete initialized decoder invariant intact. -/
theorem inflateSyncPoint_default_state {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (invariant : DefaultStateJ h r zs z s) :
    C.run (inflateSyncPoint (some r)) h =
      .ok ((if s.mode = STORED ∧ s.bits = 0 then 1 else 0), h) ∧
      DefaultStateJ h r zs z s :=
  ⟨inflateSyncPoint_spec invariant.good.live, invariant⟩

/-- The actual mark query computes the signed source value without changing
the initialized decoder or any heap object. -/
theorem inflateMark_default_state {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (invariant : DefaultStateJ h r zs z s) :
    ∃ value, C.run (inflateMark (some r)) h = .ok (value, h) ∧
      value.toInt = markValue s ∧ DefaultStateJ h r zs z s := by
  obtain ⟨value, actual, meaning⟩ := inflateMark_spec invariant.good.live
  exact ⟨value, actual, meaning, invariant⟩

/-- The actual table-extent query returns a bounded installed offset and
retains the full decoder invariant with unchanged storage. -/
theorem inflateCodesUsed_default_state {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (invariant : DefaultStateJ h r zs z s) :
    ∃ offset, offset ≤ 1444 ∧ s.next = .ref (.istate_codes zs) offset ∧
      C.run (inflateCodesUsed (some r)) h = .ok (UInt64.ofNat offset, h) ∧
      DefaultStateJ h r zs z s := by
  obtain ⟨offset, bounded, pointer, actual⟩ := inflateCodesUsed_spec invariant.good
  exact ⟨offset, bounded, pointer, actual, invariant⟩

#print axioms inflateSyncPoint_default_state
#print axioms inflateMark_default_state
#print axioms inflateCodesUsed_default_state
end Zlib.Inflate.Proofs
