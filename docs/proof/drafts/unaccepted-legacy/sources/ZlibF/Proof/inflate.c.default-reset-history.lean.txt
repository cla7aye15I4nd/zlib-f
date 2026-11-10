import ZlibF.Proof.«inflate.c.reset2-default-state»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The translated reset-keep call extends an actual reachable history and
retains the established default decoder relation. -/
theorem inflateResetKeep_default_history {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (reachable : StreamReachable .inflate h r)
    (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z) :
    ∃ after stream state, C.run (inflateResetKeep (some r)) h = .ok (Z_OK, after) ∧
      DefaultStateJ after r zs stream state ∧ DefAlloc stream ∧
      StreamReachable .inflate after r := by
  obtain ⟨after, stream, state, run, current, finalAllocator⟩ :=
    inflateResetKeep_default_state invariant allocator
  have executed : (Call.inflateResetKeep (some r)).execute default h =
      .ok ((Z_OK, default), after) := by
    change inflateResetKeep (some r) h = _ at run
    simp only [Call.execute, heapCall, run]
  have operation : StreamOperation .inflate r (.inflateResetKeep (some r)) := by
    simp [StreamOperation]
  have arguments : StreamArguments h r (.inflateResetKeep (some r)) := trivial
  exact ⟨after, stream, state, run, current, finalAllocator,
    StreamReachable.step reachable operation arguments executed⟩

/-- The translated ordinary reset likewise extends reachable history and
restores the default decoder relation. -/
theorem inflateReset_default_history {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (reachable : StreamReachable .inflate h r)
    (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z) :
    ∃ after stream state, C.run (inflateReset (some r)) h = .ok (Z_OK, after) ∧
      DefaultStateJ after r zs stream state ∧ DefAlloc stream ∧
      StreamReachable .inflate after r := by
  obtain ⟨after, stream, state, run, current, finalAllocator⟩ :=
    inflateReset_default_state invariant allocator
  have executed : (Call.inflateReset (some r)).execute default h =
      .ok ((Z_OK, default), after) := by
    change inflateReset (some r) h = _ at run
    simp only [Call.execute, heapCall, run]
  have operation : StreamOperation .inflate r (.inflateReset (some r)) := by
    simp [StreamOperation]
  have arguments : StreamArguments h r (.inflateReset (some r)) := trivial
  exact ⟨after, stream, state, run, current, finalAllocator,
    StreamReachable.step reachable operation arguments executed⟩

end Zlib.Inflate.Proofs
