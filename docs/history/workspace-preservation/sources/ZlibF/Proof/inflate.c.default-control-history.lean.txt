import ZlibF.Proof.«inflate.c.default-state-controls»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Actual priming extends a reachable default stream for every signed
bit count and value, including refusal and clearing. -/
theorem inflatePrime_default_history {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (reachable : StreamReachable .inflate h r)
    (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (bits value : Int32) :
    ∃ rc after state, C.run (inflatePrime (some r) bits value) h = .ok (rc, after) ∧
      DefaultStateJ after r zs z state ∧ DefAlloc z ∧
      StreamReachable .inflate after r := by
  obtain ⟨rc, after, state, run, current, finalAllocator, _⟩ :=
    inflatePrime_default_state invariant allocator bits value
  have executed : (Call.inflatePrime (some r) bits value).execute default h =
      .ok ((rc, default), after) := by
    change inflatePrime (some r) bits value h = _ at run
    simp only [Call.execute, heapCall, run]
  have operation : StreamOperation .inflate r (.inflatePrime (some r) bits value) := by
    simp [StreamOperation]
  have arguments : StreamArguments h r (.inflatePrime (some r) bits value) := trivial
  exact ⟨rc, after, state, run, current, finalAllocator,
    StreamReachable.step reachable operation arguments executed⟩

/-- The translated validation toggle retains J and actual reachability. -/
theorem inflateValidate_default_history {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (reachable : StreamReachable .inflate h r)
    (invariant : DefaultStateJ h r zs z s) (check : Int32) :
    ∃ after state, C.run (inflateValidate (some r) check) h = .ok (Z_OK, after) ∧
      DefaultStateJ after r zs z state ∧ StreamReachable .inflate after r := by
  obtain ⟨after, state, run, _, _, current⟩ := inflateValidate_default_state invariant check
  have executed : (Call.inflateValidate (some r) check).execute default h =
      .ok ((Z_OK, default), after) := by
    change inflateValidate (some r) check h = _ at run
    simp only [Call.execute, heapCall, run]
  have operation : StreamOperation .inflate r (.inflateValidate (some r) check) := by
    simp [StreamOperation]
  have arguments : StreamArguments h r (.inflateValidate (some r) check) := trivial
  exact ⟨after, state, run, current,
    StreamReachable.step reachable operation arguments executed⟩

end Zlib.Inflate.Proofs
