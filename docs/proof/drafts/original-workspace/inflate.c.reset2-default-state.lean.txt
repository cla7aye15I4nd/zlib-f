import ZlibF.Proof.«inflate.c.reset-default-state»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- `int inflateReset2(z_streamp strm, int windowBits)` with the default
windowBits of 15. The translated call restores the default zlib wrapper and
the complete decoder relation after an arbitrary earlier default-history
mode, including raw recovery. -/
theorem inflateReset2_15_default_state {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (invariant : DefaultStateJ h r zs z s)
    (allocator : DefAlloc z) :
    ∃ after stream state, C.run (inflateReset2 (some r) 15) h = .ok (Z_OK, after) ∧
      DefaultStateJ after r zs stream state ∧ DefAlloc stream := by
  have params : reset2Params 15 = some (5, 15) := by decide
  obtain ⟨rc, after, run, result⟩ := inflateReset2_safe invariant.good allocator.2 15
  rw [params] at result
  obtain ⟨code, heap, good, _⟩ := result
  subst rc
  have defaultBits : i2u (15 : Int32) = (15 : UInt32) := by decide
  have sameBits : s.wbits = i2u (15 : Int32) := by
    exact invariant.window.trans defaultBits.symm
  have resetHeap : reset2Heap h 15 s = h := by
    simp [reset2Heap, sameBits]
  have globals : LibraryGlobals after := by
    rw [heap, resetHeap]
    simpa only [LibraryGlobals, setI, ZStreamRef.put_static] using invariant.globals
  have platform : ZlibF.PlatformMemory.ByteObjectsFit after := by
    rw [heap, resetHeap]
    exact (invariant.platform.put_stream _ _).with_istates _
  have window : (resetPre (reset2Pre 5 15 s)).wbits = 15 := by
    simp [resetPre, reset2Pre, sameBits, defaultBits]
  have requested : (resetPre (reset2Pre 5 15 s)).reqbits = 15 := by
    simp [resetPre, reset2Pre, sameBits, defaultBits]
  have wrapper : (resetPre (reset2Pre 5 15 s)).wrap = 0 ∨
      (resetPre (reset2Pre 5 15 s)).wrap = 1 ∨
      (resetPre (reset2Pre 5 15 s)).wrap = 5 := by
    simp [resetPre, reset2Pre, sameBits, defaultBits]
  have requestedWrapper : (resetPre (reset2Pre 5 15 s)).reqwrap = 1 ∨
      (resetPre (reset2Pre 5 15 s)).reqwrap = 5 := by
    simp [resetPre, reset2Pre, sameBits, defaultBits]
  exact ⟨after, _, _, run, default_reset_head_state good window requested wrapper
    requestedWrapper globals platform, allocator⟩

/-- The same actual reset is a legal public-history transition. The
reachable witness is constructed from the translated call, not assumed. -/
theorem inflateReset2_15_history {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (reachable : StreamReachable .inflate h r)
    (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z) :
    ∃ after stream state, C.run (inflateReset2 (some r) 15) h = .ok (Z_OK, after) ∧
      DefaultStateJ after r zs stream state ∧ DefAlloc stream ∧
      StreamReachable .inflate after r := by
  obtain ⟨after, stream, state, run, current, finalAllocator⟩ :=
    inflateReset2_15_default_state invariant allocator
  have executed : (Call.inflateReset2 (some r) 15).execute default h =
      .ok ((Z_OK, default), after) := by
    change inflateReset2 (some r) 15 h = _ at run
    simp only [Call.execute, heapCall, run]
  have operation : StreamOperation .inflate r (.inflateReset2 (some r) 15) := by
    simp [StreamOperation]
  have arguments : StreamArguments h r (.inflateReset2 (some r) 15) := trivial
  exact ⟨after, stream, state, run, current, finalAllocator,
    StreamReachable.step reachable operation arguments executed⟩

end Zlib.Inflate.Proofs
