import ZlibF.Proof.«inflate.c.default-public-state»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual reset writes put the decoder at HEAD. Construction and data
clauses are inactive there; the requested configuration and real library
storage still satisfy the initialized relation. -/
theorem default_reset_head_state {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {prior : InflateState} (good : Good h r zs z (resetKeepState zs prior))
    (window : prior.wbits = 15) (requested : prior.reqbits = 15)
    (wrapper : prior.wrap = 0 ∨ prior.wrap = 1 ∨ prior.wrap = 5)
    (requestedWrapper : prior.reqwrap = 1 ∨ prior.reqwrap = 5)
    (globals : LibraryGlobals h) (platform : ZlibF.PlatformMemory.ByteObjectsFit h) :
    DefaultStateJ h r zs z (resetKeepState zs prior) := by
  refine ⟨⟨good, dataTableInvariant_head rfl, dataPendingInvariant_head rfl rfl,
    ?_, ?_, ?_, window, wrapper, rfl, Or.inl rfl, ?_, globals, platform⟩,
    requested, requestedWrapper, Or.inl rfl⟩
  · intro active
    change HEAD = CODELENS at active
    contradiction
  · intro active
    change HEAD = LENLENS at active
    contradiction
  · change 0 < 1
    decide
  · rintro (active | active)
    · change HEAD = CHECK at active
      contradiction
    · change HEAD = LENGTH at active
      contradiction

/-- `int inflateResetKeep(z_streamp strm)`.
The actual source reset preserves the complete default relation and allocator.
The existing window is kept, including after raw recovery. -/
theorem inflateResetKeep_default_state {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z) :
    ∃ after stream state, C.run (inflateResetKeep (some r)) h = .ok (Z_OK, after) ∧
      DefaultStateJ after r zs stream state ∧ DefAlloc stream := by
  obtain ⟨after, run, heapEq, good, live⟩ := inflateResetKeep_safe invariant.good
  have globals : LibraryGlobals after := by
    rw [heapEq]
    simpa only [LibraryGlobals, setI, ZStreamRef.put_static] using invariant.globals
  have platform : ZlibF.PlatformMemory.ByteObjectsFit after := by
    rw [heapEq]
    exact (invariant.platform.put_stream _ _).with_istates _
  exact ⟨after, _, _, run, default_reset_head_state good invariant.window invariant.requestedBits
    invariant.wrapper invariant.requestedWrap globals platform, allocator⟩

/-- `int inflateReset(z_streamp strm)`.
Default window size and requested size coincide, so the actual reset restores
the requested zlib wrapper and empties the existing window without freeing it.
The complete default relation and allocator are re-established. -/
theorem inflateReset_default_state {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z) :
    ∃ after stream state, C.run (inflateReset (some r)) h = .ok (Z_OK, after) ∧
      DefaultStateJ after r zs stream state ∧ DefAlloc stream := by
  have sameSize : s.wbits = s.reqbits := invariant.window.trans invariant.requestedBits.symm
  have pre : resetPre s = { s with wrap := s.reqwrap, wsize := 0, whave := 0, wnext := 0 } := by
    simp only [resetPre, sameSize, bne_self_eq_false, Bool.false_eq_true, ite_false]
  have heap : resetHeap h s = h := by
    simp only [resetHeap, sameSize, bne_self_eq_false, Bool.false_eq_true, ite_false]
  obtain ⟨after, run, heapEq, good, owned⟩ := inflateReset_safe invariant.good allocator.2
  have globals : LibraryGlobals after := by
    rw [heapEq, heap]
    simpa only [LibraryGlobals, setI, ZStreamRef.put_static] using invariant.globals
  have platform : ZlibF.PlatformMemory.ByteObjectsFit after := by
    rw [heapEq, heap]
    exact (invariant.platform.put_stream _ _).with_istates _
  have window : (resetPre s).wbits = 15 := by rw [pre]; exact invariant.window
  have requested : (resetPre s).reqbits = 15 := by rw [pre]; exact invariant.requestedBits
  have wrapper : (resetPre s).wrap = 0 ∨ (resetPre s).wrap = 1 ∨ (resetPre s).wrap = 5 := by
    rw [pre]
    exact Or.inr invariant.requestedWrap
  have requestedWrapper : (resetPre s).reqwrap = 1 ∨ (resetPre s).reqwrap = 5 := by
    rw [pre]
    exact invariant.requestedWrap
  exact ⟨after, _, _, run, default_reset_head_state good window requested wrapper requestedWrapper
    globals platform, allocator⟩

end Zlib.Inflate.Proofs
