import ZlibF.Proof.«inflate.c.default-foundation»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The only two table origins installed by completed decoder calls. This is
an internal history fact; `Good` alone deliberately allows more pointer shapes. -/
def CopyTableOrigin (zs : Nat) (s : InflateState) : Prop :=
  s.lencode = .ref (.istate_codes zs) 0 ∨
    (s.lencode = .ref .st_lenfix 0 ∧ s.distcode = .ref .st_distfix 0)

/-- The actual default initializer leaves the decoder in HEAD with no window
and all three mutable table pointers at the start of its `codes` array. -/
theorem inflate_default_copy_origin
    {h after : Heap} {r : ZStreamRef} {version : BPtr}
    (domain : InitDomain h r version)
    (allocation : h.allocOk h.nalloc = true)
    (run : C.run (inflateInit_ (some r) version 112) h = .ok (Z_OK, after))
    {z : ZStream} {s : InflateState}
    (good : Good after r h.nextBlk z s) :
    s.mode = HEAD ∧ s.window = .null ∧
      s.next = .ref (.istate_codes h.nextBlk) 0 ∧
      s.lencode = .ref (.istate_codes h.nextBlk) 0 ∧
      s.distcode = .ref (.istate_codes h.nextBlk) 0 ∧
      CopyTableOrigin h.nextBlk s := by
  obtain ⟨fresh, _, _, validVersion, before, get, allocators, _⟩ := domain
  obtain ⟨nonnull, first⟩ :=
    ZlibF.Spec.Public.Proofs.InflateInit.version_value_read validVersion
  have expected : C.run (inflateInit_ (some r) version 112) h =
      .ok (Z_OK, initOkHeap h r before 5 15) := by
    change inflateInit2_ (some r) 15 version 112 h = _
    exact inflateInit2_success get fresh allocation allocators.1
      allocators.2 nonnull first (by decide +kernel)
  have heapEq : after = initOkHeap h r before 5 15 :=
    congrArg Prod.snd (Except.ok.inj (run.symm.trans expected))
  have stateEq : s = resetKeepState h.nextBlk
      (resetPre (reset2Pre 5 15 (initState r))) := by
    apply Option.some.inj
    rw [← good.live.hs, heapEq]
    simp [initOkHeap]
  rw [stateEq]
  simp [CopyTableOrigin, resetKeepState, resetPre, reset2Pre,
    initState]

/-- The actual successful default initialization establishes both the
existing default relation and the code-origin field on one returned state. -/
theorem inflate_default_copy_ready
    (h : Heap) (r : ZStreamRef) (version : BPtr)
    (domain : InitDomain h r version)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit h)
    (allocation : h.allocOk h.nalloc = true) :
    ∃ after z s,
      C.run (inflateInit_ (some r) version 112) h = .ok (Z_OK, after) ∧
      DefaultStateJ after r h.nextBlk z s ∧
      StreamReachable .inflate after r ∧
      s.mode = HEAD ∧ s.window = .null ∧
      s.next = .ref (.istate_codes h.nextBlk) 0 ∧
      s.lencode = .ref (.istate_codes h.nextBlk) 0 ∧
      s.distcode = .ref (.istate_codes h.nextBlk) 0 ∧
      CopyTableOrigin h.nextBlk s := by
  obtain ⟨after, z, s, run, _, invariant, reachable⟩ :=
    inflate_default_state_initial h r version domain platform allocation
  have origin := inflate_default_copy_origin domain allocation run invariant.good
  exact ⟨after, z, s, run, invariant, reachable,
    origin.1, origin.2.1, origin.2.2.1, origin.2.2.2.1,
    origin.2.2.2.2.1, origin.2.2.2.2.2⟩

/-- If the first allocator call fails, the actual copy clears only the
destination state binding. It has allocated no live block. -/
theorem inflateCopy_first_allocation_failure
    {h : Heap} {source dest : ZStreamRef} {zs : Nat}
    {z oldDest : ZStream} {s : InflateState}
    (good : Good h source zs z s)
    (allocator : DefAlloc z)
    (destGet : dest.get h = some oldDest)
    (failure : h.allocOk h.nalloc = false) :
    C.run (inflateCopy (some dest) (some source)) h =
      .ok (Z_MEM_ERROR,
        dest.put { h with nalloc := h.nalloc + 1 }
          { oldDest with state := none }) := by
  have sourceCheck := stateCheck_live good.live
  have allocRun : ZALLOCS (some source) h =
      .ok (none, { h with nalloc := h.nalloc + 1 }) := by
    simp [ZALLOCS, ldZ_eq, good.live.hz, allocator.1,
      allocInflateState, failure]
  have destAfter : dest.get { h with nalloc := h.nalloc + 1 } =
      some oldDest := by
    cases dest <;> simpa [ZStreamRef.get] using destGet
  have destRo : dest.isRo = false := by cases dest <;> rfl
  change (inflateCopy (some dest) (some source)) h = _
  simp [inflateCopy, sourceCheck, ldZ_eq, good.live.hz,
    good.live.zst, castI, allocRun, wrZ, destAfter,
    stZStream_ok destAfter destRo]

/-- The first failure has a genuine failed-allocation witness and no new or
released live object, while the destination is safe to end. -/
theorem inflateCopy_first_failure_cleanup
    {h : Heap} {source dest : ZStreamRef} {zs : Nat}
    {z oldDest : ZStream} {s : InflateState}
    (good : Good h source zs z s)
    (allocator : DefAlloc z)
    (destGet : dest.get h = some oldDest)
    (failure : h.allocOk h.nalloc = false) :
    ∃ after,
      C.run (inflateCopy (some dest) (some source)) h =
        .ok (Z_MEM_ERROR, after) ∧
      dest.get after = some { oldDest with state := none } ∧
      AllocationFailed h after ∧
      LiveChange h after (fun _ => False) (fun _ => False) := by
  let middle := { h with nalloc := h.nalloc + 1 }
  let after := dest.put middle { oldDest with state := none }
  have run : C.run (inflateCopy (some dest) (some source)) h =
      .ok (Z_MEM_ERROR, after) :=
    inflateCopy_first_allocation_failure good allocator destGet failure
  have destMiddle : dest.get middle = some oldDest := by
    cases dest <;> simpa [middle, ZStreamRef.get] using destGet
  have destState : dest.get after = some { oldDest with state := none } := by
    simp [after, ZStreamRef.get_put, destMiddle]
  have failed : AllocationFailed h after := by
    refine ⟨h.nalloc, Nat.le_refl _, ?_, failure⟩
    simp only [after, ZStreamRef.put_nalloc, middle]
    omega
  have shapeMiddle : Shape h middle := by
    intro b
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have shapeAfter : Shape middle after := shape_put destMiddle _
  have shape : Shape h after := shapeMiddle.trans shapeAfter
  refine ⟨after, run, destState, failed, ?_⟩
  intro b
  simpa only [LiveChange, Bool.not_eq_true, not_false_eq_true, and_true,
    or_false] using (shape.live b)

#print axioms inflate_default_copy_origin
#print axioms inflate_default_copy_ready
#print axioms inflateCopy_first_allocation_failure
#print axioms inflateCopy_first_failure_cleanup
end Zlib.Inflate.Proofs
