import ZlibF.Proof.«inflate.c.default-extended-memory-contract»
import ZlibF.Proof.«inflate.c.copy-origin»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Internal history facts needed by recovery and copying. The flags are
the unread-header sentinel or the completed zlib-header value; the table
pointers come from the dynamic base or the paired fixed tables. These
facts supplement J and must be established by actual history, not required
as additional public caller obligations. -/
structure DefaultOriginState (h : Heap) (r : ZStreamRef) (zs : Nat)
    (z : ZStream) (s : InflateState) : Prop extends DefaultStateJ h r zs z s where
  flagsOrigin : s.flags = -1 ∨ s.flags = 0
  tableOrigin : CopyTableOrigin zs s

/-- Actual default initialization writes the unread-header sentinel.
This fact follows from the complete translated initializer's exact heap. -/
theorem inflate_default_initial_flags {h after : Heap} {r : ZStreamRef} {version : BPtr}
    (domain : InitDomain h r version) (allocation : h.allocOk h.nalloc = true)
    (run : C.run (inflateInit_ (some r) version 112) h = .ok (Z_OK, after))
    {z : ZStream} {s : InflateState} (good : Good after r h.nextBlk z s) :
    s.flags = -1 := by
  obtain ⟨fresh, _, _, validVersion, before, get, allocators, _⟩ := domain
  obtain ⟨nonnull, first⟩ := ZlibF.Spec.Public.Proofs.InflateInit.version_value_read validVersion
  have expected : C.run (inflateInit_ (some r) version 112) h =
      .ok (Z_OK, initOkHeap h r before 5 15) := by
    change inflateInit2_ (some r) 15 version 112 h = _
    exact inflateInit2_success get fresh allocation allocators.1 allocators.2 nonnull first
      (by decide +kernel)
  have heapEq : after = initOkHeap h r before 5 15 :=
    congrArg Prod.snd (Except.ok.inj (run.symm.trans expected))
  have stateEq : s = resetKeepState h.nextBlk (resetPre (reset2Pre 5 15 (initState r))) := by
    apply Option.some.inj
    rw [← good.live.hs, heapEq]
    simp [initOkHeap]
  rw [stateEq]
  rfl

/-- The real default initializer establishes both history origins together
with J, the actual allocator and original public reachability. -/
theorem inflate_default_origin_initial (h : Heap) (r : ZStreamRef) (version : BPtr)
    (domain : InitDomain h r version) (platform : ZlibF.PlatformMemory.ByteObjectsFit h)
    (allocation : h.allocOk h.nalloc = true) :
    ∃ after z s, C.run (inflateInit_ (some r) version 112) h = .ok (Z_OK, after) ∧
      DefaultOriginState after r h.nextBlk z s ∧ DefAlloc z ∧ StreamReachable .inflate after r := by
  obtain ⟨after, z, s, run, initial, current, reachable⟩ :=
    inflate_default_state_initial h r version domain platform allocation
  have flags := inflate_default_initial_flags domain allocation run current.good
  have origin := (inflate_default_copy_origin domain allocation run current.good).2.2.2.2.2
  obtain ⟨initialZ, _initialS, good, alloc, free, _⟩ := initial
  have same : initialZ = z := Option.some.inj (good.live.hz.symm.trans current.good.live.hz)
  subst initialZ
  exact ⟨after, z, s, run, ⟨current, Or.inl flags, origin⟩, ⟨alloc, free⟩, reachable⟩

/-- Origin facts transport across a checked state update that retains the
three source fields. This is a record lemma, not a callee assumption. -/
theorem DefaultOriginState.of_fields {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState} (before : DefaultOriginState h r zs z s)
    (current : DefaultStateJ after r zs stream state) (flags : state.flags = s.flags)
    (lengths : state.lencode = s.lencode) (distances : state.distcode = s.distcode) :
    DefaultOriginState after r zs stream state := by
  refine ⟨current, ?_, ?_⟩
  · rw [flags]
    exact before.flagsOrigin
  · simpa only [CopyTableOrigin, lengths, distances] using before.tableOrigin

/-- Legal caller edits retain the decoder state and both history origins. -/
theorem rebuffer_default_origin {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (before : DefaultOriginState h r zs z s)
    (edit : Rebuffer h after r) (platform : ZlibF.PlatformMemory.ByteObjectsFit after) :
    ∃ stream, DefaultOriginState after r zs stream s := by
  obtain ⟨stream, current⟩ := rebuffer_default_state before.toDefaultStateJ edit platform
  exact ⟨stream, ⟨current, before.flagsOrigin, before.tableOrigin⟩⟩

/-- Reset-keep installs canonical origins even when the input J did not
yet record them. The exact output state is from the actual reset theorem. -/
theorem inflateResetKeep_default_origin {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (before : DefaultStateJ h r zs z s) :
    ∃ after, C.run (inflateResetKeep (some r)) h = .ok (Z_OK, after) ∧
      DefaultOriginState after r zs (resetKeepStream z s) (resetKeepState zs s) := by
  obtain ⟨after, run, _heap, current, _live⟩ := inflateResetKeep_default_state before
  exact ⟨after, run, ⟨current, Or.inl rfl, Or.inl rfl⟩⟩

/-- Ordinary default reset also establishes both canonical origins. -/
theorem inflateReset_default_origin {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (before : DefaultStateJ h r zs z s)
    (free : z.zfree = .fn "zcfree") (request : DefaultRequest s) :
    ∃ after, C.run (inflateReset (some r)) h = .ok (Z_OK, after) ∧
      DefaultOriginState after r zs (resetKeepStream z (resetPre s))
        (resetKeepState zs (resetPre s)) := by
  obtain ⟨after, run, current, _live⟩ := inflateReset_default_state before free request
  exact ⟨after, run, ⟨current, Or.inl rfl, Or.inl rfl⟩⟩

/-- Reset2 with the selected fifteen-bit configuration establishes the
same canonical history origins from its actual reset output. -/
theorem inflateReset2_15_default_origin {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (before : DefaultStateJ h r zs z s)
    (free : z.zfree = .fn "zcfree") :
    ∃ after, C.run (inflateReset2 (some r) 15) h = .ok (Z_OK, after) ∧
      DefaultOriginState after r zs (resetKeepStream z (resetPre (reset2Pre 5 15 s)))
        (resetKeepState zs (resetPre (reset2Pre 5 15 s))) := by
  obtain ⟨after, run, current, _live⟩ := inflateReset2_15_default_state before free
  exact ⟨after, run, ⟨current, Or.inl rfl, Or.inl rfl⟩⟩

/-- Scalar data-decoder state writes retain both source origins. -/
theorem DefaultOriginState.decode_update {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState} (before : DefaultOriginState h r zs z s)
    (current : DefaultStateJ after r zs stream state) (frame : DecodeStateFrame s state) :
    DefaultOriginState after r zs stream state :=
  before.of_fields current (by rw [frame]) (by rw [frame]) (by rw [frame])

/-- Actual window-only state changes retain both history origins. -/
theorem DefaultOriginState.window_update {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState} (before : DefaultOriginState h r zs z s)
    (current : DefaultStateJ after r zs stream state) (frame : WindowStateFrame s state) :
    DefaultOriginState after r zs stream state :=
  before.of_fields current (by rw [frame]) (by rw [frame]) (by rw [frame])

/-- The block-header selector either retains both pointers or installs the
paired fixed tables, so it preserves the table origin and header sentinel. -/
theorem DefaultOriginState.block_update {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState} (before : DefaultOriginState h r zs z s)
    (current : DefaultStateJ after r zs stream state) (frame : BlockHeaderFrame s state)
    (pointers : BlockHeaderPointers s state) : DefaultOriginState after r zs stream state := by
  refine ⟨current, ?_, ?_⟩
  · rw [frame]
    exact before.flagsOrigin
  · rcases pointers with ⟨lengths, distances⟩ | fixed
    · simpa only [CopyTableOrigin, lengths, distances] using before.tableOrigin
    · exact Or.inr fixed

/-- A concrete actual initializer realizes the strengthened history state. -/
theorem default_origin_state_witness :
    ∃ after z s,
      C.run (inflateInit_ (some (.tab 0)) (.ref (.blk 1) 0) 112) witnessHeap = .ok (Z_OK, after) ∧
      DefaultOriginState after (.tab 0) witnessHeap.nextBlk z s ∧ DefAlloc z ∧
      StreamReachable .inflate after (.tab 0) :=
  inflate_default_origin_initial witnessHeap (.tab 0) (.ref (.blk 1) 0)
    ZlibF.Spec.Public.Proofs.InflateInit.public_witness_domain inflate_default_witness_platform rfl

#print axioms inflate_default_initial_flags
#print axioms inflate_default_origin_initial
#print axioms rebuffer_default_origin
#print axioms inflateResetKeep_default_origin
#print axioms inflateReset_default_origin
#print axioms inflateReset2_15_default_origin
#print axioms DefaultOriginState.decode_update
#print axioms DefaultOriginState.window_update
#print axioms DefaultOriginState.block_update
#print axioms default_origin_state_witness
end Zlib.Inflate.Proofs
