import ZlibF.Proof.«inflate.c.default-readonly-controls»
import ZlibF.Proof.«inflate.c.copy-origin»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Internal history facts needed by recovery and copying. The table
pointers come from the dynamic base or the paired fixed tables. These
facts supplement J and must be established by actual history, not required
as additional public caller obligations. -/
structure DefaultOriginState (h : Heap) (r : ZStreamRef) (zs : Nat)
    (z : ZStream) (s : InflateState) : Prop extends DefaultStateJ h r zs z s where
  tableOrigin : CopyTableOrigin zs s

/-- The real default initializer establishes the table origin together
with J, the actual allocator and original public reachability. -/
theorem inflate_default_origin_initial (h : Heap) (r : ZStreamRef) (version : BPtr)
    (domain : InitDomain h r version) (platform : ZlibF.PlatformMemory.ByteObjectsFit h)
    (allocation : h.allocOk h.nalloc = true) :
    ∃ after z s, C.run (inflateInit_ (some r) version 112) h = .ok (Z_OK, after) ∧
      DefaultOriginState after r h.nextBlk z s ∧ DefAlloc z ∧ StreamReachable .inflate after r := by
  obtain ⟨after, z, s, run, initial, current, reachable⟩ :=
    inflate_default_state_initial h r version domain platform allocation
  have origin := (inflate_default_copy_origin domain allocation run current.good).2.2.2.2.2
  obtain ⟨initialZ, _initialS, good, alloc, free, _⟩ := initial
  have same : initialZ = z := Option.some.inj (good.live.hz.symm.trans current.good.live.hz)
  subst initialZ
  exact ⟨after, z, s, run, ⟨current, origin⟩, ⟨alloc, free⟩, reachable⟩

/-- Origin facts transport across a checked state update that retains the
three source fields. This is a record lemma, not a callee assumption. -/
theorem DefaultOriginState.of_fields {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState} (before : DefaultOriginState h r zs z s)
    (current : DefaultStateJ after r zs stream state) (flags : state.flags = s.flags)
    (lengths : state.lencode = s.lencode) (distances : state.distcode = s.distcode) :
    DefaultOriginState after r zs stream state :=
  ⟨current, by simpa only [CopyTableOrigin, lengths, distances] using before.tableOrigin⟩

/-- Legal caller edits retain the decoder state and the table origin. -/
theorem rebuffer_default_origin {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (before : DefaultOriginState h r zs z s)
    (edit : Rebuffer h after r) (platform : ZlibF.PlatformMemory.ByteObjectsFit after) :
    ∃ stream, DefaultOriginState after r zs stream s := by
  obtain ⟨stream, current⟩ := rebuffer_default_state before.toDefaultStateJ edit platform
  exact ⟨stream, ⟨current, before.tableOrigin⟩⟩

/-- Scalar data-decoder state writes retain the table origin. -/
theorem DefaultOriginState.decode_update {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState} (before : DefaultOriginState h r zs z s)
    (current : DefaultStateJ after r zs stream state) (frame : DecodeStateFrame s state) :
    DefaultOriginState after r zs stream state :=
  before.of_fields current (by rw [frame]) (by rw [frame]) (by rw [frame])

/-- Actual window-only state changes retain the table origin. -/
theorem DefaultOriginState.window_update {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState} (before : DefaultOriginState h r zs z s)
    (current : DefaultStateJ after r zs stream state) (frame : WindowStateFrame s state) :
    DefaultOriginState after r zs stream state :=
  before.of_fields current (by rw [frame]) (by rw [frame]) (by rw [frame])

/-- The block-header selector either retains both pointers or installs the
paired fixed tables, so it preserves the table origin. -/
theorem DefaultOriginState.block_update {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState} (before : DefaultOriginState h r zs z s)
    (current : DefaultStateJ after r zs stream state) (frame : BlockHeaderFrame s state)
    (pointers : BlockHeaderPointers s state) : DefaultOriginState after r zs stream state := by
  refine ⟨current, ?_⟩
  rcases pointers with ⟨lengths, distances⟩ | fixed
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
#print axioms DefaultOriginState.decode_update
#print axioms DefaultOriginState.window_update
#print axioms DefaultOriginState.block_update
#print axioms default_origin_state_witness
end Zlib.Inflate.Proofs
