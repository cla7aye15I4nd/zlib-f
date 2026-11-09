import ZlibF.Proof.«inftrees.c.code-length-meaning-state»
import ZlibF.Proof.«inflate.c.origin-fields-construction-tail»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The installed alphabet is a ghost value distinct from the mutable lens
buffer. This is the CODES-content component of a semantic state relation;
it does not relate the entire input or output to the stream format. -/
structure DefaultCodeLengthState (h : Heap) (r : ZStreamRef) (zs : Nat)
    (z : ZStream) (s : InflateState) : Prop extends DefaultOriginState h r zs z s where
  codeMeaning : s.mode = CODELENS → ∃ alphabet,
    Zlib.Inftrees.Proofs.CodeLengthMeaning s.codes 0 s.lenbits.toNat alphabet

/-- A checked state outside CODELENS needs no installed code-length alphabet. -/
theorem DefaultOriginState.code_length_inactive {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (before : DefaultOriginState h r zs z s)
    (inactive : s.mode ≠ CODELENS) : DefaultCodeLengthState h r zs z s :=
  ⟨before, fun active => False.elim (inactive active)⟩

/-- Actual default initialization establishes this semantic-state component.
Its inactive HEAD clause follows from the real initialized record. -/
theorem inflate_default_code_length_initial (h : Heap) (r : ZStreamRef) (version : BPtr)
    (domain : InitDomain h r version) (platform : ZlibF.PlatformMemory.ByteObjectsFit h)
    (allocation : h.allocOk h.nalloc = true) :
    ∃ after z s, C.run (inflateInit_ (some r) version 112) h = .ok (Z_OK, after) ∧
      DefaultCodeLengthState after r h.nextBlk z s ∧ DefAlloc z ∧ StreamReachable .inflate after r := by
  obtain ⟨after, z, s, run, current, allocator, reachable⟩ :=
    inflate_default_origin_initial h r version domain platform allocation
  obtain ⟨after2, z2, s2, run2, _initial, good, mode, _⟩ :=
    inflate_default_init_boundary h r version domain platform allocation
  have same := Except.ok.inj (run2.symm.trans run)
  cases same
  have states : s2 = s := Option.some.inj (good.live.hs.symm.trans current.good.live.hs)
  subst s2
  have inactive : s.mode ≠ CODELENS := by rw [mode]; decide
  exact ⟨after, z, s, run, current.code_length_inactive inactive, allocator, reachable⟩

/-- Rebinding legal caller buffers retains the exact installed table state. -/
theorem rebuffer_default_code_length {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (before : DefaultCodeLengthState h r zs z s)
    (edit : Rebuffer h after r) (platform : ZlibF.PlatformMemory.ByteObjectsFit after) :
    ∃ stream, DefaultCodeLengthState after r zs stream s := by
  obtain ⟨stream, current⟩ := rebuffer_default_origin before.toDefaultOriginState edit platform
  exact ⟨stream, current, before.codeMeaning⟩

/-- The actual length-reading loop keeps the installed table and its root
while overwriting lens. The alphabet witness is retained independently of
those writes, on wait, BAD and normal completion. -/
theorem clRead_default_code_length_of_run {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState} {l regs : IL} {bs : List UInt8} {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (before : DefaultCodeLengthState h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = CODELENS)
    (actual : runX (clRead c) l h = .ok ((outcome, regs), after))
    (current : DefaultStateJ after r zs stream state) : DefaultCodeLengthState after r zs stream state := by
  have origins := before.toDefaultOriginState.of_field_frame current
    (originFieldFrameX_clRead r c E.strm _ _ _ _ _ actual)
  obtain ⟨outcome2, regs2, after2, run2, full, _⟩ :=
    clRead_run_full_cursor E.strm E.st E.hz E.hs before.good.inv.wf.1 mode before.lengths buffers.bits
  rw [actual] at run2
  cases run2
  obtain ⟨stored, _used, get, _bound, _bits, _shape, _budget, frame, _⟩ := full.1
  have states : stored = state := Option.some.inj (get.symm.trans current.good.live.hs)
  subst stored
  refine ⟨origins, ?_⟩
  intro _active
  obtain ⟨alphabet, meaning⟩ := before.codeMeaning mode
  refine ⟨alphabet, ?_⟩
  rw [frame]
  exact meaning

/-- The real length-reading callee is total under the initialized state and
returns its persistent semantic table component, without an assumed callee
contract. Its full parser input/output meaning remains a later obligation. -/
theorem clRead_default_code_length_state {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (before : DefaultCodeLengthState h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = CODELENS) :
    ∃ outcome regs after stream state,
      runX (clRead c) l h = .ok ((outcome, regs), after) ∧
      DefaultCodeLengthState after r zs stream state := by
  obtain ⟨outcome, regs, after, stream, state, _used, _bound, run, current, _⟩ :=
    clRead_default_state_complete E before.toDefaultStateJ buffers mode
  exact ⟨outcome, regs, after, stream, state, run,
    clRead_default_code_length_of_run E before buffers mode run current⟩

/-- A real initialized heap inhabits the strengthened table-state component. -/
theorem default_code_length_state_witness :
    ∃ after z s, C.run (inflateInit_ (some (.tab 0)) (.ref (.blk 1) 0) 112) witnessHeap = .ok (Z_OK, after) ∧
      DefaultCodeLengthState after (.tab 0) witnessHeap.nextBlk z s ∧ DefAlloc z ∧
      StreamReachable .inflate after (.tab 0) :=
  inflate_default_code_length_initial witnessHeap (.tab 0) (.ref (.blk 1) 0)
    ZlibF.Spec.Public.Proofs.InflateInit.public_witness_domain inflate_default_witness_platform rfl

#print axioms inflate_default_code_length_initial
#print axioms clRead_default_code_length_state
#print axioms default_code_length_state_witness
end Zlib.Inflate.Proofs
