import ZlibF.Proof.«inflate.c.code-length-meaning-state»
import ZlibF.Proof.«inflate.c.code-length-install»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The stronger installed-content component retains exceptional cells as
well as ordinary symbol meaning. The alphabet remains independent of lens. -/
structure DefaultCodeLengthContentsState (h : Heap) (r : ZStreamRef) (zs : Nat)
    (z : ZStream) (s : InflateState) : Prop extends DefaultOriginState h r zs z s where
  codeContents : s.mode = CODELENS → ∃ alphabet,
    Zlib.Inftrees.Proofs.CodeLengthContents s.codes 0 s.lenbits.toNat alphabet

theorem DefaultCodeLengthContentsState.toMeaningState {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (before : DefaultCodeLengthContentsState h r zs z s) :
    DefaultCodeLengthState h r zs z s := by
  refine ⟨before.toDefaultOriginState, ?_⟩
  intro mode
  obtain ⟨alphabet, contents⟩ := before.codeContents mode
  exact ⟨alphabet, contents.toCodeLengthMeaning⟩

/-- Real initialization establishes the stronger component at HEAD. -/
theorem inflate_default_code_length_contents_initial (h : Heap) (r : ZStreamRef) (version : BPtr)
    (domain : InitDomain h r version) (platform : ZlibF.PlatformMemory.ByteObjectsFit h)
    (allocation : h.allocOk h.nalloc = true) :
    ∃ after z s, C.run (inflateInit_ (some r) version 112) h = .ok (Z_OK, after) ∧
      DefaultCodeLengthContentsState after r h.nextBlk z s ∧ DefAlloc z ∧ StreamReachable .inflate after r := by
  obtain ⟨after, z, s, run, current, allocator, reachable⟩ :=
    inflate_default_origin_initial h r version domain platform allocation
  obtain ⟨after2, z2, s2, run2, _initial, good, mode, _⟩ :=
    inflate_default_init_boundary h r version domain platform allocation
  have same := Except.ok.inj (run2.symm.trans run)
  cases same
  have states : s2 = s := Option.some.inj (good.live.hs.symm.trans current.good.live.hs)
  subst s2
  refine ⟨after, z, s, run, ⟨current, ?_⟩, allocator, reachable⟩
  intro active
  rw [mode] at active
  cases active

/-- Replacing admitted buffers retains the actual table and its contents. -/
theorem rebuffer_default_code_length_contents {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (before : DefaultCodeLengthContentsState h r zs z s)
    (edit : Rebuffer h after r) (platform : ZlibF.PlatformMemory.ByteObjectsFit after) :
    ∃ stream, DefaultCodeLengthContentsState after r zs stream s := by
  obtain ⟨stream, current⟩ := rebuffer_default_origin before.toDefaultOriginState edit platform
  exact ⟨stream, current, before.codeContents⟩

/-- clRead preserves all installed-table fields while overwriting lens,
including wait, BAD and complete results. This observer retains the actual
same-run state established by its existing totality theorem. -/
theorem clRead_default_code_length_contents_of_run {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState} {l regs : IL} {bs : List UInt8} {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (before : DefaultCodeLengthContentsState h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = CODELENS)
    (actual : runX (clRead c) l h = .ok ((outcome, regs), after))
    (current : DefaultStateJ after r zs stream state) : DefaultCodeLengthContentsState after r zs stream state := by
  have ordinary := clRead_default_code_length_of_run E before.toMeaningState buffers mode actual current
  obtain ⟨outcome2, regs2, after2, run2, full, _⟩ :=
    clRead_run_full_cursor E.strm E.st E.hz E.hs before.good.inv.wf.1 mode before.lengths buffers.bits
  rw [actual] at run2
  cases run2
  obtain ⟨stored, _used, get, _bound, _bits, _shape, _budget, frame, _⟩ := full.1
  have states : stored = state := Option.some.inj (get.symm.trans current.good.live.hs)
  subst stored
  refine ⟨ordinary.toDefaultOriginState, ?_⟩
  intro _active
  obtain ⟨alphabet, contents⟩ := before.codeContents mode
  refine ⟨alphabet, ?_⟩
  rw [frame]
  exact contents

/-- The actual complete reading callee preserves the stronger installed
contents, with its caller invariant established rather than assumed as a
callee specification. -/
theorem clRead_default_code_length_contents_state {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (before : DefaultCodeLengthContentsState h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = CODELENS) :
    ∃ outcome regs after stream state,
      runX (clRead c) l h = .ok ((outcome, regs), after) ∧
      DefaultCodeLengthContentsState after r zs stream state := by
  obtain ⟨outcome, regs, after, stream, state, _used, _bound, run, current, _⟩ :=
    clRead_default_state_complete E before.toDefaultStateJ buffers mode
  exact ⟨outcome, regs, after, stream, state, run,
    clRead_default_code_length_contents_of_run E before buffers mode run current⟩

/-- The stronger state is inhabited by the real default initializer. -/
theorem default_code_length_contents_state_witness :
    ∃ after z s, C.run (inflateInit_ (some (.tab 0)) (.ref (.blk 1) 0) 112) witnessHeap = .ok (Z_OK, after) ∧
      DefaultCodeLengthContentsState after (.tab 0) witnessHeap.nextBlk z s ∧ DefAlloc z ∧
      StreamReachable .inflate after (.tab 0) :=
  inflate_default_code_length_contents_initial witnessHeap (.tab 0) (.ref (.blk 1) 0)
    ZlibF.Spec.Public.Proofs.InflateInit.public_witness_domain inflate_default_witness_platform rfl

#print axioms inflate_default_code_length_contents_initial
#print axioms clRead_default_code_length_contents_state
#print axioms default_code_length_contents_state_witness
end Zlib.Inflate.Proofs
