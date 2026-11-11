import ZlibF.Proof.«inflate.c.default-foundation»
import ZlibF.Proof.«inflate.c.platform»

/-!
# inflate.c: the decoder invariant from every raw or zlib initialization

`inflateInit2_` with any accepted raw window (`windowBits` -8..-15) or zlib
window (8..15) establishes the decoder invariant on its actual returned heap.
Gzip and automatic detection (`windowBits` 16 and above) and a zlib window
taken from the stream header (`windowBits` 0) are not covered here.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- `int inflateInit2_(z_streamp strm, int windowBits, const char *version, int stream_size)`.
Every raw or zlib request with a window of 8 to 15 bits establishes the
decoder invariant, together with public reachability. -/
theorem inflate_general_J_initial
    (h : Heap) (r : ZStreamRef) (version : BPtr) (wb : Int32)
    (wrap : ZlibF.Spec.Api.Wrap) (bits : Nat)
    (domain : InitDomain h r version) (platform : ZlibF.PlatformMemory.ByteObjectsFit h)
    (params : ZlibF.Spec.Api.inflWbits wb.toInt = some (wrap, bits))
    (kind : wrap = .raw ∨ wrap = .zlib) (low : 8 ≤ bits)
    (allocation : h.allocOk h.nalloc = true) :
    ∃ after z s, C.run (inflateInit2_ (some r) wb version 112) h = .ok (Z_OK, after) ∧
      InflateInitial h after r wrap bits ∧ DefaultStateJ after r h.nextBlk z s ∧
      StreamReachable .inflate after r := by
  obtain ⟨after, run, initial, reachable, fit⟩ :=
    ZlibF.Spec.Public.Proofs.InflateInit.inflate_domain_general_platform
      h r version wb wrap bits domain platform params allocation
  have initialCopy := initial
  obtain ⟨z, s, good, _, _, head, _, wbitsEq, reqbitsEq, wrapEq, reqwrapEq, _, _, _, _, _, _,
    header, _, _, _, frame, _⟩ := initialCopy
  obtain ⟨fresh, _, globalsBefore, value, z0, get, allocators, _⟩ := domain
  obtain ⟨nonnull, read⟩ := ZlibF.Spec.Public.Proofs.InflateInit.version_value_read value
  have parameters := ZlibF.Spec.Public.Proofs.InflateInit.params_equiv wb
  rw [params] at parameters
  change reset2Params wb =
    some (ZlibF.Spec.Public.Proofs.InflateInit.publicWrap wrap, Int32.ofInt bits) at parameters
  have actual := inflateInit2_success get fresh allocation allocators.1 allocators.2
    nonnull read parameters
  have heapEq : after = initOkHeap h r z0
      (ZlibF.Spec.Public.Proofs.InflateInit.publicWrap wrap) (Int32.ofInt bits) := by
    have equality := run.symm.trans actual
    cases equality
    rfl
  have stateEq : s = resetKeepState h.nextBlk (resetPre (reset2Pre
      (ZlibF.Spec.Public.Proofs.InflateInit.publicWrap wrap) (Int32.ofInt bits) (initState r))) := by
    apply Option.some.inj
    rw [← good.live.hs, heapEq]
    simp [initOkHeap]
  have sane : s.sane = 1 := by rw [stateEq]; rfl
  have pending : DataPendingInvariant s := by
    refine ⟨sane, ?_, ?_, ?_, ?_⟩
    all_goals intro selected; rw [head] at selected; contradiction
  have globals : LibraryGlobals after := by
    change after.static = _
    rw [← frame.1]
    exact globalsBefore
  have upper := good.inv.win.wbits
  have wrapper : s.wrap = 0 ∨ s.wrap = 1 ∨ s.wrap = 5 := by
    rcases kind with raw | zlib
    · subst raw
      exact Or.inl wrapEq
    · subst zlib
      exact Or.inr (Or.inr wrapEq)
  have requestedWrap : s.reqwrap = 0 ∨ s.reqwrap = 1 ∨ s.reqwrap = 5 := by
    rw [reqwrapEq]
    exact wrapper
  have requestedBits : s.reqbits = s.wbits :=
    UInt32.toNat_inj.mp (reqbitsEq.trans wbitsEq.symm)
  refine ⟨after, z, s, run, initial, ⟨⟨good, dataTableInvariant_head head, pending,
    ?_, ?_, inflate_initial_hold initial good, ⟨by omega, upper⟩, wrapper, header,
    Or.inl head, ?_, globals, fit⟩, requestedBits, requestedWrap, Or.inl head⟩, reachable⟩
  · intro active
    rw [head] at active
    contradiction
  · intro active
    rw [head] at active
    contradiction
  · rintro (active | active) <;> rw [head] at active <;> contradiction

#print axioms inflate_general_J_initial

end Zlib.Inflate.Proofs
