import ZlibF.Proof.«inflate.c.reset-default-state»
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



end Zlib.Inflate.Proofs
