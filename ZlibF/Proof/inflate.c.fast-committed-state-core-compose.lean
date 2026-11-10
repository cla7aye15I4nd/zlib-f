import ZlibF.Proof.«inflate.c.fast-committed-load-state-core»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Actual fast decoding may update mode; suffix normalizes held bits;
LOAD may reset `back`. Every other decoder state field is identical. -/
def FastFinalStateFrame (base finalState : InflateState) : Prop :=
  finalState = { base with mode := finalState.mode, hold := finalState.hold, bits := finalState.bits, back := finalState.back }

theorem FastFinalStateFrame.compose
    {s s0 s1 s2 : InflateState}
    (loop : FastModeFrame s s0)
    (suffix : s1 = {s0 with hold := s1.hold, bits := s1.bits})
    (load : s2 = {s1 with back := s2.back}) :
    FastFinalStateFrame s s2 := by
  unfold FastFinalStateFrame FastModeFrame at *
  rw [load, suffix, loop]

theorem FastFinalStateFrame.restore_input
    {s loadedState : InflateState} {slow : IL}
    (frame : FastFinalStateFrame (leaveState s slow) loadedState) :
    FastFinalStateFrame s loadedState := by
  unfold FastFinalStateFrame at frame ⊢
  rw [frame]
  simp only [leaveState]

#print axioms FastFinalStateFrame.compose
#print axioms FastFinalStateFrame.restore_input
end Zlib.Inflate.Proofs
