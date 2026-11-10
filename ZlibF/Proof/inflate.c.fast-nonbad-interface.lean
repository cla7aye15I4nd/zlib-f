import ZlibF.Proof.«inflate.c.fast-length-bad-consumed-word»
import ZlibF.Proof.«inflate.c.rejected-consumed-word-math»
namespace Zlib.Inflate.Proofs.FastArbitraryBody
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- A produced actual body return that has not entered BAD. This is an
execution conclusion, separate from an independent valid-source premise. -/
def BodyNonBad (h : Heap) (r : ZStreamRef) (zs : Nat) (c : Zlib.Inffast.Ctx) (fast : Zlib.Inffast.L) : Prop :=
  ∃ result after z s, C.run (Zlib.Inffast.inflate_fast_body c fast) h = .ok (result, after) ∧
    Good after r zs z s ∧ s.mode ≠ BAD

/-- Active payload modes and TYPE are not the decoder's rejected mode. -/
theorem data_mode_ne_bad {s : InflateState} (mode : DataTableMode s.mode) : s.mode ≠ BAD := by
  intro bad
  rw [bad] at mode
  exact (by unfold DataTableMode; decide : ¬ DataTableMode BAD) mode

#print axioms data_mode_ne_bad
end Zlib.Inflate.Proofs.FastArbitraryBody
