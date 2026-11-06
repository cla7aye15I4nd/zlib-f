import ZlibF.Spec.InflateFast
import ZlibF.Spec.InflateFastOrigin

/-!
# One actual fast body preserves the source-bit origin

The safety postcondition retains scalar bounds but does not identify the
buffer's value. This obligation threads the source suffix through actual
refills, code drops, extra-bit drops, copying and error/end exits.
-/

namespace Zlib.Inffast.Spec.BodyOrigin
open C Zlib.Inffast Zlib.Inffast.Proofs

/-- Actual bit movement consumes a nonnegative exact prefix of the
original fast-call input and retains the complete existing body result.
This property alone does not assign DEFLATE meanings to the consumed bits. -/
def Goal.actual_body_preserves_origin : Prop :=
  ∀ (e : Env) (c : Ctx) (bytes : Array UInt8) (msg : BPtr) (mode : UInt32)
    (l : L) (i o used : Nat),
    StepPre e c bytes l i o → Origin.Inv e l.hold.toNat l.bits.toNat i used →
    ∃ (l' : L) (after : Heap),
      C.run (inflate_fast_body c l) (e.heap bytes msg mode) = .ok (l', after) ∧
      StepPost e bytes msg mode i o l' after ∧
      ∃ i' o' used',
        LS e l' i' o' ∧ Origin.Inv e l'.hold.toNat l'.bits.toNat i' used' ∧ used ≤ used'

end Zlib.Inffast.Spec.BodyOrigin
