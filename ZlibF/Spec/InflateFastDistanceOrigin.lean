import ZlibF.Spec.InflateFast
import ZlibF.Spec.InflateFastOrigin

/-!
# Source-bit origin through the actual fast distance sub-block

The source split dolenDist includes lookup, extra bits and copying. Its
old error postcondition does not retain the bit stream. Origin must hold
on error as well as on a successful copy.
-/

namespace Zlib.Inffast.Spec.DistanceOrigin
open C Zlib.Inffast Zlib.Inffast.Proofs

/-- The complete actual distance sub-block retains its existing result
and the exact source suffix on every exit. These are internal data
preconditions, not an assumed distance-callee contract. -/
def Goal.actual_distance_block_preserves_origin : Prop :=
  ∀ (e : Env) (c : Ctx) (bytes : Array UInt8) (msg : BPtr) (mode : UInt32)
    (l : L) (i o used : Nat),
    CtxOK e c → LS e l i o →
    e.o0 + e.sm0.avail_out.toNat ≤ bytes.size →
    o + 258 ≤ e.o0 + e.sm0.avail_out.toNat → bytes.size < 2 ^ 63 →
    l.broke = false → (3 ≤ l.len.toNat ∧ l.len.toNat ≤ 258) →
    15 ≤ l.bits.toNat →
    (i + 2 ≤ e.i0 + e.sm0.avail_in.toNat ∨
      (i + 1 ≤ e.i0 + e.sm0.avail_in.toNat ∧ 20 ≤ l.bits.toNat)) →
    Origin.Inv e l.hold.toNat l.bits.toNat i used →
    ∃ (l' : L) (after : Heap),
      C.run (dolenDist c l) (e.heap bytes msg mode) = .ok (l', after) ∧
      (∃ entry consumed,
        consumed ≤ 15 ∧
        DistLook e l.hold.toNat (l.hold.toNat % 2 ^ e.s0.distbits.toNat) entry consumed ∧
        DistEnd e bytes msg mode ((Sg e l.hold.toNat l.bits.toNat i).drop consumed)
          i o l.len.toNat entry l' after) ∧
      ∃ i' o' used',
        LS e l' i' o' ∧ Origin.Inv e l'.hold.toNat l'.bits.toNat i' used' ∧ used ≤ used'

end Zlib.Inffast.Spec.DistanceOrigin
