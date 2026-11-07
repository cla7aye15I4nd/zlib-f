import ZlibF.Spec.InflateFastBodyOrigin

/-!
# Exact remaining source input after a whole fast call

Body origin must survive the actual loop and epilogue. This property
identifies the final heap registers with the original input suffix. It
does not assign a DEFLATE token meaning to the bits consumed.
-/

namespace Zlib.Inffast.Spec.CallOrigin
open C Zlib.Inffast Zlib.Inffast.Proofs

def HasOrigin (e : Env) (after : Heap) : Prop :=
  ∃ (state : InflateState) (stream : ZStream) (input used : Nat),
    after.istates e.stid = some state ∧ e.r.get after = some stream ∧
    stream.next_in = .ref (.blk e.ib) input ∧
    input + stream.avail_in.toNat = e.i0 + e.sm0.avail_in.toNat ∧
    Origin.Inv e state.hold.toNat state.bits.toNat input used

/-- The actual whole call preserves the source suffix through every
body and rollback, retaining its full existing safety/frame result.
The actual body-origin theorem must be proved, not taken as a premise. -/
def Goal.actual_fast_preserves_origin : Prop :=
  ∀ e : Env, ∃ after,
    C.run (inflate_fast e.strm e.start) e.h0 = .ok ((), after) ∧
    FastPost e after ∧ HasOrigin e after

end Zlib.Inffast.Spec.CallOrigin
