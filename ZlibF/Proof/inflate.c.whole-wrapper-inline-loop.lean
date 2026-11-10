import ZlibF.Proof.«inflate.c.whole-wrapper-call-progress»
namespace Zlib.Inflate.Proofs.WholeWrapper
open C Zlib.Inflate
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

/-- Identical actual first-switch observations leave the identical tail
of the original fuelled loop. No completed direct return is restarted. -/
theorem wrapper_loop_first_eq {body : X Unit} {l : IL} {before after : Heap}
    (same : runX body l before = runX body l after) :
    runX (xwhile (pure true) body) l before = runX (xwhile (pure true) body) l after := by
  unfold xwhile xwhileBrk cwhile
  generalize C.fuel = remaining
  cases remaining with
  | zero => simp [runX, cwhile.go, ExceptT.run, ExceptT.mk, StateT.run, bind]
  | succ remaining =>
    simp [runX, cwhile.go, ExceptT.run, ExceptT.mk, StateT.run, bind, ExceptT.bind,
      ExceptT.bindCont, StateT.bind, pure, ExceptT.pure, StateT.pure] at same ⊢
    rw [same]

#print axioms wrapper_loop_first_eq
end Zlib.Inflate.Proofs.WholeWrapper
