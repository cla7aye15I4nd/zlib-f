import ZlibF.Math.InflateTableGeometry
import ZlibF.Proof.«inftrees.c.cover.fn»

/-!
# inftrees.c: discharge the content invariant's geometry premise

Geometry follows from the actual loop environment. Complete codes and the
accepted incomplete single-symbol case are handled separately.
-/

namespace Zlib.Inftrees.Proofs
open Zlib.Inftrees.Canon
set_option autoImplicit false

/-- Every actual nonempty constructor loop environment establishes Geo;
it is no longer a condition left for a public caller to assume. -/
theorem Env.geometry (e : Env) : e.Geo := by
  rcases e.h_end with complete | ⟨_, single, _⟩
  · apply geometry_complete
    refine ⟨?_, ?_, e.h_R1, e.h_Rmx, ?_, ?_⟩
    · change 0 < Canon.nz (lensOf e.f e.n)
      rw [Zlib.Inftrees.Proofs.nz_eq]
      exact e.h_pos
    · exact Cover.complete_of_Kc complete
    · change mxl e.f e.n = Canon.L (lensOf e.f e.n) (Canon.nz (lensOf e.f e.n) - 1)
      rw [Zlib.Inftrees.Proofs.nz_eq, L_eq e.f e.n (by have := e.h_pos; omega)]
      rfl
    · change Canon.L (lensOf e.f e.n) 0 ≤ e.R
      rw [L_eq e.f e.n e.h_pos]
      exact e.h_R0
  · apply geometry_single
    change Canon.nz (lensOf e.f e.n) = 1
    rw [Zlib.Inftrees.Proofs.nz_eq]
    exact single

/-- Recover unconditional written-cell and link facts from the existing
loop content result, using the proved geometry of that same environment. -/
theorem Cont.established {e : Env} {written links : Nat} {ca : Array C.Code}
    (content : Cont e written links ca) : Written e written ca ∧ Links e links ca :=
  content e.geometry

end Zlib.Inftrees.Proofs
