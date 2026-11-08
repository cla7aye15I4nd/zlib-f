import ZlibF.Proof.«inflate.c.origin-fields-macros»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- A concrete load followed by its field-preserving state store retains
the global field projection, before entering its actual remaining program. -/
theorem originFieldFrameM_ldS_update {α : Type} (r : ZStreamRef) (owner pointer : InflateStatePtr)
    (update : InflateState → InflateState) (next : InflateState → M α)
    (window : ∀ state, originStateFields (update state) = originStateFields state)
    (tailFrame : ∀ state, OriginFieldFrameM r owner (next state)) :
    OriginFieldFrameM r owner (do
      let state ← ldInflateState pointer
      stInflateState pointer (update state)
      next state) := by
  intro h value after run
  cases pointer with
  | none => cases run
  | some pointer =>
    cases pointer with
    | tab zs =>
      cases get : h.istates zs with
      | none => simp only [bind_app, ldI_eq, get] at run; cases run
      | some state =>
        simp only [bind_app, ldI_eq, stI_eq, get, Option.isSome_some, ↓reduceIte] at run
        exact (show OriginFieldFrame r owner h (setI h zs (update state)) from
          decoderOriginFields_setI get (window state)).trans
          (tailFrame state _ value after run)

theorem originFieldFrameM_ldS_store (r : ZStreamRef) (owner pointer : InflateStatePtr)
    (update : InflateState → InflateState) (window : ∀ state, originStateFields (update state) = originStateFields state) :
    OriginFieldFrameM r owner (do
      let state ← ldInflateState pointer
      stInflateState pointer (update state)) := by
  intro h value after run
  cases pointer with
  | none => cases run
  | some pointer =>
    cases pointer with
    | tab zs =>
      cases get : h.istates zs with
      | none => simp only [bind_app, ldI_eq, get] at run; cases run
      | some state =>
        simp only [bind_app, ldI_eq, stI_eq, get, Option.isSome_some, ↓reduceIte] at run
        cases run
        exact decoderOriginFields_setI get (window state)

theorem originFieldFrameM_wrS_any (r : ZStreamRef) (owner pointer : InflateStatePtr)
    (update : InflateState → InflateState) (window : ∀ state, originStateFields (update state) = originStateFields state) :
    OriginFieldFrameM r owner (wrS pointer update) := originFieldFrameM_wrS r pointer update window

theorem originFieldFrameM_stZ (r : ZStreamRef) (owner : InflateStatePtr) (pointer : ZStreamPtr) (stream : ZStream) :
    OriginFieldFrameM r owner (stZStream pointer stream) := by
  intro h value after run
  cases pointer with
  | none => cases run
  | some root =>
    rw [stZ_eq] at run
    split at run
    · cases run
      funext b
      simp only [decoderOriginFields, ZStreamRef.put_istates]
    · cases run

end Zlib.Inflate.Proofs
