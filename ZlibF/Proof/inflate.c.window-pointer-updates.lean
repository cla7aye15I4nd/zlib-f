import ZlibF.Proof.«inflate.c.window-pointer-macros»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- A concrete load followed by its window-preserving state store retains
the global window graph, before entering its actual remaining program. -/
theorem windowFrameM_ldS_update {α : Type} (r : ZStreamRef) (owner pointer : InflateStatePtr)
    (update : InflateState → InflateState) (next : InflateState → M α)
    (window : ∀ state, (update state).window = state.window)
    (tailFrame : ∀ state, WindowFrameM r owner (next state)) :
    WindowFrameM r owner (do
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
        exact (show WindowFrame r owner h (setI h zs (update state)) from
          decoderWindows_setI get (window state)).trans
          (tailFrame state _ value after run)

theorem windowFrameM_ldS_store (r : ZStreamRef) (owner pointer : InflateStatePtr)
    (update : InflateState → InflateState) (window : ∀ state, (update state).window = state.window) :
    WindowFrameM r owner (do
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
        exact decoderWindows_setI get (window state)

theorem windowFrameM_wrS_any (r : ZStreamRef) (owner pointer : InflateStatePtr)
    (update : InflateState → InflateState) (window : ∀ state, (update state).window = state.window) :
    WindowFrameM r owner (wrS pointer update) := windowFrameM_wrS r pointer update window

theorem windowFrameM_stZ (r : ZStreamRef) (owner : InflateStatePtr) (pointer : ZStreamPtr) (stream : ZStream) :
    WindowFrameM r owner (stZStream pointer stream) := by
  intro h value after run
  cases pointer with
  | none => cases run
  | some root =>
    rw [stZ_eq] at run
    split at run
    · cases run
      funext b
      simp only [decoderWindows, ZStreamRef.put_istates]
    · cases run

end Zlib.Inflate.Proofs
