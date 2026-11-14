import ZlibF.Proof.«inffast.c.match»

/-!
# inffast.c: the frame of pure match-copy arrays

Each copied byte stays inside the requested destination interval. These are
theorems about the existing array functions, with no new semantic definitions.
-/

namespace Zlib.Inffast.Proofs
open C Zlib.Inffast Zlib.Inffast.Spec

theorem blitN_frame (S : Array UInt8) : ∀ k fo oo (A : Array UInt8) j,
    j < oo ∨ oo + k ≤ j → (blitN S k fo oo A)[j]? = A[j]?
  | 0, _, _, _, _, _ => rfl
  | k + 1, fo, oo, A, j, hj => by
    rw [blitN, blitN_frame S k (fo + 1) (oo + 1) (A.set! oo (S.getD fo 0)) j (by omega)]
    have hne : oo ≠ j := by omega
    simp [Array.set!, hne]

theorem cpyN_frame : ∀ k fo oo (A : Array UInt8) j,
    j < oo ∨ oo + k ≤ j → (cpyN k fo oo A)[j]? = A[j]?
  | 0, _, _, _, _, _ => rfl
  | k + 1, fo, oo, A, j, hj => by
    rw [cpyN, cpyN_frame k (fo + 1) (oo + 1) (A.set! oo (A.getD fo 0)) j (by omega)]
    have hne : oo ≠ j := by omega
    simp [Array.set!, hne]

theorem matchArr_frame (wsize wnext woff : Nat) (W : Array UInt8)
    (bg o dist len : Nat) (A : Array UInt8) (j : Nat) (hj : j < o ∨ o + len ≤ j) :
    (matchArr wsize wnext woff W bg o dist len A)[j]? = A[j]? := by
  unfold matchArr
  dsimp only
  repeat' split
  all_goals
    repeat' first
      | rw [cpyN_frame _ _ _ _ _ (by omega)]
      | rw [blitN_frame _ _ _ _ _ _ (by omega)]

theorem matchArrA_frame (wsize woff : Nat) (bg o dist len : Nat) (A : Array UInt8) (j : Nat)
    (hj : j < o ∨ o + len ≤ j) : (matchArrA wsize woff bg o dist len A)[j]? = A[j]? := by
  unfold matchArrA
  dsimp only
  repeat' split
  all_goals
    repeat' first
      | rw [cpyN_frame _ _ _ _ _ (by omega)]

theorem EnvG.mArr_frame {α : Bool} (e : EnvG α) (bg o dist len : Nat) (A : Array UInt8) (j : Nat)
    (hj : j < o ∨ o + len ≤ j) : (e.mArr bg o dist len A)[j]? = A[j]? := by
  cases α with
  | false => exact matchArr_frame _ _ _ _ _ _ _ _ _ _ hj
  | true =>
    simp only [EnvG.mArr]
    split
    · exact matchArrA_frame _ _ _ _ _ _ _ _ hj
    · exact matchArr_frame _ _ _ _ _ _ _ _ _ _ hj

end Zlib.Inffast.Proofs
