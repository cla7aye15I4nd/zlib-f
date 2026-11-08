import ZlibF.Math.DeflateSymbolMass
import ZlibF.Math.DeflateTreeForce

/-! # Natural frequency budgets through dummy-leaf writes -/

namespace ZlibF.Math.DeflateSymbols
set_option autoImplicit false

theorem mass_mono {f g : Nat → Nat} {n : Nat} (bound : ∀ k, k < n → f k ≤ g k) :
    mass f n ≤ mass g n := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    have before := ih (fun k hk => bound k (by omega))
    have last := bound n (by omega)
    simp only [mass]
    omega

/-- Writing one dummy frequency adds at most one to a natural leaf sum.
This holds even without freshness of the selected leaf. -/
theorem mass_write_one_le (f : Nat → Nat) (n node : Nat) :
    mass (fun k => if k = node then 1 else f k) n ≤ mass f n + 1 := by
  have bound := mass_mono (n := n) (f := fun k => if k = node then 1 else f k)
    (g := fun k => f k + if k = node then 1 else 0) (by
      intro k _
      by_cases same : k = node <;> simp [same])
  rw [mass_add, mass_single] at bound
  split at bound <;> omega

/-- The exact unsigned-frequency update has the same natural bound. -/
theorem frequency_mass_write_one_le (f : Nat → UInt16) (n node : Nat) :
    mass (fun k => (if k = node then (1 : UInt16) else f k).toNat) n ≤
      mass (fun k => (f k).toNat) n + 1 := by
  have equal := mass_congr (n := n)
    (f := fun k => (if k = node then (1 : UInt16) else f k).toNat)
    (g := fun k => if k = node then 1 else (f k).toNat) (by
      intro k _
      by_cases same : k = node <;> simp only [same, ite_true, ite_false] <;> rfl)
  rw [equal]
  exact mass_write_one_le _ _ _

end ZlibF.Math.DeflateSymbols
