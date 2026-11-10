import ZlibF.Math.DeflateSymbols

/-! # Every buffered symbol represents at least one input byte -/

namespace ZlibF.Math.DeflateSymbols
set_option autoImplicit false

theorem symbol_bytes_positive (s : Symbol) : 1 ≤ s.bytes := by
  unfold Symbol.bytes
  split <;> omega

theorem length_le_represented (xs : List Symbol) : xs.length ≤ represented xs := by
  induction xs with
  | nil => simp [represented]
  | cons s xs ih =>
    have positive := symbol_bytes_positive s
    simp only [List.length_cons, represented]
    omega

end ZlibF.Math.DeflateSymbols
