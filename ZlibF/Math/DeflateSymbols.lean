import Std

/-! # Symbols, frequencies and the bytes represented by a deflate block -/

namespace ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Distance zero denotes a literal. A match stores its length minus three. -/
structure Symbol where
  distance : Nat
  value : Nat
  deriving DecidableEq

def Symbol.Valid (s : Symbol) : Prop := s.distance ≤ 32768 ∧ s.value < 256

def Symbol.bytes (s : Symbol) : Nat := if s.distance = 0 then 1 else s.value + 3

def Symbol.literalKey (lengthCode : Nat → Nat) (s : Symbol) : Nat :=
  if s.distance = 0 then s.value else lengthCode s.value + 257

def Symbol.distanceKey (distanceCode : Nat → Nat) (s : Symbol) : Option Nat :=
  if s.distance = 0 then none else some (distanceCode (s.distance - 1))

def represented : List Symbol → Nat
  | [] => 0
  | s :: rest => s.bytes + represented rest

def countKey {α : Type} (key : α → Option Nat) : List α → Nat → Nat
  | [], _ => 0
  | s :: rest, k => (if key s = some k then 1 else 0) + countKey key rest k

def literalFrequency (lengthCode : Nat → Nat) (symbols : List Symbol) (k : Nat) : Nat :=
  (if k = 256 then 1 else 0) + countKey (fun s => some (s.literalKey lengthCode)) symbols k

def distanceFrequency (distanceCode : Nat → Nat) (symbols : List Symbol) (k : Nat) : Nat :=
  countKey (Symbol.distanceKey distanceCode) symbols k

theorem represented_append (xs ys : List Symbol) :
    represented (xs ++ ys) = represented xs + represented ys := by
  induction xs with
  | nil => simp [represented]
  | cons s xs ih => simp [represented, ih, Nat.add_assoc]

theorem represented_snoc (xs : List Symbol) (s : Symbol) :
    represented (xs ++ [s]) = represented xs + s.bytes := by
  simp [represented_append, represented]

theorem symbol_bytes_le {s : Symbol} (valid : s.Valid) : s.bytes ≤ 258 := by
  unfold Symbol.bytes
  split <;> have := valid.2 <;> omega

/-- The bound depends on the number of stored symbols, not on a caller's
claim about the signed block position. -/
theorem represented_le {xs : List Symbol} (valid : ∀ s ∈ xs, s.Valid) :
    represented xs ≤ 258 * xs.length := by
  induction xs with
  | nil => simp [represented]
  | cons s xs ih =>
    have first := symbol_bytes_le (valid s (by simp))
    have rest := ih (fun t member => valid t (by simp [member]))
    simp only [represented, List.length_cons, Nat.mul_add, Nat.mul_one]
    omega

theorem countKey_append {α : Type} (key : α → Option Nat) (xs ys : List α) (k : Nat) :
    countKey key (xs ++ ys) k = countKey key xs k + countKey key ys k := by
  induction xs with
  | nil => simp [countKey]
  | cons s xs ih => simp [countKey, ih, Nat.add_assoc]

theorem countKey_le {α : Type} (key : α → Option Nat) (xs : List α) (k : Nat) :
    countKey key xs k ≤ xs.length := by
  induction xs with
  | nil => simp [countKey]
  | cons s xs ih => simp only [countKey, List.length_cons]; split <;> omega

theorem literal_frequency_snoc (lc : Nat → Nat) (xs : List Symbol) (s : Symbol) (k : Nat) :
    literalFrequency lc (xs ++ [s]) k =
      literalFrequency lc xs k + if s.literalKey lc = k then 1 else 0 := by
  simp [literalFrequency, countKey_append, countKey, Nat.add_assoc]

theorem distance_frequency_snoc (dc : Nat → Nat) (xs : List Symbol) (s : Symbol) (k : Nat) :
    distanceFrequency dc (xs ++ [s]) k =
      distanceFrequency dc xs k + if s.distanceKey dc = some k then 1 else 0 := by
  simp [distanceFrequency, countKey_append, countKey]

theorem literal_frequency_le (lc : Nat → Nat) (xs : List Symbol) (k : Nat) :
    literalFrequency lc xs k ≤ xs.length + 1 := by
  have bound := countKey_le (fun s => some (s.literalKey lc)) xs k
  unfold literalFrequency
  split <;> omega

theorem distance_frequency_le (dc : Nat → Nat) (xs : List Symbol) (k : Nat) :
    distanceFrequency dc xs k ≤ xs.length := countKey_le _ _ _

end ZlibF.Math.DeflateSymbols
