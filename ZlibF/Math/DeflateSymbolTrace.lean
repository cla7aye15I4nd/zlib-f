import ZlibF.Math.DeflateSymbols
import ZlibF.Spec.Format.Deflate

/-! # Buffered symbols reproduce the logical input prefix

Match meaning permits overlap. The decoding result uses the independent
format's bytewise copyBack, not the compressor's window-copy procedure.
-/

namespace ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The literal value or every copied byte agrees with the input at pos. -/
def Symbol.Meaning (input : Nat → UInt8) (pos : Nat) (s : Symbol) : Prop :=
  s.Valid ∧ if s.distance = 0 then s.value = (input pos).toNat else
    s.distance ≤ pos ∧ ∀ j, j < s.value + 3 →
      input (pos - s.distance + j) = input (pos + j)

/-- Symbols are interpreted in their real order, at cumulative byte positions. -/
inductive Trace (input : Nat → UInt8) (base : Nat) : List Symbol → Prop
  | empty : Trace input base []
  | snoc {xs : List Symbol} {s : Symbol} : Trace input base xs →
      s.Meaning input (base + represented xs) → Trace input base (xs ++ [s])

theorem Symbol.meaning_literal (input : Nat → UInt8) (pos : Nat) :
    (Symbol.mk 0 (input pos).toNat).Meaning input pos := by
  exact ⟨⟨by change 0 ≤ 32768; decide, (input pos).toNat_lt⟩, rfl⟩

theorem Symbol.Meaning.extend {input next : Nat → UInt8} {pos limit : Nat} {s : Symbol}
    (meaning : s.Meaning input pos) (bound : pos + s.bytes ≤ limit)
    (agrees : ∀ i, i < limit → next i = input i) : s.Meaning next pos := by
  unfold Symbol.Meaning at meaning ⊢
  refine ⟨meaning.1, ?_⟩
  by_cases literal : s.distance = 0
  · simp only [literal, if_true] at meaning ⊢
    have size : s.bytes = 1 := by simp [Symbol.bytes, literal]
    rw [agrees pos (by omega)]
    exact meaning.2
  · simp only [literal, if_false] at meaning ⊢
    have size : s.bytes = s.value + 3 := by simp [Symbol.bytes, literal]
    refine ⟨meaning.2.1, ?_⟩
    intro j hj
    rw [agrees _ (by omega), agrees _ (by omega)]
    exact meaning.2.2 j hj

theorem Trace.extend {input next : Nat → UInt8} {base limit : Nat} {xs : List Symbol}
    (trace : Trace input base xs) (bound : base + represented xs ≤ limit)
    (agrees : ∀ i, i < limit → next i = input i) : Trace next base xs := by
  induction trace with
  | empty => exact .empty
  | @snoc xs s trace meaning ih =>
    rw [represented_snoc] at bound
    exact .snoc (ih (by omega)) (meaning.extend (by omega) agrees)

def inputPrefix (input : Nat → UInt8) (n : Nat) : List UInt8 := (List.range n).map input

theorem input_prefix_length (input : Nat → UInt8) (n : Nat) : (inputPrefix input n).length = n := by
  simp [inputPrefix]

theorem input_prefix_succ (input : Nat → UInt8) (n : Nat) :
    inputPrefix input (n + 1) = inputPrefix input n ++ [input n] := by
  simp [inputPrefix, List.range_succ]

theorem input_prefix_getD (input : Nat → UInt8) (n i : Nat) (bound : i < n) :
    (inputPrefix input n).getD i 0 = input i := by
  simp [inputPrefix, List.getD_eq_getElem?_getD, bound]

/-- The independent sequential back-reference copy reproduces every
input byte, including bytes whose source is within the same match. -/
theorem copy_back_input (input : Nat → UInt8) (distance count : Nat) (positive : 1 ≤ distance) :
    ∀ pos, distance ≤ pos →
      (∀ j, j < count → input (pos - distance + j) = input (pos + j)) →
      ZlibF.Spec.copyBack [] distance count (inputPrefix input pos) = inputPrefix input (pos + count) := by
  induction count with
  | zero => intro pos _ _; simp [ZlibF.Spec.copyBack]
  | succ count ih =>
    intro pos bound matching
    have source : (inputPrefix input pos).getD (pos - distance) 0 = input pos := by
      rw [input_prefix_getD input pos _ (by omega)]
      simpa using matching 0 (by omega)
    rw [ZlibF.Spec.copyBack]
    simp only [List.nil_append, input_prefix_length, source, ← input_prefix_succ]
    have next := ih (pos + 1) (by omega) (by
      intro j hj
      have matched := matching (j + 1) (by omega)
      have left : pos - distance + (j + 1) = pos + 1 - distance + j := by omega
      have right : pos + (j + 1) = pos + 1 + j := by omega
      rwa [left, right] at matched)
    simpa only [Nat.add_assoc, Nat.add_comm 1 count] using next

def expandSymbol (history : List UInt8) (s : Symbol) : List UInt8 :=
  if s.distance = 0 then history ++ [UInt8.ofNat s.value]
  else ZlibF.Spec.copyBack [] s.distance (s.value + 3) history

def expandSymbols (xs : List Symbol) (history : List UInt8) : List UInt8 := xs.foldl expandSymbol history

theorem meaning_expands {input : Nat → UInt8} {pos : Nat} {s : Symbol}
    (meaning : s.Meaning input pos) :
    expandSymbol (inputPrefix input pos) s = inputPrefix input (pos + s.bytes) := by
  by_cases literal : s.distance = 0
  · have value : UInt8.ofNat s.value = input pos := by
      have equal : s.value = (input pos).toNat := by simpa [Symbol.Meaning, literal] using meaning.2
      rw [equal]
      exact UInt8.ofNat_toNat
    simp [expandSymbol, literal, Symbol.bytes, value, input_prefix_succ]
  · have copy : s.distance ≤ pos ∧ ∀ j, j < s.value + 3 →
        input (pos - s.distance + j) = input (pos + j) := by
      simpa only [literal, if_false] using meaning.2
    simpa only [expandSymbol, literal, if_false, Symbol.bytes] using
      copy_back_input input s.distance (s.value + 3) (by omega) pos copy.1 copy.2

/-- A stored-symbol trace decodes to the actual input prefix under the
independent format copy, not only to a byte count of the same length. -/
theorem Trace.expands {input : Nat → UInt8} {base : Nat} {xs : List Symbol}
    (trace : Trace input base xs) :
    expandSymbols xs (inputPrefix input base) = inputPrefix input (base + represented xs) := by
  induction trace with
  | empty => simp [expandSymbols, represented]
  | @snoc xs s trace meaning ih =>
    simp only [expandSymbols, List.foldl_append, List.foldl_cons, List.foldl_nil] at ih ⊢
    rw [ih, meaning_expands meaning, represented_snoc, Nat.add_assoc]

end ZlibF.Math.DeflateSymbols
