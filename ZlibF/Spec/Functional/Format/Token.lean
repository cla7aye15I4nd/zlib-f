import ZlibF.Spec.Functional.Format.Deflate

/-!
# One independent Huffman-block token

These relations use only the format decoder, extra-bit tables and bytewise
history copying. They do not mention a heap or a decoding-table entry.
A token may be justified even when later, unread tokens are invalid.
-/

namespace ZlibF.Spec.Token

/-- One literal, complete match, or end-of-block symbol. The final Boolean
is true only for end of block. The remaining bits are not required to have
a valid completion; no future input is chosen to justify earlier output. -/
inductive Step (L D : List Nat) (dict : List UInt8) :
    List UInt8 → List Bool → List Bool → List UInt8 → Bool → Prop
  | literal {history : List UInt8} {input rest : List Bool} {symbol : Nat} :
      decodeSym L input = some (symbol, rest) → symbol < 256 →
      Step L D dict history input rest (history ++ [symbol.toUInt8]) false
  | copy {history : List UInt8} {input r1 r2 r3 rest : List Bool}
      {symbol distanceSymbol lengthExtra distanceExtra : Nat} :
      decodeSym L input = some (symbol, r1) → 257 ≤ symbol → symbol ≤ 285 →
      readBits (lengthExtras.getD (symbol - 257) 0) r1 = some (lengthExtra, r2) →
      decodeSym D r2 = some (distanceSymbol, r3) → distanceSymbol ≤ 29 →
      readBits (distExtras.getD distanceSymbol 0) r3 = some (distanceExtra, rest) →
      distBases.getD distanceSymbol 0 + distanceExtra ≤ (dict ++ history).length →
      Step L D dict history input rest
        (copyBack dict (distBases.getD distanceSymbol 0 + distanceExtra)
          (lengthBases.getD (symbol - 257) 0 + lengthExtra) history) false
  | eob {history : List UInt8} {input rest : List Bool} :
      decodeSym L input = some (256, rest) →
      Step L D dict history input rest history true

/-- Independent reasons for rejecting the current token. Invalid-code
rejection rules out every future extension. A too-far match uses the same
dictionary-plus-output bound as `Symbols.copy`. -/
inductive Rejected (L D : List Nat) (dict history : List UInt8) : List Bool → Prop
  | length {input : List Bool} :
      (∀ more : List Bool,
        ¬ ∃ (symbol : Nat) (rest : List Bool),
          decodeSym L (input ++ more) = some (symbol, rest) ∧ symbol ≤ 285) →
      Rejected L D dict history input
  | distance {input r1 r2 : List Bool} {symbol lengthExtra : Nat} :
      decodeSym L input = some (symbol, r1) → 257 ≤ symbol → symbol ≤ 285 →
      readBits (lengthExtras.getD (symbol - 257) 0) r1 = some (lengthExtra, r2) →
      (∀ more : List Bool,
        ¬ ∃ (distanceSymbol : Nat) (rest : List Bool),
          decodeSym D (r2 ++ more) = some (distanceSymbol, rest) ∧ distanceSymbol ≤ 29) →
      Rejected L D dict history input
  | tooFar {input r1 r2 r3 rest : List Bool}
      {symbol distanceSymbol lengthExtra distanceExtra : Nat} :
      decodeSym L input = some (symbol, r1) → 257 ≤ symbol → symbol ≤ 285 →
      readBits (lengthExtras.getD (symbol - 257) 0) r1 = some (lengthExtra, r2) →
      decodeSym D r2 = some (distanceSymbol, r3) → distanceSymbol ≤ 29 →
      readBits (distExtras.getD distanceSymbol 0) r3 = some (distanceExtra, rest) →
      (dict ++ history).length < distBases.getD distanceSymbol 0 + distanceExtra →
      Rejected L D dict history input

/-- A successful local token composes with the original format relation.
An end token itself supplies the original end-of-block constructor. -/
def Goal.step_composes_symbols : Prop :=
  ∀ (L D : List Nat) (dict history : List UInt8) (input rest : List Bool)
    (next : List UInt8) (finished : Bool),
    Step L D dict history input rest next finished →
    (finished = true → next = history ∧ Symbols L D dict history input rest next) ∧
    (finished = false → ∀ (tail : List Bool) (output : List UInt8),
      Symbols L D dict next rest tail output → Symbols L D dict history input tail output)

/-- Every original Huffman-block derivation exposes one such token.
Together with composition, this prevents weakening the format by using
the local token relation as the implementation's postcondition. -/
def Goal.symbols_exposes_step : Prop :=
  ∀ (L D : List Nat) (dict history : List UInt8) (input tail : List Bool)
    (output : List UInt8),
    Symbols L D dict history input tail output →
    ∃ (rest : List Bool) (next : List UInt8) (finished : Bool),
      Step L D dict history input rest next finished ∧
      ((finished = true ∧ rest = tail ∧ next = output) ∨
       (finished = false ∧ Symbols L D dict next rest tail output))

/-- Every stated rejection contradicts the original format relation.
No table predicate, heap condition or valid-input assumption is needed. -/
def Goal.rejected_has_no_symbols : Prop :=
  ∀ (L D : List Nat) (dict history : List UInt8) (input : List Bool),
    Rejected L D dict history input →
    ∀ (rest : List Bool) (output : List UInt8),
      ¬ Symbols L D dict history input rest output

end ZlibF.Spec.Token
