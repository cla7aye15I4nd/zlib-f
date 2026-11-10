import ZlibF.Proof.«inflate.c.payload-loop-token-stage»
import ZlibF.Math.«code-length-prefix»

namespace ZlibF.Spec.Token
open ZlibF.Spec Zlib.Inffast.Proofs
set_option autoImplicit false
set_option maxRecDepth 8192

private theorem decoded_rest_strict
    {lens : List Nat} {input rest : List Bool} {symbol : Nat}
    (decoded : decodeSym lens input = some (symbol, rest)) :
    rest.length < input.length := by
  obtain ⟨_, positive, _, suffix⟩ :=
    Zlib.Inftrees.Proofs.decoded_symbol_prefix decoded
  rw [suffix, List.length_drop]
  have width : lens.getD symbol 0 ≤ input.length := by
    have pref := (Zlib.Inftrees.Proofs.decoded_symbol_prefix decoded).2.2.1
    have length : (codeOf lens symbol).length = lens.getD symbol 0 := by
      simp only [codeOf, ZlibF.Spec.Proofs.natToBitsMSB_length]
    rw [← length]
    exact List.IsPrefix.length_le pref
  omega

private theorem read_rest_le
    {n : Nat} {input rest : List Bool} {value : Nat}
    (read : readBits n input = some (value, rest)) :
    rest.length ≤ input.length := by
  obtain ⟨_, source⟩ := ZlibF.Math.CodeLengthPrefix.read_word read
  rw [source]
  simp only [List.length_append]
  omega

private theorem append_prefix
    {a b c : List Bool}
    (first : ∃ p : List Bool, a = p ++ b)
    (second : ∃ q : List Bool, b = q ++ c) :
    ∃ p : List Bool, a = p ++ c := by
  obtain ⟨p, hp⟩ := first
  obtain ⟨q, hq⟩ := second
  exact ⟨p ++ q, by rw [hp, hq, List.append_assoc]⟩

/-- Every valid independent symbol consumes at least one input bit. -/
theorem Step.rest_strict
    {L D : List Nat} {dict history : List UInt8}
    {input rest : List Bool} {next : List UInt8} {done : Bool}
    (step : Step L D dict history input rest next done) :
    rest.length < input.length := by
  cases step with
  | literal decoded _ => exact decoded_rest_strict decoded
  | eob decoded => exact decoded_rest_strict decoded
  | copy decoded _ _ lengthRead distanceDecoded _ distanceRead _ =>
      have first := decoded_rest_strict decoded
      have second := read_rest_le lengthRead
      have third := decoded_rest_strict distanceDecoded
      have fourth := read_rest_le distanceRead
      omega

/-- A valid token has a concrete nonempty consumed prefix, including both
Huffman words and any extra bits of a match. -/
theorem Step.consumed_prefix
    {L D : List Nat} {dict history : List UInt8}
    {input rest : List Bool} {next : List UInt8} {done : Bool}
    (step : Step L D dict history input rest next done) :
    ∃ consumed : List Bool,
      consumed ≠ [] ∧ input = consumed ++ rest := by
  have sourcePrefix : ∃ consumed : List Bool, input = consumed ++ rest := by
    cases step with
    | literal decoded _ =>
        exact ⟨_, ZlibF.Math.CodeLengthPrefix.decoded_word decoded⟩
    | eob decoded =>
        exact ⟨_, ZlibF.Math.CodeLengthPrefix.decoded_word decoded⟩
    | copy decoded _ _ lengthRead distanceDecoded _ distanceRead _ =>
        have first := ZlibF.Math.CodeLengthPrefix.decoded_word decoded
        obtain ⟨_, second⟩ := ZlibF.Math.CodeLengthPrefix.read_word lengthRead
        have third := ZlibF.Math.CodeLengthPrefix.decoded_word distanceDecoded
        obtain ⟨_, fourth⟩ := ZlibF.Math.CodeLengthPrefix.read_word distanceRead
        exact append_prefix
          (append_prefix (append_prefix ⟨_, first⟩ ⟨_, second⟩)
            ⟨_, third⟩)
          ⟨_, fourth⟩
  obtain ⟨consumed, source⟩ := sourcePrefix
  refine ⟨consumed, ?_, source⟩
  intro empty
  have strict := step.rest_strict
  rw [source, empty] at strict
  simp only [List.nil_append] at strict
  omega

/-- The token's bit count is an exact positive drop of the original source. -/
theorem Step.consumed_count
    {L D : List Nat} {dict history : List UInt8}
    {input rest : List Bool} {next : List UInt8} {done : Bool}
    (step : Step L D dict history input rest next done) :
    ∃ count : Nat,
      0 < count ∧ count ≤ input.length ∧
      rest = input.drop count ∧ input.length = count + rest.length := by
  obtain ⟨consumed, nonempty, source⟩ := step.consumed_prefix
  refine ⟨consumed.length, ?_, ?_, ?_, ?_⟩
  · cases consumed with
    | nil => exact False.elim (nonempty rfl)
    | cons _ _ => simp
  · rw [source, List.length_append]
    omega
  · rw [source, List.drop_left]
  · rw [source, List.length_append]

/-- A complete Huffman-symbol sequence consumes a nonempty bit prefix. -/
theorem Symbols.input_strict
    {L D : List Nat} {dict history : List UInt8}
    {input rest : List Bool} {output : List UInt8}
    (parsed : Symbols L D dict history input rest output) :
    rest.length < input.length := by
  induction parsed with
  | eob decoded => exact decoded_rest_strict decoded
  | lit decoded _ _ ih =>
      have first := decoded_rest_strict decoded
      omega
  | copy decoded lower upper lengthRead distanceDecoded distanceBound
      distanceRead fits _ ih =>
      have first := decoded_rest_strict decoded
      have second := read_rest_le lengthRead
      have third := decoded_rest_strict distanceDecoded
      have fourth := read_rest_le distanceRead
      omega

#print axioms Step.rest_strict
#print axioms Step.consumed_prefix
#print axioms Step.consumed_count
#print axioms Symbols.input_strict
end ZlibF.Spec.Token
