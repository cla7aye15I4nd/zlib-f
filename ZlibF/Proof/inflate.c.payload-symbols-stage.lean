import ZlibF.Proof.«inflate.c.payload-valid-body-stage»
import ZlibF.Proof.Format.Token

namespace ZlibF.Spec.Token
set_option autoImplicit false

/-- The independent bit parser fixes the result of a local valid token. -/
theorem Step.unique
    {L D : List Nat} {dict history : List UInt8}
    {input rest₁ rest₂ : List Bool}
    {next₁ next₂ : List UInt8} {done₁ done₂ : Bool}
    (first : Step L D dict history input rest₁ next₁ done₁)
    (second : Step L D dict history input rest₂ next₂ done₂) :
    rest₁ = rest₂ ∧ next₁ = next₂ ∧ done₁ = done₂ := by
  cases first <;> cases second <;> simp_all <;> omega

/-- The actual local token outcome inherits the original finite block's
exact continuation, by parser determinism. -/
theorem Step.align_symbols
    {L D : List Nat} {dict history : List UInt8}
    {input rest tail : List Bool} {next target : List UInt8}
    {finished : Bool}
    (actual : Step L D dict history input rest next finished)
    (parsed : Symbols L D dict history input tail target) :
    (finished = true → rest = tail ∧ next = target) ∧
    (finished = false → Symbols L D dict next rest tail target) := by
  obtain ⟨otherRest, otherNext, otherDone, canonical, continuation⟩ :=
    symbols_exposes_step L D dict history input tail target parsed
  obtain ⟨restEq, nextEq, doneEq⟩ := actual.unique canonical
  subst otherRest
  subst otherNext
  subst otherDone
  rcases continuation with ⟨done, restFinal, nextFinal⟩ |
    ⟨running, later⟩
  · simp_all
  · simp_all

/-- Every independent valid token supplies exactly the parse facts used by
`inflate_fast_body`; extra fields are irrelevant for literal/end tokens. -/
theorem Step.parse
    {L D : List Nat} {dict history : List UInt8}
    {input rest : List Bool} {next : List UInt8} {done : Bool}
    (token : Step L D dict history input rest next done) :
    ∃ symbol distanceSymbol lengthExtra distanceExtra : Nat,
      ∃ r1 r2 r3 : List Bool,
      decodeSym L input = some (symbol, r1) ∧ symbol ≤ 285 ∧
      (257 ≤ symbol →
        readBits (lengthExtras.getD (symbol - 257) 0) r1 =
          some (lengthExtra, r2)) ∧
      (257 ≤ symbol → decodeSym D r2 = some (distanceSymbol, r3)) ∧
      (257 ≤ symbol → distanceSymbol ≤ 29) ∧
      (257 ≤ symbol →
        readBits (distExtras.getD distanceSymbol 0) r3 =
          some (distanceExtra, rest)) ∧
      (257 ≤ symbol →
        distBases.getD distanceSymbol 0 + distanceExtra ≤
          (dict ++ history).length) := by
  cases token with
  | literal decoded small =>
    exact ⟨_, 0, 0, 0, _, [], [], decoded, by omega,
      (by omega), (by omega), (by omega), (by omega), (by omega)⟩
  | eob decoded =>
    exact ⟨256, 0, 0, 0, _, [], [], decoded, by omega,
      (by omega), (by omega), (by omega), (by omega), (by omega)⟩
  | copy decoded lower upper lengthRead distanceDecoded distanceBound distanceRead fits =>
    exact ⟨_, _, _, _, _, _, _, decoded, upper,
      (fun _ => lengthRead), (fun _ => distanceDecoded),
      (fun _ => distanceBound), (fun _ => distanceRead),
      (fun _ => fits)⟩

#print axioms Step.parse

#print axioms Step.align_symbols

#print axioms Step.unique
end ZlibF.Spec.Token

namespace ZlibF.Math.LZ77Copy
open C ZlibF.Spec Zlib.Inffast.Proofs
set_option autoImplicit false
private theorem payload_written_length (bytes : Array UInt8) (offset count : Nat)
    (hc : count ≤ offset) (hb : offset ≤ bytes.size) :
    (writtenBytes bytes offset count).length = count := by
  simp only [writtenBytes, List.length_take, List.length_drop, Array.length_toList]
  omega

private theorem payload_written_get (bytes : Array UInt8) (offset count i : Nat) :
    (writtenBytes bytes offset count)[i]? =
      if i < count then bytes[offset - count + i]? else none := by
  simp only [writtenBytes, List.getElem?_take, List.getElem?_drop, Array.getElem?_toList]

theorem written_set_append_payload (bytes : Array UInt8) (offset count : Nat)
    (value : UInt8) (hc : count ≤ offset) (hb : offset < bytes.size) :
    writtenBytes (bytes.set! offset value) (offset + 1) (count + 1) =
      writtenBytes bytes offset count ++ [value] := by
  apply List.ext_getElem?
  intro i
  rw [payload_written_get, List.getElem?_append, payload_written_length bytes offset count hc (by omega)]
  have hstart : offset + 1 - (count + 1) = offset - count := by omega
  rw [hstart]
  by_cases hi : i < count
  · have hne : offset ≠ offset - count + i := by omega
    simp [hi, show i < count + 1 by omega, payload_written_get, Array.set!_eq_setIfInBounds, hne]
  · by_cases he : i = count
    · subst i
      have hs : offset - count + count = offset := by omega
      simp [show ¬ count < count by omega, show count < count + 1 by omega, hs,
        Array.set!_eq_setIfInBounds, hb]
    · have hn : ¬ i < count + 1 := by omega
      have hz : i - count ≠ 0 := by omega
      simp [hi, hn, hz]


#print axioms written_set_append_payload
end ZlibF.Math.LZ77Copy
