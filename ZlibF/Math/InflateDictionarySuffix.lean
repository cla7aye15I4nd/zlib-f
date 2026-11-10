import ZlibF.Proof.Format.Token
import ZlibF.Proof.Format.Deflate
import ZlibF.Math.LZ77History

namespace ZlibF.Math.InflateDictionarySuffix
open ZlibF.Spec ZlibF.Math.LZ77History
set_option autoImplicit false

private theorem distance_base_positive : ∀ i : Fin 30, 1 ≤ distBases.getD i.val 0 := by
  decide +kernel

/-- Enlarging a dictionary only by adding older bytes preserves every
valid local token and its exact output. Existing distance validity prevents
that token from observing the additional older prefix. -/
theorem token_step
    {L D : List Nat} {small large history next : List UInt8} {input rest : List Bool} {ended : Bool}
    (suffix : small <:+ large) (step : Token.Step L D small history input rest next ended) :
    Token.Step L D large history input rest next ended := by
  cases step with
  | literal decoded below => exact .literal decoded below
  | eob decoded => exact .eob decoded
  | @copy _ _ _ _ symbol distance extraLength extraDistance decoded lower upper
      lengthRead distanceDecode distanceBound distanceRead fits =>
    have positive := distance_base_positive ⟨distance, by omega⟩
    change 1 ≤ distBases.getD distance 0 at positive
    have suffix' : small <:+ large ++ [] := by simpa only [List.append_nil] using suffix
    have bound : distBases.getD distance 0 + extraDistance ≤ small.length + history.length := by
      simpa only [List.length_append] using fits
    have same := retained_history_agrees large [] history small
      (distBases.getD distance 0 + extraDistance) (lengthBases.getD (symbol - 257) 0 + extraLength)
      suffix' (by omega) bound
    simp only [List.nil_append] at same
    have largeBound : distBases.getD distance 0 + extraDistance ≤ (large ++ history).length := by
      have size := suffix.length_le
      simp only [List.length_append]
      omega
    simpa only [same] using Token.Step.copy decoded lower upper lengthRead distanceDecode distanceBound distanceRead largeBound

theorem symbols
    {L D : List Nat} {small large history output : List UInt8} {input rest : List Bool}
    (suffix : small <:+ large) (parsed : Symbols L D small history input rest output) :
    Symbols L D large history input rest output := by
  induction parsed with
  | eob decoded => exact .eob decoded
  | lit decoded below continuation ih => exact .lit decoded below ih
  | @copy h inp r1 r2 r3 r4 tail symbol distance extraLength extraDistance out decoded lower upper
      lengthRead distanceDecode distanceBound distanceRead fits continuation ih =>
    have positive := distance_base_positive ⟨distance, by omega⟩
    change 1 ≤ distBases.getD distance 0 at positive
    have suffix' : small <:+ large ++ [] := by simpa only [List.append_nil] using suffix
    have bound : distBases.getD distance 0 + extraDistance ≤ small.length + h.length := by
      simp only [List.length_append] at fits
      omega
    have same := retained_history_agrees large [] h small
      (distBases.getD distance 0 + extraDistance) (lengthBases.getD (symbol - 257) 0 + extraLength)
      suffix' (by omega) bound
    simp only [List.nil_append] at same
    apply Symbols.copy decoded lower upper lengthRead distanceDecode distanceBound distanceRead
    · have size := suffix.length_le
      simp only [List.length_append]
      omega
    · rw [same]
      exact ih

theorem body
    {small large history output : List UInt8} {kind : Nat} {input rest : List Bool}
    (suffix : small <:+ large) (parsed : Body small kind history input rest output) :
    Body large kind history input rest output := by
  cases parsed with
  | stored first second complement bytes => exact .stored first second complement bytes
  | fixed parsed => exact .fixed (symbols suffix parsed)
  | dynamic a b c d e f g h i j parsed => exact .dynamic a b c d e f g h i j (symbols suffix parsed)

theorem blocks
    {small large history output : List UInt8} {input rest : List Bool}
    (suffix : small <:+ large) (parsed : Blocks small history input rest output) :
    Blocks large history input rest output := by
  induction parsed with
  | last final kind parsed => exact .last final kind (body suffix parsed)
  | more final kind parsed continuation ih => exact .more final kind (body suffix parsed) ih

theorem deflate_prefix
    {small large input tail output : List UInt8}
    (suffix : small <:+ large) (parsed : Deflate.Prefix small input tail output) :
    Deflate.Prefix large input tail output := by
  obtain ⟨rest, parsed, padding⟩ := parsed
  exact ⟨rest, blocks suffix parsed, padding⟩

/-- The dictionary retained for a smaller advertised window is a suffix
of that retained for a larger configured window. This is an independent
bridge for valid-source claims; it changes no format or public target. -/
theorem retained_suffix (dictionary : List UInt8) {small large : Nat} (capacity : small ≤ large) :
    dictionary.drop (dictionary.length - small) <:+ dictionary.drop (dictionary.length - large) := by
  exact List.drop_suffix_drop_left _ (by omega)

#print axioms token_step
#print axioms symbols
#print axioms body
#print axioms blocks
#print axioms deflate_prefix
#print axioms retained_suffix
end ZlibF.Math.InflateDictionarySuffix
