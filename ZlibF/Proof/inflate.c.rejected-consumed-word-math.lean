import ZlibF.Proof.«inflate.c.fast-bad-word-interface»
import ZlibF.Math.LZ77History
namespace Zlib.Inflate.Proofs.FastArbitraryBody
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inffast.Spec Zlib.Inftrees Zlib.Inffast.Proofs
open ZlibF.Math.CodeLengthPrefix ZlibF.Math.InflateDecode
set_option autoImplicit false
set_option maxRecDepth 8192

/-- A real length code and extra read prepend a finite causal word to an
invalid distance word. Every later suffix is still rejected. -/
theorem distance_rejected_word
    {L D : List Nat} {dict history : List UInt8} {input r1 r2 rest badWord : List Bool}
    {symbol lengthExtra : Nat}
    (lengths : Acceptable .litLen L)
    (decoded : decodeSym L input = some (symbol, r1)) (lower : 257 ≤ symbol) (upper : symbol ≤ 285)
    (read : readBits (lengthExtras.getD (symbol - 257) 0) r1 = some (lengthExtra, r2))
    (source : r2 = badWord ++ rest)
    (invalid : ∀ future : List Bool, ¬ ∃ distanceSymbol tail,
      decodeSym D (badWord ++ future) = some (distanceSymbol, tail) ∧ distanceSymbol ≤ 29) :
    ∃ word, input = word ++ rest ∧ ∀ future : List Bool, Token.Rejected L D dict history (word ++ future) := by
  let word := codeOf L symbol ++ bitsOfNat lengthExtra (lengthExtras.getD (symbol - 257) 0) ++ badWord
  obtain ⟨bound, readSource⟩ := read_word read
  have nonzero := (Zlib.Inftrees.Proofs.decoded_symbol_prefix decoded).2.1
  refine ⟨word, ?_, ?_⟩
  · rw [decoded_word decoded, readSource, source]
    simp only [word, List.append_assoc]
  · intro future
    dsimp only [word]
    simp only [List.append_assoc]
    apply Token.Rejected.distance (decode_canonical_word lengths _ nonzero _) lower upper
      (ZlibF.Math.TokenSuffix.read_consumed_word _ _ bound _)
    intro later
    simpa only [List.append_assoc] using invalid (future ++ later)

/-- All bits of a too-far match form its finite rejected word. The saved
history bound is the real checked distance bound, not a validity premise. -/
theorem too_far_rejected_word
    {L D : List Nat} {dict history : List UInt8} {input r1 r2 r3 rest : List Bool}
    {symbol distanceSymbol lengthExtra distanceExtra : Nat}
    (lengths : Acceptable .litLen L) (distances : Acceptable .dist D)
    (decoded : decodeSym L input = some (symbol, r1)) (lower : 257 ≤ symbol) (upper : symbol ≤ 285)
    (lengthRead : readBits (lengthExtras.getD (symbol - 257) 0) r1 = some (lengthExtra, r2))
    (distanceDecoded : decodeSym D r2 = some (distanceSymbol, r3)) (distanceBound : distanceSymbol ≤ 29)
    (distanceRead : readBits (distExtras.getD distanceSymbol 0) r3 = some (distanceExtra, rest))
    (unavailable : (dict ++ history).length < distBases.getD distanceSymbol 0 + distanceExtra) :
    ∃ word, input = word ++ rest ∧ ∀ future : List Bool, Token.Rejected L D dict history (word ++ future) := by
  let word := codeOf L symbol ++ bitsOfNat lengthExtra (lengthExtras.getD (symbol - 257) 0) ++
    codeOf D distanceSymbol ++ bitsOfNat distanceExtra (distExtras.getD distanceSymbol 0)
  obtain ⟨lenBound, lenSource⟩ := read_word lengthRead
  obtain ⟨distBound, distSource⟩ := read_word distanceRead
  have lenNonzero := (Zlib.Inftrees.Proofs.decoded_symbol_prefix decoded).2.1
  have distNonzero := (Zlib.Inftrees.Proofs.decoded_symbol_prefix distanceDecoded).2.1
  refine ⟨word, ?_, ?_⟩
  · rw [decoded_word decoded, lenSource, decoded_word distanceDecoded, distSource]
    simp only [word, List.append_assoc]
  · intro future
    dsimp only [word]
    simp only [List.append_assoc]
    exact Token.Rejected.tooFar (decode_canonical_word lengths _ lenNonzero _) lower upper
      (ZlibF.Math.TokenSuffix.read_consumed_word _ _ lenBound _) (decode_canonical_word distances _ distNonzero _)
      distanceBound (ZlibF.Math.TokenSuffix.read_consumed_word _ _ distBound _) unavailable

/-- Physical raw input accounting turns an exact whole-stream word split
into the credited held/raw split required by the public causal ledger. -/
theorem rejected_word_credit
    {slow finalSlow : IL} {word : List Bool} {raw : List UInt8} {used : Nat}
    (source : stream slow raw = word ++ stream finalSlow (raw.drop used)) :
    natBits slow.bits.toNat slow.hold.toNat ++ bytesBits (raw.take used) =
      word ++ natBits finalSlow.bits.toNat finalSlow.hold.toNat := by
  have split : bytesBits raw = bytesBits (raw.take used) ++ bytesBits (raw.drop used) := by
    rw [← bytesBits_append, List.take_append_drop]
  change natBits slow.bits.toNat slow.hold.toNat ++ bytesBits raw =
    word ++ (natBits finalSlow.bits.toNat finalSlow.hold.toNat ++ bytesBits (raw.drop used)) at source
  rw [split, ← List.append_assoc, ← List.append_assoc] at source
  exact List.append_cancel_right source

/-- Rejection on the exact retained physical history also rejects the full
logical history: format distances are at most the retained capacity. -/
theorem rejected_retained_context
    {L D : List Nat} {dict past current : List UInt8} {input : List Bool}
    (rejected : Token.Rejected L D ((dict ++ past).drop ((dict ++ past).length - 32768)) current input) :
    Token.Rejected L D dict (past ++ current) input := by
  cases rejected with
  | length invalid => exact .length invalid
  | distance decoded lower upper read invalid => exact .distance decoded lower upper read invalid
  | @tooFar r1 r2 r3 rest symbol distanceSymbol lengthExtra distanceExtra decoded lower upper lengthRead distanceDecoded distanceBound distanceRead unavailable =>
    apply Token.Rejected.tooFar decoded lower upper lengthRead distanceDecoded distanceBound distanceRead
    have extraBound := (read_word distanceRead).1
    obtain ⟨_positive, _extra, budget⟩ := FastArbitrarySource.format_distance_scalar_bounds _ distanceBound
    have checks := ZlibF.Math.LZ77History.window_distance_check_agrees dict past current 32768 (distBases.getD distanceSymbol 0 + distanceExtra) (by omega)
    simpa only [List.append_assoc] using checks.mp unavailable

#print axioms distance_rejected_word
#print axioms too_far_rejected_word
#print axioms rejected_word_credit
#print axioms rejected_retained_context
end Zlib.Inflate.Proofs.FastArbitraryBody
