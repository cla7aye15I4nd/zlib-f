import ZlibF.Math.«code-length-prefix»
import ZlibF.Proof.Format.Token
import ZlibF.Proof.«inflate.c.main.macros»

namespace ZlibF.Math.TokenSuffix
open ZlibF.Spec Zlib.Inffast.Proofs ZlibF.Math.InflateDecode
open ZlibF.Math.CodeLengthPrefix
set_option autoImplicit false

 theorem read_consumed_word (width value : Nat) (bound : value < 2 ^ width) (rest : List Bool) :
    readBits width (bitsOfNat value width ++ rest) = some (value, rest) := by
  simpa only [Nat.mod_eq_of_lt bound, Nat.sub_self, bitsOfNat_zero, List.nil_append] using
    readBits_bitsOfNat width width value rest (Nat.le_refl _)

/-- A genuinely accepted token determines a finite consumed word. Its
meaning holds for every trailing suffix, independent of future validity. -/
 theorem step_consumed_word
    {L D : List Nat} {dict history target : List UInt8} {input rest : List Bool} {last : Bool}
    (lengths : Acceptable .litLen L) (distances : Acceptable .dist D)
    (step : Token.Step L D dict history input rest target last) :
    ∃ word : List Bool, input = word ++ rest ∧
      ∀ suffix, Token.Step L D dict history (word ++ suffix) suffix target last := by
  cases step with
  | literal decoded small =>
    have nonzero := (Zlib.Inftrees.Proofs.decoded_symbol_prefix decoded).2.1
    exact ⟨_, decoded_word decoded, fun suffix =>
      .literal (decode_canonical_word lengths _ nonzero suffix) small⟩
  | eob decoded =>
    have nonzero := (Zlib.Inftrees.Proofs.decoded_symbol_prefix decoded).2.1
    exact ⟨_, decoded_word decoded, fun suffix => .eob (decode_canonical_word lengths _ nonzero suffix)⟩
  | @copy r1 r2 r3 _ symbol ds lv dv decoded lower upper lengthRead distanceDecoded distanceBound distanceRead fits =>
    have lenNonzero := (Zlib.Inftrees.Proofs.decoded_symbol_prefix decoded).2.1
    have distNonzero := (Zlib.Inftrees.Proofs.decoded_symbol_prefix distanceDecoded).2.1
    obtain ⟨lvBound, lengthSource⟩ := read_word lengthRead
    obtain ⟨dvBound, distanceSource⟩ := read_word distanceRead
    have source := decoded_word decoded
    rw [lengthSource, decoded_word distanceDecoded, distanceSource] at source
    let word := codeOf L symbol ++ bitsOfNat lv (lengthExtras.getD (symbol - 257) 0) ++
      codeOf D ds ++ bitsOfNat dv (distExtras.getD ds 0)
    refine ⟨word, by simpa only [word, List.append_assoc] using source, ?_⟩
    intro suffix
    simp only [word, List.append_assoc]
    exact .copy (decode_canonical_word lengths _ lenNonzero _) lower upper
      (read_consumed_word _ _ lvBound _) (decode_canonical_word distances _ distNonzero _)
      distanceBound (read_consumed_word _ _ dvBound _) fits

/-- Untouched caller input is cancelled from both sides of an actual
accepted token. It need not remain available after a legal rebuffer. -/
 theorem step_cancel_suffix
    {L D : List Nat} {dict history target : List UInt8} {input rest suffix : List Bool} {last : Bool}
    (lengths : Acceptable .litLen L) (distances : Acceptable .dist D)
    (step : Token.Step L D dict history (input ++ suffix) (rest ++ suffix) target last) :
    Token.Step L D dict history input rest target last := by
  obtain ⟨word, source, parsed⟩ := step_consumed_word lengths distances step
  rw [← List.append_assoc] at source
  have source' := List.append_cancel_right source
  rw [source']
  exact parsed rest

/-- The finite accepted word is stable under every future buffer. -/
 theorem step_append_suffix
    {L D : List Nat} {dict history target : List UInt8} {input rest : List Bool} {last : Bool}
    (lengths : Acceptable .litLen L) (distances : Acceptable .dist D)
    (step : Token.Step L D dict history input rest target last) (suffix : List Bool) :
    Token.Step L D dict history (input ++ suffix) (rest ++ suffix) target last := by
  obtain ⟨word, source, parsed⟩ := step_consumed_word lengths distances step
  rw [source, List.append_assoc]
  exact parsed _

#print axioms read_consumed_word
#print axioms step_consumed_word
#print axioms step_cancel_suffix
#print axioms step_append_suffix
end ZlibF.Math.TokenSuffix

namespace Zlib.Inflate.Proofs.SlowReverseToken
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec
set_option autoImplicit false

/-- Exact raw-used accounting trims the current byte buffer from a real
whole-stream token, retaining only actual pulled bytes and held bits. -/
 theorem token_step_held_raw_prefix
    {L D : List Nat} {dict history target : List UInt8} {l regs : IL} {bs : List UInt8} {used : Nat} {last : Bool}
    (lengths : Acceptable .litLen L) (distances : Acceptable .dist D)
    (step : Token.Step L D dict history (stream l bs) (stream regs (bs.drop used)) target last) :
    Token.Step L D dict history (natBits l.bits.toNat l.hold.toNat ++ bytesBits (bs.take used))
      (natBits regs.bits.toNat regs.hold.toNat) target last := by
  apply ZlibF.Math.TokenSuffix.step_cancel_suffix lengths distances (suffix := bytesBits (bs.drop used))
  have before : (natBits l.bits.toNat l.hold.toNat ++ bytesBits (bs.take used)) ++ bytesBits (bs.drop used) = stream l bs := by
    rw [List.append_assoc, ← bytesBits_append, List.take_append_drop]
    rfl
  rw [before]
  exact step

#print axioms token_step_held_raw_prefix
end Zlib.Inflate.Proofs.SlowReverseToken
