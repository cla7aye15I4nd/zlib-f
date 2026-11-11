import ZlibF.Proof.«inflate.c.meaning-match»
import ZlibF.Math.«code-length-prefix»
import ZlibF.Proof.«inffast.c.body-token-reject»

/-!
# inflate.c: fast-path tokens as format tokens

`inflate_fast` decodes one token per loop pass against the history the
window saved (`MatchHistory.saved`) and the output of the current call, on
the whole remaining input of the call. The format grammar (`DeflateParsed`)
reads a token on its own bits, against the body dictionary and the whole body
output. This file moves a token between the two views:

* `Token.Step.strip`: a token read on a longer input is the same token read
  on its own bits, followed by the rest;
* `Token.Step.rebase`: a token against a saved suffix of the history is the
  same token against the whole history (`retained_history_agrees`).
-/

namespace Zlib.Inflate.Proofs.MeaningFast
open ZlibF.Spec ZlibF.Spec.Proofs
open Zlib.Inffast.Proofs.BodyTokenReject (decodeSym_word readBits_word)
set_option autoImplicit false

/-- A token read on a longer input is the token read on its own bits. -/
theorem _root_.ZlibF.Spec.Token.Step.strip {L D : List Nat} {dict h : List UInt8}
    {inp rest : List Bool} {out : List UInt8} {finished : Bool} (hL : Ext L) (hD : Ext D)
    (step : Token.Step L D dict h inp rest out finished) :
    ∃ tokenBits, inp = tokenBits ++ rest ∧ Token.Step L D dict h tokenBits [] out finished := by
  cases step with
  | literal d lt =>
    obtain ⟨word, split, d'⟩ := decodeSym_word d
    exact ⟨word, split, .literal d' lt⟩
  | copy d lo hi x e ds y bound =>
    obtain ⟨w1, s1, d1⟩ := decodeSym_word d
    obtain ⟨w2, s2, x2⟩ := readBits_word x
    obtain ⟨w3, s3, e3⟩ := decodeSym_word e
    obtain ⟨w4, s4, y4⟩ := readBits_word y
    refine ⟨w1 ++ (w2 ++ (w3 ++ w4)), ?_, ?_⟩
    · rw [s1, s2, s3, s4]
      simp only [List.append_assoc]
    · have dL := hL _ _ _ (w2 ++ (w3 ++ w4)) d1
      have xL := readBits_append _ _ _ _ (w3 ++ w4) x2
      have eL := hD _ _ _ w4 e3
      have yL := y4
      simp only [List.nil_append] at dL xL eL
      exact .copy dL lo hi xL eL ds yL bound
  | eob d =>
    obtain ⟨word, split, d'⟩ := decodeSym_word d
    exact ⟨word, split, .eob d'⟩

/-- A token against a retained suffix of the history is the same token
against the whole history, with the earlier output in front. -/
theorem _root_.ZlibF.Spec.Token.Step.rebase {L D : List Nat} {saved dict past current : List UInt8}
    {inp rest : List Bool} {out : List UInt8} {finished : Bool}
    (suffix : saved <:+ dict ++ past)
    (step : Token.Step L D saved current inp rest out finished) :
    Token.Step L D dict (past ++ current) inp rest (past ++ out) finished := by
  cases step with
  | literal d lt =>
    rw [← List.append_assoc]
    exact .literal d lt
  | @copy _ _ _ _ symbol distanceSymbol lengthExtra distanceExtra d lo hi x e ds y bound =>
    have positive : 0 < distBases.getD distanceSymbol 0 + distanceExtra := by
      have := MeaningMatch.distBases_ge distanceSymbol (by omega)
      omega
    rw [← ZlibF.Math.LZ77History.retained_history_agrees dict past current saved _ _ suffix
      positive (by simpa only [List.length_append] using bound)]
    have savedLe := suffix.length_le
    refine .copy d lo hi x e ds y ?_
    simp only [List.length_append] at bound savedLe ⊢
    omega
  | eob d => exact .eob d

#print axioms ZlibF.Spec.Token.Step.strip
#print axioms ZlibF.Spec.Token.Step.rebase

end Zlib.Inflate.Proofs.MeaningFast
