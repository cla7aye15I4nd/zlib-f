import ZlibF.Proof.«inflate.c.slow-input-fragment»
namespace Zlib.Inflate.Proofs.SlowTokenPath
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs SlowInputFragment
set_option autoImplicit false

/-- Independent syntax of one original Huffman token, including input
which may be supplied by later public calls. -/
inductive TokenSyntax (L D : List Nat) where
  | literal (symbol : Nat) (input rest : List Bool)
      (decoded : decodeSym L input = some (symbol, rest)) (small : symbol < 256)
  | copy (parsed : CopySyntax L D)
  | eob (input rest : List Bool) (decoded : decodeSym L input = some (256, rest))

def TokenSyntax.input {L D : List Nat} : TokenSyntax L D → List Bool
  | .literal _ input _ _ _ => input
  | .copy p => p.input
  | .eob input _ _ => input

def TokenSyntax.rest {L D : List Nat} : TokenSyntax L D → List Bool
  | .literal _ _ rest _ _ => rest
  | .copy p => p.rest
  | .eob _ rest _ => rest

def TokenSyntax.symbol {L D : List Nat} : TokenSyntax L D → Nat
  | .literal symbol _ _ _ _ => symbol
  | .copy p => p.symbol
  | .eob _ _ _ => 256

def TokenSyntax.codeRest {L D : List Nat} : TokenSyntax L D → List Bool
  | .literal _ _ rest _ _ => rest
  | .copy p => p.r1
  | .eob _ rest _ => rest

def TokenSyntax.effect {L D : List Nat} (token : TokenSyntax L D) (dict history : List UInt8) : List UInt8 :=
  match token with
  | .literal symbol _ _ _ _ => history ++ [symbol.toUInt8]
  | .copy p => copyBack dict (distBases.getD p.distanceSymbol 0 + p.distanceValue)
      (lengthBases.getD (p.symbol - 257) 0 + p.lengthValue) history
  | .eob _ _ _ => history

def TokenSyntax.ended {L D : List Nat} : TokenSyntax L D → Bool
  | .literal _ _ _ _ _ => false
  | .copy _ => false
  | .eob _ _ _ => true

def TokenSyntax.admissible {L D : List Nat} (token : TokenSyntax L D) (dict history : List UInt8) : Prop :=
  match token with
  | .literal _ _ _ _ _ => True
  | .copy p => distBases.getD p.distanceSymbol 0 + p.distanceValue ≤ (dict ++ history).length
  | .eob _ _ _ => True

/-- The semantic stage is an internal ghost established by real decoding.
LIT stores the already decoded byte while waiting for output. Copy stages
reuse the actual scalar relation already proved for every copy phase. -/
inductive TokenPhase {L D : List Nat} : TokenSyntax L D → InflateState → List Bool → Prop
  | code {token : TokenSyntax L D} {s : InflateState} :
      (s.mode = LEN ∨ s.mode = LEN_) → TokenPhase token s token.input
  | literal {symbol : Nat} {input rest : List Bool}
      {decoded : decodeSym L input = some (symbol, rest)} {small : symbol < 256} {s : InflateState} :
      s.mode = LIT → s.length.toNat = symbol → s.back = Int32.ofNat (L.getD symbol 0) →
      TokenPhase (.literal symbol input rest decoded small) s rest
  | copy {p : CopySyntax L D} {s : InflateState} {residual : List Bool} :
      PendingSyntax p s residual → TokenPhase (.copy p) s residual

/-- Every independent token supplies the first actual code symbol. -/
theorem TokenSyntax.decode_code {L D : List Nat} (token : TokenSyntax L D) :
    decodeSym L token.input = some (token.symbol, token.codeRest) := by
  cases token with
  | literal symbol input rest decoded small => exact decoded
  | copy p => exact p.lengthDecode
  | eob input rest decoded => exact decoded

theorem TokenSyntax.valid_symbol {L D : List Nat} (token : TokenSyntax L D) : token.symbol ≤ 285 := by
  cases token with
  | literal symbol input rest decoded small => exact Nat.le_trans (Nat.le_of_lt small) (by decide)
  | copy p => exact p.lengthUpper
  | eob input rest decoded => change 256 ≤ 285; decide

/-- Syntax gives precisely the original local token constructor. -/
theorem TokenSyntax.step {L D : List Nat} (token : TokenSyntax L D) (dict history : List UInt8)
    (valid : token.admissible dict history) :
    Token.Step L D dict history token.input token.rest (token.effect dict history) token.ended := by
  cases token with
  | literal symbol input rest decoded small => exact .literal decoded small
  | copy p =>
    exact .copy p.lengthDecode p.lengthLower p.lengthUpper p.lengthRead p.distanceDecode
      p.distanceUpper p.distanceRead (by simpa only [TokenSyntax.admissible] using valid)
  | eob input rest decoded => exact .eob decoded

/-- The original Symbols relation supplies the independent token and its
unchanged continuation. The ghost introduces no translated run premise. -/
theorem TokenSyntax.of_symbols {L D : List Nat} {dict history output : List UInt8} {input tail : List Bool}
    (parsed : Symbols L D dict history input tail output) :
    ∃ token : TokenSyntax L D, token.input = input ∧ token.admissible dict history ∧
      ((token.ended = true ∧ token.rest = tail ∧ output = history) ∨
       (token.ended = false ∧ Symbols L D dict (token.effect dict history) token.rest tail output)) := by
  cases parsed with
  | eob decoded => exact ⟨.eob _ _ decoded, rfl, trivial, Or.inl ⟨rfl, rfl, rfl⟩⟩
  | lit decoded small continuation => exact ⟨.literal _ _ _ decoded small, rfl, trivial, Or.inr ⟨rfl, continuation⟩⟩
  | copy decoded lower upper lengthRead distanceRead valid distanceExtra fits continuation =>
    let p : CopySyntax L D := ⟨_, _, _, _, _, _, _, _, _, decoded, lower, upper, lengthRead, distanceRead, valid, distanceExtra⟩
    refine ⟨.copy p, rfl, ?_, Or.inr ⟨rfl, continuation⟩⟩
    simpa only [TokenSyntax.admissible, p, Nat.add_comm] using fits

#print axioms TokenSyntax.decode_code
#print axioms TokenSyntax.valid_symbol
#print axioms TokenSyntax.step
#print axioms TokenSyntax.of_symbols
end Zlib.Inflate.Proofs.SlowTokenPath
