import ZlibF.Math.InflateTokenContext

namespace ZlibF.Math.InflateHuffmanBodyContext
open ZlibF.Spec ZlibF.Spec.Proofs
set_option autoImplicit false

/-- Independent source reads identifying a fixed or dynamic Huffman body.
This records only the accepted header; it asserts no complete payload exists. -/
inductive Header : Nat → List Bool → List Nat → List Nat → List Bool → Prop
  | fixed (input : List Bool) : Header 1 input fixedLitLens fixedDistLens input
  | dynamic {input r1 r2 r3 r4 payload : List Bool} {hlit hdist hclen : Nat}
      {cl lens : List Nat} :
      readBits 5 input = some (hlit, r1) → readBits 5 r1 = some (hdist, r2) →
      readBits 4 r2 = some (hclen, r3) → DynamicCountsOK hlit hdist →
      readCodeLenLens (hclen + 4) r3 = some (cl, r4) → Acceptable .codeLength cl →
      CodeLens cl (hlit + 257 + (hdist + 1)) [] r4 payload lens →
      HasEndOfBlock (lens.take (hlit + 257)) →
      Acceptable .litLen (lens.take (hlit + 257)) →
      Acceptable .dist (lens.drop (hlit + 257)) →
      Header 2 input (lens.take (hlit + 257)) (lens.drop (hlit + 257)) payload

theorem Header.ext {kind : Nat} {input payload : List Bool} {L D : List Nat}
    (header : Header kind input L D payload) : Ext L ∧ Ext D := by
  cases header with
  | fixed => exact ⟨ext_fixedLit, ext_fixedDist⟩
  | dynamic _ _ _ _ _ _ _ _ validL validD => exact ⟨ext_acceptable validL, ext_acceptable validD⟩

/-- An accepted source header gives an exact Body/Symbols equivalence.
The reverse implication reconstructs the original Body at EOB. -/
theorem Header.body_iff {kind : Nat} {input payload rest : List Bool} {L D : List Nat}
    {dict history output : List UInt8} (header : Header kind input L D payload) :
    Body dict kind history input rest output ↔ Symbols L D dict history payload rest output := by
  cases header with
  | fixed =>
    constructor
    · intro body; cases body with | fixed symbols => exact symbols
    · exact Body.fixed
  | dynamic a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 =>
    constructor
    · intro body
      cases body with
      | dynamic b1 b2 b3 _ b5 _ b7 _ _ _ symbols =>
        rw [a1] at b1; obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj b1)
        rw [a2] at b2; obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj b2)
        rw [a3] at b3; obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj b3)
        rw [a5] at b5; obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj b5)
        obtain ⟨rfl, rfl⟩ := a7.det b7
        exact symbols
    · intro symbols
      exact Body.dynamic a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 symbols

theorem Header.append {kind : Nat} {input payload : List Bool} {L D : List Nat}
    (header : Header kind input L D payload) (future : List Bool) :
    Header kind (input ++ future) L D (payload ++ future) := by
  cases header with
  | fixed => exact .fixed _
  | dynamic a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 =>
    exact .dynamic (readBits_append _ _ _ _ _ a1) (readBits_append _ _ _ _ _ a2)
      (readBits_append _ _ _ _ _ a3) a4 (readCodeLenLens_append _ _ _ _ _ a5) a6
      (a7.append (ext_acceptable a6) _) a8 a9 a10

/-- The token context attaches to the independently accepted block header.
All future suffixes remain quantified; a malformed residual is allowed. -/
theorem Header.current_body_iff {kind : Nat} {input payload current future rest : List Bool}
    {L D : List Nat} {dict original history output : List UInt8}
    (header : Header kind input L D payload)
    (tokens : InflateTokenContext.Context L D dict original payload history current) :
    Body dict kind original (input ++ future) rest output ↔
      Symbols L D dict history (current ++ future) rest output :=
  (header.append future).body_iff.trans (tokens future rest output)

/-- Real accepted EOB plus the causal token context reconstructs the whole
original body, without assuming an independently valid future. -/
theorem Header.finish {kind : Nat} {input payload current rest : List Bool}
    {L D : List Nat} {dict original history next : List UInt8}
    (header : Header kind input L D payload)
    (tokens : InflateTokenContext.Context L D dict original payload history current)
    (eob : Token.Step L D dict history current rest next true) :
    next = history ∧ Body dict kind original input rest next := by
  obtain ⟨same, symbols⟩ := tokens.finish eob
  exact ⟨same, header.body_iff.mpr symbols⟩

/-- Causal grammar ledger for one active compressed block. The header
and committed tokens come from accepted source events. No desired output
or complete parse is stored as an invariant assumption. -/
structure ActiveBlock (dict originalOutput : List UInt8) (originalInput : List Bool)
    (history : List UInt8) (current : List Bool) (L D : List Nat) where
  before : List UInt8
  blockInput : List Bool
  afterFinal : List Bool
  bodyInput : List Bool
  payloadInput : List Bool
  kind : Nat
  last : Nat
  blockContext : InflateBlockContext.Context dict originalOutput originalInput before blockInput
  finalRead : readBits 1 blockInput = some (last, afterFinal)
  typeRead : readBits 2 afterFinal = some (kind, bodyInput)
  header : Header kind bodyInput L D payloadInput
  tokens : InflateTokenContext.Context L D dict before payloadInput history current

def ActiveBlock.advance {dict original history next : List UInt8}
    {originalInput current rest : List Bool} {L D : List Nat}
    (ledger : ActiveBlock dict original originalInput history current L D)
    (step : Token.Step L D dict history current rest next false) :
    ActiveBlock dict original originalInput next rest L D := by
  obtain ⟨before, blockInput, afterFinal, bodyInput, payloadInput, kind, last,
    context, finalRead, typeRead, header, tokens⟩ := ledger
  exact ⟨before, blockInput, afterFinal, bodyInput, payloadInput, kind, last,
    context, finalRead, typeRead, header, tokens.advance header.ext.1 header.ext.2 step⟩

/-- Rebuffering extends all source cuts by exactly the same observed bytes. -/
def ActiveBlock.extend {dict original history : List UInt8}
    {originalInput current : List Bool} {L D : List Nat}
    (ledger : ActiveBlock dict original originalInput history current L D) (bytes : List UInt8) :
    ActiveBlock dict original (originalInput ++ bytesToBits bytes)
      history (current ++ bytesToBits bytes) L D := by
  obtain ⟨before, blockInput, afterFinal, bodyInput, payloadInput, kind, last,
    context, finalRead, typeRead, header, tokens⟩ := ledger
  exact ⟨before, blockInput ++ bytesToBits bytes, afterFinal ++ bytesToBits bytes,
    bodyInput ++ bytesToBits bytes, payloadInput ++ bytesToBits bytes, kind, last,
    context.extend bytes, readBits_append _ _ _ _ _ finalRead,
    readBits_append _ _ _ _ _ typeRead, header.append _, tokens.extend _⟩

/-- EOB closes the original body and routes by the actual BFINAL read:
nonfinal blocks restore the next-block context; final blocks reconstruct
the complete original Blocks relation. -/
theorem ActiveBlock.finish {dict original history next : List UInt8}
    {originalInput current rest : List Bool} {L D : List Nat}
    (ledger : ActiveBlock dict original originalInput history current L D)
    (eob : Token.Step L D dict history current rest next true) :
    next = history ∧
    (ledger.last = 0 → InflateBlockContext.Context dict original originalInput history rest) ∧
    (ledger.last = 1 → Blocks dict original originalInput rest history) := by
  obtain ⟨same, body⟩ := ledger.header.finish ledger.tokens eob
  subst next
  refine ⟨rfl, ?_, ?_⟩
  · intro last
    exact ledger.blockContext.advance (by simpa only [last] using ledger.finalRead)
      ledger.typeRead body
  · intro last
    exact ledger.blockContext.finish (by simpa only [last] using ledger.finalRead)
      ledger.typeRead body

/-- On any independently valid original Blocks source, the causal
ledger yields the actual remaining token grammar and its output prefix.
This is a conditional consequence, not a valid-future invariant premise. -/
theorem ActiveBlock.valid_source {dict original history output : List UInt8}
    {originalInput current rest : List Bool} {L D : List Nat} {future : List UInt8}
    (ledger : ActiveBlock dict original originalInput history current L D)
    (parsed : Blocks dict original (originalInput ++ bytesToBits future) rest output) :
    ∃ bodyRest bodyOutput,
      Symbols L D dict history (current ++ bytesToBits future) bodyRest bodyOutput ∧
      history <+: bodyOutput ∧ bodyOutput <+: output := by
  have remaining := (ledger.blockContext (future) rest output).mp parsed
  have finalRead := readBits_append _ _ _ _ (bytesToBits future) ledger.finalRead
  have typeRead := readBits_append _ _ _ _ (bytesToBits future) ledger.typeRead
  have body : ∃ bodyRest bodyOutput,
      Body dict ledger.kind ledger.before (ledger.bodyInput ++ bytesToBits future)
        bodyRest bodyOutput ∧ bodyOutput <+: output := by
    cases remaining with
    | last otherFinal otherType otherBody =>
      obtain ⟨_, sameMiddle⟩ := Prod.mk.inj (Option.some.inj (finalRead.symm.trans otherFinal))
      rw [← sameMiddle] at otherType
      obtain ⟨sameKind, sameInput⟩ := Prod.mk.inj (Option.some.inj (typeRead.symm.trans otherType))
      rw [← sameKind, ← sameInput] at otherBody
      exact ⟨_, _, otherBody, List.prefix_refl _⟩
    | more otherFinal otherType otherBody continuation =>
      obtain ⟨_, sameMiddle⟩ := Prod.mk.inj (Option.some.inj (finalRead.symm.trans otherFinal))
      rw [← sameMiddle] at otherType
      obtain ⟨sameKind, sameInput⟩ := Prod.mk.inj (Option.some.inj (typeRead.symm.trans otherType))
      rw [← sameKind, ← sameInput] at otherBody
      exact ⟨_, _, otherBody, InflateBlockContext.blocks_history_prefix continuation⟩
  obtain ⟨bodyRest, bodyOutput, actualBody, outputPrefix⟩ := body
  have symbols := (ledger.header.current_body_iff ledger.tokens).mp actualBody
  exact ⟨bodyRest, bodyOutput, symbols, InflateBlockContext.symbols_history_prefix symbols, outputPrefix⟩

end ZlibF.Math.InflateHuffmanBodyContext
