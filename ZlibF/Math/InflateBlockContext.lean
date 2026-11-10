import ZlibF.Proof.Format.Deflate
import ZlibF.Math.LZ77History

namespace ZlibF.Math.InflateBlockContext
open ZlibF.Spec ZlibF.Spec.Proofs
set_option autoImplicit false

/-- The original completed nonfinal blocks are a causal parser context.
The equivalence holds for every later byte suffix, including malformed
suffixes; no complete valid continuation is asserted to exist. -/
def Context (dict originalOutput : List UInt8) (originalInput : List Bool)
    (currentOutput : List UInt8) (currentInput : List Bool) : Prop :=
  ∀ (future : List UInt8) (rest : List Bool) (output : List UInt8),
    Blocks dict originalOutput (originalInput ++ bytesToBits future) rest output ↔
      Blocks dict currentOutput (currentInput ++ bytesToBits future) rest output

theorem Context.initial (dict history : List UInt8) (input : List Bool) :
    Context dict history input history input := by
  intro _ _ _
  rfl

theorem Context.trans
    {dict original middle current : List UInt8} {input middleBits currentBits : List Bool}
    (first : Context dict original input middle middleBits)
    (second : Context dict middle middleBits current currentBits) :
    Context dict original input current currentBits := by
  intro future rest output
  exact (first future rest output).trans (second future rest output)

theorem bytesToBits_append (first second : List UInt8) :
    bytesToBits (first ++ second) = bytesToBits first ++ bytesToBits second := by
  simp only [bytesToBits, List.flatMap_append]

/-- Crediting actual new input bytes extends both sides of the same
causal context. It does not silently discard unconsumed held bits. -/
theorem Context.extend
    {dict original current : List UInt8} {input currentBits : List Bool}
    (context : Context dict original input current currentBits) (bytes : List UInt8) :
    Context dict original (input ++ bytesToBits bytes) current (currentBits ++ bytesToBits bytes) := by
  intro future rest output
  simpa only [bytesToBits_append, List.append_assoc] using context (bytes ++ future) rest output

/-- A completed nonfinal body gives the exact next-block parser context.
This is a statement about the independent grammar, not an assumed library
contract. Runtime producers must establish the three source reads. -/
theorem nonfinal_body_iff
    {dict before after output : List UInt8} {input middle bodyInput next rest : List Bool} {kind : Nat}
    (last : readBits 1 input = some (0, middle))
    (type : readBits 2 middle = some (kind, bodyInput))
    (body : Body dict kind before bodyInput next after) :
    Blocks dict before input rest output ↔ Blocks dict after next rest output := by
  constructor
  · intro blocks
    cases blocks with
    | last other _ _ =>
      have impossible : (0 : Nat) = 1 := congrArg Prod.fst (Option.some.inj (last.symm.trans other))
      omega
    | more otherLast otherType otherBody continuation =>
      obtain ⟨_zero, sameMiddle⟩ := Prod.mk.inj (Option.some.inj (last.symm.trans otherLast))
      subst sameMiddle
      obtain ⟨sameKind, sameBody⟩ := Prod.mk.inj (Option.some.inj (type.symm.trans otherType))
      subst sameKind sameBody
      obtain ⟨sameNext, sameOutput⟩ := body.det otherBody
      subst sameNext sameOutput
      exact continuation
  · intro continuation
    exact .more last type body continuation

/-- Only a real completed nonfinal Body advances the block context.
Whole-byte future extension preserves stored-block alignment as well as
fixed/dynamic parsing. No future-validity hypothesis is introduced. -/
theorem Context.advance
    {dict original before after : List UInt8} {input current middle bodyInput next : List Bool} {kind : Nat}
    (context : Context dict original input before current)
    (last : readBits 1 current = some (0, middle))
    (type : readBits 2 middle = some (kind, bodyInput))
    (body : Body dict kind before bodyInput next after) :
    Context dict original input after next := by
  intro future rest output
  have first := readBits_append 1 current 0 middle (bytesToBits future) last
  have second := readBits_append 2 middle kind bodyInput (bytesToBits future) type
  have whole : (bytesToBits future).length % 8 = 0 := by rw [bytesToBits_len]; omega
  exact (context future rest output).trans (nonfinal_body_iff first second (body.append _ whole))

/-- A real completed final body reconstructs the original Blocks parse.
This is the soundness endpoint used after accepted local tokens/EOB and
actual last-block metadata have been reconstructed from source. -/
theorem Context.finish
    {dict original before after : List UInt8} {input current middle bodyInput rest : List Bool} {kind : Nat}
    (context : Context dict original input before current)
    (last : readBits 1 current = some (1, middle))
    (type : readBits 2 middle = some (kind, bodyInput))
    (body : Body dict kind before bodyInput rest after) :
    Blocks dict original input rest after := by
  have completed := (context [] rest after).mpr (by simpa only [bytesToBits, List.flatMap_nil, List.append_nil] using Blocks.last last type body)
  simpa only [bytesToBits, List.flatMap_nil, List.append_nil] using completed

theorem symbols_history_prefix
    {L D : List Nat} {dict history output : List UInt8} {input rest : List Bool}
    (parsed : Symbols L D dict history input rest output) : history <+: output := by
  induction parsed with
  | eob _ => exact List.prefix_refl _
  | lit _ _ _ ih => exact (List.prefix_append _ _).trans ih
  | copy _ _ _ _ _ _ _ _ _ ih =>
    exact (ZlibF.Math.LZ77History.copy_back_extends_history _ _ _ _).1.trans ih

theorem body_history_prefix
    {dict history output : List UInt8} {kind : Nat} {input rest : List Bool}
    (parsed : Body dict kind history input rest output) : history <+: output := by
  cases parsed with
  | stored _ _ _ _ => exact List.prefix_append _ _
  | fixed symbols => exact symbols_history_prefix symbols
  | dynamic _ _ _ _ _ _ _ _ _ _ symbols => exact symbols_history_prefix symbols

theorem blocks_history_prefix
    {dict history output : List UInt8} {input rest : List Bool}
    (parsed : Blocks dict history input rest output) : history <+: output := by
  induction parsed with
  | last _ _ body => exact body_history_prefix body
  | more _ _ body _ ih => exact (body_history_prefix body).trans ih

/-- On an independently valid complete stream, the same causal context
gives the remaining original Blocks parse and the cumulative output-prefix
property. This direction is separate from Context.finish soundness. -/
theorem Context.valid_source
    {dict original current output : List UInt8} {input currentBits rest : List Bool} {future : List UInt8}
    (context : Context dict original input current currentBits)
    (parsed : Blocks dict original (input ++ bytesToBits future) rest output) :
    Blocks dict current (currentBits ++ bytesToBits future) rest output ∧ current <+: output := by
  have remaining := (context future rest output).mp parsed
  exact ⟨remaining, blocks_history_prefix remaining⟩

#print axioms Context.initial
#print axioms Context.trans
#print axioms Context.extend
#print axioms nonfinal_body_iff
#print axioms Context.advance
#print axioms Context.finish
#print axioms Context.valid_source
end ZlibF.Math.InflateBlockContext
