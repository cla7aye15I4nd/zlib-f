import ZlibF.Proof.«inflate.c.slow-reverse-token-compose»
import ZlibF.Proof.«inflate.c.token-suffix-cancel»

namespace Zlib.Inflate.Proofs.SlowReverseToken
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs SlowInputFragment Zlib.Inffast.Proofs
open ZlibF.Math.CodeLengthPrefix ZlibF.Math.InflateDecode ZlibF.Math.TokenSuffix
set_option autoImplicit false

/-- An accepted partial phase depends only on its finite consumed word.
No claim is made that its arbitrary future completes a valid token. -/
 theorem ReadPrefix.consumed_word
    {L D : List Nat} {input residual : List Bool} {s : InflateState}
    (lengths : Acceptable .litLen L) (distances : Acceptable .dist D)
    (phase : ReadPrefix L D input s residual) :
    ∃ word : List Bool, input = word ++ residual ∧
      ∀ suffix, ReadPrefix L D (word ++ suffix) s suffix := by
  cases phase with
  | code mode => exact ⟨[], rfl, fun _ => .code mode⟩
  | literal decoded small mode length back =>
    have nonzero := (Zlib.Inftrees.Proofs.decoded_symbol_prefix decoded).2.1
    exact ⟨_, decoded_word decoded, fun suffix =>
      .literal (decode_canonical_word lengths _ nonzero suffix) small mode length back⟩
  | lenext decoded lower upper mode length extra back =>
    have nonzero := (Zlib.Inftrees.Proofs.decoded_symbol_prefix decoded).2.1
    exact ⟨_, decoded_word decoded, fun suffix =>
      .lenext (decode_canonical_word lengths _ nonzero suffix) lower upper mode length extra back⟩
  | @dist symbol r1 value residual decoded lower upper read mode length was back =>
    have nonzero := (Zlib.Inftrees.Proofs.decoded_symbol_prefix decoded).2.1
    obtain ⟨bound, readSource⟩ := read_word read
    have source := decoded_word decoded
    rw [readSource] at source
    let word := codeOf L symbol ++ bitsOfNat value (lengthExtras.getD (symbol - 257) 0)
    refine ⟨word, by simpa only [word, List.append_assoc] using source, ?_⟩
    intro suffix
    simp only [word, List.append_assoc]
    exact .dist (decode_canonical_word lengths _ nonzero _) lower upper
      (read_consumed_word _ _ bound _) mode length was back
  | @distext symbol r1 value r2 ds residual decoded lower upper read distanceDecoded distanceUpper mode length was offset extra back =>
    have lenNonzero := (Zlib.Inftrees.Proofs.decoded_symbol_prefix decoded).2.1
    have distNonzero := (Zlib.Inftrees.Proofs.decoded_symbol_prefix distanceDecoded).2.1
    obtain ⟨bound, readSource⟩ := read_word read
    have source := decoded_word decoded
    rw [readSource, decoded_word distanceDecoded] at source
    let word := codeOf L symbol ++ bitsOfNat value (lengthExtras.getD (symbol - 257) 0) ++ codeOf D ds
    refine ⟨word, by simpa only [word, List.append_assoc] using source, ?_⟩
    intro suffix
    simp only [word, List.append_assoc]
    exact .distext (decode_canonical_word lengths _ lenNonzero _) lower upper
      (read_consumed_word _ _ bound _) (decode_canonical_word distances _ distNonzero _)
      distanceUpper mode length was offset extra back
  | matching p inputEq mode length was distance =>
    have lenNonzero := (Zlib.Inftrees.Proofs.decoded_symbol_prefix p.lengthDecode).2.1
    have distNonzero := (Zlib.Inftrees.Proofs.decoded_symbol_prefix p.distanceDecode).2.1
    obtain ⟨lvBound, lengthSource⟩ := read_word p.lengthRead
    obtain ⟨dvBound, distanceSource⟩ := read_word p.distanceRead
    have source := decoded_word p.lengthDecode
    rw [lengthSource, decoded_word p.distanceDecode, distanceSource] at source
    let word := codeOf L p.symbol ++ bitsOfNat p.lengthValue (lengthExtras.getD (p.symbol - 257) 0) ++
      codeOf D p.distanceSymbol ++ bitsOfNat p.distanceValue (distExtras.getD p.distanceSymbol 0)
    refine ⟨word, by simpa only [inputEq, word, List.append_assoc] using source, ?_⟩
    intro suffix
    let r3 := bitsOfNat p.distanceValue (distExtras.getD p.distanceSymbol 0) ++ suffix
    let r2 := codeOf D p.distanceSymbol ++ r3
    let r1 := bitsOfNat p.lengthValue (lengthExtras.getD (p.symbol - 257) 0) ++ r2
    let q : CopySyntax L D := ⟨word ++ suffix, r1, r2, r3, suffix, p.symbol, p.distanceSymbol,
      p.lengthValue, p.distanceValue,
      by simpa only [word, r1, r2, r3, List.append_assoc] using decode_canonical_word lengths p.symbol lenNonzero r1,
      p.lengthLower, p.lengthUpper, read_consumed_word _ _ lvBound r2,
      decode_canonical_word distances _ distNonzero r3, p.distanceUpper, read_consumed_word _ _ dvBound suffix⟩
    exact .matching q rfl mode length was distance

 theorem ReadPrefix.cancel_suffix
    {L D : List Nat} {input rest suffix : List Bool} {s : InflateState}
    (lengths : Acceptable .litLen L) (distances : Acceptable .dist D)
    (phase : ReadPrefix L D (input ++ suffix) s (rest ++ suffix)) :
    ReadPrefix L D input s rest := by
  obtain ⟨word, source, parsed⟩ := phase.consumed_word lengths distances
  rw [← List.append_assoc] at source
  rw [List.append_cancel_right source]
  exact parsed rest

 theorem ReadPrefix.append_suffix
    {L D : List Nat} {input rest : List Bool} {s : InflateState}
    (lengths : Acceptable .litLen L) (distances : Acceptable .dist D)
    (phase : ReadPrefix L D input s rest) (suffix : List Bool) :
    ReadPrefix L D (input ++ suffix) s (rest ++ suffix) := by
  obtain ⟨word, source, parsed⟩ := phase.consumed_word lengths distances
  rw [source, List.append_assoc]
  exact parsed _

 theorem read_prefix_held_raw_prefix
    {L D : List Nat} {l regs : IL} {bs : List UInt8} {used : Nat} {s : InflateState}
    (lengths : Acceptable .litLen L) (distances : Acceptable .dist D)
    (phase : ReadPrefix L D (stream l bs) s (stream regs (bs.drop used))) :
    ReadPrefix L D (natBits l.bits.toNat l.hold.toNat ++ bytesBits (bs.take used)) s
      (natBits regs.bits.toNat regs.hold.toNat) := by
  apply ReadPrefix.cancel_suffix lengths distances (suffix := bytesBits (bs.drop used))
  have before : (natBits l.bits.toNat l.hold.toNat ++ bytesBits (bs.take used)) ++ bytesBits (bs.drop used) = stream l bs := by
    rw [List.append_assoc, ← bytesBits_append, List.take_append_drop]
    rfl
  rw [before]
  exact phase

#print axioms ReadPrefix.consumed_word
#print axioms ReadPrefix.cancel_suffix
#print axioms ReadPrefix.append_suffix
#print axioms read_prefix_held_raw_prefix
end Zlib.Inflate.Proofs.SlowReverseToken

namespace Zlib.Inflate.Proofs.SlowReverseToken
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs SlowInputFragment
set_option autoImplicit false

 theorem CurrentTables.acceptable {h : Heap} {s : InflateState} {L D : List Nat}
    (tables : CurrentTables h s L D) : Acceptable .litLen L ∧ Acceptable .dist D := by
  obtain ⟨⟨_, _, _, _, _, _, _, len⟩, ⟨_, _, _, _, _, _, _, dist⟩⟩ := tables
  exact ⟨len.acceptable, dist.acceptable⟩

/-- Accepted semantic metadata after cancelling untouched raw bytes.
The ordinary TokenEvent separately retains physical effects and whether
accepted output is still pending or partially emitted. -/
 def CausalEvent (L D : List Nat) (dict history : List UInt8) (input : List Bool)
    (outcome : Except Ex Unit) (state : InflateState) (regs : IL) : Prop :=
  (outcome = .error Ex.leave ∧ ReadPrefix L D input state (natBits regs.bits.toNat regs.hold.toNat) ∧
    (regs.have_ = 0 ∨ regs.left = 0)) ∨
  (outcome = .ok () ∧ state.mode = BAD) ∨
  (outcome = .ok () ∧ ∃ target last,
    Token.Step L D dict history input (natBits regs.bits.toNat regs.hold.toNat) target last)

 theorem TokenEvent.held
    {L D : List Nat} {dict history : List UInt8} {l regs : IL} {bs : List UInt8} {used : Nat}
    {r : ZStreamRef} {zs : Nat} {outcome : Except Ex Unit} {after : Heap} {z : ZStream} {state : InflateState}
    (lengths : Acceptable .litLen L) (distances : Acceptable .dist D)
    (event : TokenEvent L D dict history (stream l bs) r zs outcome regs after z state (bs.drop used)) :
    CausalEvent L D dict history (natBits l.bits.toNat l.hold.toNat ++ bytesBits (bs.take used)) outcome state regs := by
  cases event with
  | wait _view phase empty => exact Or.inl ⟨rfl, read_prefix_held_raw_prefix lengths distances phase, empty⟩
  | bad _good _B mode => exact Or.inr (Or.inl ⟨rfl, mode⟩)
  | literalPending _view _phase _mode step _length _small =>
    exact Or.inr (Or.inr ⟨rfl, _, false, token_step_held_raw_prefix lengths distances step⟩)
  | eob _view _mode _back step =>
    exact Or.inr (Or.inr ⟨rfl, _, true, token_step_held_raw_prefix lengths distances step⟩)
  | literalDone _good _buffers _mode _get _put _physical step =>
    exact Or.inr (Or.inr ⟨rfl, _, false, token_step_held_raw_prefix lengths distances step⟩)
  | copy p _made _dest _off _array _inputEq residual _good _buffers _dictionary _positive _bound
      _length _mode _get _put _physical _count _remaining step =>
    rw [residual] at step
    exact Or.inr (Or.inr ⟨rfl, _, false, token_step_held_raw_prefix lengths distances step⟩)

/-- The real slow-token source classifier also produces its held-only
causal event in the same execution. No assumption about replacing a raw
buffer or a future valid compressed suffix is needed. -/
 theorem slow_token_dispatch_event_held
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {l : IL}
    {bs dict history : List UInt8} {L D : List Nat}
    (E : Env c h r zs z s) (view : PayloadView h r zs z s l bs dict history L D)
    (mode : s.mode = LEN_ ∨ s.mode = LEN)
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    ∃ outcome regs after finalZ state used,
      runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) ∧ used ≤ bs.length ∧
      BitInv after regs (bs.drop used) ∧ regs.next = inputAdvance l.next used ∧
      regs.have_.toNat + used = l.have_.toNat ∧
      TokenEvent L D dict history (stream l bs) r zs outcome regs after finalZ state (bs.drop used) ∧
      CausalEvent L D dict history (natBits l.bits.toNat l.hold.toNat ++ bytesBits (bs.take used)) outcome state regs := by
  obtain ⟨outcome, regs, after, finalZ, state, used, actual, bound, B, cursor, count, event⟩ :=
    slow_token_dispatch_event E view mode slow
  have alphabets := view.semantic.acceptable
  exact ⟨outcome, regs, after, finalZ, state, used, actual, bound, B, cursor, count, event,
    event.held alphabets.1 alphabets.2⟩

#print axioms CurrentTables.acceptable
#print axioms CausalEvent
#print axioms TokenEvent.held
#print axioms slow_token_dispatch_event_held
end Zlib.Inflate.Proofs.SlowReverseToken
