import ZlibF.Proof.«inflate.c.global-payload-representation»

namespace Zlib.Inflate.Proofs.FunctionalEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inftrees
open SlowTokenPath SlowInputFragment
set_option autoImplicit false

theorem copyBack_history_prefix (dict : List UInt8) (distance count : Nat) (history : List UInt8) :
    history <+: copyBack dict distance count history := by
  induction count generalizing history with
  | zero => exact List.prefix_refl _
  | succ count ih => exact (List.prefix_append _ _).trans (ih _)

/-- The independent grammar itself supplies the output-prefix ghost at a
payload cut. This is not an expected-output assumption on a source history. -/
theorem symbols_history_prefix {L D : List Nat} {dict history output : List UInt8}
    {input rest : List Bool} (symbols : Symbols L D dict history input rest output) :
    history <+: output := by
  induction symbols with
  | eob _ => exact List.prefix_refl _
  | lit _ _ _ ih => exact (List.prefix_append _ _).trans ih
  | copy _ _ _ _ _ _ _ _ _ ih => exact (copyBack_history_prefix _ _ _ _).trans ih

theorem token_effect_prefix {L D : List Nat} (token : TokenSyntax L D) (dict history : List UInt8) :
    history <+: token.effect dict history := by
  cases token with
  | literal _ _ _ _ _ => exact List.prefix_append _ _
  | copy _ => exact copyBack_history_prefix _ _ _ _
  | eob _ _ _ => exact List.prefix_refl _

/-- Exact global raw cursor and unchanged current-call output at a real
no-output code point. The residual bit source remains in CodePoint.source. -/
theorem code_point_global_cursor
    {h after : Heap} {s state : InflateState} {l regs : IL} {input : List UInt8}
    {future residual : List Bool} {r : ZStreamRef} {zs : Nat} {z initial : ZStream}
    {priorUsed used : Nat}
    (buffers : DispatchBuffers h r l (input.drop priorUsed))
    (priorBound : priorUsed ≤ input.length)
    (priorNext : l.next = inputAdvance initial.next_in priorUsed)
    (priorCount : l.have_.toNat + priorUsed = initial.avail_in.toNat)
    (priorPut : l.put = initial.next_out) (priorLeft : l.left = initial.avail_out)
    (priorOut : l.out_ = initial.avail_out)
    (point : CodePoint h s l (input.drop priorUsed) future r zs z after state regs used residual) :
    priorUsed + used ≤ input.length ∧
      regs.next = inputAdvance initial.next_in (priorUsed + used) ∧
      regs.have_.toNat + (priorUsed + used) = initial.avail_in.toNat ∧
      regs.put = initial.next_out ∧ regs.left = initial.avail_out ∧ regs.out_ = initial.avail_out ∧
      FutureSource regs (input.drop (priorUsed + used)) future residual := by
  have usedBound := point.bound
  simp only [List.length_drop] at usedBound
  have beforeCount := buffers.bits.have_eq
  have afterCount := point.bits.have_eq
  simp only [List.length_drop] at beforeCount afterCount
  refine ⟨by omega, ?_, by omega, ?_, ?_, ?_, ?_⟩
  · rw [point.cursor, priorNext, inputAdvance_add]
  · rw [point.shape]; exact priorPut
  · rw [point.shape]; exact priorLeft
  · rw [point.shape]; exact priorOut
  · simpa only [List.drop_drop] using point.source

def RepresentedCodeWait {L D : List Nat} (token : TokenSyntax L D) (c : Ctx)
    (h : Heap) (s : InflateState) (l : IL) (bs : List UInt8) (future : List Bool)
    (r : ZStreamRef) (zs : Nat) (z : ZStream) (logical : List UInt8) : Prop :=
  ∃ regs state,
    InputWait (inflate_dispatch c) h (setI h zs state) l bs future token.input regs ∧
    PayloadRepresentation (setI h zs state) r zs z state regs [] L D logical ∧
    TokenPhase token state token.input ∧ state = {s with mode := LEN, back := 0}

theorem code_wait_representation
    {L D : List Nat} {token : TokenSyntax L D} {c : Ctx} {h : Heap}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {future : List Bool} {logical : List UInt8}
    (E : Env c h r zs z s) (before : PayloadRepresentation h r zs z s l bs L D logical)
    (wait : TokenCodeWait token c h s l bs future r zs z) :
    RepresentedCodeWait token c h s l bs future r zs z logical := by
  obtain ⟨regs, state, source, point, phase, fields⟩ := wait
  obtain ⟨representation, _unchanged⟩ := code_point_representation E before point source.actual
  exact ⟨regs, state, source, by simpa only [List.drop_length] using representation, phase, fields⟩

/-- Actual LENS pointer resolution and stability are consumed from the
same representation produced by header installation. A literal code
either really waits or enters LIT with preserved tables/window/cursors. -/
theorem payload_literal_event
    {L D : List Nat} {symbol : Nat} {input rest : List Bool}
    (decoded : decodeSym L input = some (symbol, rest)) (small : symbol < 256)
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {future : List Bool} {logical : List UInt8}
    (E : Env c h r zs z s) (before : PayloadRepresentation h r zs z s l bs L D logical)
    (source : FutureSource l bs future input) (mode : s.mode = LEN ∨ s.mode = LEN_)
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    RepresentedCodeWait (.literal symbol input rest decoded small : TokenSyntax L D)
      c h s l bs future r zs z logical ∨
    (∃ after state regs used,
      CodePoint h s l bs future r zs z after state regs used rest ∧
      PayloadRepresentation after r zs z state regs (bs.drop used) L D logical ∧
      state.mode = LIT ∧ TokenPhase (.literal symbol input rest decoded small : TokenSyntax L D) state rest ∧
      runX (inflate_dispatch c) l h = .ok ((.ok (), regs), after)) := by
  have incoming := before
  obtain ⟨origin, buffers, _bits, tables, _dictionary⟩ := incoming
  obtain ⟨ref, offset, ca, extent, pointer, get, meaning, stable⟩ := tables.1
  have safe := origin.tables (mode.elim (fun m => Or.inr (Or.inl m)) Or.inl)
  rcases literal_code_event decoded small E origin.good safe pointer get meaning stable buffers.bits source mode slow with wait | progress
  · exact Or.inl (code_wait_representation E before wait)
  · obtain ⟨after, state, regs, used, point, lit, phase, actual⟩ := progress
    exact Or.inr ⟨after, state, regs, used, point,
      (code_point_representation E before point actual).1, lit, phase, actual⟩

/-- EOB reaches the real TYPE dispatch boundary on the same installed
representation and exact bit source. The outer loop remains live; this
theorem does not turn TYPE into a public return. -/
theorem payload_eob_event
    {L D : List Nat} {input rest : List Bool}
    (decoded : decodeSym L input = some (256, rest))
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {future : List Bool} {logical : List UInt8}
    (E : Env c h r zs z s) (before : PayloadRepresentation h r zs z s l bs L D logical)
    (source : FutureSource l bs future input) (mode : s.mode = LEN ∨ s.mode = LEN_)
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    RepresentedCodeWait (.eob input rest decoded : TokenSyntax L D)
      c h s l bs future r zs z logical ∨
    (∃ after state regs used,
      CodePoint h s l bs future r zs z after state regs used rest ∧
      PayloadRepresentation after r zs z state regs (bs.drop used) L D logical ∧
      state.mode = TYPE ∧ state.back = -1 ∧
      runX (inflate_dispatch c) l h = .ok ((.ok (), regs), after) ∧
      ∀ dict history, Token.Step L D dict history input rest history true ∧ Symbols L D dict history input rest history) := by
  have incoming := before
  obtain ⟨origin, buffers, _bits, tables, _dictionary⟩ := incoming
  obtain ⟨ref, offset, ca, extent, pointer, get, meaning, stable⟩ := tables.1
  have safe := origin.tables (mode.elim (fun m => Or.inr (Or.inl m)) Or.inl)
  rcases eob_code_event decoded E origin.good safe pointer get meaning stable buffers.bits source mode slow with wait | progress
  · exact Or.inl (code_wait_representation E before wait)
  · obtain ⟨after, state, regs, used, point, type, back, actual, token⟩ := progress
    exact Or.inr ⟨after, state, regs, used, point,
      (code_point_representation E before point actual).1, type, back, actual, token⟩

#print axioms copyBack_history_prefix
#print axioms symbols_history_prefix
#print axioms token_effect_prefix
#print axioms code_point_global_cursor
#print axioms code_wait_representation
#print axioms payload_literal_event
#print axioms payload_eob_event
end Zlib.Inflate.Proofs.FunctionalEpoch
