import ZlibF.Proof.«inflate.c.slow-token-code-boundary»
namespace Zlib.Inflate.Proofs.SlowTokenPath
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inffast.Proofs Zlib.Inffast.Spec
open SlowInputFragment
open Zlib.Inftrees Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness
set_option autoImplicit false

/-- A no-output actual code transition, with the raw cursor distinct from
its independently remaining global bit source. -/
structure CodePoint (h : Heap) (s : InflateState) (l : IL) (bs : List UInt8) (future : List Bool)
    (r : ZStreamRef) (zs : Nat) (z : ZStream)
    (after : Heap) (state : InflateState) (regs : IL) (used : Nat) (residual : List Bool) : Prop where
  bound : used ≤ bs.length
  good : Good after r zs z state
  tables : DataTablesSafe after state
  bits : BitInv after regs (bs.drop used)
  source : FutureSource regs (bs.drop used) future residual
  shape : SymbolRegShape l regs
  cursor : regs.next = inputAdvance l.next used
  frame : DecodeStateFrame s state
  heap : after = setI h zs state

/-- A code wait has consumed all raw input but no logical code bits. -/
def TokenCodeWait {L D : List Nat} (token : TokenSyntax L D) (c : Ctx)
    (h : Heap) (s : InflateState) (l : IL) (bs : List UInt8) (future : List Bool)
    (r : ZStreamRef) (zs : Nat) (z : ZStream) : Prop :=
  ∃ regs state, InputWait (inflate_dispatch c) h (setI h zs state) l bs future token.input regs ∧
    CodePoint h s l bs future r zs z (setI h zs state) state regs bs.length token.input ∧
    TokenPhase token state token.input ∧ state = {s with mode := LEN, back := 0}

/-- Actual generic code waiting also supplies every no-output source and
buffer frame. Its instruction is the actual current dispatch. -/
theorem token_code_wait {L D : List Nat} {token : TokenSyntax L D}
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s state : InflateState}
    {l regs : IL} {bs : List UInt8} {future : List Bool}
    (E : Env c h r zs z s) (mode : s.mode = LEN ∨ s.mode = LEN_)
    (wait : InputWait (inflate_LEN_ c) h (setI h zs state) l bs future token.input regs)
    (good : Good (setI h zs state) r zs z state) (tables : DataTablesSafe (setI h zs state) state)
    (phase : TokenPhase token state token.input) (stateEq : state = {s with mode := LEN, back := 0}) :
    TokenCodeWait token c h s l bs future r zs z := by
  have actual := (dispatch_LEN_source_cut E l mode).trans wait.actual
  exact ⟨regs, state, {wait with actual := actual},
    ⟨Nat.le_refl _, good, tables, by simpa only [List.drop_length] using wait.bits,
      by simpa only [List.drop_length] using wait.source, wait.shape, wait.cursor, by rw [stateEq]; rfl, rfl⟩, phase, stateEq⟩

/-- A literal's real code either waits for input or installs LIT and the
actual byte/back fields. No output is emitted by this dispatch. -/
theorem literal_code_event {L D : List Nat} {symbol : Nat} {input rest : List Bool}
    (decoded : decodeSym L input = some (symbol, rest)) (small : symbol < 256)
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {future : List Bool}
    {ref : CodeRef} {offset extent : Nat} {ca : Array Code}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (pointer : s.lencode = .ref ref offset) (tableGet : Space.get h ref = some ca)
    (meaning : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS ca offset s.lenbits.toNat extent L)
    (stable : Zlib.Inftrees.Spec.DecodeTableStability.StableQuery LENS ca offset s.lenbits.toNat)
    (B : BitInv h l bs) (source : FutureSource l bs future input) (mode : s.mode = LEN ∨ s.mode = LEN_)
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    TokenCodeWait (.literal symbol input rest decoded small : TokenSyntax L D) c h s l bs future r zs z ∨
    (∃ after state regs used, CodePoint h s l bs future r zs z after state regs used rest ∧
      state.mode = LIT ∧ TokenPhase (.literal symbol input rest decoded small : TokenSyntax L D) state rest ∧
      runX (inflate_dispatch c) l h = .ok ((.ok (), regs), after)) := by
  rcases LEN_future_code_boundary (.literal symbol input rest decoded small : TokenSyntax L D)
      E good tables pointer tableGet meaning stable B source slow with wait | progress
  · obtain ⟨regs, state, actual, current, currentTables, phase, stateEq⟩ := wait
    exact Or.inl (token_code_wait E mode actual current currentTables phase stateEq)
  · obtain ⟨regs, used, heap, state, entry, cut, bound, current, currentTables, bits,
      symbolMeaning, nextSource, length, back, frame, shape, cursor, heapEq⟩ := progress
    have fields : entry.op = 0 ∧ entry.val.toNat = symbol := by
      simpa only [TokenSyntax.symbol, SymbolEntry, ite_true, small] using symbolMeaning
    let final := {state with mode := LIT}
    let after := setI heap zs final
    have env : Env c heap r zs z state := ⟨E.strm, E.st, current.live.hz, current.live.hs⟩
    have suffix : runX (lenLeafTail c entry) regs heap = .ok ((.ok (), regs), after) := by
      unfold lenLeafTail
      rw [fields.1]
      simp only [UInt8.toNat_zero, beq_self_eq_true, ite_true, runX_bind, runX_setMode env, runX_pure]
      rfl
    have finalGood : Good after r zs z final := current.decode_update rfl (by change HEAD ≤ LIT ∧ LIT ≤ SYNC; decide)
    have finalTables := currentTables.decode_update current.live.hs (after := final) rfl
    have finalBits := bits.decode_update zs final
    have point : CodePoint h s l bs future r zs z after final regs used rest :=
      ⟨bound, finalGood, finalTables, finalBits, nextSource, shape, cursor, frame.trans (by rfl), by
        dsimp only [after]; rw [heapEq, setI_setI]⟩
    have finalPhase : TokenPhase (.literal symbol input rest decoded small : TokenSyntax L D) final rest :=
      .literal rfl (by change state.length.toNat = symbol; rw [length, UInt16.toNat_toUInt32, fields.2]) back
    exact Or.inr ⟨after, final, regs, used, point, rfl, finalPhase, (dispatch_LEN_source_cut E l mode).trans (cut.trans suffix)⟩

/-- An EOB code either waits or really returns from this one dispatch in
TYPE. It does not force the outer loop or the public call to stop there. -/
theorem eob_code_event {L D : List Nat} {input rest : List Bool}
    (decoded : decodeSym L input = some (256, rest))
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {future : List Bool}
    {ref : CodeRef} {offset extent : Nat} {ca : Array Code}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (pointer : s.lencode = .ref ref offset) (tableGet : Space.get h ref = some ca)
    (meaning : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS ca offset s.lenbits.toNat extent L)
    (stable : Zlib.Inftrees.Spec.DecodeTableStability.StableQuery LENS ca offset s.lenbits.toNat)
    (B : BitInv h l bs) (source : FutureSource l bs future input) (mode : s.mode = LEN ∨ s.mode = LEN_)
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    TokenCodeWait (.eob input rest decoded : TokenSyntax L D) c h s l bs future r zs z ∨
    (∃ after state regs used, CodePoint h s l bs future r zs z after state regs used rest ∧
      state.mode = TYPE ∧ state.back = -1 ∧
      runX (inflate_dispatch c) l h = .ok ((.ok (), regs), after) ∧
      ∀ dict history, Token.Step L D dict history input rest history true ∧ Symbols L D dict history input rest history) := by
  rcases LEN_future_code_boundary (.eob input rest decoded : TokenSyntax L D)
      E good tables pointer tableGet meaning stable B source slow with wait | progress
  · obtain ⟨regs, state, actual, current, currentTables, phase, stateEq⟩ := wait
    exact Or.inl (token_code_wait E mode actual current currentTables phase stateEq)
  · obtain ⟨regs, used, heap, state, entry, cut, bound, current, currentTables, bits,
      symbolMeaning, nextSource, _length, _back, frame, shape, cursor, heapEq⟩ := progress
    have fields : entry.op = 96 ∧ entry.val = 0 := by
      simpa only [TokenSyntax.symbol, SymbolEntry, ite_true, show ¬ 256 < 256 by decide, ite_false] using symbolMeaning
    let final := {state with mode := TYPE, back := (-1 : Int32)}
    let after := setI heap zs final
    have env : Env c heap r zs z state := ⟨E.strm, E.st, current.live.hz, current.live.hs⟩
    have tailCode : lenLeafTail c entry = (do wrS c.st fun s => {s with back := -1, mode := TYPE}; pure ()) := by
      unfold lenLeafTail
      rw [fields.1]
      rfl
    have suffix : runX (lenLeafTail c entry) regs heap = .ok ((.ok (), regs), after) := by
      rw [tailCode]
      simp only [runX_bind, runX_wrS env, runX_pure]
      rfl
    have finalGood : Good after r zs z final := current.decode_update rfl (by change HEAD ≤ TYPE ∧ TYPE ≤ SYNC; decide)
    have finalTables := currentTables.decode_update current.live.hs (after := final) rfl
    have finalBits := bits.decode_update zs final
    have point : CodePoint h s l bs future r zs z after final regs used rest :=
      ⟨bound, finalGood, finalTables, finalBits, nextSource, shape, cursor, frame.trans (by rfl), by dsimp only [after]; rw [heapEq, setI_setI]⟩
    exact Or.inr ⟨after, final, regs, used, point, rfl, rfl, (dispatch_LEN_source_cut E l mode).trans (cut.trans suffix),
      fun _ _ => ⟨.eob decoded, .eob decoded⟩⟩

#print axioms token_code_wait
#print axioms literal_code_event
#print axioms eob_code_event
end Zlib.Inflate.Proofs.SlowTokenPath
