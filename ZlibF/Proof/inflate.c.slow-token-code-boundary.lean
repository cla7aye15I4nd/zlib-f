import ZlibF.Proof.«inflate.c.slow-token-syntax»
import ZlibF.Proof.«inflate.c.slow-short-code-wait»
import ZlibF.Proof.«inflate.c.slow-fragment-resume»
namespace Zlib.Inflate.Proofs.SlowTokenPath
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inffast.Proofs Zlib.Inffast.Spec
open SlowInputFragment SlowCopyTokenPath
open Zlib.Inftrees Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness
set_option autoImplicit false

/-- Every independent future token either really waits for its code or
reaches the actual selected-leaf suffix. No code-width/current-input or
full-token lookahead premise is imposed. -/
theorem LEN_future_code_boundary {L D : List Nat} (token : TokenSyntax L D)
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {future : List Bool}
    {ref : CodeRef} {offset extent : Nat} {ca : Array Code}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (pointer : s.lencode = .ref ref offset) (tableGet : Space.get h ref = some ca)
    (meaning : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS ca offset s.lenbits.toNat extent L)
    (stable : Zlib.Inftrees.Spec.DecodeTableStability.StableQuery LENS ca offset s.lenbits.toNat)
    (B : BitInv h l bs) (source : FutureSource l bs future token.input)
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    (∃ regs state, InputWait (inflate_LEN_ c) h (setI h zs state) l bs future token.input regs ∧
      Good (setI h zs state) r zs z state ∧ DataTablesSafe (setI h zs state) state ∧
      TokenPhase token state token.input ∧ state = {s with mode := LEN, back := 0}) ∨
    (∃ regs used after state entry,
      runX (inflate_LEN_ c) l h = runX (lenLeafTail c entry) regs after ∧
      used ≤ bs.length ∧ Good after r zs z state ∧ DataTablesSafe after state ∧
      BitInv after regs (bs.drop used) ∧ SymbolEntry LENS token.symbol entry ∧
      FutureSource regs (bs.drop used) future token.codeRest ∧ state.length = entry.val.toUInt32 ∧
      state.back = Int32.ofNat (L.getD token.symbol 0) ∧ DecodeStateFrame s state ∧
      SymbolRegShape l regs ∧ regs.next = inputAdvance l.next used ∧ after = setI h zs state) := by
  have valid : ValidSymbol LENS token.symbol := by simpa only [ValidSymbol, ite_true] using token.valid_symbol
  by_cases fits : L.getD token.symbol 0 ≤ (stream l bs).length
  · have decoded : decodeSym L (stream l bs ++ future) = some (token.symbol, token.codeRest) := by
      rw [source]; exact token.decode_code
    obtain ⟨localDecode, suffix⟩ := decodeSym_restrict decoded fits
    obtain ⟨regs, used, after, state, entry, actual, bound, current, currentTables, bits,
      symbol, rest, length, back, frame, shape, cursor, heap⟩ :=
      LEN_start_leaf_fields E good tables pointer tableGet meaning stable B localDecode valid slow
    exact Or.inr ⟨regs, used, after, state, entry, actual, bound, current, currentTables, bits, symbol,
      (by unfold FutureSource; rw [rest]; exact suffix.symm), length, back, frame, shape, cursor, heap⟩
  · let state := {s with mode := LEN, back := (0 : Int32)}
    let heap := setI h zs state
    have current : Good heap r zs z state := good.decode_update rfl (by change HEAD ≤ LEN ∧ LEN ≤ SYNC; decide)
    have currentTables : DataTablesSafe heap state := tables.decode_update good.live.hs rfl
    have currentGet : Space.get heap ref = some ca := by
      rw [decode_code_views good.live.hs (after := state) rfl]; exact tableGet
    have safe : LenTableSafe ca offset s.lenbits.toNat := by
      obtain ⟨otherRef, otherOffset, otherArray, otherPointer, otherGet, safe⟩ := tables.lengthTable
      rw [pointer] at otherPointer
      cases otherPointer
      have same := Option.some.inj (tableGet.symm.trans otherGet)
      subst otherArray
      exact safe
    obtain ⟨regs, wait⟩ := lenLookup_short_future E.st current.live.hs pointer currentGet safe meaning stable
      (B.decode_update zs state) source token.decode_code valid (by omega)
    have actual : runX (inflate_LEN_ c) l h = .ok ((.error Ex.leave, regs), heap) := by
      unfold inflate_LEN_
      rw [runX_bind, runX_setMode E]
      change runX (inflate_LEN c) l (setI h zs {s with mode := LEN}) = _
      rw [inflate_LEN_slow_cut slow, lenSlow_split, runX_bind]
      have env0 : Env c (setI h zs {s with mode := LEN}) r zs z {s with mode := LEN} :=
        ⟨E.strm, E.st, by simpa using E.hz, by simp⟩
      rw [runX_wrS env0]
      change runX (do lenLookup c; lenFinish c) l (setI (setI h zs {s with mode := LEN}) zs state) = _
      rw [setI_setI, runX_bind, wait.actual]
    exact Or.inl ⟨regs, state, {wait with actual := actual}, current, currentTables, .code (Or.inl rfl), rfl⟩

/-- The same code result belongs to the actual dispatch on either LEN
entry. The source's mode write is a self write on ordinary LEN. -/
theorem dispatch_LEN_source_cut {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) (l : IL) (mode : s.mode = LEN ∨ s.mode = LEN_) :
    runX (inflate_dispatch c) l h = runX (inflate_LEN_ c) l h := by
  rcases mode with mode | mode
  · exact (inflate_dispatch_LEN E l mode).trans (LEN_start_self E l mode).symm
  · exact inflate_dispatch_LEN_start E l mode

#print axioms LEN_future_code_boundary
#print axioms dispatch_LEN_source_cut
end Zlib.Inflate.Proofs.SlowTokenPath
