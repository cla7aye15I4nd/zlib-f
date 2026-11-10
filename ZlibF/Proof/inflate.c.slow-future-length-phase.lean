import ZlibF.Proof.«inflate.c.slow-copy-token»
import ZlibF.Proof.«inflate.c.slow-future-prefix»
namespace Zlib.Inflate.Proofs.SlowInputFragment
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inffast.Proofs Zlib.Inffast.Spec
open Zlib.Inftrees Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness
open SlowLenTokenPath SlowCopyTokenPath
set_option autoImplicit false
set_option maxRecDepth 10000
/-- Strengthen the already proved actual LEN_ code cut with the mode
written by its literal source suffix. No extra code or token premise. -/
theorem LEN_start_length_fields_mode
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {ref : CodeRef} {offset extent : Nat} {ca : Array Code} {L : List Nat}
    {l : IL} {bs : List UInt8} {symbol : Nat} {rest : List Bool}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (pointer : s.lencode = .ref ref offset) (tableGet : Space.get h ref = some ca)
    (meaning : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS ca offset s.lenbits.toNat extent L)
    (stable : Zlib.Inftrees.Spec.DecodeTableStability.StableQuery LENS ca offset s.lenbits.toNat)
    (B : BitInv h l bs) (decoded : decodeSym L (stream l bs) = some (symbol, rest))
    (lower : 257 ≤ symbol) (upper : symbol ≤ 285)
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    ∃ regs used after state,
      runX (inflate_LEN_ c) l h = runX (inflate_LENEXT c) regs after ∧
      used ≤ bs.length ∧ Good after r zs z state ∧ DataTablesSafe after state ∧
      BitInv after regs (bs.drop used) ∧ stream regs (bs.drop used) = rest ∧
      state.length.toNat = lengthBases.getD (symbol - 257) 0 ∧
      state.extra.toNat = lengthExtras.getD (symbol - 257) 0 ∧
      state.back = Int32.ofNat (L.getD symbol 0) ∧ state.mode = LENEXT ∧ DecodeStateFrame s state ∧
      SymbolRegShape l regs ∧ regs.next = inputAdvance l.next used ∧ after = setI h zs state := by
  obtain ⟨regs, used, heap, state, entry, cut, bound, current, currentTables, currentBits,
    symbolMeaning, restEq, length, back, frame, shape, cursor, heapEq⟩ :=
    LEN_start_leaf_fields E good tables pointer tableGet meaning stable B decoded
      (by simpa only [ValidSymbol, ite_true] using upper) slow
  have meaningFields : entry.op.toNat = 16 + lengthExtras.getD (symbol - 257) 0 ∧
      entry.val.toNat = lengthBases.getD (symbol - 257) 0 := by
    simpa only [SymbolEntry, ite_true, show ¬ symbol < 256 by omega,
      show symbol ≠ 256 by omega, ite_false, upper] using symbolMeaning
  have budget := length_symbol_budget (symbol - 257) (by omega)
  have opEq : entry.op = UInt8.ofNat (16 + lengthExtras.getD (symbol - 257) 0) := by
    apply UInt8.toNat_inj.mp
    rw [meaningFields.1, UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  have flags := length_flag_fields ⟨lengthExtras.getD (symbol - 257) 0, by omega⟩
  have nonzero : entry.op.toNat ≠ 0 := by rw [opEq]; exact flags.1
  have noEnd : entry.op &&& 32 = 0 := by rw [opEq]; exact flags.2.1
  have noInvalid : entry.op &&& 64 = 0 := by rw [opEq]; exact flags.2.2.1
  let final := {state with extra := entry.op.toUInt32 &&& 15, mode := LENEXT}
  let after := setI heap zs final
  have env : Env c heap r zs z state := ⟨E.strm, E.st, current.live.hz, current.live.hs⟩
  have tail : runX (lenLeafTail c entry) regs heap = runX (inflate_LENEXT c) regs after := by
    unfold lenLeafTail
    simp only [beq_iff_eq, nonzero, ite_false, noEnd, noInvalid, bne_self_eq_false,
      Bool.false_eq_true, runX_bind, runX_wrS env]
    rfl
  refine ⟨regs, used, after, final, cut.trans tail, bound,
    current.decode_update rfl (by change HEAD ≤ LENEXT ∧ LENEXT ≤ SYNC; decide),
    currentTables.decode_update current.live.hs rfl, currentBits.decode_update zs final,
    restEq, ?_, ?_, back, rfl, frame.trans (by rfl), shape, cursor, ?_⟩
  · change state.length.toNat = _
    rw [length, UInt16.toNat_toUInt32, meaningFields.2]
  · change (entry.op.toUInt32 &&& 15).toNat = _
    rw [opEq]
    exact flags.2.2.2
  · change setI heap zs final = _
    rw [heapEq, setI_setI]


/-- A whole valid future need not fit the current buffers. Once only its
length code fits, the actual source establishes the persistent LENEXT
syntax and the remaining global source, before reading any extra bits. -/
theorem LEN_future_phase {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {ref : CodeRef} {offset extent : Nat} {ca : Array Code}
    {L D : List Nat} {p : CopySyntax L D} {l : IL} {bs : List UInt8} {future : List Bool}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (pointer : s.lencode = .ref ref offset) (tableGet : Space.get h ref = some ca)
    (meaning : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS ca offset s.lenbits.toNat extent L)
    (stable : Zlib.Inftrees.Spec.DecodeTableStability.StableQuery LENS ca offset s.lenbits.toNat)
    (B : BitInv h l bs) (source : FutureSource l bs future p.input)
    (fits : L.getD p.symbol 0 ≤ (stream l bs).length)
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    ∃ regs used after state,
      runX (inflate_LEN_ c) l h = runX (inflate_LENEXT c) regs after ∧
      used ≤ bs.length ∧ Good after r zs z state ∧ DataTablesSafe after state ∧
      BitInv after regs (bs.drop used) ∧ state.mode = LENEXT ∧ PendingSyntax p state p.r1 ∧
      FutureSource regs (bs.drop used) future p.r1 ∧
      SymbolRegShape l regs ∧ regs.next = inputAdvance l.next used ∧ DecodeStateFrame s state ∧ after = setI h zs state := by
  have decoded : decodeSym L (stream l bs ++ future) = some (p.symbol, p.r1) := by
    rw [source]; exact p.lengthDecode
  obtain ⟨localDecode, suffix⟩ := decodeSym_restrict decoded fits
  obtain ⟨regs, used, after, state, run, bound, finalGood, finalTables, bits, streamEq,
    base, extra, back, mode, frame, shape, cursor, heap⟩ :=
    LEN_start_length_fields_mode E good tables pointer tableGet meaning stable B localDecode
      p.lengthLower p.lengthUpper slow
  refine ⟨regs, used, after, state, run, bound, finalGood, finalTables, bits, mode,
    .lenext mode base extra back, ?_, shape, cursor, frame, heap⟩
  unfold FutureSource
  rw [streamEq]
  exact suffix.symm

#print axioms LEN_start_length_fields_mode
#print axioms LEN_future_phase
end Zlib.Inflate.Proofs.SlowInputFragment
