import ZlibF.Proof.«inflate.c.slow-distance-pending-fields»
import ZlibF.Proof.«inflate.c.pending-dispatch»
import ZlibF.Proof.«inflate.c.slow-len-token»
import ZlibF.Proof.«inflate.c.slow-distance-to-match»
import ZlibF.Proof.«inflate.c.slow-match-pending»
import ZlibF.Proof.Format.Token
namespace Zlib.Inflate.Proofs.SlowCopyTokenPath
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inffast.Proofs Zlib.Inffast.Spec
open Zlib.Inftrees Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness
open SlowLenTokenPath SlowExtraSemanticPath SlowMatchCompletion
open ZlibF.Math.LZ77Copy
set_option autoImplicit false
set_option maxRecDepth 10000
/-- The actual LEN_ source reaches its selected leaf with exact code
consumption and all scalar/byte frames needed to continue parsing. -/
theorem LEN_start_leaf_fields
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {ref : CodeRef} {offset extent : Nat} {ca : Array Code} {L : List Nat}
    {l : IL} {bs : List UInt8} {symbol : Nat} {rest : List Bool}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (pointer : s.lencode = .ref ref offset) (tableGet : Space.get h ref = some ca)
    (meaning : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS ca offset s.lenbits.toNat extent L)
    (stable : Zlib.Inftrees.Spec.DecodeTableStability.StableQuery LENS ca offset s.lenbits.toNat)
    (B : BitInv h l bs) (decoded : decodeSym L (stream l bs) = some (symbol, rest))
    (valid : ValidSymbol LENS symbol)
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    ∃ regs used after state entry,
      runX (inflate_LEN_ c) l h = runX (lenLeafTail c entry) regs after ∧
      used ≤ bs.length ∧ Good after r zs z state ∧ DataTablesSafe after state ∧
      BitInv after regs (bs.drop used) ∧ SymbolEntry LENS symbol entry ∧
      stream regs (bs.drop used) = rest ∧ state.length = entry.val.toUInt32 ∧
      state.back = Int32.ofNat (L.getD symbol 0) ∧ DecodeStateFrame s state ∧
      SymbolRegShape l regs ∧ regs.next = inputAdvance l.next used ∧ after = setI h zs state := by
  let start := {s with mode := LEN, back := (0 : Int32)}
  let heap := setI h zs start
  have current : Good heap r zs z start := good.decode_update rfl
    (by change HEAD ≤ LEN ∧ LEN ≤ SYNC; decide)
  have currentTables : DataTablesSafe heap start := tables.decode_update good.live.hs rfl
  have currentGet : Space.get heap ref = some ca := by
    rw [decode_code_views good.live.hs (after := start) rfl]; exact tableGet
  obtain ⟨looked, used, heap1, state1, dropped, lookup, four, bound, dropBound,
    good1, tables1, bits1, shape1, frame1, back1, leaf, symbolMeaning,
    width, enough, source, restEq, cursor, heapEq⟩ :=
    lenLookup_token_run E.st current currentTables pointer currentGet meaning stable (B.decode_update zs start)
      rfl decoded valid
  obtain ⟨regs, after, state, finish, finalGood, finalTables, finalBits, frame, shape,
    length, back, suffix, count, here, afterEq, next⟩ :=
    lenFinish_consume_cursor dropped E.st good1 tables1 leaf
      (by rw [back1]; exact back_ofNat_small dropped dropBound) enough bits1
  have sourceRun : runX (inflate_LEN_ c) l h = runX (lenFinish c) looked heap1 := by
    unfold inflate_LEN_
    rw [runX_bind, runX_setMode E]
    change runX (inflate_LEN c) l (setI h zs {s with mode := LEN}) = _
    rw [inflate_LEN_slow_cut slow, lenSlow_split, runX_bind]
    have env0 : Env c (setI h zs {s with mode := LEN}) r zs z {s with mode := LEN} :=
      ⟨E.strm, E.st, by simpa using E.hz, by simp⟩
    rw [runX_wrS env0]
    change runX (do lenLookup c; lenFinish c) l (setI (setI h zs {s with mode := LEN}) zs start) = _
    rw [setI_setI, runX_bind, lookup]
  refine ⟨regs, used, after, state, looked.here, sourceRun.trans finish, bound, finalGood, finalTables,
    finalBits, symbolMeaning, suffix.trans restEq.symm, length, ?_,
    DecodeStateFrame.trans (by rfl) (frame1.trans frame), shape1.trans shape, next.trans cursor, ?_⟩
  · rw [back, width]
  · rw [afterEq, heapEq, setI_setI]
    exact setI_setI h zs start state

/-- Length symbol fields have the format's bounded base/extra budget. -/
theorem length_symbol_budget : ∀ index, index < 29 →
    lengthExtras.getD index 0 ≤ 5 ∧
    3 ≤ lengthBases.getD index 0 ∧
    lengthBases.getD index 0 + 2 ^ lengthExtras.getD index 0 ≤ 259 := by
  decide +kernel
/-- Length leaf operation bits carry only sixteen plus their extra count. -/
theorem length_flag_fields : ∀ extra : Fin 6,
    (UInt8.ofNat (16 + extra.val)).toNat ≠ 0 ∧
    (UInt8.ofNat (16 + extra.val) &&& 32) = 0 ∧
    (UInt8.ofNat (16 + extra.val) &&& 64) = 0 ∧
    (((UInt8.ofNat (16 + extra.val)).toUInt32 &&& 15).toNat) = extra.val := by
  decide +kernel
/-- The independently decoded length symbol installs its real base and
extra count at LENEXT, with the exact consumed-code back counter. -/
theorem LEN_start_length_fields
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
      state.back = Int32.ofNat (L.getD symbol 0) ∧ DecodeStateFrame s state ∧
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
    restEq, ?_, ?_, back, frame.trans (by rfl), shape, cursor, ?_⟩
  · change state.length.toNat = _
    rw [length, UInt16.toNat_toUInt32, meaningFields.2]
  · change (entry.op.toUInt32 &&& 15).toNat = _
    rw [opEq]
    exact flags.2.2.2
  · change setI heap zs final = _
    rw [heapEq, setI_setI]

/-- Exact actual length decoding, including its independent extra bits,
establishes parsed length = was before the real distance parser. -/
theorem LEN_start_length_read
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {ref : CodeRef} {offset extent : Nat} {ca : Array Code} {L : List Nat}
    {l : IL} {bs : List UInt8} {symbol value : Nat} {codeRest rest : List Bool}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (pointer : s.lencode = .ref ref offset) (tableGet : Space.get h ref = some ca)
    (meaning : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS ca offset s.lenbits.toNat extent L)
    (stable : Zlib.Inftrees.Spec.DecodeTableStability.StableQuery LENS ca offset s.lenbits.toNat)
    (B : BitInv h l bs) (decoded : decodeSym L (stream l bs) = some (symbol, codeRest))
    (lower : 257 ≤ symbol) (upper : symbol ≤ 285)
    (read : readBits (lengthExtras.getD (symbol - 257) 0) codeRest = some (value, rest))
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    ∃ regs used after state,
      runX (inflate_LEN_ c) l h = runX (inflate_DIST c) regs after ∧
      used ≤ bs.length ∧ Good after r zs z state ∧ DataTablesSafe after state ∧
      BitInv after regs (bs.drop used) ∧ stream regs (bs.drop used) = rest ∧
      state.length.toNat = lengthBases.getD (symbol - 257) 0 + value ∧ state.was = state.length ∧
      3 ≤ state.length.toNat ∧ state.length.toNat ≤ 258 ∧ state.mode = DIST ∧
      state.back = Int32.ofNat (L.getD symbol 0 + lengthExtras.getD (symbol - 257) 0) ∧
      DecodeStateFrame s state ∧ SymbolRegShape l regs ∧ regs.next = inputAdvance l.next used ∧
      after = setI h zs state := by
  obtain ⟨middle, used1, heap1, state1, run1, bound1, good1, tables1, B1,
    source1, base1, extra1, back1, frame1, shape1, cursor1, heapEq1⟩ :=
    LEN_start_length_fields E good tables pointer tableGet meaning stable B decoded lower upper slow
  have budget := length_symbol_budget (symbol - 257) (by omega)
  have codeBound : L.getD symbol 0 ≤ 15 := by
    by_cases inside : symbol < L.length
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inside, Option.getD_some]
      exact meaning.acceptable.1 _ (List.getElem_mem inside)
    · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : L.length ≤ symbol)]
  have read1 : readBits state1.extra.toNat (stream middle (bs.drop used1)) = some (value, rest) := by
    rw [extra1, source1]; exact read
  obtain ⟨regs, after, state, used2, run2, bound2, current, currentTables, currentB,
    mode, frame2, shape2, sourceDrop, was, length, source, low, high, back, heapEq2, cursor2, _⟩ :=
    LENEXT_read_semantics (L.getD symbol 0) E.strm E.st good1 tables1 B1
      (by rw [extra1]; exact budget.1) (by rw [base1]; exact budget.2.1)
      (by rw [base1, extra1]; exact budget.2.2) back1 codeBound read1
  have dropEq : (bs.drop used1).drop used2 = bs.drop (used1 + used2) := by rw [List.drop_drop, Nat.add_comm]
  refine ⟨regs, used1 + used2, after, state, run1.trans run2, ?_, current, currentTables,
    by simpa only [dropEq] using currentB, by simpa only [dropEq] using source,
    by rw [length, base1], was, low, high, mode, by rw [back, extra1],
    frame1.trans frame2, shape1.trans shape2, ?_, ?_⟩
  · simp only [List.length_drop] at bound2
    omega
  · rw [cursor2, cursor1, inputAdvance_add]
  · rw [heapEq2, heapEq1, setI_setI]
/-- Private scalar decoding preserves the actual retained dictionary. -/
theorem dictionary_decode_frame
    {h : Heap} {zs : Nat} {s state : InflateState} {dict : List UInt8}
    (dictionary : InflateDictionary h s dict) (frame : DecodeStateFrame s state) :
    InflateDictionary (setI h zs state) state dict := by
  have window : state.window = s.window := by rw [frame]
  have size : state.wsize = s.wsize := by rw [frame]
  have count : state.whave = s.whave := by rw [frame]
  have next : state.wnext = s.wnext := by rw [frame]
  rcases dictionary with empty | ⟨ref, off, array, pointer, get, fit, bytes⟩
  · exact Or.inl ⟨by rw [count]; exact empty.1, empty.2⟩
  · exact Or.inr ⟨ref, off, array, by rw [window]; exact pointer,
      by rw [byte_view_get_setI]; exact get,
      by simpa only [size] using fit, by simpa only [count, next] using bytes⟩
/-- A parsed MATCH prefix is a prefix of the original LEN_ dispatch,
whose first source call already falls through to MATCH. Empty output
instead makes that very first dispatch leave at the parsed pending state. -/
theorem lift_LEN_start_match_prefix
    {c : Ctx} {h parsedHeap after : Heap} {r : ZStreamRef} {zs : Nat}
    {z parsedZ : ZStream} {s parsedState : InflateState} {l parsedRegs regs : IL} {steps : Nat}
    (E : Env c h r zs z s) (mode : s.mode = LEN_)
    (parsedEnv : Env c parsedHeap r zs parsedZ parsedState) (parsedMode : parsedState.mode = MATCH)
    (cut : runX (inflate_LEN_ c) l h = runX (inflate_MATCH c) parsedRegs parsedHeap)
    (trace : MatchSteps c parsedRegs parsedHeap regs after steps)
    (empty : steps = 0 → regs.left = 0) :
    MatchSteps c l h regs after steps ∨
      runX (inflate_dispatch c) l h = .ok ((.error Ex.leave, regs), after) := by
  cases trace with
  | refl =>
    right
    rw [inflate_dispatch_LEN_start E l mode, cut]
    exact inflate_MATCH_wait c parsedHeap parsedRegs (empty rfl)
  | step first remaining =>
    left
    have dispatchCut : runX (inflate_dispatch c) l h = runX (inflate_dispatch c) parsedRegs parsedHeap := by
      rw [inflate_dispatch_LEN_start E l mode, inflate_dispatch_MATCH parsedEnv parsedRegs parsedMode]
      exact cut
    exact MatchSteps.step (dispatchCut.trans first) remaining
/-- A finite successful prefix can be followed by a future independent
Symbols derivation once its complete token has established that grammar
constructor. This introduces no validity requirement on earlier output. -/
theorem copy_token_composes_symbols
    {L D : List Nat} {dict history output : List UInt8} {input rest : List Bool}
    (token : Token.Step L D dict history input rest output false) :
    ∀ tail finalOutput, Symbols L D dict output rest tail finalOutput →
      Symbols L D dict history input tail finalOutput :=
  (Token.step_composes_symbols L D dict history input rest output false token).2 rfl
/-- An actual finite dispatch prefix followed by a proved leave executes
that very source loop; the finite prefix carries the loop budget. -/
theorem dispatch_prefix_then_leave
    {c : Ctx} {l regs : IL} {h after : Heap} {steps : Nat}
    (trace : MatchSteps c l h regs after steps)
    (leave : runX (inflate_dispatch c) regs after = .ok ((.error Ex.leave, regs), after))
    (budget : steps + 1 < fuel) :
    runX (xwhile (pure true) (inflate_dispatch c)) l h = .ok ((.error Ex.leave, regs), after) := by
  let P : Nat → IL → Heap → Prop := fun k current heap =>
    ∃ remaining, k = remaining + 1 ∧ MatchSteps c current heap regs after remaining
  let Q : Except Ex Unit → IL → Heap → Prop := fun result current heap =>
    result = .error Ex.leave ∧ current = regs ∧ heap = after
  have step : ∀ k current heap, P (k + 1) current heap →
      ∃ middle heap1, runX (pure true : X Bool) current heap = .ok ((.ok true, middle), heap1) ∧
      ∃ result final heap2, runX (do inflate_dispatch c; pure false : X Bool) middle heap1 = .ok ((result, final), heap2) ∧
        (match result with
        | .ok true => Q (.ok ()) final heap2
        | .ok false => P k final heap2
        | .error e => Q (.error e) final heap2) := by
    intro k current heap inv
    obtain ⟨remaining, count, path⟩ := inv
    refine ⟨current, heap, rfl, ?_⟩
    cases path with
    | refl =>
      refine ⟨.error Ex.leave, regs, after, ?_, rfl, rfl, rfl⟩
      rw [runX_bind, leave]
    | @step firstL firstH middle heap final after n actual rest =>
      refine ⟨.ok false, middle, heap, ?_, n, by omega, rest⟩
      rw [runX_bind, actual]
      rfl
  obtain ⟨result, final, heap, actual, resultEq, finalEq, heapEq⟩ :=
    xwhileBrk_run P Q step (by
      intro current heap inv
      obtain ⟨remaining, count, path⟩ := inv
      omega) (k := steps + 1) ⟨steps, rfl, trace⟩ budget
  subst result final heap
  exact actual
/-- Complete independent copy-token reads establish the real MATCH phase
from LEN_: parsed length, was, distance, back and exact remaining bits are
produced by the actual code, before any output segment is executed. -/
theorem slow_copy_match_entry
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {lr dr : CodeRef} {lo le doff de : Nat} {la da : Array Code} {L D : List Nat}
    {l : IL} {bs : List UInt8} {symbol ds xl xd : Nat} {r1 r2 r3 rest : List Bool}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (lp : s.lencode = .ref lr lo) (lg : Space.get h lr = some la)
    (li : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS la lo s.lenbits.toNat le L)
    (ls : Zlib.Inftrees.Spec.DecodeTableStability.StableQuery LENS la lo s.lenbits.toNat)
    (dp : s.distcode = .ref dr doff) (dg : Space.get h dr = some da)
    (di : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv DISTS da doff s.distbits.toNat de D)
    (dstable : Zlib.Inftrees.Spec.DecodeTableStability.StableQuery DISTS da doff s.distbits.toNat)
    (B : BitInv h l bs) (decoded : decodeSym L (stream l bs) = some (symbol, r1))
    (lower : 257 ≤ symbol) (upper : symbol ≤ 285)
    (lengthRead : readBits (lengthExtras.getD (symbol - 257) 0) r1 = some (xl, r2))
    (distanceDecoded : decodeSym D r2 = some (ds, r3)) (distanceValid : ds ≤ 29)
    (distanceRead : readBits (distExtras.getD ds 0) r3 = some (xd, rest))
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    ∃ regs used after state,
      runX (inflate_LEN_ c) l h = runX (inflate_MATCH c) regs after ∧
      used ≤ bs.length ∧ Good after r zs z state ∧ DataTablesSafe after state ∧
      BitInv after regs (bs.drop used) ∧ stream regs (bs.drop used) = rest ∧
      state.mode = MATCH ∧ state.length.toNat = lengthBases.getD (symbol - 257) 0 + xl ∧
      state.was = state.length ∧ 3 ≤ state.length.toNat ∧ state.length.toNat ≤ 258 ∧
      state.offset.toNat = distBases.getD ds 0 + xd ∧ 1 ≤ state.offset.toNat ∧ state.offset.toNat ≤ 32768 ∧
      state.back = Int32.ofNat (L.getD symbol 0 + lengthExtras.getD (symbol - 257) 0 + D.getD ds 0 + distExtras.getD ds 0) ∧
      DecodeStateFrame s state ∧ SymbolRegShape l regs ∧ regs.next = inputAdvance l.next used ∧
      after = setI h zs state := by
  obtain ⟨middle, used1, heap1, state1, run1, bound1, good1, tables1, B1, source1,
    length1, was1, low1, high1, mode1, back1, frame1, shape1, cursor1, heapEq1⟩ :=
    LEN_start_length_read E good tables lp lg li ls B decoded lower upper lengthRead slow
  have distancePointer : state1.distcode = .ref dr doff := by rw [frame1]; exact dp
  have distanceGet : Space.get heap1 dr = some da := by
    rw [heapEq1, decode_code_views good.live.hs frame1]; exact dg
  have distanceMeaning : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv DISTS da doff state1.distbits.toNat de D := by
    have bits : state1.distbits = s.distbits := by rw [frame1]
    rwa [bits]
  have distanceStable : Zlib.Inftrees.Spec.DecodeTableStability.StableQuery DISTS da doff state1.distbits.toNat := by
    have bits : state1.distbits = s.distbits := by rw [frame1]
    rwa [bits]
  have env1 : Env c heap1 r zs z state1 := ⟨E.strm, E.st, good1.live.hz, good1.live.hs⟩
  have codeBound : L.getD symbol 0 ≤ 15 := by
    by_cases inside : symbol < L.length
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inside, Option.getD_some]
      exact li.acceptable.1 _ (List.getElem_mem inside)
    · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : L.length ≤ symbol)]
  have extraBound := (length_symbol_budget (symbol - 257) (by omega)).1
  have distanceDecoded1 : decodeSym D (stream middle (bs.drop used1)) = some (ds, r3) := by
    rw [source1]; exact distanceDecoded
  obtain ⟨regs, after, state, used2, run2, bound2, finalGood, finalTables, finalB, finalMode,
    frame2, shape2, source, offset, distanceLow, distanceHigh, noWrap, back, heapEq2, cursor2,
    pendingLength, pendingWas⟩ :=
    SlowDistancePendingFields.DIST_to_MATCH_read_semantics_with_pending
      (L.getD symbol 0 + lengthExtras.getD (symbol - 257) 0)
      env1 good1 tables1 distancePointer distanceGet distanceMeaning distanceStable B1 back1 (by omega)
      distanceDecoded1 distanceValid distanceRead
  have dropEq : (bs.drop used1).drop used2 = bs.drop (used1 + used2) := by rw [List.drop_drop, Nat.add_comm]
  refine ⟨regs, used1 + used2, after, state, run1.trans run2, ?_, finalGood, finalTables,
    by simpa only [dropEq] using finalB, by simpa only [dropEq] using source,
    finalMode, by rw [pendingLength]; exact length1, ?_, by rw [pendingLength]; exact low1,
    by rw [pendingLength]; exact high1, offset, distanceLow, distanceHigh, back,
    frame1.trans frame2, shape1.trans shape2, ?_, ?_⟩
  · simp only [List.length_drop] at bound2
    omega
  · rw [pendingWas, was1, pendingLength]
  · rw [cursor2, cursor1, inputAdvance_add]
  · rw [heapEq2, heapEq1, setI_setI]
/-- Zero successful source steps preserve the exact registers and heap. -/
theorem matchSteps_zero {c : Ctx} {l regs : IL} {h after : Heap} {steps : Nat}
    (trace : MatchSteps c l h regs after steps) (zero : steps = 0) : regs = l ∧ after = h := by
  cases trace with
  | refl => exact ⟨rfl, rfl⟩
  | step first rest => omega
/-- A nonempty parsed MATCH prefix starts with the actual original LEN_
dispatch, rather than an invented extra call to MATCH. -/
theorem lift_LEN_start_nonempty_match_prefix
    {c : Ctx} {h parsedHeap after : Heap} {r : ZStreamRef} {zs : Nat}
    {z parsedZ : ZStream} {s parsedState : InflateState} {l parsedRegs regs : IL} {steps : Nat}
    (E : Env c h r zs z s) (mode : s.mode = LEN_)
    (parsedEnv : Env c parsedHeap r zs parsedZ parsedState) (parsedMode : parsedState.mode = MATCH)
    (cut : runX (inflate_LEN_ c) l h = runX (inflate_MATCH c) parsedRegs parsedHeap)
    (trace : MatchSteps c parsedRegs parsedHeap regs after steps) (nonempty : steps ≠ 0) :
    MatchSteps c l h regs after steps := by
  cases trace with
  | refl => exact False.elim (nonempty rfl)
  | step first rest =>
    have firstRun : runX (inflate_dispatch c) l h = runX (inflate_dispatch c) parsedRegs parsedHeap := by
      rw [inflate_dispatch_LEN_start E l mode, inflate_dispatch_MATCH parsedEnv parsedRegs parsedMode]
      exact cut
    exact MatchSteps.step (firstRun.trans first) rest

/-- A dispatch that actually leaves is exactly one iteration of its loop. -/
theorem dispatch_one_leave
    {c : Ctx} {h after : Heap} {l regs : IL}
    (actual : runX (inflate_dispatch c) l h = .ok ((.error Ex.leave, regs), after)) :
    runX (xwhile (pure true) (inflate_dispatch c)) l h = .ok ((.error Ex.leave, regs), after) := by
  have rule := xwhileBrk_run (cond := pure true) (body := (do inflate_dispatch c; pure false : X Bool))
    (fun k current heap => k = 1 ∧ current = l ∧ heap = h)
    (fun result current heap => result = .error Ex.leave ∧ current = regs ∧ heap = after)
    (by
      intro k current heap inv
      obtain ⟨count, sameL, sameH⟩ := inv
      subst current heap
      refine ⟨l, h, rfl, .error Ex.leave, regs, after, ?_, rfl, rfl, rfl⟩
      rw [runX_bind, actual])
    (by intro current heap inv; have := inv.1; omega)
    (k := 1) ⟨rfl, rfl, rfl⟩ (by unfold fuel; decide)
  obtain ⟨result, final, heap, run, rfl, rfl, rfl⟩ := rule
  exact run

theorem slow_copy_token_prefix
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {lr dr : CodeRef} {lo le doff de : Nat} {la da : Array Code} {L D : List Nat}
    {l : IL} {bs dict : List UInt8} {dest : BRef} {outOffset : Nat} {output : Array UInt8} {symbol ds xl xd : Nat} {r1 r2 r3 rest : List Bool}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (lp : s.lencode = .ref lr lo) (lg : Space.get h lr = some la)
    (li : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS la lo s.lenbits.toNat le L)
    (ls : Zlib.Inftrees.Spec.DecodeTableStability.StableQuery LENS la lo s.lenbits.toNat)
    (dp : s.distcode = .ref dr doff) (dg : Space.get h dr = some da)
    (di : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv DISTS da doff s.distbits.toNat de D)
    (dstable : Zlib.Inftrees.Spec.DecodeTableStability.StableQuery DISTS da doff s.distbits.toNat)
    (B : BitInv h l bs) (decoded : decodeSym L (stream l bs) = some (symbol, r1))
    (lower : 257 ≤ symbol) (upper : symbol ≤ 285)
    (lengthRead : readBits (lengthExtras.getD (symbol - 257) 0) r1 = some (xl, r2))
    (distanceDecoded : decodeSym D r2 = some (ds, r3)) (distanceValid : ds ≤ 29)
    (distanceRead : readBits (distExtras.getD ds 0) r3 = some (xd, rest))
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true)
    (initialMode : s.mode = LEN_) (sane : s.sane ≠ 0)
    (dictionary : InflateDictionary h s dict)
    (put : l.put = .ref dest outOffset) (get : Space.get h dest = some output) (write : Space.ro h dest = false)
    (room : outOffset + l.left.toNat ≤ output.size) (count : l.left.toNat ≤ l.out_.toNat)
    (produced : l.out_.toNat - l.left.toNat ≤ outOffset)
    (privateWindow : ∀ w, s.window = .ref (.blk w) 0 → dest ≠ .blk w)
    (separate : Separate l.next l.have_.toNat l.put l.left.toNat)
    (available : distBases.getD ds 0 + xd ≤ dict.length + (l.out_.toNat - l.left.toNat)) :
    let total := lengthBases.getD (symbol - 257) 0 + xl
    let distance := distBases.getD ds 0 + xd
    let history := writtenBytes output outOffset (l.out_.toNat - l.left.toNat)
    ∃ regs used after state array steps made,
      (MatchSteps c l h regs after steps ∨
        runX (inflate_dispatch c) l h = .ok ((.error Ex.leave, regs), after)) ∧
      used ≤ bs.length ∧ steps ≤ total ∧ made = min total l.left.toNat ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧ BitInv after regs (bs.drop used) ∧
      InflateDictionary after state dict ∧ stream regs (bs.drop used) = rest ∧
      state.offset.toNat = distance ∧ state.length.toNat = total - made ∧
      Space.get after dest = some array ∧ array.size = output.size ∧ Space.ro after dest = false ∧
      regs.left.toNat + made = l.left.toNat ∧ regs.put = .ref dest (outOffset + made) ∧
      Separate regs.next regs.have_.toNat regs.put regs.left.toNat ∧
      writtenBytes array (outOffset + made) (l.out_.toNat - l.left.toNat + made) =
        copyBack dict distance made history ∧
      Token.Step L D dict history (stream l bs) rest (copyBack dict distance total history) false ∧
      ((made = total ∧ state.mode = LEN ∧ MatchSteps c l h regs after steps) ∨
       (made < total ∧ state.mode = MATCH ∧ state.was.toNat = total ∧
        0 < state.length.toNat ∧ state.length.toNat ≤ state.was.toNat ∧
        state.back = Int32.ofNat (L.getD symbol 0 + lengthExtras.getD (symbol - 257) 0 + D.getD ds 0 + distExtras.getD ds 0) ∧
        regs.left = 0 ∧
        runX (inflate_dispatch c) regs after = .ok ((.error Ex.leave, regs), after) ∧
        runX (xwhile (pure true) (inflate_dispatch c)) l h = .ok ((.error Ex.leave, regs), after))) := by
  dsimp only
  obtain ⟨parsed, used, heap, ps, cut, bound, current, currentTables, currentB, source,
    mode, length, was, low, high, offset, distanceLow, distanceHigh, back, frame, shape, cursor, heapEq⟩ :=
    slow_copy_match_entry E good tables lp lg li ls dp dg di dstable B decoded lower upper lengthRead
      distanceDecoded distanceValid distanceRead slow
  have env : Env c heap r zs z ps := ⟨E.strm, E.st, current.live.hz, current.live.hs⟩
  have parsedDict : InflateDictionary heap ps dict := by rw [heapEq]; exact dictionary_decode_frame dictionary frame
  have parsedGet : Space.get heap dest = some output := by rw [heapEq, byte_view_get_setI]; exact get
  have parsedWrite : Space.ro heap dest = false := by rw [heapEq, byte_view_ro_setI]; exact write
  have putEq : parsed.put = l.put := by rw [shape]
  have leftEq : parsed.left = l.left := by rw [shape]
  have outEq : parsed.out_ = l.out_ := by rw [shape]
  have parsedPut : parsed.put = .ref dest outOffset := putEq.trans put
  have parsedRoom : outOffset + parsed.left.toNat ≤ output.size := by rw [leftEq]; exact room
  have parsedCount : parsed.left.toNat ≤ parsed.out_.toNat := by rw [leftEq, outEq]; exact count
  have parsedProduced : parsed.out_.toNat - parsed.left.toNat ≤ outOffset := by rw [leftEq, outEq]; exact produced
  have parsedWindow : ∀ w, ps.window = .ref (.blk w) 0 → dest ≠ .blk w := by
    intro w pointer
    apply privateWindow w
    simpa only [show ps.window = s.window by rw [frame]] using pointer
  have parsedSane : ps.sane ≠ 0 := by rw [frame]; exact sane
  have parsedSeparate : Separate parsed.next parsed.have_.toNat parsed.put parsed.left.toNat := by
    have advanced := inputAdvance_separate l.next l.put l.have_.toNat l.left.toNat used
      (by rw [B.have_eq]; exact bound) separate
    rw [cursor, putEq, leftEq]
    have countEq : parsed.have_.toNat = l.have_.toNat - used := by
      rw [currentB.have_eq, B.have_eq, List.length_drop]
    rwa [countEq]
  have parsedAvailable : ps.offset.toNat ≤ dict.length + (parsed.out_.toNat - parsed.left.toNat) := by
    rw [offset, outEq, leftEq]; exact available
  have historyLength : (writtenBytes output outOffset (l.out_.toNat - l.left.toNat)).length =
      l.out_.toNat - l.left.toNat := by
    simp only [writtenBytes, List.length_take, List.length_drop, Array.length_toList]
    omega
  have token : Token.Step L D dict (writtenBytes output outOffset (l.out_.toNat - l.left.toNat))
      (stream l bs) rest (copyBack dict (distBases.getD ds 0 + xd)
        (lengthBases.getD (symbol - 257) 0 + xl) (writtenBytes output outOffset (l.out_.toNat - l.left.toNat))) false :=
    Token.Step.copy decoded lower upper lengthRead distanceDecoded distanceValid distanceRead
      (by simpa only [List.length_append, historyLength] using available)
  by_cases enough : ps.length.toNat ≤ parsed.left.toNat
  · obtain ⟨regs, after, state, array, steps, path, stepsBound, finalGood, finalTables, finalB,
      finalDict, finalMode, finalLength, finalOffset, finalFrame, finalShape, finalGet,
      finalSize, finalWrite, finalCount, finalPut, finalSeparate, bytes⟩ :=
      complete_valid_match env current currentTables parsedDict currentB mode parsedSane parsedPut parsedGet
        parsedWrite (by omega) (by omega) parsedRoom enough parsedCount parsedProduced parsedWindow
        parsedSeparate parsedAvailable
    have nonempty : steps ≠ 0 := by
      intro zero
      obtain ⟨sameRegs, sameHeap⟩ := matchSteps_zero path zero
      have getState := finalGood.live.hs
      rw [sameHeap] at getState
      have sameState : state = ps := Option.some.inj (getState.symm.trans current.live.hs)
      rw [sameState, mode] at finalMode
      contradiction
    have actualPath := lift_LEN_start_nonempty_match_prefix E initialMode env mode cut path nonempty
    have streamRest : stream regs (bs.drop used) = rest := by rw [finalShape]; exact source
    refine ⟨regs, used, after, state, array, steps, ps.length.toNat, Or.inl actualPath, bound,
      by rw [← length]; exact stepsBound, ?_, finalGood, finalTables, finalB, finalDict, streamRest,
      by rw [finalOffset]; exact offset, ?_, finalGet, finalSize, finalWrite, ?_, ?_, finalSeparate,
      ?_, token, Or.inl ⟨length, finalMode, actualPath⟩⟩
    · rw [← length]
      exact (Nat.min_eq_left (by rwa [leftEq] at enough)).symm
    · rw [finalLength]
      simp only [UInt32.toNat_zero, ← length, Nat.sub_self]
    · rwa [leftEq] at finalCount
    · exact finalPut
    · simpa only [length, offset, outEq, leftEq] using bytes
  · have short : parsed.left.toNat < ps.length.toNat := by omega
    obtain ⟨regs, after, state, array, steps, path, stepsBound, finalGood, finalTables, finalB,
      finalDict, finalMode, remaining, positive, finalOffset, finalWas, finalBack, finalFrame,
      finalShape, finalGet, finalSize, finalWrite, finalLeft, finalPut, finalSeparate, finalStream,
      nextLeave, bytes⟩ :=
      pending_valid_match env current currentTables parsedDict currentB mode parsedSane parsedPut parsedGet
        parsedWrite (by omega) parsedRoom short parsedCount parsedProduced parsedWindow parsedSeparate parsedAvailable
    have actualPrefix := lift_LEN_start_match_prefix E initialMode env mode cut path
      (fun _ => finalLeft)
    have nextEnv : Env c after r zs z state := ⟨E.strm, E.st, finalGood.live.hz, finalGood.live.hs⟩
    have dispatchLeave : runX (inflate_dispatch c) regs after = .ok ((.error Ex.leave, regs), after) := by
      rw [inflate_dispatch_MATCH nextEnv regs finalMode]
      exact nextLeave
    have actualLoop : runX (xwhile (pure true) (inflate_dispatch c)) l h = .ok ((.error Ex.leave, regs), after) := by
      rcases actualPrefix with successful | immediate
      · exact dispatch_prefix_then_leave successful dispatchLeave (by unfold fuel; omega)
      · exact dispatch_one_leave immediate
    have streamRest := finalStream.trans source
    refine ⟨regs, used, after, state, array, steps, parsed.left.toNat, actualPrefix, bound,
      by rw [← length]; omega, ?_, finalGood, finalTables, finalB, finalDict, streamRest,
      by rw [finalOffset]; exact offset, by rw [remaining, length], finalGet, finalSize, finalWrite,
      ?_, ?_, finalSeparate, ?_, token, Or.inr ⟨?_, finalMode, ?_, positive, ?_, ?_, finalLeft, dispatchLeave, actualLoop⟩⟩
    · rw [← length, ← leftEq]
      exact (Nat.min_eq_right (by omega)).symm
    · rw [finalLeft, leftEq]
      simp only [UInt32.toNat_zero, Nat.zero_add]
    · exact finalPut
    · have index : l.out_.toNat - l.left.toNat + l.left.toNat = l.out_.toNat := by omega
      simpa only [offset, outEq, leftEq, index] using bytes
    · rw [← length]; exact short
    · rw [finalWas, was, length]
    · rw [finalWas, was]
      omega
    · rw [finalBack]
      exact back
/-- Once the current token's exact emitted prefix is known, finishing its
pending bytes yields exactly the complete independent token before the
future Symbols continuation. -/
theorem pending_token_symbols_continuation
    {L D : List Nat} {dict history : List UInt8} {input rest : List Bool} {distance total made : Nat}
    (token : Token.Step L D dict history input rest (copyBack dict distance total history) false)
    (bound : made ≤ total) :
    ∀ tail output,
      Symbols L D dict (copyBack dict distance (total - made) (copyBack dict distance made history))
        rest tail output → Symbols L D dict history input tail output := by
  intro tail output continuation
  rw [pending_copy_continuation dict history distance total made bound] at continuation
  exact copy_token_composes_symbols token tail output continuation

#print axioms LEN_start_leaf_fields
#print axioms length_symbol_budget
#print axioms length_flag_fields
#print axioms LEN_start_length_fields
#print axioms LEN_start_length_read
#print axioms dictionary_decode_frame
#print axioms lift_LEN_start_match_prefix
#print axioms copy_token_composes_symbols
#print axioms dispatch_prefix_then_leave
#print axioms slow_copy_match_entry
#print axioms matchSteps_zero
#print axioms lift_LEN_start_nonempty_match_prefix
#print axioms dispatch_one_leave
#print axioms slow_copy_token_prefix
#print axioms pending_token_symbols_continuation
end Zlib.Inflate.Proofs.SlowCopyTokenPath
