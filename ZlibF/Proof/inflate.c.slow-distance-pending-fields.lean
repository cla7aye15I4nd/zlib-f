import ZlibF.Proof.«inflate.c.slow-distance-to-match»

namespace Zlib.Inflate.Proofs.SlowDistancePendingFields
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec Zlib.Inflate.Proofs Zlib.Inffast.Proofs
open Zlib.Inftrees.Spec.DecodeSoundness Zlib.Inftrees.Spec.DecodeSemantics
open SlowDistanceSemanticPath SlowExtraSemanticPath Zlib.Inffast.Spec
set_option autoImplicit false

/-- The actual distance lookup writes only back, so pending length and
was survive both table levels on its returned heap. -/
theorem distLookup_pending_fields_of_run
    (before : Nat) {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s state : InflateState} {ref : CodeRef} {offset : Nat}
    {ca : Array Code} {l regs : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (tables : DataTablesSafe h s)
    (pointer : s.distcode = .ref ref offset) (tableGet : Space.get h ref = some ca)
    (B : BitInv h l bs) (back : s.back = Int32.ofNat before) (backBound : before ≤ 20)
    (run : runX (distLookup c) l h = .ok ((.ok (), regs), after))
    (stateGet : after.istates zs = some state) :
    state.length = s.length ∧ state.was = s.was := by
  have safe : DistTableSafe ca offset s.distbits.toNat := by
    obtain ⟨otherRef, otherOffset, otherArray, otherPointer, otherGet, otherSafe⟩ := tables.distanceTable
    rw [pointer] at otherPointer
    cases otherPointer
    have same := Option.some.inj (tableGet.symm.trans otherGet)
    subst otherArray
    exact otherSafe
  obtain ⟨result, current, used, heap, actual, _four, _bound, _bits, _shape,
    _bitBound, _kinds, done, _leave, _cursor⟩ :=
    distLookup_run_cursor E.st E.hs pointer tableGet safe before back backBound B
  have same := Except.ok.inj (actual.symm.trans run)
  cases same
  obtain ⟨dropped, _dropBound, heapEq, _leaf, _fit, _source, _count⟩ := done rfl
  rw [heapEq, setI_istates_same] at stateGet
  have stateEq := Option.some.inj stateGet
  rw [← stateEq]
  exact ⟨rfl, rfl⟩

theorem inflate_DIST_token_cut_with_pending
    (before : Nat) {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {ref : CodeRef} {offset usedExtent : Nat} {ca : Array Code} {alphabet : List Nat}
    {l : IL} {bs : List UInt8} {symbol : Nat} {rest : List Bool}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (pointer : s.distcode = .ref ref offset) (tableGet : Space.get h ref = some ca)
    (meaning : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv DISTS ca offset s.distbits.toNat usedExtent alphabet)
    (stable : Zlib.Inftrees.Spec.DecodeTableStability.StableQuery DISTS ca offset s.distbits.toNat)
    (B : BitInv h l bs) (back : s.back = Int32.ofNat before) (backBound : before ≤ 20)
    (decoded : decodeSym alphabet (stream l bs) = some (symbol, rest))
    (valid : ValidSymbol DISTS symbol) :
    ∃ regs used after state entry,
      runX (inflate_DIST c) l h = runX (distLeafTail c entry) regs after ∧
      used ≤ 4 ∧ used ≤ bs.length ∧ Good after r zs z state ∧ DataTablesSafe after state ∧
      BitInv after regs (bs.drop used) ∧ SymbolEntry DISTS symbol entry ∧
      rest = stream regs (bs.drop used) ∧
      state.back = Int32.ofNat (before + alphabet.getD symbol 0) ∧
      DecodeStateFrame s state ∧ SymbolRegShape l regs ∧
      regs.next = inputAdvance l.next used ∧ after = setI h zs state ∧
      state.length = s.length ∧ state.was = s.was := by
  obtain ⟨looked, used, heap, lookupState, dropped, lookup, four, bound, dropBound,
    current, currentTables, bits, lookupShape, lookupFrame, currentBack, leaf, symbolMeaning,
    width, enough, source, restEq, cursor, heapEq⟩ :=
    distLookup_token_run before E.st good tables pointer tableGet meaning stable B back backBound decoded valid
  have pendingFields := distLookup_pending_fields_of_run before E tables pointer tableGet B back backBound lookup current.live.hs
  obtain ⟨regs, after, state, finish, finalGood, finalTables, finalBits, frame, regShape,
    finalHeap, stateEq, suffix, count, here, next⟩ :=
    distFinish_consume_cursor before dropped E.st current currentTables leaf currentBack backBound enough bits
  refine ⟨regs, used, after, state, looked.here, ?_, four, bound, finalGood, finalTables,
    finalBits, symbolMeaning, restEq.trans suffix.symm, ?_, lookupFrame.trans frame,
    lookupShape.trans regShape, next.trans cursor, ?_, ?_, ?_⟩
  · rw [inflate_DIST_lookup_cut, runX_bind, lookup]
    exact finish
  · rw [stateEq]
    change Int32.ofNat (before + dropped + looked.here.bits.toNat) = _
    rw [Nat.add_assoc, width]
  · rw [finalHeap, heapEq, setI_setI]

  · rw [stateEq]
    exact pendingFields.1
  · rw [stateEq]
    exact pendingFields.2

theorem inflate_DIST_symbol_fields_with_pending
    (before : Nat) {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {ref : CodeRef} {offset usedExtent : Nat} {ca : Array Code} {alphabet : List Nat}
    {l : IL} {bs : List UInt8} {symbol : Nat} {rest : List Bool}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (pointer : s.distcode = .ref ref offset) (tableGet : Space.get h ref = some ca)
    (meaning : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv DISTS ca offset s.distbits.toNat usedExtent alphabet)
    (stable : Zlib.Inftrees.Spec.DecodeTableStability.StableQuery DISTS ca offset s.distbits.toNat)
    (B : BitInv h l bs) (back : s.back = Int32.ofNat before) (backBound : before ≤ 20)
    (decoded : decodeSym alphabet (stream l bs) = some (symbol, rest)) (valid : symbol ≤ 29) :
    ∃ regs used after state,
      runX (inflate_DIST c) l h = runX (inflate_DISTEXT c) regs after ∧
      used ≤ 4 ∧ used ≤ bs.length ∧ Good after r zs z state ∧ DataTablesSafe after state ∧
      BitInv after regs (bs.drop used) ∧ rest = stream regs (bs.drop used) ∧
      state.mode = DISTEXT ∧ state.offset.toNat = distBases.getD symbol 0 ∧
      state.extra.toNat = distExtras.getD symbol 0 ∧
      state.back = Int32.ofNat (before + alphabet.getD symbol 0) ∧
      DecodeStateFrame s state ∧ SymbolRegShape l regs ∧
      regs.next = inputAdvance l.next used ∧ after = setI h zs state ∧
      state.length = s.length ∧ state.was = s.was := by
  obtain ⟨regs, used, heap, state, entry, cut, four, bound, current, currentTables,
    currentBits, symbolMeaning, restEq, currentBack, frame, shape, cursor, heapEq, pendingLength, pendingWas⟩ :=
    inflate_DIST_token_cut_with_pending before E good tables pointer tableGet meaning stable B back backBound decoded
      (by simpa only [ValidSymbol, show DISTS ≠ LENS by decide, ite_false] using valid)
  have meaningFields : entry.op.toNat = 16 + distExtras.getD symbol 0 ∧
      entry.val.toNat = distBases.getD symbol 0 := by
    simpa only [SymbolEntry, show DISTS ≠ LENS by decide, ite_false, valid, ite_true] using symbolMeaning
  have extraBound := distance_extra_bound symbol (by omega)
  have opEq : entry.op = UInt8.ofNat (16 + distExtras.getD symbol 0) := by
    apply UInt8.toNat_inj.mp
    rw [meaningFields.1, UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  have flags := distance_flag_fields ⟨distExtras.getD symbol 0, by omega⟩
  have noInvalid : entry.op &&& 64 = 0 := by rw [opEq]; exact flags.1
  let final := {state with offset := entry.val.toUInt32, extra := entry.op.toUInt32 &&& 15, mode := DISTEXT}
  let after := setI heap zs final
  have env : Env c heap r zs z state := ⟨E.strm, E.st, current.live.hz, current.live.hs⟩
  have tail : runX (distLeafTail c entry) regs heap = runX (inflate_DISTEXT c) regs after := by
    unfold distLeafTail
    simp only [noInvalid, bne_self_eq_false, Bool.false_eq_true, ite_false, runX_bind, runX_wrS env]
    have env1 : Env c (setI heap zs {state with offset := entry.val.toUInt32, extra := entry.op.toUInt32 &&& 15}) r zs z
        {state with offset := entry.val.toUInt32, extra := entry.op.toUInt32 &&& 15} :=
      ⟨E.strm, E.st, by simpa using env.hz, by simp⟩
    rw [runX_setMode env1]
    simp only [setI_setI]
    rfl
  refine ⟨regs, used, after, final, cut.trans tail, four, bound,
    current.decode_update rfl (by change HEAD ≤ DISTEXT ∧ DISTEXT ≤ SYNC; decide),
    currentTables.decode_update current.live.hs rfl, currentBits.decode_update zs final,
    restEq, rfl, ?_, ?_, currentBack, frame.trans (by rfl), shape, cursor, ?_, pendingLength, pendingWas⟩
  · change entry.val.toUInt32.toNat = _
    rw [UInt16.toNat_toUInt32, meaningFields.2]
  · change (entry.op.toUInt32 &&& 15).toNat = _
    rw [opEq]
    exact flags.2
  · change setI heap zs final = _
    rw [heapEq, setI_setI]


theorem DIST_to_MATCH_read_semantics_with_pending
    (before : Nat) {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {ref : CodeRef} {offset usedExtent : Nat} {ca : Array Code} {alphabet : List Nat}
    {l : IL} {bs : List UInt8} {symbol value : Nat} {codeRest rest : List Bool}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (pointer : s.distcode = .ref ref offset) (tableGet : Space.get h ref = some ca)
    (meaning : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv DISTS ca offset s.distbits.toNat usedExtent alphabet)
    (stable : Zlib.Inftrees.Spec.DecodeTableStability.StableQuery DISTS ca offset s.distbits.toNat)
    (B : BitInv h l bs) (back : s.back = Int32.ofNat before) (backBound : before ≤ 20)
    (decoded : decodeSym alphabet (stream l bs) = some (symbol, codeRest)) (valid : symbol ≤ 29)
    (read : readBits (distExtras.getD symbol 0) codeRest = some (value, rest)) :
    ∃ regs after state used,
      runX (inflate_DIST c) l h = runX (inflate_MATCH c) regs after ∧
      used ≤ bs.length ∧ Good after r zs z state ∧ DataTablesSafe after state ∧
      BitInv after regs (bs.drop used) ∧ state.mode = MATCH ∧ DecodeStateFrame s state ∧
      SymbolRegShape l regs ∧ stream regs (bs.drop used) = rest ∧
      state.offset.toNat = distBases.getD symbol 0 + value ∧
      1 ≤ state.offset.toNat ∧ state.offset.toNat ≤ 32768 ∧
      distBases.getD symbol 0 + value < 2 ^ 32 ∧
      state.back = Int32.ofNat (before + alphabet.getD symbol 0 + distExtras.getD symbol 0) ∧
      after = setI h zs state ∧ regs.next = inputAdvance l.next used ∧
      state.length = s.length ∧ state.was = s.was := by
  obtain ⟨middle, firstUsed, firstHeap, firstState, firstRun, _four, firstBound,
    firstGood, firstTables, firstB, firstRest, firstMode, base, width,
    firstBack, firstFrame, firstShape, firstCursor, firstHeapEq, pendingLength, pendingWas⟩ :=
    inflate_DIST_symbol_fields_with_pending before E good tables pointer tableGet meaning stable B back backBound decoded valid
  have codeBound : alphabet.getD symbol 0 ≤ 15 := by
    by_cases inside : symbol < alphabet.length
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inside, Option.getD_some]
      exact meaning.acceptable.1 _ (List.getElem_mem inside)
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : alphabet.length ≤ symbol), Option.getD_none]
      decide
  have readCurrent : readBits (distExtras.getD symbol 0) (stream middle (bs.drop firstUsed)) = some (value, rest) := by
    simpa only [← firstRest] using read
  obtain ⟨regs, after, state, secondUsed, secondRun, secondBound, finalGood,
    finalTables, finalB, finalMode, secondFrame, secondShape, finalRest,
    exactOffset, stateEq, lower, upper, noWrap, finalHeapEq, finalCursor, _bits⟩ :=
    DISTEXT_symbol_read_semantics (before + alphabet.getD symbol 0) E.strm E.st
      firstGood firstTables firstB valid base width firstBack (by omega) readCurrent
  have dropEq : (bs.drop firstUsed).drop secondUsed = bs.drop (firstUsed + secondUsed) := by
    rw [List.drop_drop, Nat.add_comm]
  have finalBack : state.back = Int32.ofNat (before + alphabet.getD symbol 0 + distExtras.getD symbol 0) := by
    rw [stateEq]
    simp only [width]
  refine ⟨regs, after, state, firstUsed + secondUsed, firstRun.trans secondRun, ?_,
    finalGood, finalTables, ?_, finalMode, firstFrame.trans secondFrame,
    firstShape.trans secondShape, ?_, exactOffset, lower, upper, noWrap,
    finalBack, ?_, ?_, (by rw [stateEq]; exact pendingLength), (by rw [stateEq]; exact pendingWas)⟩
  · have bound := secondBound
    simp only [List.length_drop] at bound
    omega
  · simpa only [dropEq] using finalB
  · simpa only [dropEq] using finalRest
  · rw [finalHeapEq, firstHeapEq, setI_setI]
  · rw [finalCursor, firstCursor, inputAdvance_add]


#print axioms distLookup_pending_fields_of_run
#print axioms DIST_to_MATCH_read_semantics_with_pending
#print axioms inflate_DIST_token_cut_with_pending
#print axioms inflate_DIST_symbol_fields_with_pending
end Zlib.Inflate.Proofs.SlowDistancePendingFields
