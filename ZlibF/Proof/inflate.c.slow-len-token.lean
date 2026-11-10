import ZlibF.Proof.«inflate.c.slow-subtable-path»

namespace Zlib.Inflate.Proofs.SlowLenTokenPath
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec
open Zlib.Inflate.Proofs Zlib.Inftrees
open Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness
open Zlib.Inffast.Proofs Zlib.Inffast.Spec
open Zlib.Inflate.Proofs.SlowSubtablePath
set_option autoImplicit false

/-- A valid token traverses the actual remembered-root lookup and commits
exactly the root bit drop and checked back update of lenSubLookup. -/
theorem lenSubLookup_token_run
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {ref : CodeRef} {offset usedExtent : Nat} {ca : Array Code} {alphabet : List Nat}
    {l : IL} {bs : List UInt8} {symbol : Nat} {rest : List Bool} {first : Code}
    (hc : c.st = some (.tab zs)) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (pointer : s.lencode = .ref ref offset) (tableGet : Space.get h ref = some ca)
    (meaning : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS ca offset s.lenbits.toNat usedExtent alphabet)
    (stable : Zlib.Inftrees.Spec.DecodeTableStability.StableQuery LENS ca offset s.lenbits.toNat)
    (B : BitInv h l bs) (back : s.back = 0)
    (rootCell : ca[offset + l.hold.toNat % 2 ^ s.lenbits.toNat]? = some first)
    (rootEnough : s.lenbits.toNat ≤ l.bits.toNat)
    (link : Zlib.Inftrees.Spec.Subtable.IsLink LENS first = true)
    (linkShape : LinkOK LenLeaf ca offset first)
    (decoded : decodeSym alphabet (stream l bs) = some (symbol, rest))
    (valid : ValidSymbol LENS symbol) :
    ∃ regs used,
      let state := {s with back := Int32.ofNat first.bits.toNat}
      let after := setI h zs state
      runX (lenSubLookup c first) l h = .ok ((.ok (), regs), after) ∧
      used ≤ 2 ∧ used ≤ bs.length ∧ Good after r zs z state ∧ DataTablesSafe after state ∧
      BitInv after regs (bs.drop used) ∧ SymbolRegShape l regs ∧
      LenLeaf first.bits.toNat regs.here ∧ SymbolEntry LENS symbol regs.here ∧
      first.bits.toNat + regs.here.bits.toNat = alphabet.getD symbol 0 ∧
      regs.here.bits.toNat ≤ regs.bits.toNat ∧
      stream regs (bs.drop used) = (stream l bs).drop first.bits.toNat ∧
      rest = (stream regs (bs.drop used)).drop regs.here.bits.toNat ∧
      regs.next = inputAdvance l.next used := by
  let start := {l with last := first}
  have startInv : BitInv h start bs := ⟨B.have_eq, B.next, B.hold_lt⟩
  obtain ⟨current, used, lookup, two, bound, currentInv, source, shape,
    lastEq, cursor, symbolMeaning, width, totalEnough, restEq⟩ :=
    lookup2_token_run (first := first) hc good.live.hs pointer tableGet meaning stable startInv rfl rootCell rootEnough
      link decoded valid
  have selectedLeaf : LenLeaf first.bits.toNat current.here := by
    obtain ⟨otherResult, otherRegs, otherUsed, otherRun, _, _, _, _, _, _, _, selected, leaf,
      _, _, _, _, _⟩ := lookup2_data_run_cursor false first hc good.live.hs pointer tableGet
        (l := start) rfl linkShape (fun _ leaf => leaf.1) startInv
    have same := Prod.mk.inj (Prod.mk.inj (Except.ok.inj (lookup.symm.trans otherRun))).1
    obtain ⟨sameResult, sameRegs⟩ := same
    rwa [← sameRegs] at leaf
  have rootSmall : first.bits.toUInt32.toNat < 64 := by
    rw [UInt8.toNat_toUInt32]
    have bound := linkShape.1
    omega
  have rootFit : first.bits.toUInt32.toNat ≤ current.bits.toNat := by
    rw [UInt8.toNat_toUInt32]
    omega
  obtain ⟨nextInv, nextStream, nextCount⟩ := DROPBITS_inv currentInv first.bits.toUInt32 rootFit rootSmall
  let regs := {current with hold := current.hold >>> first.bits.toUInt32.toUInt64, bits := current.bits - first.bits.toUInt32}
  let state := {s with back := Int32.ofNat first.bits.toNat}
  let after := setI h zs state
  have checked : chkI32 (s.back.toInt + first.bits.toNat) h = .ok (Int32.ofNat first.bits.toNat, h) := by
    rw [back]
    simp only [Int32.toInt_zero, Int.zero_add]
    unfold chkI32
    have rootBound := linkShape.1
    split
    · rfl
    · omega
  have load : ldInflateState c.st h = .ok (s, h) := by rw [hc, ldI_eq, good.live.hs]
  have write : wrS c.st (fun s => {s with back := Int32.ofNat first.bits.toNat}) h = .ok ((), after) := by
    rw [hc, wrI_eq, good.live.hs]
  have actual : runX (lenSubLookup c first) l h = .ok ((.ok (), regs), after) := by
    unfold lenSubLookup
    rw [runX_bind, runX_modify]
    change runX (do
      lookup2 c false
      let last := (← get).last
      DROPBITS last.bits.toUInt32
      let s ← ldInflateState c.st
      let bk ← chkI32 (s.back.toInt + last.bits.toNat)
      wrS c.st fun s => {s with back := bk}) start h = _
    simp only [runX_bind, lookup, runX_get, lastEq,
      DROPBITS_run current h _ rootSmall, runX_lift_ok load,
      runX_lift_ok checked, runX_lift_ok write]
    simp only [regs, lastEq]
  have finalSource : stream regs (bs.drop used) = (stream l bs).drop first.bits.toNat := by
    change stream regs (bs.drop used) = (stream start bs).drop first.bits.toNat
    simpa only [UInt8.toNat_toUInt32] using nextStream.trans
      (congrArg (List.drop first.bits.toUInt32.toNat) source)
  have finalRest : rest = (stream regs (bs.drop used)).drop regs.here.bits.toNat := by
    rw [finalSource, List.drop_drop]
    simpa only [Nat.add_comm, regs, start, stream] using restEq
  refine ⟨regs, used, actual, two, bound,
    good.decode_update rfl good.live.mode, tables.decode_update good.live.hs rfl,
    nextInv.decode_update zs state, ?_, selectedLeaf, symbolMeaning, width, ?_, finalSource, finalRest, cursor⟩
  · exact (SymbolRegShape.trans (b := start) (by rfl) shape.symbol).trans (by rfl)
  · change current.here.bits.toNat ≤ (current.bits - first.bits.toUInt32).toNat
    rw [nextCount, UInt8.toNat_toUInt32]
    omega

/-- Both actual root and link paths of lenLookup produce the same
independent valid token, including the exact consumed-root prefix. -/
theorem lenLookup_token_run
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {ref : CodeRef} {offset usedExtent : Nat} {ca : Array Code} {alphabet : List Nat}
    {l : IL} {bs : List UInt8} {symbol : Nat} {rest : List Bool}
    (hc : c.st = some (.tab zs)) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (pointer : s.lencode = .ref ref offset) (tableGet : Space.get h ref = some ca)
    (meaning : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS ca offset s.lenbits.toNat usedExtent alphabet)
    (stable : Zlib.Inftrees.Spec.DecodeTableStability.StableQuery LENS ca offset s.lenbits.toNat)
    (B : BitInv h l bs) (back : s.back = 0)
    (decoded : decodeSym alphabet (stream l bs) = some (symbol, rest))
    (valid : ValidSymbol LENS symbol) :
    ∃ regs used after state dropped,
      runX (lenLookup c) l h = .ok ((.ok (), regs), after) ∧
      used ≤ 4 ∧ used ≤ bs.length ∧ dropped ≤ 15 ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧ BitInv after regs (bs.drop used) ∧
      SymbolRegShape l regs ∧ DecodeStateFrame s state ∧ state.back = Int32.ofNat dropped ∧
      LenLeaf dropped regs.here ∧ SymbolEntry LENS symbol regs.here ∧
      dropped + regs.here.bits.toNat = alphabet.getD symbol 0 ∧ regs.here.bits.toNat ≤ regs.bits.toNat ∧
      stream regs (bs.drop used) = (stream l bs).drop dropped ∧
      rest = (stream regs (bs.drop used)).drop regs.here.bits.toNat ∧
      regs.next = inputAdvance l.next used ∧ after = setI h zs state := by
  have safe : LenTableSafe ca offset s.lenbits.toNat := by
    obtain ⟨otherRef, otherOffset, otherArray, otherPointer, otherGet, otherSafe⟩ := tables.lengthTable
    rw [pointer] at otherPointer
    cases otherPointer
    have same := Option.some.inj (tableGet.symm.trans otherGet)
    subst otherArray
    exact otherSafe
  obtain ⟨current, used, lookup, two, bound, inv, source, shape, cursor, selected, enough⟩ :=
    lookup1_valid_token_run hc good.live.hs pointer tableGet meaning B decoded valid
  have cell : ca[offset + current.hold.toNat % 2 ^ s.lenbits.toNat]? = some current.here := by
    have inside : offset + current.hold.toNat % 2 ^ s.lenbits.toNat < ca.size := by
      have extent := meaning.rootTable.2.2.1
      have index := Nat.mod_lt current.hold.toNat (Nat.two_pow_pos s.lenbits.toNat)
      omega
    rw [selected, codeLookupValue, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem inside, Option.getD_some]
  have classification := safe.2.2 _ (Nat.mod_lt current.hold.toNat (Nat.two_pow_pos s.lenbits.toNat))
  change current.here = ca.getD (offset + current.hold.toNat % 2 ^ s.lenbits.toNat) default at selected
  rw [← selected] at classification
  have prefixRun : runX (lenLookup c) l h = runX (lenRootTail c current.here) current h := by
    unfold lenLookup
    rw [runX_bind, lookup]
    simp only [runX_bind, runX_get]
  by_cases slowLink : SlowLenLink current.here
  · have fastLink := slowLenLink_fast slowLink
    rw [ite_eq_left fastLink] at classification
    have link : Zlib.Inftrees.Spec.Subtable.IsLink LENS current.here = true := by
      simp only [Zlib.Inftrees.Spec.Subtable.IsLink, ite_true, Bool.and_eq_true, bne_iff_ne, beq_iff_eq]
      exact slowLink
    have rootBits := (meaning.subtables _ current.here
      (Nat.mod_lt _ (Nat.two_pow_pos _)) cell link).1
    have rootEnough : s.lenbits.toNat ≤ current.bits.toNat := by omega
    have decodedCurrent : decodeSym alphabet (stream current (bs.drop used)) = some (symbol, rest) := by
      rw [source]; exact decoded
    obtain ⟨regs, used2, subRun, two2, bound2, good2, tables2, inv2, shape2,
      leaf, symbolMeaning, width, fit, bits, restEq, next⟩ :=
      lenSubLookup_token_run hc good tables pointer tableGet meaning stable inv back cell rootEnough
        link classification decodedCurrent valid
    let state := {s with back := Int32.ofNat current.here.bits.toNat}
    let after := setI h zs state
    have totalBound : used + used2 ≤ bs.length := by
      simp only [List.length_drop] at bound2
      omega
    have finalInv : BitInv after regs (bs.drop (used + used2)) := by
      simpa only [List.drop_drop, Nat.add_comm] using inv2
    have finalSource : stream regs (bs.drop (used + used2)) =
        (stream l bs).drop current.here.bits.toNat := by
      simpa only [List.drop_drop, Nat.add_comm] using bits.trans
        (congrArg (List.drop current.here.bits.toNat) source)
    refine ⟨regs, used + used2, after, state, current.here.bits.toNat, ?_, by omega,
      totalBound, classification.1, good2, tables2, finalInv, shape.symbol.trans shape2,
      rfl, rfl, leaf, symbolMeaning, width, fit, finalSource, ?_, ?_, rfl⟩
    · rw [prefixRun, lenRootTail_link c current.here slowLink]
      exact subRun
    · simpa only [List.drop_drop, Nat.add_comm] using restEq
    · rw [next, cursor, inputAdvance_add]
  · have notFastLink : ¬ LenLink current.here := by
      intro link
      have table := classification
      rw [ite_eq_left link] at table
      exact slowLink (lenLink_slow link table)
    rw [ite_eq_right notFastLink] at classification
    obtain ⟨suffix, query⟩ := ZlibF.Math.InflateHeldBits.padded_query inv.hold_lt meaning.rootTable.2.1
    have heldQuery : tableRead LENS ca offset s.lenbits.toNat
        (Zlib.Inftrees.Spec.DecodeShort.padded (bitsOfNat current.hold.toNat current.bits.toNat)) =
        some (current.here, current.here.bits.toNat) := by
      simp [tableRead, query, cell]
      intro nonzero high
      exact False.elim (slowLink ⟨nonzero, high⟩)
    have fullQuery := stable _ _ _ heldQuery
      (by simpa only [bitsOfNat_length] using enough) (bytesBits (bs.drop used))
    have sourceEq : bitsOfNat current.hold.toNat current.bits.toNat ++ bytesBits (bs.drop used) = stream l bs := by
      simpa only [stream, natBits_testBit, bitsOfNat] using source
    rw [sourceEq] at fullQuery
    obtain ⟨desired, consumed, forward, accepted, symbolMeaning, width, fitted, restEq⟩ :=
      Zlib.Inftrees.Proofs.DecodeForward.lookup_of_decode meaning decoded valid
    obtain ⟨entries, widths⟩ := Prod.mk.inj (Option.some.inj (fullQuery.symm.trans forward))
    rw [← entries] at symbolMeaning
    refine ⟨current, used, h, s, 0, ?_, by omega, bound, by omega, good, tables, inv,
      shape.symbol, rfl, by change s.back = 0; exact back,
      classification, symbolMeaning, by simpa using widths.trans width, enough, ?_, ?_, cursor, ?_⟩
    · rw [prefixRun, lenRootTail_leaf c current.here slowLink, runX_pure]
    · simpa using source
    · rw [source]
      rwa [← widths] at restEq
    · simp only [setI, upd_self _ _ _ good.live.hs]

/-- A complete independent token reaches the exact actual LEN leaf
classification cut, after both root and leaf bit consumption. -/
theorem slow_LEN_token_cut
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {ref : CodeRef} {offset usedExtent : Nat} {ca : Array Code} {alphabet : List Nat}
    {l : IL} {bs : List UInt8} {symbol : Nat} {rest : List Bool}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (pointer : s.lencode = .ref ref offset) (tableGet : Space.get h ref = some ca)
    (meaning : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS ca offset s.lenbits.toNat usedExtent alphabet)
    (stable : Zlib.Inftrees.Spec.DecodeTableStability.StableQuery LENS ca offset s.lenbits.toNat)
    (B : BitInv h l bs)
    (decoded : decodeSym alphabet (stream l bs) = some (symbol, rest))
    (valid : ValidSymbol LENS symbol)
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    ∃ regs used after state entry,
      runX (inflate_LEN c) l h = runX (lenLeafTail c entry) regs after ∧
      used ≤ 4 ∧ used ≤ bs.length ∧ Good after r zs z state ∧ DataTablesSafe after state ∧
      BitInv after regs (bs.drop used) ∧ SymbolEntry LENS symbol entry ∧
      rest = stream regs (bs.drop used) ∧ state.length = entry.val.toUInt32 ∧
      regs.put = l.put ∧ regs.left = l.left ∧ regs.next = inputAdvance l.next used ∧
      after = setI h zs state := by
  let reset := {s with back := (0 : Int32)}
  let h0 := setI h zs reset
  have good0 : Good h0 r zs z reset := good.decode_update rfl good.live.mode
  have tables0 : DataTablesSafe h0 reset := tables.decode_update good.live.hs rfl
  have get0 : Space.get h0 ref = some ca := by
    rw [decode_code_views good.live.hs (after := reset) rfl]; exact tableGet
  obtain ⟨looked, used, heap, lookupState, dropped, lookup, four, bound, dropBound,
    current, currentTables, bits, lookupShape, lookupFrame, back, leaf, symbolMeaning,
    width, enough, source, restEq, cursor, heapEq⟩ :=
    lenLookup_token_run E.st good0 tables0 pointer get0 meaning stable (B.decode_update zs reset)
      rfl decoded valid
  have backNat : lookupState.back.toInt = dropped := by
    rw [back]
    exact back_ofNat_small dropped dropBound
  obtain ⟨regs, after, state, finish, finalGood, finalTables, finalBits, frame, regShape,
    length, _back, suffix, _count, _here, finalHeap, next⟩ :=
    lenFinish_consume_cursor dropped E.st current currentTables leaf backNat enough bits
  refine ⟨regs, used, after, state, looked.here, ?_, four, bound, finalGood, finalTables,
    finalBits, symbolMeaning, restEq.trans suffix.symm, length, ?_, ?_, next.trans cursor, ?_⟩
  · rw [inflate_LEN_slow_cut slow, lenSlow_split, runX_bind, runX_wrS E]
    change runX (do lenLookup c; lenFinish c) l h0 = _
    rw [runX_bind, lookup]
    exact finish
  · rw [regShape, lookupShape]
  · rw [regShape, lookupShape]
  · rw [finalHeap, heapEq, setI_setI]
    exact setI_setI h zs reset state

/-- Every independent literal token, through either actual table path,
executes slow LEN then LIT and writes exactly that byte to a generic
caller view. Public separation permits disjoint ranges in one object. -/
theorem slow_literal_output
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {ref : CodeRef} {offset usedExtent : Nat} {ca : Array Code} {alphabet D : List Nat}
    {l : IL} {bs dict history : List UInt8} {symbol : Nat} {rest : List Bool}
    {dest : BRef} {off : Nat} {array : Array UInt8}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (pointer : s.lencode = .ref ref offset) (tableGet : Space.get h ref = some ca)
    (meaning : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS ca offset s.lenbits.toNat usedExtent alphabet)
    (stable : Zlib.Inftrees.Spec.DecodeTableStability.StableQuery LENS ca offset s.lenbits.toNat)
    (B : BitInv h l bs)
    (decoded : decodeSym alphabet (stream l bs) = some (symbol, rest)) (small : symbol < 256)
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true)
    (left : l.left ≠ 0) (put : l.put = .ref dest off)
    (outputGet : Space.get h dest = some array) (write : Space.ro h dest = false)
    (fit : off < array.size)
    (separate : ZlibF.Spec.Public.Separate l.next l.have_.toNat l.put l.left.toNat) :
    ∃ regs used after,
      runX (do inflate_LEN c; inflate_LIT c) l h = .ok ((.ok (), regs), after) ∧
      used ≤ 4 ∧ used ≤ bs.length ∧ BitInv after regs (bs.drop used) ∧
      stream regs (bs.drop used) = rest ∧
      ZlibF.Spec.Public.Bytes after l.put 1 [symbol.toUInt8] ∧
      Token.Step alphabet D dict history (stream l bs) rest (history ++ [symbol.toUInt8]) false ∧
      (∀ tail output, Symbols alphabet D dict (history ++ [symbol.toUInt8]) rest tail output →
        Symbols alphabet D dict history (stream l bs) tail output) := by
  have valid : ValidSymbol LENS symbol := by simp only [ValidSymbol, ite_true]; omega
  obtain ⟨middle, used, heap, state, entry, cut, four, bound, current, currentTables,
    currentBits, symbolMeaning, restEq, length, putEq, leftEq, cursor, heapEq⟩ :=
    slow_LEN_token_cut E good tables pointer tableGet meaning stable B decoded valid slow
  have literal : entry.op = 0 ∧ entry.val.toNat = symbol := by
    simpa only [SymbolEntry, ite_true, small] using symbolMeaning
  let litState := {state with mode := LIT}
  let litHeap := setI heap zs litState
  have env : Env c heap r zs z state := ⟨E.strm, E.st, current.live.hz, current.live.hs⟩
  have tail : runX (lenLeafTail c entry) middle heap = .ok ((.ok (), middle), litHeap) := by
    unfold lenLeafTail
    simp only [literal.1, UInt8.toNat_zero, beq_self_eq_true, ite_true,
      runX_bind, runX_setMode env, runX_pure]
    rfl
  have lenRun := cut.trans tail
  have litGood : Good litHeap r zs z litState := current.decode_update rfl
    (by change HEAD ≤ LIT ∧ LIT ≤ SYNC; decide)
  have litEnv : Env c litHeap r zs z litState := ⟨E.strm, E.st, litGood.live.hz, litGood.live.hs⟩
  have litBits : BitInv litHeap middle (bs.drop used) := currentBits.decode_update zs litState
  have litLength : litState.length.toNat = symbol := by
    change state.length.toNat = symbol
    rw [length, UInt16.toNat_toUInt32, literal.2]
  have currentGet : Space.get litHeap dest = some array := by
    rw [byte_view_get_setI, heapEq, byte_view_get_setI]
    exact outputGet
  have currentWrite : Space.ro litHeap dest = false := by
    rw [byte_view_ro_setI, heapEq, byte_view_ro_setI]
    exact write
  have currentLeft : middle.left ≠ 0 := by rw [leftEq]; exact left
  have currentPut : middle.put = .ref dest off := putEq.trans put
  have currentSeparate : ZlibF.Spec.Public.Separate middle.next middle.have_.toNat middle.put middle.left.toNat := by
    have advanced := inputAdvance_separate l.next l.put l.have_.toNat l.left.toNat used
      (by rw [B.have_eq]; exact bound) separate
    rw [cursor, putEq, leftEq]
    have count : middle.have_.toNat = l.have_.toNat - used := by
      rw [currentBits.have_eq, B.have_eq, List.length_drop]
    rwa [count]
  have decodedCurrent : decodeSym alphabet (stream l bs) = some (symbol, stream middle (bs.drop used)) := by
    rw [← restEq]; exact decoded
  obtain ⟨litRun, finalBits, finalStream, bytes, token, continuation⟩ :=
    Zlib.Inflate.Proofs.SlowPayloadPath.literal_emit_semantics (L := alphabet) (D := D)
      (dict := dict) (history := history) litEnv litBits currentLeft currentPut currentGet currentWrite
      fit currentSeparate litLength small decodedCurrent
  let regs := {middle with put := .ref dest (off + 1), left := middle.left - 1}
  let after := setI (Space.put litHeap dest (array.set! off symbol.toUInt8)) zs {litState with mode := LEN}
  have finalRest : stream regs (bs.drop used) = rest := finalStream.trans restEq.symm
  refine ⟨regs, used, after, ?_, four, bound, finalBits, finalRest, ?_, ?_, ?_⟩
  · rw [runX_bind, lenRun]
    exact litRun
  · rw [← putEq]
    exact bytes
  · rwa [finalStream, ← restEq] at token
  · rwa [finalStream, ← restEq] at continuation

/-- An independent EOB symbol traverses either actual table path and
returns at TYPE with back = -1 and exactly the independent bit suffix. -/
theorem slow_eob_run
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {ref : CodeRef} {offset usedExtent : Nat} {ca : Array Code} {alphabet D : List Nat}
    {l : IL} {bs dict history : List UInt8} {rest : List Bool}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (pointer : s.lencode = .ref ref offset) (tableGet : Space.get h ref = some ca)
    (meaning : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS ca offset s.lenbits.toNat usedExtent alphabet)
    (stable : Zlib.Inftrees.Spec.DecodeTableStability.StableQuery LENS ca offset s.lenbits.toNat)
    (B : BitInv h l bs)
    (decoded : decodeSym alphabet (stream l bs) = some (256, rest))
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    ∃ regs used after state,
      runX (inflate_LEN c) l h = .ok ((.ok (), regs), after) ∧
      used ≤ 4 ∧ used ≤ bs.length ∧ Good after r zs z state ∧ DataTablesSafe after state ∧
      BitInv after regs (bs.drop used) ∧ state.mode = TYPE ∧ state.back = -1 ∧
      stream regs (bs.drop used) = rest ∧ regs.put = l.put ∧ regs.left = l.left ∧
      Token.Step alphabet D dict history (stream l bs) rest history true ∧
      Symbols alphabet D dict history (stream l bs) rest history ∧ after = setI h zs state := by
  obtain ⟨regs, used, heap, state, entry, cut, four, bound, current, currentTables,
    currentBits, symbolMeaning, restEq, length, putEq, leftEq, cursor, heapEq⟩ :=
    slow_LEN_token_cut E good tables pointer tableGet meaning stable B decoded (by change (256 : Nat) ≤ 285; decide) slow
  have eob : entry.op = 96 ∧ entry.val = 0 := by
    simpa [SymbolEntry] using symbolMeaning
  let final := {state with back := (-1 : Int32), mode := TYPE}
  let after := setI heap zs final
  have env : Env c heap r zs z state := ⟨E.strm, E.st, current.live.hz, current.live.hs⟩
  have tailCode : lenLeafTail c entry = (do
      wrS c.st fun s => {s with back := -1, mode := TYPE}
      pure ()) := by
    unfold lenLeafTail
    rw [eob.1]
    rfl
  have tail : runX (lenLeafTail c entry) regs heap = .ok ((.ok (), regs), after) := by
    rw [tailCode]
    simp only [runX_bind, runX_wrS env, runX_pure]
    rfl
  refine ⟨regs, used, after, final, cut.trans tail, four, bound,
    current.decode_update rfl (by change HEAD ≤ TYPE ∧ TYPE ≤ SYNC; decide),
    currentTables.decode_update current.live.hs rfl, currentBits.decode_update zs final,
    rfl, rfl, restEq.symm, putEq, leftEq, Token.Step.eob decoded, Symbols.eob decoded, ?_⟩
  change setI heap zs final = setI h zs final
  rw [heapEq, setI_setI]

/-- The actual LEN_ mode write reaches the same independent token cut;
no additional load or caller-run assumption is introduced. -/
theorem slow_LEN_start_token_cut
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {ref : CodeRef} {offset usedExtent : Nat} {ca : Array Code} {alphabet : List Nat}
    {l : IL} {bs : List UInt8} {symbol : Nat} {rest : List Bool}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (pointer : s.lencode = .ref ref offset) (tableGet : Space.get h ref = some ca)
    (meaning : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS ca offset s.lenbits.toNat usedExtent alphabet)
    (stable : Zlib.Inftrees.Spec.DecodeTableStability.StableQuery LENS ca offset s.lenbits.toNat)
    (B : BitInv h l bs)
    (decoded : decodeSym alphabet (stream l bs) = some (symbol, rest))
    (valid : ValidSymbol LENS symbol)
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    ∃ regs used after state entry,
      runX (inflate_LEN_ c) l h = runX (lenLeafTail c entry) regs after ∧
      used ≤ 4 ∧ used ≤ bs.length ∧ Good after r zs z state ∧ DataTablesSafe after state ∧
      BitInv after regs (bs.drop used) ∧ SymbolEntry LENS symbol entry ∧
      rest = stream regs (bs.drop used) ∧ state.length = entry.val.toUInt32 ∧
      regs.put = l.put ∧ regs.left = l.left ∧ regs.next = inputAdvance l.next used ∧
      after = setI h zs state := by
  let start := {s with mode := LEN}
  let heap := setI h zs start
  have current : Good heap r zs z start := good.decode_update rfl
    (by change HEAD ≤ LEN ∧ LEN ≤ SYNC; decide)
  have currentTables : DataTablesSafe heap start := tables.decode_update good.live.hs rfl
  have currentGet : Space.get heap ref = some ca := by
    rw [decode_code_views good.live.hs (after := start) rfl]
    exact tableGet
  have env : Env c heap r zs z start := ⟨E.strm, E.st, current.live.hz, current.live.hs⟩
  obtain ⟨regs, used, after, state, entry, cut, four, bound, finalGood, finalTables,
    finalBits, symbolMeaning, restEq, length, put, left, next, heapEq⟩ :=
    slow_LEN_token_cut env current currentTables pointer currentGet meaning stable
      (B.decode_update zs start) decoded valid slow
  refine ⟨regs, used, after, state, entry, ?_, four, bound, finalGood, finalTables,
    finalBits, symbolMeaning, restEq, length, put, left, next, ?_⟩
  · unfold inflate_LEN_
    rw [runX_bind, runX_setMode E]
    exact cut
  · rw [heapEq]
    exact setI_setI h zs start state

#print axioms lenSubLookup_token_run
#print axioms lenLookup_token_run
#print axioms slow_LEN_token_cut
#print axioms slow_literal_output
#print axioms slow_eob_run
#print axioms slow_LEN_start_token_cut
end Zlib.Inflate.Proofs.SlowLenTokenPath
