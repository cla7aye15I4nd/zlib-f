import ZlibF.Proof.«inflate.c.slow-subtable-path»
import ZlibF.Proof.«inflate.c.distance-finish»
namespace Zlib.Inflate.Proofs.SlowDistanceSemanticPath
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec
open Zlib.Inflate.Proofs Zlib.Inftrees
open Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness
open Zlib.Inffast.Proofs Zlib.Inffast.Spec
open Zlib.Inflate.Proofs.SlowSubtablePath
set_option autoImplicit false
theorem distLookup2_token_run
    {c : Ctx} {h : Heap} {zs : Nat} {s : InflateState}
    {ref : CodeRef} {offset usedExtent : Nat} {ca : Array Code} {alphabet : List Nat}
    {l : IL} {bs : List UInt8} {symbol : Nat} {rest : List Bool} {first : Code}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (pointer : s.distcode = .ref ref offset) (get : Space.get h ref = some ca)
    (meaning : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv DISTS ca offset s.distbits.toNat usedExtent alphabet)
    (stable : Zlib.Inftrees.Spec.DecodeTableStability.StableQuery DISTS ca offset s.distbits.toNat)
    (B : BitInv h l bs) (remembered : l.last = first)
    (rootCell : ca[offset + l.hold.toNat % 2 ^ s.distbits.toNat]? = some first)
    (rootEnough : s.distbits.toNat ≤ l.bits.toNat)
    (link : Zlib.Inftrees.Spec.Subtable.IsLink DISTS first = true)
    (decoded : decodeSym alphabet (stream l bs) = some (symbol, rest))
    (valid : ValidSymbol DISTS symbol) :
    ∃ regs used,
      runX (lookup2 c true) l h = .ok ((.ok (), regs), h) ∧
      used ≤ 2 ∧ used ≤ bs.length ∧ BitInv h regs (bs.drop used) ∧
      stream regs (bs.drop used) = stream l bs ∧ LookupRegShape l regs ∧ regs.last = first ∧
      regs.next = inputAdvance l.next used ∧
      SymbolEntry DISTS symbol regs.here ∧
      first.bits.toNat + regs.here.bits.toNat = alphabet.getD symbol 0 ∧
      first.bits.toNat + regs.here.bits.toNat ≤ regs.bits.toNat ∧
      rest = (stream l bs).drop (first.bits.toNat + regs.here.bits.toNat) := by
  obtain ⟨rootBits, safe⟩ := meaning.subtables _ first
    (Nat.mod_lt _ (Nat.two_pow_pos _)) rootCell link
  let P : Nat → Code → Prop := fun dropped entry => entry.bits.toNat + dropped ≤ 15
  have links : LinkOK P ca offset first := by
    refine ⟨by have := safe.2.2.1; omega, safe.2.1, by have := safe.2.2.1; omega,
      safe.2.2.2.1, ?_⟩
    intro j within
    obtain ⟨entry, cell, lower, upper⟩ := safe.2.2.2.2 j within
    have same : ca.getD (offset + first.val.toNat + j) default = entry := by
      simp [Array.getD_eq_getD_getElem?, cell]
    rw [same]
    dsimp only [P]
    have total := safe.2.2.1
    omega
  let need := fun entry : Code => first.bits.toUInt32 + entry.bits.toUInt32
  have leaf : ∀ current, P first.bits.toNat (subLookupValue ca offset first current) :=
    fun current => links.2.2.2.2 _ (subLookupIndex_lt first current)
  have needNat : ∀ current, (need (subLookupValue ca offset first current)).toNat =
      first.bits.toNat + (subLookupValue ca offset first current).bits.toNat := by
    intro current
    have bound := leaf current
    dsimp only [P] at bound
    rw [UInt32.toNat_add, UInt8.toNat_toUInt32, UInt8.toNat_toUInt32,
      Nat.mod_eq_of_lt (by omega)]
  obtain ⟨result, regs, used, run, two, bound, inv, source, shape, count,
    bitBound, selected, entryBound, kinds, enough, exhausted, cursor⟩ :=
    Zlib.Inflate.Proofs.SlowPayloadPath.lookupLoop_run_cursor_short
      (query := subLookupValue ca offset first) (need := need) (fun _ => rfl)
      (by intro current; rw [needNat]; have bound := leaf current; dsimp only [P] at bound; omega)
      (by
        intro current frame
        have lastEq : current.last = first := by rw [frame, remembered]
        exact dataSubLookupBody_run true current first hc hs pointer get lastEq links) B
  have totalNat : (need regs.here).toNat = first.bits.toNat + regs.here.bits.toNat := by
    rw [selected, needNat]
  have currentRoot : ca[offset + regs.hold.toNat % 2 ^ s.distbits.toNat]? = some first :=
    root_cell_of_stream rootEnough (by omega) source rootCell
  have heldQuery := subtable_query_read meaning inv currentRoot link selected
  obtain ⟨desired, consumed, forward, accepted, symbolMeaning, width, fit, restEq⟩ :=
    Zlib.Inftrees.Proofs.DecodeForward.lookup_of_decode meaning decoded valid
  have normal : result = .ok () := by
    rcases kinds with normal | leave
    · exact normal
    · obtain ⟨empty, short⟩ := exhausted leave
      have noBytes : bs.drop used = [] := List.length_eq_zero_iff.mp
        (inv.have_eq.symm.trans (by rw [empty]; rfl))
      have sourceEq : bitsOfNat regs.hold.toNat regs.bits.toNat = stream l bs := by
        simpa only [noBytes, stream, bytesBits, List.flatMap_nil, List.append_nil,
          natBits_testBit, bitsOfNat] using source
      have fullQuery : tableRead DISTS ca offset s.distbits.toNat
          (Zlib.Inftrees.Spec.DecodeShort.padded (stream l bs)) =
          some (regs.here, first.bits.toNat + regs.here.bits.toNat) := by
        simpa only [sourceEq] using heldQuery
      have same := Prod.mk.inj (Option.some.inj (fullQuery.symm.trans forward))
      have sizeEq : (stream l bs).length = regs.bits.toNat := by rw [← sourceEq, bitsOfNat_length]
      rw [totalNat] at short
      omega
  have fitted : first.bits.toNat + regs.here.bits.toNat ≤ regs.bits.toNat := by
    rw [← totalNat]
    exact enough normal
  have fullQuery := stable _ _ _ heldQuery
    (by simpa only [bitsOfNat_length] using fitted) (bytesBits (bs.drop used))
  have sourceEq : bitsOfNat regs.hold.toNat regs.bits.toNat ++ bytesBits (bs.drop used) = stream l bs := by
    simpa only [stream, natBits_testBit, bitsOfNat] using source
  rw [sourceEq] at fullQuery
  obtain ⟨entries, widths⟩ := Prod.mk.inj (Option.some.inj (fullQuery.symm.trans forward))
  rw [← entries] at symbolMeaning
  refine ⟨regs, used, ?_, two, bound, inv, source, shape, ?_, cursor,
    symbolMeaning, widths.trans width, fitted, ?_⟩
  · rw [lookup2_data_eq]
    simpa only [normal] using run
  · rw [shape, remembered]
  · rwa [← widths] at restEq

theorem distLookup1_valid_token_run
    {c : Ctx} {h : Heap} {zs : Nat} {s : InflateState}
    {ref : CodeRef} {offset usedExtent : Nat} {ca : Array Code} {alphabet : List Nat}
    {l : IL} {bs : List UInt8} {symbol : Nat} {rest : List Bool}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (pointer : s.distcode = .ref ref offset) (get : Space.get h ref = some ca)
    (meaning : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv DISTS ca offset s.distbits.toNat usedExtent alphabet)
    (B : BitInv h l bs)
    (decoded : decodeSym alphabet (stream l bs) = some (symbol, rest))
    (valid : ValidSymbol DISTS symbol) :
    ∃ regs used,
      runX (lookup1 c true) l h = .ok ((.ok (), regs), h) ∧
      used ≤ 2 ∧ used ≤ bs.length ∧ BitInv h regs (bs.drop used) ∧
      stream regs (bs.drop used) = stream l bs ∧ LookupRegShape l regs ∧
      regs.next = inputAdvance l.next used ∧
      regs.here = codeLookupValue ca offset s.distbits.toNat regs ∧
      regs.here.bits.toNat ≤ regs.bits.toNat := by
  have readable : RootTableReadable ca offset s.distbits.toNat := by
    refine ⟨meaning.rootTable.2.1, meaning.rootTable.2.2.1, ?_⟩
    intro i within
    obtain ⟨entry, cell, lower, upper⟩ := meaning.rootTable.2.2.2 i within
    have same : ca.getD (offset + i) default = entry := by
      simp [Array.getD_eq_getD_getElem?, cell]
    rw [same]
    have root := meaning.rootTable.2.1
    omega
  obtain ⟨desired, consumed, forward, accepted, symbolMeaning, width, fit, restEq⟩ :=
    Zlib.Inftrees.Proofs.DecodeForward.lookup_of_decode meaning decoded
      valid
  obtain ⟨result, regs, used, run, two, bound, inv, source, shape, count,
    bitBound, selected, entryBound, kinds, enough, exhausted, cursor⟩ :=
    Zlib.Inflate.Proofs.SlowPayloadPath.lookupLoop_run_cursor_short (query := codeLookupValue ca offset s.distbits.toNat)
      (need := fun entry => entry.bits.toUInt32) (fun _ => rfl)
      (by intro current; rw [UInt8.toNat_toUInt32]; exact readable.2.2 _ (Nat.mod_lt _ (Nat.two_pow_pos _)))
      (by intro current _; exact dataLookupBody_run true current hc hs pointer get readable) B
  have normal : result = .ok () := by
    rcases kinds with normal | leave
    · exact normal
    · obtain ⟨empty, short⟩ := exhausted leave
      have noBytes : bs.drop used = [] := List.length_eq_zero_iff.mp
        (inv.have_eq.symm.trans (by rw [empty]; rfl))
      have sourceEq : bitsOfNat regs.hold.toNat regs.bits.toNat = stream l bs := by
        simpa only [noBytes, stream, bytesBits, List.flatMap_nil, List.append_nil,
          natBits_testBit, bitsOfNat] using source
      obtain ⟨suffix, query⟩ := ZlibF.Math.InflateHeldBits.padded_query inv.hold_lt meaning.rootTable.2.1
      have inside : offset + regs.hold.toNat % 2 ^ s.distbits.toNat < ca.size := by
        have extent := meaning.rootTable.2.2.1
        have index := Nat.mod_lt regs.hold.toNat (Nat.two_pow_pos s.distbits.toNat)
        omega
      have cell : ca[offset + regs.hold.toNat % 2 ^ s.distbits.toNat]? = some regs.here := by
        rw [selected, codeLookupValue, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem inside, Option.getD_some]
      rw [← sourceEq] at forward
      have lower := tableRead_root_lower query cell forward
      have sizeEq : (stream l bs).length = regs.bits.toNat := by rw [← sourceEq, bitsOfNat_length]
      rw [UInt8.toNat_toUInt32] at short
      omega
  refine ⟨regs, used, ?_, two, bound, inv, source, shape, cursor, selected, ?_⟩
  · rw [lookup1_data_eq]
    simpa only [normal] using run
  · simpa only [UInt8.toNat_toUInt32] using enough normal

theorem distSubLookup_token_run
    (before : Nat) {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {ref : CodeRef} {offset usedExtent : Nat} {ca : Array Code} {alphabet : List Nat}
    {l : IL} {bs : List UInt8} {symbol : Nat} {rest : List Bool} {first : Code}
    (hc : c.st = some (.tab zs)) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (pointer : s.distcode = .ref ref offset) (tableGet : Space.get h ref = some ca)
    (meaning : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv DISTS ca offset s.distbits.toNat usedExtent alphabet)
    (stable : Zlib.Inftrees.Spec.DecodeTableStability.StableQuery DISTS ca offset s.distbits.toNat)
    (B : BitInv h l bs) (back : s.back = Int32.ofNat before) (backBound : before ≤ 20)
    (rootCell : ca[offset + l.hold.toNat % 2 ^ s.distbits.toNat]? = some first)
    (rootEnough : s.distbits.toNat ≤ l.bits.toNat)
    (link : Zlib.Inftrees.Spec.Subtable.IsLink DISTS first = true)
    (linkShape : LinkOK DistLeaf ca offset first)
    (decoded : decodeSym alphabet (stream l bs) = some (symbol, rest))
    (valid : ValidSymbol DISTS symbol) :
    ∃ regs used,
      let state := {s with back := Int32.ofNat (before + first.bits.toNat)}
      let after := setI h zs state
      runX (distSubLookup c first) l h = .ok ((.ok (), regs), after) ∧
      used ≤ 2 ∧ used ≤ bs.length ∧ Good after r zs z state ∧ DataTablesSafe after state ∧
      BitInv after regs (bs.drop used) ∧ SymbolRegShape l regs ∧
      DistLeaf first.bits.toNat regs.here ∧ SymbolEntry DISTS symbol regs.here ∧
      first.bits.toNat + regs.here.bits.toNat = alphabet.getD symbol 0 ∧
      regs.here.bits.toNat ≤ regs.bits.toNat ∧
      stream regs (bs.drop used) = (stream l bs).drop first.bits.toNat ∧
      rest = (stream regs (bs.drop used)).drop regs.here.bits.toNat ∧
      regs.next = inputAdvance l.next used := by
  let start := {l with last := first}
  have startInv : BitInv h start bs := ⟨B.have_eq, B.next, B.hold_lt⟩
  obtain ⟨current, used, lookup, two, bound, currentInv, source, shape,
    lastEq, cursor, symbolMeaning, width, totalEnough, restEq⟩ :=
    distLookup2_token_run (first := first) hc good.live.hs pointer tableGet meaning stable startInv rfl rootCell rootEnough
      link decoded valid
  have selectedLeaf : DistLeaf first.bits.toNat current.here := by
    obtain ⟨otherResult, otherRegs, otherUsed, otherRun, _, _, _, _, _, _, _, selected, leaf,
      _, _, _, _, _⟩ := lookup2_data_run_cursor true first hc good.live.hs pointer tableGet
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
  let state := {s with back := Int32.ofNat (before + first.bits.toNat)}
  let after := setI h zs state
  have checked : chkI32 (s.back.toInt + first.bits.toNat) h = .ok (Int32.ofNat (before + first.bits.toNat), h) := by
    rw [back]
    rw [show (Int32.ofNat before).toInt = (before : Int) from int32_ofInt_toInt before (by omega) (by omega)]
    unfold chkI32
    have rootBound := linkShape.1
    split
    · rfl
    · omega
  have load : ldInflateState c.st h = .ok (s, h) := by rw [hc, ldI_eq, good.live.hs]
  have write : wrS c.st (fun s => {s with back := Int32.ofNat (before + first.bits.toNat)}) h = .ok ((), after) := by
    rw [hc, wrI_eq, good.live.hs]
  have actual : runX (distSubLookup c first) l h = .ok ((.ok (), regs), after) := by
    unfold distSubLookup
    rw [runX_bind, runX_modify]
    change runX (do
      lookup2 c true
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

theorem distLookup_token_run
    (before : Nat) {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {ref : CodeRef} {offset usedExtent : Nat} {ca : Array Code} {alphabet : List Nat}
    {l : IL} {bs : List UInt8} {symbol : Nat} {rest : List Bool}
    (hc : c.st = some (.tab zs)) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (pointer : s.distcode = .ref ref offset) (tableGet : Space.get h ref = some ca)
    (meaning : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv DISTS ca offset s.distbits.toNat usedExtent alphabet)
    (stable : Zlib.Inftrees.Spec.DecodeTableStability.StableQuery DISTS ca offset s.distbits.toNat)
    (B : BitInv h l bs) (back : s.back = Int32.ofNat before) (backBound : before ≤ 20)
    (decoded : decodeSym alphabet (stream l bs) = some (symbol, rest))
    (valid : ValidSymbol DISTS symbol) :
    ∃ regs used after state dropped,
      runX (distLookup c) l h = .ok ((.ok (), regs), after) ∧
      used ≤ 4 ∧ used ≤ bs.length ∧ dropped ≤ 15 ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧ BitInv after regs (bs.drop used) ∧
      SymbolRegShape l regs ∧ DecodeStateFrame s state ∧ state.back = Int32.ofNat (before + dropped) ∧
      DistLeaf dropped regs.here ∧ SymbolEntry DISTS symbol regs.here ∧
      dropped + regs.here.bits.toNat = alphabet.getD symbol 0 ∧ regs.here.bits.toNat ≤ regs.bits.toNat ∧
      stream regs (bs.drop used) = (stream l bs).drop dropped ∧
      rest = (stream regs (bs.drop used)).drop regs.here.bits.toNat ∧
      regs.next = inputAdvance l.next used ∧ after = setI h zs state := by
  have safe : DistTableSafe ca offset s.distbits.toNat := by
    obtain ⟨otherRef, otherOffset, otherArray, otherPointer, otherGet, otherSafe⟩ := tables.distanceTable
    rw [pointer] at otherPointer
    cases otherPointer
    have same := Option.some.inj (tableGet.symm.trans otherGet)
    subst otherArray
    exact otherSafe
  obtain ⟨current, used, lookup, two, bound, inv, source, shape, cursor, selected, enough⟩ :=
    distLookup1_valid_token_run hc good.live.hs pointer tableGet meaning B decoded valid
  have cell : ca[offset + current.hold.toNat % 2 ^ s.distbits.toNat]? = some current.here := by
    have inside : offset + current.hold.toNat % 2 ^ s.distbits.toNat < ca.size := by
      have extent := meaning.rootTable.2.2.1
      have index := Nat.mod_lt current.hold.toNat (Nat.two_pow_pos s.distbits.toNat)
      omega
    rw [selected, codeLookupValue, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem inside, Option.getD_some]
  have classification := safe.2.2 _ (Nat.mod_lt current.hold.toNat (Nat.two_pow_pos s.distbits.toNat))
  change current.here = ca.getD (offset + current.hold.toNat % 2 ^ s.distbits.toNat) default at selected
  rw [← selected] at classification
  have prefixRun : runX (distLookup c) l h = runX (distRootTail c current.here) current h := by
    unfold distLookup
    rw [runX_bind, lookup]
    simp only [runX_bind, runX_get]
  by_cases slowLink : SlowDistLink current.here
  · have fastLink := slowDistLink_fast slowLink
    rw [ite_eq_left fastLink] at classification
    have link : Zlib.Inftrees.Spec.Subtable.IsLink DISTS current.here = true := by
      change (current.here.op &&& 240 == 0) = true
      exact beq_iff_eq.mpr slowLink
    have rootBits := (meaning.subtables _ current.here
      (Nat.mod_lt _ (Nat.two_pow_pos _)) cell link).1
    have rootEnough : s.distbits.toNat ≤ current.bits.toNat := by omega
    have decodedCurrent : decodeSym alphabet (stream current (bs.drop used)) = some (symbol, rest) := by
      rw [source]; exact decoded
    obtain ⟨regs, used2, subRun, two2, bound2, good2, tables2, inv2, shape2,
      leaf, symbolMeaning, width, fit, bits, restEq, next⟩ :=
      distSubLookup_token_run before hc good tables pointer tableGet meaning stable inv back backBound cell rootEnough
        link classification decodedCurrent valid
    let state := {s with back := Int32.ofNat (before + current.here.bits.toNat)}
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
    · rw [prefixRun, distRootTail_link c current.here slowLink]
      exact subRun
    · simpa only [List.drop_drop, Nat.add_comm] using restEq
    · rw [next, cursor, inputAdvance_add]
  · have notFastLink : ¬ DistLink current.here := by
      intro link
      have table := classification
      rw [ite_eq_left link] at table
      exact slowLink (distLink_slow table)
    rw [ite_eq_right notFastLink] at classification
    obtain ⟨suffix, query⟩ := ZlibF.Math.InflateHeldBits.padded_query inv.hold_lt meaning.rootTable.2.1
    have heldQuery : tableRead DISTS ca offset s.distbits.toNat
        (Zlib.Inftrees.Spec.DecodeShort.padded (bitsOfNat current.hold.toNat current.bits.toNat)) =
        some (current.here, current.here.bits.toNat) := by
      have nonlink : current.here.op &&& 240 ≠ 0 := slowLink
      simp [tableRead, query, cell, show DISTS ≠ LENS by decide, nonlink]
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
      shape.symbol, rfl, by simpa using back,
      classification, symbolMeaning, by simpa using widths.trans width, enough, ?_, ?_, cursor, ?_⟩
    · rw [prefixRun, distRootTail_leaf c current.here slowLink, runX_pure]
    · simpa using source
    · rw [source]
      rwa [← widths] at restEq
    · simp only [setI, upd_self _ _ _ good.live.hs]

/-- Consume both actual distance code levels and retain the independent
symbol at the exact source cut preceding distance-field installation. -/
theorem inflate_DIST_token_cut
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
      regs.next = inputAdvance l.next used ∧ after = setI h zs state := by
  obtain ⟨looked, used, heap, lookupState, dropped, lookup, four, bound, dropBound,
    current, currentTables, bits, lookupShape, lookupFrame, currentBack, leaf, symbolMeaning,
    width, enough, source, restEq, cursor, heapEq⟩ :=
    distLookup_token_run before E.st good tables pointer tableGet meaning stable B back backBound decoded valid
  obtain ⟨regs, after, state, finish, finalGood, finalTables, finalBits, frame, regShape,
    finalHeap, stateEq, suffix, count, here, next⟩ :=
    distFinish_consume_cursor before dropped E.st current currentTables leaf currentBack backBound enough bits
  refine ⟨regs, used, after, state, looked.here, ?_, four, bound, finalGood, finalTables,
    finalBits, symbolMeaning, restEq.trans suffix.symm, ?_, lookupFrame.trans frame,
    lookupShape.trans regShape, next.trans cursor, ?_⟩
  · rw [inflate_DIST_lookup_cut, runX_bind, lookup]
    exact finish
  · rw [stateEq]
    change Int32.ofNat (before + dropped + looked.here.bits.toNat) = _
    rw [Nat.add_assoc, width]
  · rw [finalHeap, heapEq, setI_setI]

/-- The valid distance alphabet's extra-bit count is at most thirteen. -/
theorem distance_extra_bound : ∀ symbol, symbol < 30 → (distExtras.getD symbol 0) ≤ 13 := by
  decide +kernel
/-- The table's sixteen flag leaves exactly its independent extra count. -/
theorem distance_flag_fields : ∀ extra : Fin 14,
    ((UInt8.ofNat (16 + extra.val)) &&& 64) = 0 ∧
    (((UInt8.ofNat (16 + extra.val)).toUInt32 &&& 15).toNat) = extra.val := by
  decide +kernel

/-- A valid distance symbol installs its independent base and extra count
before the same real DISTEXT continuation. No callee run is a premise. -/
theorem inflate_DIST_symbol_fields
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
      regs.next = inputAdvance l.next used ∧ after = setI h zs state := by
  obtain ⟨regs, used, heap, state, entry, cut, four, bound, current, currentTables,
    currentBits, symbolMeaning, restEq, currentBack, frame, shape, cursor, heapEq⟩ :=
    inflate_DIST_token_cut before E good tables pointer tableGet meaning stable B back backBound decoded
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
    restEq, rfl, ?_, ?_, currentBack, frame.trans (by rfl), shape, cursor, ?_⟩
  · change entry.val.toUInt32.toNat = _
    rw [UInt16.toNat_toUInt32, meaningFields.2]
  · change (entry.op.toUInt32 &&& 15).toNat = _
    rw [opEq]
    exact flags.2
  · change setI heap zs final = _
    rw [heapEq, setI_setI]

#print axioms distLookup_token_run
#print axioms distSubLookup_token_run
#print axioms distLookup2_token_run
#print axioms distLookup1_valid_token_run
#print axioms inflate_DIST_token_cut
#print axioms distance_extra_bound
#print axioms distance_flag_fields
#print axioms inflate_DIST_symbol_fields
end Zlib.Inflate.Proofs.SlowDistanceSemanticPath
