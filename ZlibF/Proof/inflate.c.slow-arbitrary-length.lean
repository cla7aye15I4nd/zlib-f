import ZlibF.Proof.«inflate.c.slow-subtable-path»
import ZlibF.Proof.«inflate.c.accepted-token-soundness»
namespace Zlib.Inflate.Proofs.SlowArbitraryLength
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec
open Zlib.Inflate.Proofs Zlib.Inftrees
open Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness
open Zlib.Inffast.Proofs Zlib.Inffast.Spec
open SlowSubtablePath
set_option autoImplicit false
theorem lookup2_actual_query
    {c : Ctx} {h : Heap} {zs : Nat} {s : InflateState}
    {ref : CodeRef} {offset usedExtent : Nat} {ca : Array Code} {alphabet : List Nat}
    {l : IL} {bs : List UInt8} {first : Code}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (pointer : s.lencode = .ref ref offset) (get : Space.get h ref = some ca)
    (meaning : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS ca offset s.lenbits.toNat usedExtent alphabet)
    (B : BitInv h l bs) (remembered : l.last = first)
    (rootCell : ca[offset + l.hold.toNat % 2 ^ s.lenbits.toNat]? = some first)
    (rootEnough : s.lenbits.toNat ≤ l.bits.toNat)
    (link : Zlib.Inftrees.Spec.Subtable.IsLink LENS first = true)
    :
    ∃ result regs used,
      runX (lookup2 c false) l h = .ok ((result, regs), h) ∧
      used ≤ 2 ∧ used ≤ bs.length ∧ BitInv h regs (bs.drop used) ∧
      stream regs (bs.drop used) = stream l bs ∧ LookupRegShape l regs ∧ regs.last = first ∧
      regs.next = inputAdvance l.next used ∧ regs.bits.toNat = l.bits.toNat + 8 * used ∧ regs.bits.toNat ≤ max l.bits.toNat 22 ∧
      regs.here = subLookupValue ca offset first regs ∧
      tableRead LENS ca offset s.lenbits.toNat
        (Zlib.Inftrees.Spec.DecodeShort.padded (bitsOfNat regs.hold.toNat regs.bits.toNat)) =
        some (regs.here, first.bits.toNat + regs.here.bits.toNat) ∧
      (result = .ok () ∨ result = .error Ex.leave) ∧
      (result = .ok () → first.bits.toNat + regs.here.bits.toNat ≤ regs.bits.toNat) ∧
      (result = .error Ex.leave → regs.have_ = 0 ∧
        regs.bits.toNat < first.bits.toNat + regs.here.bits.toNat) ∧
      (result = .ok () → LeafAccepted LENS regs.here →
        ∃ symbol, ValidSymbol LENS symbol ∧ SymbolEntry LENS symbol regs.here ∧
          first.bits.toNat + regs.here.bits.toNat = alphabet.getD symbol 0 ∧
          decodeSym alphabet (stream l bs) = some (symbol,
            (stream l bs).drop (first.bits.toNat + regs.here.bits.toNat))) := by
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
        exact dataSubLookupBody_run false current first hc hs pointer get lastEq links) B
  have totalNat : (need regs.here).toNat = first.bits.toNat + regs.here.bits.toNat := by
    rw [selected, needNat]
  have currentRoot : ca[offset + regs.hold.toNat % 2 ^ s.lenbits.toNat]? = some first :=
    root_cell_of_stream rootEnough (by omega) source rootCell
  have heldQuery := subtable_query_read meaning inv currentRoot link selected
  refine ⟨result, regs, used, ?_, two, bound, inv, source, shape, ?_, cursor,
    count, bitBound, selected, heldQuery, kinds, ?_, ?_, ?_⟩
  · rw [lookup2_data_eq]
    exact run
  · rw [shape, remembered]
  · intro normal
    rw [← totalNat]
    exact enough normal
  · intro leave
    obtain ⟨empty, short⟩ := exhausted leave
    rw [totalNat] at short
    exact ⟨empty, short⟩
  · intro normal accepted
    have fitted : first.bits.toNat + regs.here.bits.toNat ≤ regs.bits.toNat := by
      rw [← totalNat]
      exact enough normal
    obtain ⟨symbol, valid, fields, width, decoded⟩ :=
      subtable_query_meaning meaning inv currentRoot link selected fitted accepted
    exact ⟨symbol, valid, fields, width, by rwa [source] at decoded⟩

#print axioms lookup2_actual_query

theorem lenSubLookup_actual_meaning {c : Ctx} {h : Heap} {zs : Nat} {s : InflateState}
    {ref : CodeRef} {offset extent : Nat} {ca : Array Code} {alphabet : List Nat} {l : IL} {bs : List UInt8}
    (root : Code) (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (pointer : s.lencode = .ref ref offset) (tableGet : Space.get h ref = some ca)
    (link : LinkOK LenLeaf ca offset root) (back : s.back = 0) (B : BitInv h l bs)
    (meaning : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS ca offset s.lenbits.toNat extent alphabet)
    (rootCell : ca[offset + l.hold.toNat % 2 ^ s.lenbits.toNat]? = some root)
    (rootEnough : s.lenbits.toNat ≤ l.bits.toNat)
    (queryLink : Zlib.Inftrees.Spec.Subtable.IsLink LENS root = true) :
    ∃ result regs used after,
      runX (lenSubLookup c root) l h = .ok ((result, regs), after) ∧
      used ≤ 2 ∧ used ≤ bs.length ∧ BitInv after regs (bs.drop used) ∧
      SymbolRegShape l regs ∧ regs.last = root ∧ regs.bits.toNat ≤ max l.bits.toNat 22 ∧
      (result = .ok () ∨ result = .error Ex.leave) ∧
      (result = .ok () →
        after = setI h zs { s with back := Int32.ofNat root.bits.toNat } ∧
        LenLeaf root.bits.toNat regs.here ∧ regs.here.bits.toNat ≤ regs.bits.toNat ∧
        stream regs (bs.drop used) = (stream l bs).drop root.bits.toNat ∧
        regs.bits.toNat = l.bits.toNat + 8 * used - root.bits.toNat) ∧
      (result = .error Ex.leave → after = h ∧ regs.have_ = 0 ∧
        stream regs (bs.drop used) = stream l bs) ∧ regs.next = inputAdvance l.next used ∧
      (result = .ok () → LeafAccepted LENS regs.here →
        ∃ symbol, ValidSymbol LENS symbol ∧ SymbolEntry LENS symbol regs.here ∧
          root.bits.toNat + regs.here.bits.toNat = alphabet.getD symbol 0 ∧
          decodeSym alphabet (stream l bs) = some (symbol,
            (stream l bs).drop (root.bits.toNat + regs.here.bits.toNat))) ∧
      (result = .error Ex.leave → regs.bits.toNat < root.bits.toNat + regs.here.bits.toNat) := by
  let start := { l with last := root }
  have startInv : BitInv h start bs := ⟨B.have_eq, B.next, B.hold_lt⟩
  obtain ⟨result, current, used, run, usedTwo, usedBound, currentInv, sameStream, shape,
    lastRemembered, cursor, count, bitBound, selected, _query, kinds, enough, empty, semantic⟩ :=
    lookup2_actual_query (first := root) hc hs pointer tableGet meaning startInv rfl rootCell rootEnough queryLink
  have leaf : LenLeaf root.bits.toNat current.here := by
    rw [selected]
    exact link.2.2.2.2 _ (subLookupIndex_lt _ _)
  have lastEq : current.last = root := by rw [shape]
  have symbolShape : SymbolRegShape l current :=
    SymbolRegShape.trans (b := start) (by rfl) shape.symbol
  -- Input exhaustion must be returned before the continuation is entered.
  cases result with
  | error e =>
    have equal : e = Ex.leave := by rcases kinds with impossible | equal; cases impossible; exact Except.error.inj equal
    subst e
    refine ⟨.error Ex.leave, current, used, h, ?_, usedTwo, usedBound, currentInv,
      symbolShape, lastEq, bitBound, Or.inr rfl, ?_, ?_, cursor, ?_, ?_⟩
    · unfold lenSubLookup
      rw [runX_bind, runX_modify]
      simp only []
      rw [runX_bind, run]
    · intro impossible
      cases impossible
    · intro _
      exact ⟨rfl, (empty rfl).1, sameStream⟩
    · intro impossible; cases impossible
    · intro _; exact (empty rfl).2
  | ok resultUnit =>
    cases resultUnit
    have source : runX (lenSubLookup c root) l h =
        runX (do
          let last := (← get).last
          DROPBITS last.bits.toUInt32
          let s ← ldInflateState c.st
          let bk ← chkI32 (s.back.toInt + last.bits.toNat)
          wrS c.st fun s => { s with back := bk }) current h := by
      unfold lenSubLookup
      rw [runX_bind, runX_modify]
      simp only []
      rw [runX_bind, run]
    have totalEnough := enough rfl
    have rootEnough : root.bits.toNat ≤ current.bits.toNat := by omega
    have rootSmall : root.bits.toUInt32.toNat < 64 := by rw [UInt8.toNat_toUInt32]; have := link.1; omega
    obtain ⟨finalInv, finalStream, finalCount⟩ :=
      DROPBITS_inv currentInv root.bits.toUInt32 (by simpa using rootEnough) rootSmall
    let final := { current with hold := current.hold >>> root.bits.toUInt32.toUInt64, bits := current.bits - root.bits.toUInt32 }
    let after := setI h zs { s with back := Int32.ofNat root.bits.toNat }
    have checked : chkI32 (s.back.toInt + root.bits.toNat) h = .ok (Int32.ofNat root.bits.toNat, h) := by
      rw [back]
      simp only [Int32.toInt_zero, Int.zero_add]
      unfold chkI32
      have rootBound := link.1
      split
      · rfl
      · omega
    have load : ldInflateState c.st h = .ok (s, h) := by rw [hc, ldI_eq, hs]
    have write : wrS c.st (fun s => { s with back := Int32.ofNat root.bits.toNat }) h = .ok ((), after) := by
      rw [hc, wrI_eq, hs]
    refine ⟨.ok (), final, used, after, ?_, usedTwo, usedBound, (by
        refine ⟨finalInv.have_eq, ?_, finalInv.hold_lt⟩
        rcases finalInv.next with nil | ⟨ref, array, off, pointer, arrayGet, bound, contents⟩
        · exact Or.inl nil
        · refine Or.inr ⟨ref, array, off, pointer, ?_, bound, contents⟩
          cases ref <;> exact arrayGet),
      symbolShape.trans (by rfl), lastEq, ?_, Or.inl rfl, ?_, ?_, cursor, ?_, ?_⟩
    · rw [source]
      simp only [runX_bind, runX_get, lastEq, DROPBITS_run current h _ rootSmall,
        runX_lift_ok load, runX_lift_ok checked, runX_lift_ok write]
      simp only [final, lastEq]
    · change (current.bits - root.bits.toUInt32).toNat ≤ _
      rw [finalCount]
      change current.bits.toNat ≤ max l.bits.toNat 22 at bitBound
      omega
    · intro _
      refine ⟨rfl, leaf, ?_, ?_, ?_⟩
      · change current.here.bits.toNat ≤ (current.bits - root.bits.toUInt32).toNat
        rw [UInt32.toNat_sub_of_le _ _ (by apply UInt32.le_iff_toNat_le.mpr; simpa using rootEnough), UInt8.toNat_toUInt32]
        omega
      · simpa only [UInt8.toNat_toUInt32, stream, start, final] using finalStream.trans (congrArg (List.drop root.bits.toUInt32.toNat) sameStream)
      · change (current.bits - root.bits.toUInt32).toNat = _
        rw [UInt32.toNat_sub_of_le _ _ (by apply UInt32.le_iff_toNat_le.mpr; simpa using rootEnough), UInt8.toNat_toUInt32]
        exact congrArg (fun n => n - root.bits.toNat) count
    · intro impossible
      cases impossible

    · intro _ accepted
      exact semantic rfl accepted
    · intro impossible; cases impossible

#print axioms lenSubLookup_actual_meaning

theorem lookup1_actual_meaning
    {c : Ctx} {h : Heap} {zs : Nat} {s : InflateState}
    {ref : CodeRef} {offset usedExtent : Nat} {ca : Array Code} {alphabet : List Nat}
    {l : IL} {bs : List UInt8}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (pointer : s.lencode = .ref ref offset) (get : Space.get h ref = some ca)
    (meaning : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS ca offset s.lenbits.toNat usedExtent alphabet)
    (B : BitInv h l bs) :
    ∃ result regs used,
      runX (lookup1 c false) l h = .ok ((result, regs), h) ∧
      used ≤ 2 ∧ used ≤ bs.length ∧ BitInv h regs (bs.drop used) ∧
      stream regs (bs.drop used) = stream l bs ∧ LookupRegShape l regs ∧
      regs.here = codeLookupValue ca offset s.lenbits.toNat regs ∧
      regs.next = inputAdvance l.next used ∧
      regs.here.bits.toNat ≤ 15 ∧
      (result = .ok () → regs.here.bits.toNat ≤ regs.bits.toNat) ∧
      (result = .ok () ∨ result = .error Ex.leave) ∧
      (result = .error Ex.leave → regs.have_ = 0 ∧ regs.bits.toNat < regs.here.bits.toNat) ∧
      regs.bits.toNat = l.bits.toNat + 8 * used ∧
      regs.bits.toNat ≤ max l.bits.toNat 22 ∧
      (result = .ok () → ¬ SlowLenLink regs.here → LeafAccepted LENS regs.here →
        ∃ symbol, ValidSymbol LENS symbol ∧ SymbolEntry LENS symbol regs.here ∧
          regs.here.bits.toNat = alphabet.getD symbol 0 ∧
          decodeSym alphabet (stream l bs) =
            some (symbol, (stream l bs).drop regs.here.bits.toNat)) := by
  have readable : RootTableReadable ca offset s.lenbits.toNat := by
    refine ⟨meaning.rootTable.2.1, meaning.rootTable.2.2.1, ?_⟩
    intro i small
    obtain ⟨entry, cell, lower, upper⟩ := meaning.rootTable.2.2.2 i small
    have selected : ca.getD (offset + i) default = entry := by
      simp [Array.getD_eq_getD_getElem?, cell]
    rw [selected]
    have rootBound := meaning.rootTable.2.1
    omega
  obtain ⟨result, regs, used, run, two, bound, inv, source, shape, count,
    bitBound, selected, entryWidth, kinds, enough, empty, cursor⟩ :=
    SlowPayloadPath.lookupLoop_run_cursor_short
      (query := codeLookupValue ca offset s.lenbits.toNat)
      (need := fun entry => entry.bits.toUInt32) (fun _ => rfl)
      (by intro current; rw [UInt8.toNat_toUInt32]; exact readable.2.2 _ (Nat.mod_lt _ (Nat.two_pow_pos _)))
      (fun current _ => dataLookupBody_run false current hc hs pointer get readable) B
  have actual : runX (lookup1 c false) l h = .ok ((result, regs), h) := by
    rw [lookup1_data_eq]; exact run
  have width : regs.here.bits.toNat ≤ 15 := by simpa only [UInt8.toNat_toUInt32] using entryWidth
  have fitted : result = .ok () → regs.here.bits.toNat ≤ regs.bits.toNat := by
    intro normal; simpa only [UInt8.toNat_toUInt32] using enough normal
  have exhausted : result = .error Ex.leave → regs.have_ = 0 ∧ regs.bits.toNat < regs.here.bits.toNat := by
    intro leave; simpa only [UInt8.toNat_toUInt32] using empty leave
  refine ⟨result, regs, used, actual, two, bound, inv, source, shape, selected, cursor, width,
    fitted, kinds, exhausted, count, bitBound, ?_⟩
  intro normal nonlink accepted
  obtain ⟨suffix, query⟩ := ZlibF.Math.InflateHeldBits.padded_query inv.hold_lt meaning.rootTable.2.1
  have inside : offset + regs.hold.toNat % 2 ^ s.lenbits.toNat < ca.size := by
    have root := meaning.rootTable.2.2.1
    have index := Nat.mod_lt regs.hold.toNat (Nat.two_pow_pos s.lenbits.toNat)
    omega
  have cell : ca[offset + regs.hold.toNat % 2 ^ s.lenbits.toNat]? = some regs.here := by
    rw [selected, codeLookupValue, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem inside,
      Option.getD_some]
  have mathRead : tableRead LENS ca offset s.lenbits.toNat
      (Zlib.Inftrees.Spec.DecodeShort.padded (bitsOfNat regs.hold.toNat regs.bits.toNat)) =
      some (regs.here, regs.here.bits.toNat) := by
    simp [tableRead, query, cell]
    intro nonzero high
    exact False.elim (nonlink ⟨nonzero, high⟩)

  have fitted : regs.here.bits.toNat ≤ (bitsOfNat regs.hold.toNat regs.bits.toNat).length := by
    rw [bitsOfNat_length]
    exact fitted normal
  obtain ⟨symbol, valid, symbolMeaning, width, _decoded, continued⟩ :=
    meaning.short _ _ _ mathRead fitted accepted
  have extended := continued (bytesBits (bs.drop used))
  have streamEq : bitsOfNat regs.hold.toNat regs.bits.toNat ++ bytesBits (bs.drop used) =
      stream l bs := by
    simpa only [stream, natBits_testBit, bitsOfNat] using source
  have residual : (bitsOfNat regs.hold.toNat regs.bits.toNat).drop regs.here.bits.toNat ++
      bytesBits (bs.drop used) = (stream l bs).drop regs.here.bits.toNat := by
    rw [← streamEq, List.drop_append_of_le_length fitted]
  rw [streamEq, residual] at extended
  exact ⟨symbol, valid, symbolMeaning, width, extended⟩


#print axioms lookup1_actual_meaning

theorem lenLookup_actual_meaning {c : Ctx} {h : Heap} {zs : Nat} {s : InflateState}
    {ref : CodeRef} {offset extent : Nat} {ca : Array Code} {alphabet : List Nat} {l : IL} {bs : List UInt8}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (pointer : s.lencode = .ref ref offset) (tableGet : Space.get h ref = some ca)
    (safe : LenTableSafe ca offset s.lenbits.toNat) (back : s.back = 0) (B : BitInv h l bs)
    (meaning : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS ca offset s.lenbits.toNat extent alphabet) :
    ∃ result regs used after,
      runX (lenLookup c) l h = .ok ((result, regs), after) ∧
      used ≤ 4 ∧ used ≤ bs.length ∧ BitInv after regs (bs.drop used) ∧
      SymbolRegShape l regs ∧ regs.bits.toNat ≤ max l.bits.toNat 22 ∧
      (result = .ok () ∨ result = .error Ex.leave) ∧
      (result = .ok () → ∃ dropped, dropped ≤ 15 ∧
        after = setI h zs { s with back := Int32.ofNat dropped } ∧
        LenLeaf dropped regs.here ∧ regs.here.bits.toNat ≤ regs.bits.toNat ∧
        stream regs (bs.drop used) = (stream l bs).drop dropped ∧
        regs.bits.toNat = l.bits.toNat + 8 * used - dropped) ∧
      (result = .error Ex.leave → after = h ∧ regs.have_ = 0 ∧
        stream regs (bs.drop used) = stream l bs) ∧ regs.next = inputAdvance l.next used ∧
      (result = .ok () → LeafAccepted LENS regs.here →
        ∃ symbol dropped, dropped ≤ 15 ∧ ValidSymbol LENS symbol ∧ SymbolEntry LENS symbol regs.here ∧
          dropped + regs.here.bits.toNat = alphabet.getD symbol 0 ∧
          after = setI h zs {s with back := Int32.ofNat dropped} ∧
          stream regs (bs.drop used) = (stream l bs).drop dropped ∧
          decodeSym alphabet (stream l bs) = some (symbol,
            (stream l bs).drop (dropped + regs.here.bits.toNat))) := by
  obtain ⟨first, current, used, run, usedTwo, usedBound, inv, sameStream, shape,
    selected, cursor, entryBound, enough, kinds, empty, count, bitBound, rootMeaning⟩ :=
    lookup1_actual_meaning hc hs pointer tableGet meaning B
  have classification : if LenLink current.here then LinkOK LenLeaf ca offset current.here else LenLeaf 0 current.here := by
    rw [selected]
    exact safe.2.2 _ (Nat.mod_lt _ (Nat.two_pow_pos _))
  cases first with
  | error e =>
    have equal : e = Ex.leave := by
      rcases kinds with impossible | equal
      · cases impossible
      · exact Except.error.inj equal
    subst e
    refine ⟨.error Ex.leave, current, used, h, ?_, by omega, usedBound, inv, shape.symbol,
      bitBound, Or.inr rfl, ?_, fun _ => ⟨rfl, (empty rfl).1, sameStream⟩, cursor, ?_⟩
    · unfold lenLookup
      rw [runX_bind, run]
    · intro impossible
      cases impossible
    · intro impossible; cases impossible
  | ok resultUnit =>
    cases resultUnit
    have prefixRun : runX (lenLookup c) l h = runX (lenRootTail c current.here) current h := by
      unfold lenLookup
      rw [runX_bind, run]
      simp only [runX_bind, runX_get]
    by_cases slow : SlowLenLink current.here
    · have link : LenLink current.here := slowLenLink_fast slow
      rw [ite_eq_left link] at classification
      obtain ⟨result, final, used2, after, subRun, usedTwo2, usedBound2, finalInv, finalShape,
        _, finalBound, kinds2, done, leave, subCursor, subMeaning, _short⟩ :=
        lenSubLookup_actual_meaning current.here hc hs pointer tableGet classification back inv meaning
          (by
            have inside : offset + current.hold.toNat % 2 ^ s.lenbits.toNat < ca.size := by
              have extent := meaning.rootTable.2.2.1
              have index := Nat.mod_lt current.hold.toNat (Nat.two_pow_pos s.lenbits.toNat)
              omega
            rw [selected, codeLookupValue, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem inside, Option.getD_some])
          (by
            have cell : ca[offset + current.hold.toNat % 2 ^ s.lenbits.toNat]? = some current.here := by
              have inside : offset + current.hold.toNat % 2 ^ s.lenbits.toNat < ca.size := by
                have extent := meaning.rootTable.2.2.1
                have index := Nat.mod_lt current.hold.toNat (Nat.two_pow_pos s.lenbits.toNat)
                omega
              rw [selected, codeLookupValue, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem inside, Option.getD_some]
            have isLink : Zlib.Inftrees.Spec.Subtable.IsLink LENS current.here = true := by
              simpa [Zlib.Inftrees.Spec.Subtable.IsLink, SlowLenLink] using slow
            have rootBits := (meaning.subtables _ _ (Nat.mod_lt _ (Nat.two_pow_pos _)) cell isLink).1
            rw [← rootBits]
            exact enough rfl)
          (by simpa [Zlib.Inftrees.Spec.Subtable.IsLink, SlowLenLink] using slow)
      have totalBound : used + used2 ≤ bs.length := by
        simp only [List.length_drop] at usedBound2
        omega
      have finalInv' : BitInv after final (bs.drop (used + used2)) := by
        simpa only [List.drop_drop, Nat.add_comm] using finalInv
      have actual : runX (lenLookup c) l h = .ok ((result, final), after) := by
        rw [prefixRun, lenRootTail_link c current.here slow]
        exact subRun
      refine ⟨result, final, used + used2, after, actual, by omega, totalBound, finalInv',
        shape.symbol.trans finalShape, ?_, kinds2, ?_, ?_, by rw [subCursor, cursor, inputAdvance_add], ?_⟩
      · exact Nat.le_trans finalBound (by omega)
      · intro success
        obtain ⟨heapEq, leaf, fits, bits, finalCount⟩ := done success
        refine ⟨current.here.bits.toNat, entryBound, heapEq, leaf, fits, ?_, ?_⟩
        · simpa only [List.drop_drop, Nat.add_comm] using bits.trans (congrArg (List.drop current.here.bits.toNat) sameStream)
        · simp only [count] at finalCount
          simpa only [Nat.mul_add, Nat.add_assoc] using finalCount
      · intro exhausted
        obtain ⟨heapEq, zero, bits⟩ := leave exhausted
        refine ⟨heapEq, zero, ?_⟩
        simpa only [List.drop_drop, Nat.add_comm] using bits.trans sameStream
      · intro success accepted
        obtain ⟨symbol, valid, fields, width, decode⟩ := subMeaning success accepted
        obtain ⟨heapEq, _, _, bits, _⟩ := done success
        refine ⟨symbol, current.here.bits.toNat, entryBound, valid, fields, width, heapEq, ?_, ?_⟩
        · simpa only [List.drop_drop, Nat.add_comm] using bits.trans (congrArg (List.drop current.here.bits.toNat) sameStream)
        · rwa [sameStream] at decode
    · have notLink : ¬ LenLink current.here := by
        intro link
        have table := classification
        rw [ite_eq_left link] at table
        exact slow (lenLink_slow link table)
      rw [ite_eq_right notLink] at classification
      refine ⟨.ok (), current, used, h, ?_, by omega, usedBound, inv, shape.symbol,
        bitBound, Or.inl rfl, ?_, ?_, cursor, ?_⟩
      · rw [prefixRun, lenRootTail_leaf c current.here slow, runX_pure]
      · intro _
        refine ⟨0, by omega, ?_, classification, enough rfl, ?_, ?_⟩
        · have stateEq : { s with back := Int32.ofNat 0 } = s := by
            change { s with back := 0 } = s
            rw [← back]
          rw [stateEq]
          simp only [setI, upd_self _ _ _ hs]
        · simpa using sameStream
        · simpa using count
      · intro impossible
        cases impossible

      · intro _ accepted
        obtain ⟨symbol, valid, fields, width, decoded⟩ := rootMeaning rfl slow accepted
        refine ⟨symbol, 0, by omega, valid, fields, by simpa using width, ?_, ?_, ?_⟩
        · have stateEq : { s with back := Int32.ofNat 0 } = s := by
            change {s with back := 0} = s
            rw [← back]
          rw [stateEq]
          simp only [setI, upd_self _ _ _ hs]
        · simpa using sameStream
        · simpa using decoded

#print axioms lenLookup_actual_meaning

theorem LEN_arbitrary_lookup_boundary {c : Ctx} {l : IL} {h : Heap}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8}
    {ref : CodeRef} {offset extent : Nat} {ca : Array Code} {alphabet : List Nat}
    (hc : c.st = some (.tab zs)) (good : Good h r zs z s)
    (tables : DataTablesSafe h s) (B : BitInv h l bs)
    (pointer : s.lencode = .ref ref offset) (tableGet : Space.get h ref = some ca)
    (safe : LenTableSafe ca offset s.lenbits.toNat)
    (meaning : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS ca offset s.lenbits.toNat extent alphabet)
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    (∃ regs after state used,
      used ≤ 4 ∧ used ≤ bs.length ∧
      runX (inflate_LEN c) l h = .ok ((.error Ex.leave, regs), after) ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧
      BitInv after regs (bs.drop used) ∧ regs.have_ = 0 ∧
      stream regs (bs.drop used) = stream l bs ∧ SymbolRegShape l regs ∧
      DecodeStateFrame s state ∧ regs.bits.toNat ≤ max l.bits.toNat 22 ∧ regs.next = inputAdvance l.next used ∧ after = setI h zs state ∧ state.mode = s.mode) ∨
    (∃ regs after state used dropped,
      used ≤ 4 ∧ used ≤ bs.length ∧ dropped ≤ 15 ∧
      runX (inflate_LEN c) l h = runX (lenFinish c) regs after ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧
      BitInv after regs (bs.drop used) ∧ LenLeaf dropped regs.here ∧
      regs.here.bits.toNat ≤ regs.bits.toNat ∧ state.back = Int32.ofNat dropped ∧
      stream regs (bs.drop used) = (stream l bs).drop dropped ∧
      SymbolRegShape l regs ∧ DecodeStateFrame s state ∧
      regs.bits.toNat = l.bits.toNat + 8 * used - dropped ∧
      regs.bits.toNat ≤ max l.bits.toNat 22 ∧ after = setI h zs state ∧ regs.next = inputAdvance l.next used ∧
      (LeafAccepted LENS regs.here →
        ∃ symbol, ValidSymbol LENS symbol ∧ SymbolEntry LENS symbol regs.here ∧
          dropped + regs.here.bits.toNat = alphabet.getD symbol 0 ∧
          decodeSym alphabet (stream l bs) = some (symbol,
            (stream l bs).drop (dropped + regs.here.bits.toNat)))) := by
  let reset := { s with back := 0 }
  let heap := setI h zs reset
  have resetGood : Good heap r zs z reset := good.decode_update rfl good.live.mode
  have resetTables : DataTablesSafe heap reset := tables.decode_update good.live.hs rfl
  have getReset : Space.get heap ref = some ca := by
    rw [decode_code_views good.live.hs (after := reset) rfl]
    exact tableGet
  obtain ⟨result, regs, used, after, run, usedFour, usedBound, inv, shape, bitBound, kinds, done, leave, cursor, semantic⟩ :=
    lenLookup_actual_meaning hc resetGood.live.hs pointer getReset safe rfl (B.decode_update zs reset) meaning
  have source : runX (inflate_LEN c) l h = runX (do lenLookup c; lenFinish c) l heap := by
    rw [inflate_LEN_slow_cut slow, lenSlow_split]
    have write : wrS c.st (fun s => { s with back := 0 }) h = .ok ((), heap) := by rw [hc, wrI_eq, good.live.hs]
    rw [runX_bind, runX_lift_ok write]
  cases result with
  | error e =>
    have equal : e = Ex.leave := by
      rcases kinds with impossible | equal
      · cases impossible
      · exact Except.error.inj equal
    subst e
    obtain ⟨heapEq, empty, bits⟩ := leave rfl
    subst after
    left
    refine ⟨regs, heap, reset, used, usedFour, usedBound, ?_, resetGood, resetTables,
      inv, empty, bits, shape, rfl, bitBound, cursor, rfl, rfl⟩
    rw [source, runX_bind, run]
  | ok resultUnit =>
    cases resultUnit
    obtain ⟨dropped, dropBound, heapEq, leaf, enough, bits, count⟩ := done rfl
    subst after
    let state := { reset with back := Int32.ofNat dropped }
    have finalGood : Good (setI heap zs state) r zs z state :=
      resetGood.decode_update rfl resetGood.live.mode
    have finalTables : DataTablesSafe (setI heap zs state) state :=
      resetTables.decode_update resetGood.live.hs rfl
    right
    refine ⟨regs, setI heap zs state, state, used, dropped, usedFour, usedBound, dropBound,
      ?_, finalGood, finalTables, inv, leaf, enough, rfl, bits, shape, rfl, count, bitBound, by simp [heap], cursor, ?_⟩
    rw [source, runX_bind, run]

    intro accepted
    obtain ⟨symbol, semanticDrop, semanticBound, valid, fields, width, semanticHeap, _, decoded⟩ := semantic rfl accepted
    have stateSame : {reset with back := Int32.ofNat semanticDrop} = state := by
      apply Option.some.inj
      rw [← setI_istates_same heap zs {reset with back := Int32.ofNat semanticDrop}, ← semanticHeap]
      rw [setI_istates_same]
    have dropSame := congrArg (fun st : InflateState => st.back.toInt) stateSame
    change (Int32.ofNat semanticDrop).toInt = (Int32.ofNat dropped).toInt at dropSame
    rw [back_ofNat_small semanticDrop semanticBound, back_ofNat_small dropped dropBound] at dropSame
    have sameNat : semanticDrop = dropped := by omega
    subst semanticDrop
    exact ⟨symbol, valid, fields, width, decoded⟩

#print axioms LEN_arbitrary_lookup_boundary
end Zlib.Inflate.Proofs.SlowArbitraryLength

namespace Zlib.Inflate.Proofs.SlowArbitraryLength
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec
open Zlib.Inflate.Proofs Zlib.Inftrees
open Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness
open Zlib.Inffast.Proofs Zlib.Inffast.Spec
set_option autoImplicit false

/-- Arbitrary input either truly exhausts the current raw input or reaches
its actual leaf classifier with the selected code fully consumed. Accepted
leaves determine an independent symbol; no valid suffix is assumed. -/
theorem LEN_arbitrary_finish_cut
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {ref : CodeRef} {offset extent : Nat} {ca : Array Code} {L : List Nat}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s) (B : BitInv h l bs)
    (pointer : s.lencode = .ref ref offset) (tableGet : Space.get h ref = some ca)
    (safe : LenTableSafe ca offset s.lenbits.toNat)
    (meaning : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS ca offset s.lenbits.toNat extent L)
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    (∃ regs after state used,
      used ≤ 4 ∧ used ≤ bs.length ∧ runX (inflate_LEN c) l h = .ok ((.error Ex.leave, regs), after) ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧ BitInv after regs (bs.drop used) ∧
      regs.have_ = 0 ∧ stream regs (bs.drop used) = stream l bs ∧ SymbolRegShape l regs ∧
      DecodeStateFrame s state ∧ regs.next = inputAdvance l.next used ∧ after = setI h zs state ∧ state.mode = s.mode) ∨
    (∃ regs after state used entry consumed,
      used ≤ 4 ∧ used ≤ bs.length ∧ consumed ≤ 15 ∧
      runX (inflate_LEN c) l h = runX (lenLeafTail c entry) regs after ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧ BitInv after regs (bs.drop used) ∧
      SymbolRegShape l regs ∧ DecodeStateFrame s state ∧ regs.next = inputAdvance l.next used ∧
      state.length = entry.val.toUInt32 ∧ state.back = Int32.ofNat consumed ∧
      stream regs (bs.drop used) = (stream l bs).drop consumed ∧ after = setI h zs state ∧
      LenLeaf 0 entry ∧
      (LeafAccepted LENS entry → ∃ symbol, ValidSymbol LENS symbol ∧ SymbolEntry LENS symbol entry ∧
        consumed = L.getD symbol 0 ∧ decodeSym L (stream l bs) = some (symbol, stream regs (bs.drop used)))) := by
  rcases LEN_arbitrary_lookup_boundary E.st good tables B pointer tableGet safe meaning slow with wait | reached
  · obtain ⟨regs, after, state, used, four, bound, run, current, currentTables, bits, empty,
      source, shape, frame, _bitsBound, cursor, heap, mode⟩ := wait
    exact Or.inl ⟨regs, after, state, used, four, bound, run, current, currentTables, bits,
      empty, source, shape, frame, cursor, heap, mode⟩
  · obtain ⟨looked, heap, lookupState, used, dropped, four, bound, droppedBound, cut, current,
      currentTables, bits, leaf, enough, back, source, shape, frame, _count, _bitsBound, heapEq, cursor, semantic⟩ := reached
    have backNat : lookupState.back.toInt = dropped := by rw [back]; exact back_ofNat_small _ droppedBound
    obtain ⟨regs, after, state, finish, finalGood, finalTables, finalBits, finalFrame, regShape,
      length, finalBack, suffix, _count, _here, finalHeap, next⟩ :=
      lenFinish_consume_cursor dropped E.st current currentTables leaf backNat enough bits
    have consumedBound : dropped + looked.here.bits.toNat ≤ 15 := by have := leaf.1; omega
    have sourceFinal : stream regs (bs.drop used) = (stream l bs).drop (dropped + looked.here.bits.toNat) := by
      rw [suffix, source, List.drop_drop]
    have leaf0 : LenLeaf 0 looked.here := ⟨by omega, leaf.2⟩
    refine Or.inr ⟨regs, after, state, used, looked.here, dropped + looked.here.bits.toNat,
      four, bound, consumedBound, cut.trans finish, finalGood, finalTables, finalBits,
      shape.trans regShape, frame.trans finalFrame, next.trans cursor, length, finalBack,
      sourceFinal, ?_, leaf0, ?_⟩
    · rw [finalHeap, heapEq, setI_setI]
    · intro accepted
      obtain ⟨symbol, valid, fields, width, decoded⟩ := semantic accepted
      exact ⟨symbol, valid, fields, width, by rwa [sourceFinal]⟩

#print axioms LEN_arbitrary_finish_cut
end Zlib.Inflate.Proofs.SlowArbitraryLength

namespace Zlib.Inflate.Proofs.SlowArbitraryLength
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec
open Zlib.Inflate.Proofs Zlib.Inftrees
open Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness
open Zlib.Inffast.Proofs Zlib.Inffast.Spec
set_option autoImplicit false

private theorem accepted_eob_flag {entry : Code} {symbol : Nat}
    (valid : ValidSymbol LENS symbol) (fields : SymbolEntry LENS symbol entry)
    (ending : entry.op &&& 32 ≠ 0) : symbol = 256 := by
  have upper : symbol ≤ 285 := by simpa [ValidSymbol] using valid
  by_cases small : symbol < 256
  · have lit : entry.op = 0 ∧ entry.val.toNat = symbol := by simpa [SymbolEntry, small] using fields
    exact (ending (by rw [lit.1]; rfl)).elim
  · by_cases eob : symbol = 256
    · exact eob
    · have data : entry.op.toNat = 16 + lengthExtras.getD (symbol - 257) 0 ∧
          entry.val.toNat = lengthBases.getD (symbol - 257) 0 := by
        simpa [SymbolEntry, small, eob, upper] using fields
      have extras : ∀ n : Fin 29, lengthExtras.getD n.val 0 ≤ 5 := by decide +kernel
      have bound : lengthExtras.getD (symbol - 257) 0 ≤ 5 := extras ⟨symbol - 257, by omega⟩
      have noEnd : ∀ op : UInt8, 16 ≤ op.toNat → op.toNat ≤ 21 → op &&& 32 = 0 := by
        apply u8_forall
        decide +kernel
      exact (ending (noEnd entry.op (by omega) (by omega))).elim

/-- The actual classifier chooses precisely an emitted-later literal,
block end, malformed-code return, or length-extra continuation. Every
accepted event includes its independently decoded symbol on arbitrary
current input. This helper does not assume a decoded future suffix. -/
theorem leaf_arbitrary_classifier
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {entry : Code} {L : List Nat} {input : List Bool}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s) (B : BitInv h l bs)
    (leaf : LenLeaf 0 entry) (length : s.length = entry.val.toUInt32)
    (semantic : LeafAccepted LENS entry → ∃ symbol, ValidSymbol LENS symbol ∧ SymbolEntry LENS symbol entry ∧
      decodeSym L input = some (symbol, stream l bs)) :
    (∃ after state symbol,
      runX (lenLeafTail c entry) l h = .ok ((.ok (), l), after) ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧ BitInv after l bs ∧
      state.mode = LIT ∧ state.length.toNat = symbol ∧ symbol < 256 ∧
      decodeSym L input = some (symbol, stream l bs) ∧ state.back = s.back ∧ after = setI h zs state) ∨
    (∃ after state,
      runX (lenLeafTail c entry) l h = .ok ((.ok (), l), after) ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧ BitInv after l bs ∧
      state.mode = TYPE ∧ state.back = -1 ∧ decodeSym L input = some (256, stream l bs) ∧ after = setI h zs state) ∨
    (∃ after stream state,
      runX (lenLeafTail c entry) l h = .ok ((.ok (), l), after) ∧
      Good after r zs stream state ∧ BitInv after l bs ∧ state.mode = BAD) ∨
    (∃ after state symbol,
      runX (lenLeafTail c entry) l h = runX (inflate_LENEXT c) l after ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧ BitInv after l bs ∧
      state.mode = LENEXT ∧ 257 ≤ symbol ∧ symbol ≤ 285 ∧
      state.length.toNat = lengthBases.getD (symbol - 257) 0 ∧
      state.extra.toNat = lengthExtras.getD (symbol - 257) 0 ∧ state.back = s.back ∧
      decodeSym L input = some (symbol, stream l bs) ∧ after = setI h zs state) := by
  by_cases literal : entry.op = 0
  · have accepted : LeafAccepted LENS entry := by simp [LeafAccepted, literal]
    obtain ⟨symbol, valid, fields, decoded⟩ := semantic accepted
    obtain ⟨small, value⟩ := AcceptedToken.literal_symbol valid fields literal
    let state := {s with mode := LIT}
    let after := setI h zs state
    have current := good.decode_update (after := state) rfl (by change HEAD ≤ LIT ∧ LIT ≤ SYNC; decide)
    refine Or.inl ⟨after, state, symbol, ?_, current,
      tables.decode_update good.live.hs rfl, B.decode_update zs state, rfl, ?_, small, decoded, rfl, rfl⟩
    · unfold lenLeafTail
      simp only [literal, UInt8.toNat_zero, beq_self_eq_true, ite_true, runX_bind, runX_setMode E, runX_pure]
      rfl
    · change s.length.toNat = symbol
      rw [length, UInt16.toNat_toUInt32, value]
  · right
    have literalNat : entry.op.toNat ≠ 0 := by intro zero; exact literal (UInt8.toNat_inj.mp zero)
    by_cases ending : entry.op &&& 32 ≠ 0
    · have accepted : LeafAccepted LENS entry := by simp [LeafAccepted, ending]
      obtain ⟨symbol, valid, fields, decoded⟩ := semantic accepted
      have symbolEq := accepted_eob_flag valid fields ending
      subst symbol
      let state := {s with back := (-1 : Int32), mode := TYPE}
      let after := setI h zs state
      have current := good.decode_update (after := state) rfl (by change HEAD ≤ TYPE ∧ TYPE ≤ SYNC; decide)
      refine Or.inl ⟨after, state, ?_, current, tables.decode_update good.live.hs rfl,
        B.decode_update zs state, rfl, rfl, decoded, rfl⟩
      have entryOp : entry.op = 96 := by
        have exactFields : entry.op = 96 ∧ entry.val = 0 := by simpa [SymbolEntry] using fields
        exact exactFields.1
      have tailCode : lenLeafTail c entry = (do
          wrS c.st fun s => {s with back := -1, mode := TYPE}
          pure ()) := by
        unfold lenLeafTail
        rw [entryOp]
        rfl
      rw [tailCode]
      simp only [runX_bind, runX_wrS E, runX_pure]
      rfl
    · right
      by_cases invalid : entry.op &&& 64 ≠ 0
      · have member : "invalid literal/length code" ∈ strTable := by decide +kernel
        obtain ⟨i, _, badRun⟩ := badMode_run E member
        let stream := {z with msg := .ref (.str i) 0}
        let state := {s with mode := BAD}
        have inv : StInv h zs state := good.inv.of_fields rfl rfl rfl rfl rfl rfl rfl rfl rfl good.inv.bits rfl rfl rfl
        have current : Good (badHeap h r zs z s i) r zs stream state :=
          good.setZI rfl good.live.zalloc good.live.zfree rfl (by change HEAD ≤ BAD ∧ BAD ≤ SYNC; decide) inv
        have bits : BitInv (badHeap h r zs z s i) l bs := by
          refine ⟨B.have_eq, ?_, B.hold_lt⟩
          rcases B.next with empty | ⟨ref, array, off, pointer, arrayGet, bound, contents⟩
          · exact Or.inl empty
          · refine Or.inr ⟨ref, array, off, pointer, ?_, bound, contents⟩
            cases ref with
            | str sourceIndex =>
              have stable : C.LibcBorrow.BorrowStable h (badHeap h r zs z s i) (.str sourceIndex) := by
                apply Or.inr
                cases r <;> simp only [badHeap, setI, ZStreamRef.put] <;>
                  first | rfl | split <;> rfl
              exact (C.LibcBorrow.str_view_stable stable).trans arrayGet
            | _ =>
              cases r <;> simp only [badHeap, setI, Space.get, ZStreamRef.put] <;>
                first | exact arrayGet | split <;> exact arrayGet
        refine Or.inl ⟨badHeap h r zs z s i, stream, state, ?_, current, bits, rfl⟩
        unfold lenLeafTail
        simp [beq_iff_eq, bne_iff_ne, literalNat, ending, invalid, runX_bind, runX_lift_ok badRun, runX_pure]
      · have accepted : LeafAccepted LENS entry := by
          have noInvalid : entry.op &&& 64 = 0 := Classical.byContradiction invalid
          exact Or.inr noInvalid
        obtain ⟨symbol, valid, fields, decoded⟩ := semantic accepted
        have base : entry.op &&& 16 ≠ 0 := by
          rcases leaf.2 with lit | base | bad
          · exact (literal lit).elim
          · exact base.1
          · exact (invalid bad.2).elim
        obtain ⟨lower, upper, extra, value⟩ := AcceptedToken.base_symbol valid fields base
        let state := {s with extra := entry.op.toUInt32 &&& 15, mode := LENEXT}
        let after := setI h zs state
        have current := good.decode_update (after := state) rfl (by change HEAD ≤ LENEXT ∧ LENEXT ≤ SYNC; decide)
        refine Or.inr ⟨after, state, symbol, ?_, current, tables.decode_update good.live.hs rfl,
          B.decode_update zs state, rfl, lower, upper, ?_, ?_, rfl, decoded, rfl⟩
        · unfold lenLeafTail
          simp only [beq_iff_eq, bne_iff_ne, literalNat, ending, invalid, ite_false, runX_bind, runX_wrS E]
          rfl
        · change s.length.toNat = _
          rw [length, UInt16.toNat_toUInt32, value]
        · change (entry.op.toUInt32 &&& 15).toNat = _
          rw [mask15, extra]

#print axioms leaf_arbitrary_classifier
end Zlib.Inflate.Proofs.SlowArbitraryLength

namespace Zlib.Inflate.Proofs.SlowArbitraryLength
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec
open Zlib.Inflate.Proofs Zlib.Inftrees
open Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness
open Zlib.Inffast.Proofs Zlib.Inffast.Spec
set_option autoImplicit false

/-- A source-driven classifier for arbitrary current input. It covers root
and linked queries, genuine input exhaustion, malformed leaves and each
accepted independent event. No valid-future premise is used. LENEXT is
exposed as the actual next source continuation before any extra-bit read. -/
theorem LEN_arbitrary_source_classifier
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {ref : CodeRef} {offset extent : Nat} {ca : Array Code} {L : List Nat}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s) (B : BitInv h l bs)
    (pointer : s.lencode = .ref ref offset) (tableGet : Space.get h ref = some ca)
    (safe : LenTableSafe ca offset s.lenbits.toNat)
    (meaning : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS ca offset s.lenbits.toNat extent L)
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    (∃ regs after state used,
      used ≤ 4 ∧ used ≤ bs.length ∧ runX (inflate_LEN c) l h = .ok ((.error Ex.leave, regs), after) ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧ BitInv after regs (bs.drop used) ∧
      regs.have_ = 0 ∧ stream regs (bs.drop used) = stream l bs ∧ SymbolRegShape l regs ∧
      DecodeStateFrame s state ∧ regs.next = inputAdvance l.next used ∧ after = setI h zs state ∧ state.mode = s.mode) ∨
    (∃ regs used consumed cutHeap cutState,
      used ≤ 4 ∧ used ≤ bs.length ∧ consumed ≤ 15 ∧
      SymbolRegShape l regs ∧ DecodeStateFrame s cutState ∧ regs.next = inputAdvance l.next used ∧
      cutHeap = setI h zs cutState ∧ cutState.back = Int32.ofNat consumed ∧
      stream regs (bs.drop used) = (stream l bs).drop consumed ∧
      (
    (∃ after state symbol,
      runX (inflate_LEN c) l h = .ok ((.ok (), regs), after) ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧ BitInv after regs (bs.drop used) ∧
      state.mode = LIT ∧ state.length.toNat = symbol ∧ symbol < 256 ∧
      decodeSym L (stream l bs) = some (symbol, stream regs (bs.drop used)) ∧ state.back = cutState.back ∧ after = setI cutHeap zs state) ∨
    (∃ after state,
      runX (inflate_LEN c) l h = .ok ((.ok (), regs), after) ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧ BitInv after regs (bs.drop used) ∧
      state.mode = TYPE ∧ state.back = -1 ∧ decodeSym L (stream l bs) = some (256, stream regs (bs.drop used)) ∧ after = setI cutHeap zs state) ∨
    (∃ after stream state,
      runX (inflate_LEN c) l h = .ok ((.ok (), regs), after) ∧
      Good after r zs stream state ∧ BitInv after regs (bs.drop used) ∧ state.mode = BAD) ∨
    (∃ after state symbol,
      runX (inflate_LEN c) l h = runX (inflate_LENEXT c) regs after ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧ BitInv after regs (bs.drop used) ∧
      state.mode = LENEXT ∧ 257 ≤ symbol ∧ symbol ≤ 285 ∧
      state.length.toNat = lengthBases.getD (symbol - 257) 0 ∧
      state.extra.toNat = lengthExtras.getD (symbol - 257) 0 ∧ state.back = cutState.back ∧
      decodeSym L (stream l bs) = some (symbol, stream regs (bs.drop used)) ∧ after = setI cutHeap zs state))) := by
  rcases LEN_arbitrary_finish_cut E good tables B pointer tableGet safe meaning slow with wait | reached
  · exact Or.inl wait
  · obtain ⟨regs, cutHeap, cutState, used, entry, consumed, four, bound, consumedBound, cut,
      current, currentTables, bits, shape, frame, cursor, length, back, source, heap, leaf, semantic⟩ := reached
    have env : Env c cutHeap r zs z cutState := ⟨E.strm, E.st, current.live.hz, current.live.hs⟩
    have events := leaf_arbitrary_classifier (L := L) (input := stream l bs) env current currentTables bits leaf length
      (fun accepted => by
        obtain ⟨symbol, valid, fields, _width, decoded⟩ := semantic accepted
        exact ⟨symbol, valid, fields, decoded⟩)
    refine Or.inr ⟨regs, used, consumed, cutHeap, cutState, four, bound, consumedBound,
      shape, frame, cursor, heap, back, source, ?_⟩
    simpa only [← cut] using events

#print axioms LEN_arbitrary_source_classifier
end Zlib.Inflate.Proofs.SlowArbitraryLength
