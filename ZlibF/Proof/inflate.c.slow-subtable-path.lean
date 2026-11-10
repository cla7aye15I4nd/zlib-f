import ZlibF.Proof.«inflate.c.slow-payload-path»
import ZlibF.Math.InflateDecodeBits

namespace Zlib.Inflate.Proofs.SlowSubtablePath
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec
open Zlib.Inflate.Proofs Zlib.Inftrees
open Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness
open Zlib.Inffast.Proofs Zlib.Inffast.Spec
set_option autoImplicit false

/-- The actual mask/shift subtable index is the mathematical query on
zero-padded held bits. Padding contributes no consumed source bits. -/
theorem padded_subquery {value width dropped count : Nat}
    (normalized : value < 2 ^ width) (bounded : dropped + count ≤ 15) :
    ∃ suffix, readBits count
      ((Zlib.Inftrees.Spec.DecodeShort.padded (bitsOfNat value width)).drop dropped) =
      some (value % 2 ^ (dropped + count) / 2 ^ dropped, suffix) := by
  have padded : Zlib.Inftrees.Spec.DecodeShort.padded (bitsOfNat value width) =
      bitsOfNat value (width + (15 - width)) := by
    rw [ZlibF.Math.InflateHeldBits.extend_zero normalized]
    simp only [Zlib.Inftrees.Spec.DecodeShort.padded, bitsOfNat_length]
  rw [padded]
  have prefixRead := ZlibF.Math.InflateDecode.read_drop_prefix
    (value := value) (width := width + (15 - width)) (suffix := []) dropped count
    (by omega) (by omega)
  simp only [List.append_nil] at prefixRead
  simpa only [ZlibF.Math.InflateLookup.slice_eq] using prefixRead

/-- A held root query is fixed by the independent source across refills. -/
theorem root_cell_of_stream
    {ca : Array Code} {offset root : Nat} {before after : IL}
    {input rest : List UInt8} {first : Code}
    (beforeEnough : root ≤ before.bits.toNat) (afterEnough : root ≤ after.bits.toNat)
    (source : stream after rest = stream before input)
    (cell : ca[offset + before.hold.toNat % 2 ^ root]? = some first) :
    ca[offset + after.hold.toNat % 2 ^ root]? = some first := by
  have readBefore := readBits_bitsOfNat root before.bits.toNat before.hold.toNat (bytesBits input) beforeEnough
  have readAfter := readBits_bitsOfNat root after.bits.toNat after.hold.toNat (bytesBits rest) afterEnough
  have sameSource : bitsOfNat after.hold.toNat after.bits.toNat ++ bytesBits rest =
      bitsOfNat before.hold.toNat before.bits.toNat ++ bytesBits input := by
    simpa only [stream, natBits_testBit, bitsOfNat] using source
  rw [sameSource] at readAfter
  have index := congrArg Prod.fst (Option.some.inj (readBefore.symm.trans readAfter))
  dsimp only at index
  rw [← index]
  exact cell

/-- The actual mask/shift query is the mathematical padded table read,
including rejected cells. -/
theorem subtable_query_read
    {type : UInt32} {ca : Array Code} {offset root usedExtent : Nat} {alphabet : List Nat}
    {h : Heap} {regs : IL} {bs : List UInt8} {first : Code}
    (meaning : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv type ca offset root usedExtent alphabet)
    (B : BitInv h regs bs)
    (rootCell : ca[offset + regs.hold.toNat % 2 ^ root]? = some first)
    (link : Zlib.Inftrees.Spec.Subtable.IsLink type first = true)
    (selected : regs.here = subLookupValue ca offset first regs)
 :
    tableRead type ca offset root
      (Zlib.Inftrees.Spec.DecodeShort.padded (bitsOfNat regs.hold.toNat regs.bits.toNat)) =
      some (regs.here, first.bits.toNat + regs.here.bits.toNat) := by
  have safe := (meaning.subtables _ first (Nat.mod_lt _ (Nat.two_pow_pos _)) rootCell link).2
  obtain ⟨rootSuffix, rootQuery⟩ := ZlibF.Math.InflateHeldBits.padded_query B.hold_lt meaning.rootTable.2.1
  obtain ⟨subSuffix, subQuery⟩ := padded_subquery B.hold_lt safe.2.2.1
  change readBits first.op.toNat
    ((Zlib.Inftrees.Spec.DecodeShort.padded (bitsOfNat regs.hold.toNat regs.bits.toNat)).drop first.bits.toNat) =
    some (subLookupIndex first regs, subSuffix) at subQuery
  have inside : offset + first.val.toNat + subLookupIndex first regs < ca.size := by
    have extent := safe.2.2.2.1
    have index := subLookupIndex_lt first regs
    omega
  have leafCell : ca[offset + first.val.toNat + subLookupIndex first regs]? = some regs.here := by
    rw [selected, subLookupValue, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem inside, Option.getD_some]
  unfold Zlib.Inftrees.Spec.Subtable.IsLink at link
  by_cases literalLength : type = LENS
  · simp only [literalLength, ite_true, Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at link
    simp [tableRead, rootQuery, rootCell, literalLength, link.1, link.2, subQuery, leafCell]
  · simp only [literalLength, ite_false, beq_iff_eq] at link
    simp [tableRead, rootQuery, rootCell, literalLength, link, subQuery, leafCell]
/-- The actual selected second-level cell has the independent symbol on
all real held bits and unread bytes. Its root cell and enough-bit facts
are explicit representation facts at the query cut. -/
theorem subtable_query_meaning
    {type : UInt32} {ca : Array Code} {offset root usedExtent : Nat} {alphabet : List Nat}
    {h : Heap} {regs : IL} {bs : List UInt8} {first : Code}
    (meaning : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv type ca offset root usedExtent alphabet)
    (B : BitInv h regs bs)
    (rootCell : ca[offset + regs.hold.toNat % 2 ^ root]? = some first)
    (link : Zlib.Inftrees.Spec.Subtable.IsLink type first = true)
    (selected : regs.here = subLookupValue ca offset first regs)
    (enough : first.bits.toNat + regs.here.bits.toNat ≤ regs.bits.toNat)
    (accepted : LeafAccepted type regs.here) :
    ∃ symbol, ValidSymbol type symbol ∧ SymbolEntry type symbol regs.here ∧
      first.bits.toNat + regs.here.bits.toNat = alphabet.getD symbol 0 ∧
      decodeSym alphabet (stream regs bs) =
        some (symbol, (stream regs bs).drop (first.bits.toNat + regs.here.bits.toNat)) := by
  have mathRead := subtable_query_read meaning B rootCell link selected
  obtain ⟨symbol, valid, symbolMeaning, width, _decoded, continued⟩ :=
    meaning.short _ _ _ mathRead (by simpa only [bitsOfNat_length] using enough) accepted
  have extended := continued (bytesBits bs)
  have source : bitsOfNat regs.hold.toNat regs.bits.toNat ++ bytesBits bs = stream regs bs := by
    simp only [stream, natBits_testBit, bitsOfNat]
  have suffix : (bitsOfNat regs.hold.toNat regs.bits.toNat).drop
      (first.bits.toNat + regs.here.bits.toNat) ++ bytesBits bs =
      (stream regs bs).drop (first.bits.toNat + regs.here.bits.toNat) := by
    rw [← source, List.drop_append_of_le_length (by simpa only [bitsOfNat_length] using enough)]
  rw [source, suffix] at extended
  exact ⟨symbol, valid, symbolMeaning, width, extended⟩

/-- A valid independent token drives the actual second-level LEN query.
The remembered root is preserved through every refill, and a complete
real token rules out input exhaustion without a lookahead assumption. -/
theorem lookup2_token_run
    {c : Ctx} {h : Heap} {zs : Nat} {s : InflateState}
    {ref : CodeRef} {offset usedExtent : Nat} {ca : Array Code} {alphabet : List Nat}
    {l : IL} {bs : List UInt8} {symbol : Nat} {rest : List Bool} {first : Code}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (pointer : s.lencode = .ref ref offset) (get : Space.get h ref = some ca)
    (meaning : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS ca offset s.lenbits.toNat usedExtent alphabet)
    (stable : Zlib.Inftrees.Spec.DecodeTableStability.StableQuery LENS ca offset s.lenbits.toNat)
    (B : BitInv h l bs) (remembered : l.last = first)
    (rootCell : ca[offset + l.hold.toNat % 2 ^ s.lenbits.toNat]? = some first)
    (rootEnough : s.lenbits.toNat ≤ l.bits.toNat)
    (link : Zlib.Inftrees.Spec.Subtable.IsLink LENS first = true)
    (decoded : decodeSym alphabet (stream l bs) = some (symbol, rest))
    (valid : ValidSymbol LENS symbol) :
    ∃ regs used,
      runX (lookup2 c false) l h = .ok ((.ok (), regs), h) ∧
      used ≤ 2 ∧ used ≤ bs.length ∧ BitInv h regs (bs.drop used) ∧
      stream regs (bs.drop used) = stream l bs ∧ LookupRegShape l regs ∧ regs.last = first ∧
      regs.next = inputAdvance l.next used ∧
      SymbolEntry LENS symbol regs.here ∧
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
        exact dataSubLookupBody_run false current first hc hs pointer get lastEq links) B
  have totalNat : (need regs.here).toNat = first.bits.toNat + regs.here.bits.toNat := by
    rw [selected, needNat]
  have currentRoot : ca[offset + regs.hold.toNat % 2 ^ s.lenbits.toNat]? = some first :=
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
      have fullQuery : tableRead LENS ca offset s.lenbits.toNat
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

/-- A table read consumes at least the selected root entry width. -/
theorem tableRead_root_lower
    {type : UInt32} {ca : Array Code} {offset root index consumed : Nat}
    {input suffix : List Bool} {first entry : Code}
    (query : readBits root input = some (index, suffix))
    (cell : ca[offset + index]? = some first)
    (table : tableRead type ca offset root input = some (entry, consumed)) :
    first.bits.toNat ≤ consumed := by
  simp only [tableRead, query, bind, Option.bind, cell] at table
  change (if Zlib.Inftrees.Spec.Subtable.IsLink type first then do
    let (j, _) ← readBits first.op.toNat (input.drop first.bits.toNat)
    let second ← ca[offset + first.val.toNat + j]?
    pure (second, first.bits.toNat + second.bits.toNat)
    else some (first, first.bits.toNat)) = some (entry, consumed) at table
  split at table
  · cases subRead : readBits first.op.toNat (input.drop first.bits.toNat) with
    | none => simp only [subRead, bind, Option.bind] at table; cases table
    | some pair =>
      obtain ⟨j, rest⟩ := pair
      simp only [subRead, bind, Option.bind] at table
      cases leaf : ca[offset + first.val.toNat + j]? with
      | none => simp only [leaf] at table; cases table
      | some second =>
        simp only [leaf, pure] at table
        have width := congrArg Prod.snd (Option.some.inj table)
        dsimp only at width
        omega
  · have width := congrArg Prod.snd (Option.some.inj table)
    exact Nat.le_of_eq width

/-- A complete independent valid token forces actual root lookup to
return normally on every root branch, including short final input. -/
theorem lookup1_valid_token_run
    {c : Ctx} {h : Heap} {zs : Nat} {s : InflateState}
    {ref : CodeRef} {offset usedExtent : Nat} {ca : Array Code} {alphabet : List Nat}
    {l : IL} {bs : List UInt8} {symbol : Nat} {rest : List Bool}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (pointer : s.lencode = .ref ref offset) (get : Space.get h ref = some ca)
    (meaning : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS ca offset s.lenbits.toNat usedExtent alphabet)
    (B : BitInv h l bs)
    (decoded : decodeSym alphabet (stream l bs) = some (symbol, rest))
    (valid : ValidSymbol LENS symbol) :
    ∃ regs used,
      runX (lookup1 c false) l h = .ok ((.ok (), regs), h) ∧
      used ≤ 2 ∧ used ≤ bs.length ∧ BitInv h regs (bs.drop used) ∧
      stream regs (bs.drop used) = stream l bs ∧ LookupRegShape l regs ∧
      regs.next = inputAdvance l.next used ∧
      regs.here = codeLookupValue ca offset s.lenbits.toNat regs ∧
      regs.here.bits.toNat ≤ regs.bits.toNat := by
  have readable : RootTableReadable ca offset s.lenbits.toNat := by
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
    Zlib.Inflate.Proofs.SlowPayloadPath.lookupLoop_run_cursor_short (query := codeLookupValue ca offset s.lenbits.toNat)
      (need := fun entry => entry.bits.toUInt32) (fun _ => rfl)
      (by intro current; rw [UInt8.toNat_toUInt32]; exact readable.2.2 _ (Nat.mod_lt _ (Nat.two_pow_pos _)))
      (by intro current _; exact dataLookupBody_run false current hc hs pointer get readable) B
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
      have inside : offset + regs.hold.toNat % 2 ^ s.lenbits.toNat < ca.size := by
        have extent := meaning.rootTable.2.2.1
        have index := Nat.mod_lt regs.hold.toNat (Nat.two_pow_pos s.lenbits.toNat)
        omega
      have cell : ca[offset + regs.hold.toNat % 2 ^ s.lenbits.toNat]? = some regs.here := by
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

#print axioms padded_subquery
#print axioms root_cell_of_stream
#print axioms subtable_query_read
#print axioms subtable_query_meaning
#print axioms lookup2_token_run
#print axioms tableRead_root_lower
#print axioms lookup1_valid_token_run
end Zlib.Inflate.Proofs.SlowSubtablePath
