import ZlibF.Proof.«inflate.c.slow-distance-semantic»
import ZlibF.Proof.«inflate.c.accepted-token-soundness»
import ZlibF.Proof.«inflate.c.slow-extra-arbitrary-source»

namespace Zlib.Inflate.Proofs.SlowArbitrarySource
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inftrees Zlib.Inffast.Spec Zlib.Inffast.Proofs
open Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness
open Zlib.Inftrees.Spec.DecodeTableInvariant SlowSubtablePath SlowPayloadPath
set_option autoImplicit false

/-- Every actual accepted nonlink distance root decodes a genuine symbol
on the current source. Unread input need not be valid. -/
theorem dist_root_accepted_source
    {h : Heap} {regs : IL} {bs : List UInt8} {ca : Array Code}
    {offset root extent : Nat} {D : List Nat}
    (meaning : Inv DISTS ca offset root extent D) (B : BitInv h regs bs)
    (selected : regs.here = codeLookupValue ca offset root regs)
    (nonlink : ¬ SlowDistLink regs.here) (enough : regs.here.bits.toNat ≤ regs.bits.toNat)
    (accepted : LeafAccepted DISTS regs.here) :
    ∃ symbol, symbol ≤ 29 ∧ SymbolEntry DISTS symbol regs.here ∧
      regs.here.bits.toNat = D.getD symbol 0 ∧
      decodeSym D (stream regs bs) = some (symbol, (stream regs bs).drop regs.here.bits.toNat) := by
  obtain ⟨suffix, query⟩ := ZlibF.Math.InflateHeldBits.padded_query B.hold_lt meaning.rootTable.2.1
  have inside : offset + regs.hold.toNat % 2 ^ root < ca.size := by
    have extent := meaning.rootTable.2.2.1
    have index := Nat.mod_lt regs.hold.toNat (Nat.two_pow_pos root)
    omega
  have cell : ca[offset + regs.hold.toNat % 2 ^ root]? = some regs.here := by
    rw [selected, codeLookupValue, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem inside, Option.getD_some]
  have mathRead : tableRead DISTS ca offset root
      (Zlib.Inftrees.Spec.DecodeShort.padded (bitsOfNat regs.hold.toNat regs.bits.toNat)) =
      some (regs.here, regs.here.bits.toNat) := by
    have high : regs.here.op &&& 240 ≠ 0 := nonlink
    simp [tableRead, query, cell, high, show DISTS ≠ LENS by decide]
  have fit : regs.here.bits.toNat ≤ (bitsOfNat regs.hold.toNat regs.bits.toNat).length := by
    simpa only [bitsOfNat_length] using enough
  obtain ⟨symbol, valid, fields, width, _decoded, continued⟩ := meaning.short _ _ _ mathRead fit accepted
  have source : bitsOfNat regs.hold.toNat regs.bits.toNat ++ bytesBits bs = stream regs bs := by
    simp only [stream, natBits_testBit, bitsOfNat]
  have residual : (bitsOfNat regs.hold.toNat regs.bits.toNat).drop regs.here.bits.toNat ++ bytesBits bs =
      (stream regs bs).drop regs.here.bits.toNat := by
    rw [← source, List.drop_append_of_le_length fit]
  have result := continued (bytesBits bs)
  rw [source, residual] at result
  exact ⟨symbol, by simpa [ValidSymbol, show DISTS ≠ LENS by decide] using valid, fields, width, result⟩

/-- The real second-level distance loop exposes its actual padded table
query on arbitrary input, with a genuine wait or a fitted leaf. -/
theorem distLookup2_current_query
    {c : Ctx} {h : Heap} {zs : Nat} {s : InflateState}
    {ref : CodeRef} {offset extent : Nat} {ca : Array Code} {D : List Nat}
    {l : IL} {bs : List UInt8} {first : Code}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (pointer : s.distcode = .ref ref offset) (get : Space.get h ref = some ca)
    (meaning : Inv DISTS ca offset s.distbits.toNat extent D)
    (B : BitInv h l bs) (remembered : l.last = first)
    (rootCell : ca[offset + l.hold.toNat % 2 ^ s.distbits.toNat]? = some first)
    (rootEnough : s.distbits.toNat ≤ l.bits.toNat)
    (link : Zlib.Inftrees.Spec.Subtable.IsLink DISTS first = true) :
    ∃ result regs used,
      runX (lookup2 c true) l h = .ok ((result, regs), h) ∧
      used ≤ 2 ∧ used ≤ bs.length ∧ BitInv h regs (bs.drop used) ∧
      stream regs (bs.drop used) = stream l bs ∧ LookupRegShape l regs ∧ regs.last = first ∧
      regs.next = inputAdvance l.next used ∧
      (result = .ok () ∨ result = .error Ex.leave) ∧
      (result = .error Ex.leave → regs.have_ = 0) ∧
      (result = .ok () → first.bits.toNat + regs.here.bits.toNat ≤ regs.bits.toNat) ∧
      tableRead DISTS ca offset s.distbits.toNat
        (Zlib.Inftrees.Spec.DecodeShort.padded (bitsOfNat regs.hold.toNat regs.bits.toNat)) =
        some (regs.here, first.bits.toNat + regs.here.bits.toNat) ∧
      (result = .ok () → LeafAccepted DISTS regs.here →
        ∃ symbol, symbol ≤ 29 ∧ SymbolEntry DISTS symbol regs.here ∧
          first.bits.toNat + regs.here.bits.toNat = D.getD symbol 0 ∧
          decodeSym D (stream l bs) =
            some (symbol, (stream l bs).drop (first.bits.toNat + regs.here.bits.toNat))) := by
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
    rw [UInt32.toNat_add, UInt8.toNat_toUInt32, UInt8.toNat_toUInt32, Nat.mod_eq_of_lt (by omega)]
  obtain ⟨result, regs, used, run, two, bound, inv, source, shape, count,
    bitBound, selected, entryBound, kinds, enough, exhausted, cursor⟩ :=
    lookupLoop_run_cursor_short (query := subLookupValue ca offset first) (need := need) (fun _ => rfl)
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
  refine ⟨result, regs, used, ?_, two, bound, inv, source, shape, ?_, cursor, kinds,
    (fun wait => (exhausted wait).1), ?_, heldQuery, ?_⟩
  · rw [lookup2_data_eq]
    exact run
  · rw [shape, remembered]
  · intro normal
    rw [← totalNat]
    exact enough normal
  · intro normal accepted
    have fit : first.bits.toNat + regs.here.bits.toNat ≤ regs.bits.toNat := by
      rw [← totalNat]; exact enough normal
    obtain ⟨symbol, valid, fields, width, decoded⟩ :=
      subtable_query_meaning meaning inv currentRoot link selected fit accepted
    rw [source] at decoded
    exact ⟨symbol, by simpa [ValidSymbol, show DISTS ≠ LENS by decide] using valid, fields, width, decoded⟩

theorem distLookup2_actual_query
    {c : Ctx} {h : Heap} {zs : Nat} {s : InflateState}
    {ref : CodeRef} {offset usedExtent : Nat} {ca : Array Code} {alphabet : List Nat}
    {l : IL} {bs : List UInt8} {first : Code}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (pointer : s.distcode = .ref ref offset) (get : Space.get h ref = some ca)
    (meaning : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv DISTS ca offset s.distbits.toNat usedExtent alphabet)
    (B : BitInv h l bs) (remembered : l.last = first)
    (rootCell : ca[offset + l.hold.toNat % 2 ^ s.distbits.toNat]? = some first)
    (rootEnough : s.distbits.toNat ≤ l.bits.toNat)
    (link : Zlib.Inftrees.Spec.Subtable.IsLink DISTS first = true)
    :
    ∃ result regs used,
      runX (lookup2 c true) l h = .ok ((result, regs), h) ∧
      used ≤ 2 ∧ used ≤ bs.length ∧ BitInv h regs (bs.drop used) ∧
      stream regs (bs.drop used) = stream l bs ∧ LookupRegShape l regs ∧ regs.last = first ∧
      regs.next = inputAdvance l.next used ∧ regs.bits.toNat = l.bits.toNat + 8 * used ∧ regs.bits.toNat ≤ max l.bits.toNat 22 ∧
      regs.here = subLookupValue ca offset first regs ∧
      tableRead DISTS ca offset s.distbits.toNat
        (Zlib.Inftrees.Spec.DecodeShort.padded (bitsOfNat regs.hold.toNat regs.bits.toNat)) =
        some (regs.here, first.bits.toNat + regs.here.bits.toNat) ∧
      (result = .ok () ∨ result = .error Ex.leave) ∧
      (result = .ok () → first.bits.toNat + regs.here.bits.toNat ≤ regs.bits.toNat) ∧
      (result = .error Ex.leave → regs.have_ = 0 ∧
        regs.bits.toNat < first.bits.toNat + regs.here.bits.toNat) ∧
      (result = .ok () → LeafAccepted DISTS regs.here →
        ∃ symbol, ValidSymbol DISTS symbol ∧ SymbolEntry DISTS symbol regs.here ∧
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
        exact dataSubLookupBody_run true current first hc hs pointer get lastEq links) B
  have totalNat : (need regs.here).toNat = first.bits.toNat + regs.here.bits.toNat := by
    rw [selected, needNat]
  have currentRoot : ca[offset + regs.hold.toNat % 2 ^ s.distbits.toNat]? = some first :=
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


theorem distSubLookup_actual_meaning {c : Ctx} {h : Heap} {zs : Nat} {s : InflateState}
    {ref : CodeRef} {offset extent : Nat} {ca : Array Code} {alphabet : List Nat} {l : IL} {bs : List UInt8}
    (root : Code) (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (pointer : s.distcode = .ref ref offset) (tableGet : Space.get h ref = some ca)
    (link : LinkOK DistLeaf ca offset root) (before : Nat) (back : s.back = Int32.ofNat before) (backBound : before ≤ 20) (B : BitInv h l bs)
    (meaning : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv DISTS ca offset s.distbits.toNat extent alphabet)
    (rootCell : ca[offset + l.hold.toNat % 2 ^ s.distbits.toNat]? = some root)
    (rootEnough : s.distbits.toNat ≤ l.bits.toNat)
    (queryLink : Zlib.Inftrees.Spec.Subtable.IsLink DISTS root = true) :
    ∃ result regs used after,
      runX (distSubLookup c root) l h = .ok ((result, regs), after) ∧
      used ≤ 2 ∧ used ≤ bs.length ∧ BitInv after regs (bs.drop used) ∧
      SymbolRegShape l regs ∧ regs.last = root ∧ regs.bits.toNat ≤ max l.bits.toNat 22 ∧
      (result = .ok () ∨ result = .error Ex.leave) ∧
      (result = .ok () →
        after = setI h zs { s with back := Int32.ofNat (before + root.bits.toNat) } ∧
        DistLeaf root.bits.toNat regs.here ∧ regs.here.bits.toNat ≤ regs.bits.toNat ∧
        stream regs (bs.drop used) = (stream l bs).drop root.bits.toNat ∧
        regs.bits.toNat = l.bits.toNat + 8 * used - root.bits.toNat) ∧
      (result = .error Ex.leave → after = h ∧ regs.have_ = 0 ∧
        stream regs (bs.drop used) = stream l bs) ∧ regs.next = inputAdvance l.next used ∧
      (result = .ok () → LeafAccepted DISTS regs.here →
        ∃ symbol, ValidSymbol DISTS symbol ∧ SymbolEntry DISTS symbol regs.here ∧
          root.bits.toNat + regs.here.bits.toNat = alphabet.getD symbol 0 ∧
          decodeSym alphabet (stream l bs) = some (symbol,
            (stream l bs).drop (root.bits.toNat + regs.here.bits.toNat))) ∧
      (result = .error Ex.leave → regs.bits.toNat < root.bits.toNat + regs.here.bits.toNat) := by
  let start := { l with last := root }
  have startInv : BitInv h start bs := ⟨B.have_eq, B.next, B.hold_lt⟩
  obtain ⟨result, current, used, run, usedTwo, usedBound, currentInv, sameStream, shape,
    lastRemembered, cursor, count, bitBound, selected, _query, kinds, enough, empty, semantic⟩ :=
    distLookup2_actual_query (first := root) hc hs pointer tableGet meaning startInv rfl rootCell rootEnough queryLink
  have leaf : DistLeaf root.bits.toNat current.here := by
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
    · unfold distSubLookup
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
    have source : runX (distSubLookup c root) l h =
        runX (do
          let last := (← get).last
          DROPBITS last.bits.toUInt32
          let s ← ldInflateState c.st
          let bk ← chkI32 (s.back.toInt + last.bits.toNat)
          wrS c.st fun s => { s with back := bk }) current h := by
      unfold distSubLookup
      rw [runX_bind, runX_modify]
      simp only []
      rw [runX_bind, run]
    have totalEnough := enough rfl
    have rootEnough : root.bits.toNat ≤ current.bits.toNat := by omega
    have rootSmall : root.bits.toUInt32.toNat < 64 := by rw [UInt8.toNat_toUInt32]; have := link.1; omega
    obtain ⟨finalInv, finalStream, finalCount⟩ :=
      DROPBITS_inv currentInv root.bits.toUInt32 (by simpa using rootEnough) rootSmall
    let final := { current with hold := current.hold >>> root.bits.toUInt32.toUInt64, bits := current.bits - root.bits.toUInt32 }
    let after := setI h zs { s with back := Int32.ofNat (before + root.bits.toNat) }
    have checked : chkI32 (s.back.toInt + root.bits.toNat) h = .ok (Int32.ofNat (before + root.bits.toNat), h) := by
      rw [back]
      rw [show (Int32.ofNat before).toInt = (before : Int) from int32_ofInt_toInt before (by omega) (by omega)]
      unfold chkI32
      have rootBound := link.1
      split
      · rfl
      · omega
    have load : ldInflateState c.st h = .ok (s, h) := by rw [hc, ldI_eq, hs]
    have write : wrS c.st (fun s => { s with back := Int32.ofNat (before + root.bits.toNat) }) h = .ok ((), after) := by
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


theorem distLookup1_actual_meaning
    {c : Ctx} {h : Heap} {zs : Nat} {s : InflateState}
    {ref : CodeRef} {offset usedExtent : Nat} {ca : Array Code} {alphabet : List Nat}
    {l : IL} {bs : List UInt8}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (pointer : s.distcode = .ref ref offset) (get : Space.get h ref = some ca)
    (meaning : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv DISTS ca offset s.distbits.toNat usedExtent alphabet)
    (B : BitInv h l bs) :
    ∃ result regs used,
      runX (lookup1 c true) l h = .ok ((result, regs), h) ∧
      used ≤ 2 ∧ used ≤ bs.length ∧ BitInv h regs (bs.drop used) ∧
      stream regs (bs.drop used) = stream l bs ∧ LookupRegShape l regs ∧
      regs.here = codeLookupValue ca offset s.distbits.toNat regs ∧
      regs.next = inputAdvance l.next used ∧
      regs.here.bits.toNat ≤ 15 ∧
      (result = .ok () → regs.here.bits.toNat ≤ regs.bits.toNat) ∧
      (result = .ok () ∨ result = .error Ex.leave) ∧
      (result = .error Ex.leave → regs.have_ = 0 ∧ regs.bits.toNat < regs.here.bits.toNat) ∧
      regs.bits.toNat = l.bits.toNat + 8 * used ∧
      regs.bits.toNat ≤ max l.bits.toNat 22 ∧
      (result = .ok () → ¬ SlowDistLink regs.here → LeafAccepted DISTS regs.here →
        ∃ symbol, ValidSymbol DISTS symbol ∧ SymbolEntry DISTS symbol regs.here ∧
          regs.here.bits.toNat = alphabet.getD symbol 0 ∧
          decodeSym alphabet (stream l bs) =
            some (symbol, (stream l bs).drop regs.here.bits.toNat)) := by
  have readable : RootTableReadable ca offset s.distbits.toNat := by
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
      (query := codeLookupValue ca offset s.distbits.toNat)
      (need := fun entry => entry.bits.toUInt32) (fun _ => rfl)
      (by intro current; rw [UInt8.toNat_toUInt32]; exact readable.2.2 _ (Nat.mod_lt _ (Nat.two_pow_pos _)))
      (fun current _ => dataLookupBody_run true current hc hs pointer get readable) B
  have actual : runX (lookup1 c true) l h = .ok ((result, regs), h) := by
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
  have inside : offset + regs.hold.toNat % 2 ^ s.distbits.toNat < ca.size := by
    have root := meaning.rootTable.2.2.1
    have index := Nat.mod_lt regs.hold.toNat (Nat.two_pow_pos s.distbits.toNat)
    omega
  have cell : ca[offset + regs.hold.toNat % 2 ^ s.distbits.toNat]? = some regs.here := by
    rw [selected, codeLookupValue, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem inside,
      Option.getD_some]
  have mathRead : tableRead DISTS ca offset s.distbits.toNat
      (Zlib.Inftrees.Spec.DecodeShort.padded (bitsOfNat regs.hold.toNat regs.bits.toNat)) =
      some (regs.here, regs.here.bits.toNat) := by
    have high : regs.here.op &&& 240 ≠ 0 := nonlink
    simp [tableRead, query, cell, high, show DISTS ≠ LENS by decide]

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



theorem distLookup_actual_meaning {c : Ctx} {h : Heap} {zs : Nat} {s : InflateState}
    {ref : CodeRef} {offset extent : Nat} {ca : Array Code} {alphabet : List Nat} {l : IL} {bs : List UInt8}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (pointer : s.distcode = .ref ref offset) (tableGet : Space.get h ref = some ca)
    (safe : DistTableSafe ca offset s.distbits.toNat) (before : Nat) (back : s.back = Int32.ofNat before) (backBound : before ≤ 20) (B : BitInv h l bs)
    (meaning : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv DISTS ca offset s.distbits.toNat extent alphabet) :
    ∃ result regs used after,
      runX (distLookup c) l h = .ok ((result, regs), after) ∧
      used ≤ 4 ∧ used ≤ bs.length ∧ BitInv after regs (bs.drop used) ∧
      SymbolRegShape l regs ∧ regs.bits.toNat ≤ max l.bits.toNat 22 ∧
      (result = .ok () ∨ result = .error Ex.leave) ∧
      (result = .ok () → ∃ dropped, dropped ≤ 15 ∧
        after = setI h zs { s with back := Int32.ofNat (before + dropped) } ∧
        DistLeaf dropped regs.here ∧ regs.here.bits.toNat ≤ regs.bits.toNat ∧
        stream regs (bs.drop used) = (stream l bs).drop dropped ∧
        regs.bits.toNat = l.bits.toNat + 8 * used - dropped) ∧
      (result = .error Ex.leave → after = h ∧ regs.have_ = 0 ∧
        stream regs (bs.drop used) = stream l bs) ∧ regs.next = inputAdvance l.next used ∧
      (result = .ok () → LeafAccepted DISTS regs.here →
        ∃ symbol dropped, dropped ≤ 15 ∧ ValidSymbol DISTS symbol ∧ SymbolEntry DISTS symbol regs.here ∧
          dropped + regs.here.bits.toNat = alphabet.getD symbol 0 ∧
          after = setI h zs {s with back := Int32.ofNat (before + dropped)} ∧
          stream regs (bs.drop used) = (stream l bs).drop dropped ∧
          decodeSym alphabet (stream l bs) = some (symbol,
            (stream l bs).drop (dropped + regs.here.bits.toNat))) := by
  obtain ⟨first, current, used, run, usedTwo, usedBound, inv, sameStream, shape,
    selected, cursor, entryBound, enough, kinds, empty, count, bitBound, rootMeaning⟩ :=
    distLookup1_actual_meaning hc hs pointer tableGet meaning B
  have classification : if DistLink current.here then LinkOK DistLeaf ca offset current.here else DistLeaf 0 current.here := by
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
    · unfold distLookup
      rw [runX_bind, run]
    · intro impossible
      cases impossible
    · intro impossible; cases impossible
  | ok resultUnit =>
    cases resultUnit
    have prefixRun : runX (distLookup c) l h = runX (distRootTail c current.here) current h := by
      unfold distLookup
      rw [runX_bind, run]
      simp only [runX_bind, runX_get]
    by_cases slow : SlowDistLink current.here
    · have link : DistLink current.here := slowDistLink_fast slow
      rw [ite_eq_left link] at classification
      obtain ⟨result, final, used2, after, subRun, usedTwo2, usedBound2, finalInv, finalShape,
        _, finalBound, kinds2, done, leave, subCursor, subMeaning, _short⟩ :=
        distSubLookup_actual_meaning current.here hc hs pointer tableGet classification before back backBound inv meaning
          (by
            have inside : offset + current.hold.toNat % 2 ^ s.distbits.toNat < ca.size := by
              have extent := meaning.rootTable.2.2.1
              have index := Nat.mod_lt current.hold.toNat (Nat.two_pow_pos s.distbits.toNat)
              omega
            rw [selected, codeLookupValue, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem inside, Option.getD_some])
          (by
            have cell : ca[offset + current.hold.toNat % 2 ^ s.distbits.toNat]? = some current.here := by
              have inside : offset + current.hold.toNat % 2 ^ s.distbits.toNat < ca.size := by
                have extent := meaning.rootTable.2.2.1
                have index := Nat.mod_lt current.hold.toNat (Nat.two_pow_pos s.distbits.toNat)
                omega
              rw [selected, codeLookupValue, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem inside, Option.getD_some]
            have isLink : Zlib.Inftrees.Spec.Subtable.IsLink DISTS current.here = true := by
              simpa [Zlib.Inftrees.Spec.Subtable.IsLink, SlowDistLink, show DISTS ≠ LENS by decide] using slow
            have rootBits := (meaning.subtables _ _ (Nat.mod_lt _ (Nat.two_pow_pos _)) cell isLink).1
            rw [← rootBits]
            exact enough rfl)
          (by simpa [Zlib.Inftrees.Spec.Subtable.IsLink, SlowDistLink, show DISTS ≠ LENS by decide] using slow)
      have totalBound : used + used2 ≤ bs.length := by
        simp only [List.length_drop] at usedBound2
        omega
      have finalInv' : BitInv after final (bs.drop (used + used2)) := by
        simpa only [List.drop_drop, Nat.add_comm] using finalInv
      have actual : runX (distLookup c) l h = .ok ((result, final), after) := by
        rw [prefixRun, distRootTail_link c current.here slow]
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
    · have notLink : ¬ DistLink current.here := by
        intro link
        have table := classification
        rw [ite_eq_left link] at table
        exact slow (distLink_slow table)
      rw [ite_eq_right notLink] at classification
      refine ⟨.ok (), current, used, h, ?_, by omega, usedBound, inv, shape.symbol,
        bitBound, Or.inl rfl, ?_, ?_, cursor, ?_⟩
      · rw [prefixRun, distRootTail_leaf c current.here slow, runX_pure]
      · intro _
        refine ⟨0, by omega, ?_, classification, enough rfl, ?_, ?_⟩
        · have stateEq : { s with back := Int32.ofNat (before + 0) } = s := by
            rw [Nat.add_zero, ← back]
          rw [stateEq]
          simp only [setI, upd_self _ _ _ hs]
        · simpa using sameStream
        · simpa using count
      · intro impossible
        cases impossible

      · intro _ accepted
        obtain ⟨symbol, valid, fields, width, decoded⟩ := rootMeaning rfl slow accepted
        refine ⟨symbol, 0, by omega, valid, fields, by simpa using width, ?_, ?_, ?_⟩
        · have stateEq : { s with back := Int32.ofNat (before + 0) } = s := by
            rw [Nat.add_zero, ← back]
          rw [stateEq]
          simp only [setI, upd_self _ _ _ hs]
        · simpa using sameStream
        · simpa using decoded



theorem DIST_arbitrary_lookup_boundary {c : Ctx} {l : IL} {h : Heap}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8} (before : Nat)
    (hc : c.st = some (.tab zs)) (good : Good h r zs z s)
    (tables : DataTablesSafe h s) (B : BitInv h l bs)
    (back : s.back = Int32.ofNat before) (backBound : before ≤ 20)
    {ref : CodeRef} {offset extent : Nat} {array : Array Code} {D : List Nat}
    (pointer : s.distcode = .ref ref offset) (tableGet : Space.get h ref = some array)
    (tableSafe : DistTableSafe array offset s.distbits.toNat)
    (meaning : Inv DISTS array offset s.distbits.toNat extent D) :
    (∃ regs used,
      used ≤ 4 ∧ used ≤ bs.length ∧
      runX (inflate_DIST c) l h = .ok ((.error Ex.leave, regs), h) ∧
      BitInv h regs (bs.drop used) ∧ regs.have_ = 0 ∧
      stream regs (bs.drop used) = stream l bs ∧ SymbolRegShape l regs ∧ regs.next = inputAdvance l.next used ∧ regs.bits.toNat ≤ max l.bits.toNat 22) ∨
    (∃ regs after state used dropped,
      used ≤ 4 ∧ used ≤ bs.length ∧ dropped ≤ 15 ∧
      runX (inflate_DIST c) l h = runX (distFinish c) regs after ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧
      BitInv after regs (bs.drop used) ∧ DistLeaf dropped regs.here ∧
      regs.here.bits.toNat ≤ regs.bits.toNat ∧ state.back = Int32.ofNat (before + dropped) ∧
      stream regs (bs.drop used) = (stream l bs).drop dropped ∧
      SymbolRegShape l regs ∧ DecodeStateFrame s state ∧
      regs.bits.toNat = l.bits.toNat + 8 * used - dropped ∧
      after = setI h zs state ∧ state = { s with back := Int32.ofNat (before + dropped) } ∧ regs.next = inputAdvance l.next used ∧ regs.bits.toNat ≤ max l.bits.toNat 22 ∧
      (LeafAccepted DISTS regs.here →
        ∃ symbol, ValidSymbol DISTS symbol ∧ SymbolEntry DISTS symbol regs.here ∧
          dropped + regs.here.bits.toNat = D.getD symbol 0 ∧
          decodeSym D (stream l bs) = some (symbol, (stream l bs).drop (dropped + regs.here.bits.toNat)))) := by
  obtain ⟨result, regs, used, after, run, usedFour, usedBound, inv, shape, bitBound, kinds, done, leave, cursor, semantic⟩ :=
    distLookup_actual_meaning hc good.live.hs pointer tableGet tableSafe before back backBound B meaning
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
    refine ⟨regs, used, usedFour, usedBound, ?_, inv, empty, bits, shape, cursor, bitBound⟩
    rw [inflate_DIST_lookup_cut, runX_bind, run]
  | ok resultUnit =>
    cases resultUnit
    obtain ⟨dropped, dropBound, heapEq, leaf, enough, bits, count⟩ := done rfl
    subst after
    let state := { s with back := Int32.ofNat (before + dropped) }
    have finalGood : Good (setI h zs state) r zs z state := good.decode_update rfl good.live.mode
    have finalTables : DataTablesSafe (setI h zs state) state := tables.decode_update good.live.hs rfl
    right
    refine ⟨regs, setI h zs state, state, used, dropped, usedFour, usedBound, dropBound,
      ?_, finalGood, finalTables, inv, leaf, enough, rfl, bits, shape, rfl, count, rfl, rfl, cursor, bitBound, ?_⟩
    · rw [inflate_DIST_lookup_cut, runX_bind, run]
    · intro accepted
      obtain ⟨symbol, semanticDrop, semanticBound, valid, fields, width, semanticHeap, _, decoded⟩ := semantic rfl accepted
      have stateSame : {s with back := Int32.ofNat (before + semanticDrop)} = state := by
        apply Option.some.inj
        rw [← setI_istates_same h zs {s with back := Int32.ofNat (before + semanticDrop)}, ← semanticHeap]
        rw [setI_istates_same]
      have dropSame := congrArg (fun st : InflateState => st.back.toInt) stateSame
      change (Int32.ofNat (before + semanticDrop)).toInt = (Int32.ofNat (before + dropped)).toInt at dropSame
      rw [show (Int32.ofNat (before + semanticDrop)).toInt = ((before + semanticDrop : Nat) : Int) from int32_ofInt_toInt (before + semanticDrop) (by omega) (by omega),
        show (Int32.ofNat (before + dropped)).toInt = ((before + dropped : Nat) : Int) from int32_ofInt_toInt (before + dropped) (by omega) (by omega)] at dropSame
      have sameNat : semanticDrop = dropped := by omega
      subst semanticDrop
      exact ⟨symbol, valid, fields, width, decoded⟩

/-- The actual DIST consumes its selected code before its real leaf
classifier. Accepted leaves derive a genuine independent current decode. -/
theorem DIST_arbitrary_finish_cut
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {ref : CodeRef} {offset extent : Nat} {ca : Array Code} {D : List Nat}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s) (B : BitInv h l bs)
    (before : Nat) (back : s.back = Int32.ofNat before) (backBound : before ≤ 20)
    (pointer : s.distcode = .ref ref offset) (tableGet : Space.get h ref = some ca)
    (safe : DistTableSafe ca offset s.distbits.toNat)
    (meaning : Inv DISTS ca offset s.distbits.toNat extent D) :
    (∃ regs used,
      used ≤ 4 ∧ used ≤ bs.length ∧ runX (inflate_DIST c) l h = .ok ((.error Ex.leave, regs), h) ∧
      BitInv h regs (bs.drop used) ∧ regs.have_ = 0 ∧ stream regs (bs.drop used) = stream l bs ∧
      SymbolRegShape l regs ∧ regs.next = inputAdvance l.next used) ∨
    (∃ regs after state used entry consumed,
      used ≤ 4 ∧ used ≤ bs.length ∧ consumed ≤ 15 ∧
      runX (inflate_DIST c) l h = runX (distLeafTail c entry) regs after ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧ BitInv after regs (bs.drop used) ∧
      SymbolRegShape l regs ∧ DecodeStateFrame s state ∧ regs.next = inputAdvance l.next used ∧
      state.back = Int32.ofNat (before + consumed) ∧ state.length = s.length ∧ state.was = s.was ∧
      stream regs (bs.drop used) = (stream l bs).drop consumed ∧ after = setI h zs state ∧
      DistLeaf 0 entry ∧
      (LeafAccepted DISTS entry → ∃ symbol, ValidSymbol DISTS symbol ∧ SymbolEntry DISTS symbol entry ∧
        consumed = D.getD symbol 0 ∧ decodeSym D (stream l bs) = some (symbol, stream regs (bs.drop used)))) := by
  rcases DIST_arbitrary_lookup_boundary before E.st good tables B back backBound pointer tableGet safe meaning with wait | reached
  · obtain ⟨regs, used, four, bound, run, bits, empty, source, shape, cursor, _bitsBound⟩ := wait
    exact Or.inl ⟨regs, used, four, bound, run, bits, empty, source, shape, cursor⟩
  · obtain ⟨looked, heap, lookupState, used, dropped, four, bound, droppedBound, cut, current,
      currentTables, bits, leaf, enough, lookupBack, source, shape, frame, _count, heapEq,
      stateEq, cursor, _bitsBound, semantic⟩ := reached
    obtain ⟨regs, after, state, finish, finalGood, finalTables, finalBits, finalFrame, regShape,
      finalHeap, finalState, suffix, _count, _here, next⟩ :=
      distFinish_consume_cursor before dropped E.st current currentTables leaf lookupBack backBound enough bits
    have consumedBound : dropped + looked.here.bits.toNat ≤ 15 := by have := leaf.1; omega
    have sourceFinal : stream regs (bs.drop used) = (stream l bs).drop (dropped + looked.here.bits.toNat) := by
      rw [suffix, source, List.drop_drop]
    have leaf0 : DistLeaf 0 looked.here := ⟨by omega, leaf.2⟩
    refine Or.inr ⟨regs, after, state, used, looked.here, dropped + looked.here.bits.toNat,
      four, bound, consumedBound, cut.trans finish, finalGood, finalTables, finalBits,
      shape.trans regShape, frame.trans finalFrame, next.trans cursor, ?_, ?_, ?_,
      sourceFinal, ?_, leaf0, ?_⟩
    · rw [finalState]; simp only [Nat.add_assoc]
    · rw [finalState, stateEq]
    · rw [finalState, stateEq]
    · rw [finalHeap, heapEq, setI_setI]
    · intro accepted
      obtain ⟨symbol, valid, fields, width, decoded⟩ := semantic accepted
      exact ⟨symbol, valid, fields, width, by rwa [sourceFinal]⟩

/-- The real invalid-distance leaf branch writes BAD immediately. -/
theorem distLeafTail_invalid_source {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {here : Code} {bs : List UInt8}
    (E : Env c h r zs z s) (good : Good h r zs z s) (B : BitInv h l bs)
    (invalid : here.op &&& 64 ≠ 0) :
    ∃ after stream state, runX (distLeafTail c here) l h = .ok ((.ok (), l), after) ∧
      Good after r zs stream state ∧ DataTableInvariant after state ∧ BitInv after l bs ∧
      state.mode = BAD ∧ state = {s with mode := BAD} ∧ DecodeStateFrame s state := by
  have member : "invalid distance code" ∈ strTable := by decide +kernel
  obtain ⟨i, _, badRun⟩ := badMode_run E member
  let stream := {z with msg := .ref (.str i) 0}
  let state := {s with mode := BAD}
  have inv : StInv h zs state := good.inv.of_fields rfl rfl rfl rfl rfl rfl rfl rfl rfl good.inv.bits rfl rfl rfl
  have current : Good (badHeap h r zs z s i) r zs stream state :=
    good.setZI rfl good.live.zalloc good.live.zfree rfl
      (by change HEAD ≤ BAD ∧ BAD ≤ SYNC; decide) inv
  have bits : BitInv (badHeap h r zs z s i) l bs := by
    refine ⟨B.have_eq, ?_, B.hold_lt⟩
    rcases B.next with empty | ⟨ref, array, off, pointer, arrayGet, bound, contents⟩
    · exact Or.inl empty
    · refine Or.inr ⟨ref, array, off, pointer, ?_, bound, contents⟩
      cases ref <;> cases r <;> simp only [badHeap, setI, Space.get, ZStreamRef.put] <;>
        first | exact arrayGet | split <;> exact arrayGet
  refine ⟨_, stream, state, ?_, current, ?_, bits, rfl, rfl, rfl⟩
  · unfold distLeafTail
    simp [invalid, runX_bind, runX_lift_ok badRun, runX_pure]
  · intro active
    change DataTableMode BAD at active
    rcases active with eq | eq | eq | eq | eq | eq | eq <;> cases eq

/-- Arbitrary distance input produces either a true input wait, a real
invalid-leaf BAD, or a genuine independently decoded distance symbol and
its actual DISTEXT continuation. No future parse is assumed. -/
theorem DIST_current_source
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {ref : CodeRef} {offset extent : Nat} {ca : Array Code} {D : List Nat}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s) (B : BitInv h l bs)
    (before : Nat) (back : s.back = Int32.ofNat before) (backBound : before ≤ 20)
    (pointer : s.distcode = .ref ref offset) (tableGet : Space.get h ref = some ca)
    (safe : DistTableSafe ca offset s.distbits.toNat)
    (meaning : Inv DISTS ca offset s.distbits.toNat extent D) :
    (∃ regs used,
      used ≤ 4 ∧ used ≤ bs.length ∧ runX (inflate_DIST c) l h = .ok ((.error Ex.leave, regs), h) ∧
      BitInv h regs (bs.drop used) ∧ regs.have_ = 0 ∧ stream regs (bs.drop used) = stream l bs ∧
      SymbolRegShape l regs ∧ regs.next = inputAdvance l.next used) ∨
    (∃ (entry : Code), ∃ regs after finalZ state used consumed,
      used ≤ 4 ∧ used ≤ bs.length ∧ consumed ≤ 15 ∧ entry.op &&& 64 ≠ 0 ∧
      runX (inflate_DIST c) l h = .ok ((.ok (), regs), after) ∧
      Good after r zs finalZ state ∧ DataTableInvariant after state ∧ BitInv after regs (bs.drop used) ∧
      state.mode = BAD ∧ DecodeStateFrame s state ∧ SymbolRegShape l regs ∧
      stream regs (bs.drop used) = (stream l bs).drop consumed ∧ regs.next = inputAdvance l.next used) ∨
    (∃ regs after state used symbol consumed,
      used ≤ 4 ∧ used ≤ bs.length ∧ consumed ≤ 15 ∧ symbol ≤ 29 ∧
      decodeSym D (stream l bs) = some (symbol, stream regs (bs.drop used)) ∧ consumed = D.getD symbol 0 ∧
      runX (inflate_DIST c) l h = runX (inflate_DISTEXT c) regs after ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧ BitInv after regs (bs.drop used) ∧
      state.mode = DISTEXT ∧ state.offset.toNat = distBases.getD symbol 0 ∧
      state.extra.toNat = distExtras.getD symbol 0 ∧
      state.back = Int32.ofNat (before + consumed) ∧ state.length = s.length ∧ state.was = s.was ∧
      DecodeStateFrame s state ∧ SymbolRegShape l regs ∧
      stream regs (bs.drop used) = (stream l bs).drop consumed ∧ regs.next = inputAdvance l.next used ∧
      after = setI h zs state ∧ 1 ≤ state.offset.toNat ∧ state.extra.toNat ≤ 13 ∧
      state.offset.toNat + 2 ^ state.extra.toNat ≤ 32769) := by
  rcases DIST_arbitrary_finish_cut E good tables B before back backBound pointer tableGet safe meaning with wait | reached
  · exact Or.inl wait
  · obtain ⟨regs, heap, state, used, entry, consumed, four, bound, codeBound, cut, current,
      currentTables, bits, shape, frame, cursor, nextBack, length, was, source, heapEq, leaf, semantic⟩ := reached
    have env : Env c heap r zs z state := ⟨E.strm, E.st, current.live.hz, current.live.hs⟩
    by_cases invalid : entry.op &&& 64 ≠ 0
    · obtain ⟨after, stream, final, actual, finalGood, finalTables, finalBits, bad, stateEq, finalFrame⟩ :=
        distLeafTail_invalid_source env current bits invalid
      exact Or.inr (Or.inl ⟨entry, regs, after, stream, final, used, consumed, four, bound, codeBound,
        invalid, cut.trans actual, finalGood, finalTables, finalBits, bad, frame.trans finalFrame,
        shape, source, cursor⟩)
    · have noInvalid : entry.op &&& 64 = 0 := Classical.not_not.mp invalid
      have accepted : LeafAccepted DISTS entry := by
        simpa only [LeafAccepted, show DISTS ≠ LENS by decide, ite_false] using noInvalid
      obtain ⟨symbol, valid, fields, width, decoded⟩ := semantic accepted
      obtain ⟨symbolBound, extraField, baseField⟩ := AcceptedToken.distance_fields valid fields
      let final := {state with offset := entry.val.toUInt32, extra := entry.op.toUInt32 &&& 15, mode := DISTEXT}
      let after := setI heap zs final
      have tail : runX (distLeafTail c entry) regs heap = runX (inflate_DISTEXT c) regs after := by
        unfold distLeafTail
        simp only [noInvalid, bne_self_eq_false, Bool.false_eq_true, ite_false, runX_bind, runX_wrS env]
        have env1 : Env c (setI heap zs {state with offset := entry.val.toUInt32, extra := entry.op.toUInt32 &&& 15}) r zs z
            {state with offset := entry.val.toUInt32, extra := entry.op.toUInt32 &&& 15} :=
          ⟨E.strm, E.st, by simpa using env.hz, by simp⟩
        rw [runX_setMode env1]
        simp only [setI_setI]
        rfl
      have finalBase : final.offset.toNat = distBases.getD symbol 0 := by
        change entry.val.toUInt32.toNat = _
        rw [UInt16.toNat_toUInt32, baseField]
      have finalExtra : final.extra.toNat = distExtras.getD symbol 0 := by
        change (entry.op.toUInt32 &&& 15).toNat = _
        rw [UInt8.toNat_and] at extraField
        rw [UInt32.toNat_and, UInt8.toNat_toUInt32]
        exact extraField
      obtain ⟨basePositive, extraBound, budget⟩ := SlowExtraSemanticPath.distance_base_extra_bounds symbol symbolBound
      refine Or.inr (Or.inr ⟨regs, after, final, used, symbol, consumed, four, bound, codeBound, symbolBound,
        decoded, width, cut.trans tail,
        current.decode_update rfl (by change HEAD ≤ DISTEXT ∧ DISTEXT ≤ SYNC; decide),
        currentTables.decode_update current.live.hs rfl, bits.decode_update zs final,
        rfl, finalBase, finalExtra, nextBack, length, was, frame.trans (by rfl), shape,
        source, cursor, ?_, ?_, ?_, ?_⟩)
      · change setI heap zs final = _
        rw [heapEq, setI_setI]
      · rw [finalBase]; exact basePositive
      · rw [finalExtra]; exact extraBound
      · rw [finalBase, finalExtra]; exact budget


#print axioms dist_root_accepted_source
#print axioms distLookup2_current_query
#print axioms distLookup2_actual_query
#print axioms distSubLookup_actual_meaning
#print axioms distLookup1_actual_meaning
#print axioms distLookup_actual_meaning
#print axioms DIST_arbitrary_lookup_boundary
#print axioms DIST_arbitrary_finish_cut
#print axioms distLeafTail_invalid_source
#print axioms DIST_current_source
end Zlib.Inflate.Proofs.SlowArbitrarySource
