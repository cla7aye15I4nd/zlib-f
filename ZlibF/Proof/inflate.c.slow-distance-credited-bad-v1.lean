import ZlibF.Proof.«inflate.c.slow-distance-arbitrary-source»
import ZlibF.Proof.«inftrees.c.decode.stability-rejection»

namespace Zlib.Inflate.Proofs.SlowCreditedDistance
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inftrees Zlib.Inffast.Spec Zlib.Inffast.Proofs
open Zlib.Inftrees.Spec
open Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness
open Zlib.Inftrees.Spec.DecodeTableInvariant Zlib.Inftrees.Spec.DecodeTableStability
open SlowArbitrarySource SlowSubtablePath SlowPayloadPath
set_option autoImplicit false

/-- A fitted rejected actual held query already rejects all later bits.
The rejected word includes all bits actually pulled before the decision. -/
theorem held_query_rejected {l : IL} {bs : List UInt8}
    {codes : Array Code} {offset root extent : Nat} {D : List Nat} {entry : Code} {consumed : Nat}
    (meaning : Inv DISTS codes offset root extent D) (stable : StableQuery DISTS codes offset root)
    (query : tableRead DISTS codes offset root (DecodeShort.padded (bitsOfNat l.hold.toNat l.bits.toNat)) = some (entry, consumed))
    (fit : consumed ≤ l.bits.toNat) (rejected : ¬ LeafAccepted DISTS entry) :
    ∃ word, consumed ≤ word.length ∧ word ++ bytesBits bs = stream l bs ∧
      ∀ future : List Bool, ¬ ∃ symbol rest, decodeSym D (word ++ future) = some (symbol, rest) ∧ symbol ≤ 29 := by
  refine ⟨bitsOfNat l.hold.toNat l.bits.toNat, by simpa only [bitsOfNat_length] using fit, ?_, ?_⟩
  · simp only [stream, natBits_testBit, bitsOfNat]
  · have invalid := Zlib.Inftrees.Proofs.short_rejected_leaf_stays_invalid DISTS codes offset root extent D
      meaning stable _ _ _ query (by simpa only [bitsOfNat_length] using fit) rejected
    simpa only [ValidSymbol, show DISTS ≠ LENS by decide, ite_false] using invalid

/-- The actual nonlink root query is recorded regardless of acceptance. -/
theorem root_query_read {h : Heap} {regs : IL} {bs : List UInt8} {ca : Array Code}
    {offset root extent : Nat} {D : List Nat}
    (meaning : Inv DISTS ca offset root extent D) (B : BitInv h regs bs)
    (selected : regs.here = codeLookupValue ca offset root regs) (nonlink : ¬ SlowDistLink regs.here) :
    tableRead DISTS ca offset root (DecodeShort.padded (bitsOfNat regs.hold.toNat regs.bits.toNat)) =
      some (regs.here, regs.here.bits.toNat) := by
  obtain ⟨suffix, query⟩ := ZlibF.Math.InflateHeldBits.padded_query B.hold_lt meaning.rootTable.2.1
  have inside : offset + regs.hold.toNat % 2 ^ root < ca.size := by
    have extent := meaning.rootTable.2.2.1
    have index := Nat.mod_lt regs.hold.toNat (Nat.two_pow_pos root)
    omega
  have cell : ca[offset + regs.hold.toNat % 2 ^ root]? = some regs.here := by
    rw [selected, codeLookupValue, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem inside, Option.getD_some]
  have high : regs.here.op &&& 240 ≠ 0 := nonlink
  simp [tableRead, query, cell, high, show DISTS ≠ LENS by decide]

theorem lookup2_credited_rejection
    {c : Ctx} {h : Heap} {zs : Nat} {s : InflateState}
    {ref : CodeRef} {offset usedExtent : Nat} {ca : Array Code} {alphabet : List Nat}
    {l : IL} {bs : List UInt8} {first : Code}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (pointer : s.distcode = .ref ref offset) (get : Space.get h ref = some ca)
    (meaning : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv DISTS ca offset s.distbits.toNat usedExtent alphabet)
    (stable : StableQuery DISTS ca offset s.distbits.toNat)
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
            (stream l bs).drop (first.bits.toNat + regs.here.bits.toNat))) ∧
      (result = .ok () → ¬ LeafAccepted DISTS regs.here →
        ∃ word, first.bits.toNat + regs.here.bits.toNat ≤ word.length ∧
          word ++ bytesBits (bs.drop used) = stream l bs ∧
          ∀ future : List Bool, ¬ ∃ symbol rest, decodeSym alphabet (word ++ future) = some (symbol, rest) ∧ symbol ≤ 29) := by
  obtain ⟨result, regs, used, actual, two, bound, bits, source, shape, last, cursor,
    count, bitBound, selected, query, kinds, enough, empty, semantic⟩ :=
    distLookup2_actual_query hc hs pointer get meaning B remembered rootCell rootEnough link
  refine ⟨result, regs, used, actual, two, bound, bits, source, shape, last, cursor,
    count, bitBound, selected, query, kinds, enough, empty, semantic, ?_⟩
  intro normal rejected
  obtain ⟨word, fit, wordSource, invalid⟩ := held_query_rejected meaning stable query (enough normal) rejected
  exact ⟨word, fit, wordSource.trans source, invalid⟩

theorem lookup1_credited_rejection
    {c : Ctx} {h : Heap} {zs : Nat} {s : InflateState}
    {ref : CodeRef} {offset usedExtent : Nat} {ca : Array Code} {alphabet : List Nat}
    {l : IL} {bs : List UInt8}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (pointer : s.distcode = .ref ref offset) (get : Space.get h ref = some ca)
    (meaning : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv DISTS ca offset s.distbits.toNat usedExtent alphabet)
    (stable : StableQuery DISTS ca offset s.distbits.toNat)
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
            some (symbol, (stream l bs).drop regs.here.bits.toNat)) ∧
      (result = .ok () → ¬ SlowDistLink regs.here → ¬ LeafAccepted DISTS regs.here →
        ∃ word, regs.here.bits.toNat ≤ word.length ∧ word ++ bytesBits (bs.drop used) = stream l bs ∧
          ∀ future : List Bool, ¬ ∃ symbol rest, decodeSym alphabet (word ++ future) = some (symbol, rest) ∧ symbol ≤ 29) := by
  obtain ⟨result, regs, used, actual, two, bound, bits, source, shape, selected, cursor,
    width, enough, kinds, empty, count, bitBound, semantic⟩ :=
    distLookup1_actual_meaning hc hs pointer get meaning B
  refine ⟨result, regs, used, actual, two, bound, bits, source, shape, selected, cursor,
    width, enough, kinds, empty, count, bitBound, semantic, ?_⟩
  intro normal nonlink rejected
  have query := root_query_read meaning bits selected nonlink
  obtain ⟨word, fit, wordSource, invalid⟩ := held_query_rejected meaning stable query (enough normal) rejected
  exact ⟨word, fit, wordSource.trans source, invalid⟩

theorem subLookup_credited_rejection {c : Ctx} {h : Heap} {zs : Nat} {s : InflateState}
    {ref : CodeRef} {offset extent : Nat} {ca : Array Code} {alphabet : List Nat} {l : IL} {bs : List UInt8}
    (root : Code) (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (pointer : s.distcode = .ref ref offset) (tableGet : Space.get h ref = some ca)
    (link : LinkOK DistLeaf ca offset root) (before : Nat) (back : s.back = Int32.ofNat before) (backBound : before ≤ 20) (B : BitInv h l bs)
    (meaning : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv DISTS ca offset s.distbits.toNat extent alphabet)
    (stable : StableQuery DISTS ca offset s.distbits.toNat)
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
      (result = .error Ex.leave → regs.bits.toNat < root.bits.toNat + regs.here.bits.toNat) ∧
      (result = .ok () → ¬ LeafAccepted DISTS regs.here →
        ∃ word, root.bits.toNat + regs.here.bits.toNat ≤ word.length ∧
          word ++ bytesBits (bs.drop used) = stream l bs ∧
          ∀ future : List Bool, ¬ ∃ symbol rest, decodeSym alphabet (word ++ future) = some (symbol, rest) ∧ symbol ≤ 29) := by
  let start := { l with last := root }
  have startInv : BitInv h start bs := ⟨B.have_eq, B.next, B.hold_lt⟩
  obtain ⟨result, current, used, run, usedTwo, usedBound, currentInv, sameStream, shape,
    lastRemembered, cursor, count, bitBound, selected, _query, kinds, enough, empty, semantic, semanticBad⟩ :=
    lookup2_credited_rejection (first := root) hc hs pointer tableGet meaning stable startInv rfl rootCell rootEnough queryLink
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
      symbolShape, lastEq, bitBound, Or.inr rfl, ?_, ?_, cursor, ?_, ?_, ?_⟩
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
    · intro impossible; cases impossible
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
      symbolShape.trans (by rfl), lastEq, ?_, Or.inl rfl, ?_, ?_, cursor, ?_, ?_, ?_⟩
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
    · intro normal rejected
      exact semanticBad normal rejected

theorem distLookup_credited_rejection {c : Ctx} {h : Heap} {zs : Nat} {s : InflateState}
    {ref : CodeRef} {offset extent : Nat} {ca : Array Code} {alphabet : List Nat} {l : IL} {bs : List UInt8}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (pointer : s.distcode = .ref ref offset) (tableGet : Space.get h ref = some ca)
    (safe : DistTableSafe ca offset s.distbits.toNat) (before : Nat) (back : s.back = Int32.ofNat before) (backBound : before ≤ 20) (B : BitInv h l bs)
    (meaning : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv DISTS ca offset s.distbits.toNat extent alphabet)
    (stable : StableQuery DISTS ca offset s.distbits.toNat) :
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
            (stream l bs).drop (dropped + regs.here.bits.toNat))) ∧
      (result = .ok () → ¬ LeafAccepted DISTS regs.here →
        ∃ word dropped, dropped ≤ 15 ∧
          after = setI h zs {s with back := Int32.ofNat (before + dropped)} ∧
          dropped + regs.here.bits.toNat ≤ word.length ∧
          word ++ bytesBits (bs.drop used) = stream l bs ∧
          ∀ future : List Bool, ¬ ∃ symbol rest, decodeSym alphabet (word ++ future) = some (symbol, rest) ∧ symbol ≤ 29) := by
  obtain ⟨first, current, used, run, usedTwo, usedBound, inv, sameStream, shape,
    selected, cursor, entryBound, enough, kinds, empty, count, bitBound, rootMeaning, rootBad⟩ :=
    lookup1_credited_rejection hc hs pointer tableGet meaning stable B
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
      bitBound, Or.inr rfl, ?_, fun _ => ⟨rfl, (empty rfl).1, sameStream⟩, cursor, ?_, ?_⟩
    · unfold distLookup
      rw [runX_bind, run]
    · intro impossible
      cases impossible
    · intro impossible; cases impossible
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
        _, finalBound, kinds2, done, leave, subCursor, subMeaning, _short, subBad⟩ :=
        subLookup_credited_rejection current.here hc hs pointer tableGet classification before back backBound inv meaning stable
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
        shape.symbol.trans finalShape, ?_, kinds2, ?_, ?_, by rw [subCursor, cursor, inputAdvance_add], ?_, ?_⟩
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
      · intro success rejected
        obtain ⟨word, fit, sourceWord, invalid⟩ := subBad success rejected
        obtain ⟨heapEq, _⟩ := done success
        refine ⟨word, current.here.bits.toNat, entryBound, heapEq, fit, ?_, invalid⟩
        simpa only [List.drop_drop, Nat.add_comm] using sourceWord.trans sameStream
    · have notLink : ¬ DistLink current.here := by
        intro link
        have table := classification
        rw [ite_eq_left link] at table
        exact slow (distLink_slow table)
      rw [ite_eq_right notLink] at classification
      refine ⟨.ok (), current, used, h, ?_, by omega, usedBound, inv, shape.symbol,
        bitBound, Or.inl rfl, ?_, ?_, cursor, ?_, ?_⟩
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
      · intro normal rejected
        obtain ⟨word, fit, sourceWord, invalid⟩ := rootBad normal slow rejected
        refine ⟨word, 0, by omega, ?_, by simpa only [Nat.zero_add] using fit, sourceWord, invalid⟩
        have stateEq : {s with back := Int32.ofNat (before + 0)} = s := by rw [Nat.add_zero, ← back]
        rw [stateEq]
        simp only [setI, upd_self _ _ _ hs]

/-- The bits actually credited before the distance decision. -/
def credited (initial : IL) (bytes : List UInt8) (used : Nat) : List Bool :=
  natBits initial.bits.toNat initial.hold.toNat ++ bytesBits (bytes.take used)

/-- A query word with the actual unread suffix is exactly the credited prefix. -/
theorem credited_query_word {initial : IL} {bytes : List UInt8} {used : Nat} {word : List Bool}
    (source : word ++ bytesBits (bytes.drop used) = stream initial bytes) :
    word = credited initial bytes used := by
  have split : bytesBits bytes = bytesBits (bytes.take used) ++ bytesBits (bytes.drop used) := by
    rw [← bytesBits_append, List.take_append_drop]
  change word ++ bytesBits (bytes.drop used) = natBits initial.bits.toNat initial.hold.toNat ++ bytesBits bytes at source
  rw [split, ← List.append_assoc] at source
  exact List.append_cancel_right source

/-- Actual DROPBITS leaves exactly the undropped held suffix of the credited word. -/
theorem credited_drop_ledger {initial final : IL} {bytes : List UInt8} {used count : Nat} {word : List Bool}
    (source : word ++ bytesBits (bytes.drop used) = stream initial bytes)
    (fit : count ≤ word.length)
    (drop : stream final (bytes.drop used) = (stream initial bytes).drop count) :
    count ≤ (credited initial bytes used).length ∧
      credited initial bytes used = (credited initial bytes used).take count ++ natBits final.bits.toNat final.hold.toNat := by
  have wordEq := credited_query_word source
  rw [← source, List.drop_append_of_le_length fit] at drop
  change natBits final.bits.toNat final.hold.toNat ++ bytesBits (bytes.drop used) =
    word.drop count ++ bytesBits (bytes.drop used) at drop
  have held := List.append_cancel_right drop
  refine ⟨by rw [← wordEq]; exact fit, ?_⟩
  rw [← wordEq, held, List.take_append_drop]

theorem lookupBoundary_credited_rejection {c : Ctx} {l : IL} {h : Heap}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8} (before : Nat)
    (hc : c.st = some (.tab zs)) (good : Good h r zs z s)
    (tables : DataTablesSafe h s) (B : BitInv h l bs)
    (back : s.back = Int32.ofNat before) (backBound : before ≤ 20)
    {ref : CodeRef} {offset extent : Nat} {array : Array Code} {D : List Nat}
    (pointer : s.distcode = .ref ref offset) (tableGet : Space.get h ref = some array)
    (tableSafe : DistTableSafe array offset s.distbits.toNat)
    (meaning : Inv DISTS array offset s.distbits.toNat extent D)
    (stable : StableQuery DISTS array offset s.distbits.toNat) :
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
          decodeSym D (stream l bs) = some (symbol, (stream l bs).drop (dropped + regs.here.bits.toNat))) ∧
      (¬ LeafAccepted DISTS regs.here →
        ∃ word, dropped + regs.here.bits.toNat ≤ word.length ∧
          word ++ bytesBits (bs.drop used) = stream l bs ∧
          ∀ future : List Bool, ¬ ∃ symbol rest, decodeSym D (word ++ future) = some (symbol, rest) ∧ symbol ≤ 29)) := by
  obtain ⟨result, regs, used, after, run, usedFour, usedBound, inv, shape, bitBound, kinds, done, leave, cursor, semantic, semanticBad⟩ :=
    distLookup_credited_rejection hc good.live.hs pointer tableGet tableSafe before back backBound B meaning stable
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
      ?_, finalGood, finalTables, inv, leaf, enough, rfl, bits, shape, rfl, count, rfl, rfl, cursor, bitBound, ?_, ?_⟩
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

/- The actual DIST consumes its selected code before its real leaf
classifier. Accepted leaves derive a genuine independent current decode. -/
    · intro rejected
      obtain ⟨word, semanticDrop, semanticBound, semanticHeap, fit, sourceWord, invalid⟩ := semanticBad rfl rejected
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
      exact ⟨word, fit, sourceWord, invalid⟩

theorem DIST_rejected_finish_cut
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {ref : CodeRef} {offset extent : Nat} {ca : Array Code} {D : List Nat}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s) (B : BitInv h l bs)
    (before : Nat) (back : s.back = Int32.ofNat before) (backBound : before ≤ 20)
    (pointer : s.distcode = .ref ref offset) (tableGet : Space.get h ref = some ca)
    (safe : DistTableSafe ca offset s.distbits.toNat)
    (meaning : Inv DISTS ca offset s.distbits.toNat extent D)
    (stable : StableQuery DISTS ca offset s.distbits.toNat) :
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
        consumed = D.getD symbol 0 ∧ decodeSym D (stream l bs) = some (symbol, stream regs (bs.drop used))) ∧
      (¬ LeafAccepted DISTS entry →
        consumed ≤ (credited l bs used).length ∧
        credited l bs used = (credited l bs used).take consumed ++ natBits regs.bits.toNat regs.hold.toNat ∧
        ∀ future : List Bool, ¬ ∃ symbol rest, decodeSym D (credited l bs used ++ future) = some (symbol, rest) ∧ symbol ≤ 29)) := by
  rcases lookupBoundary_credited_rejection before E.st good tables B back backBound pointer tableGet safe meaning stable with wait | reached
  · obtain ⟨regs, used, four, bound, run, bits, empty, source, shape, cursor, _bitsBound⟩ := wait
    exact Or.inl ⟨regs, used, four, bound, run, bits, empty, source, shape, cursor⟩
  · obtain ⟨looked, heap, lookupState, used, dropped, four, bound, droppedBound, cut, current,
      currentTables, bits, leaf, enough, lookupBack, source, shape, frame, _count, heapEq,
      stateEq, cursor, _bitsBound, semantic, semanticBad⟩ := reached
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
      sourceFinal, ?_, leaf0, ?_, ?_⟩
    · rw [finalState]; simp only [Nat.add_assoc]
    · rw [finalState, stateEq]
    · rw [finalState, stateEq]
    · rw [finalHeap, heapEq, setI_setI]
    · intro accepted
      obtain ⟨symbol, valid, fields, width, decoded⟩ := semantic accepted
      exact ⟨symbol, valid, fields, width, by rwa [sourceFinal]⟩
    · intro rejected
      obtain ⟨word, fit, sourceWord, invalid⟩ := semanticBad rejected
      have ledger := credited_drop_ledger sourceWord fit sourceFinal
      have wordEq := credited_query_word sourceWord
      exact ⟨ledger.1, ledger.2, by rw [← wordEq]; exact invalid⟩

#print axioms held_query_rejected
#print axioms root_query_read
#print axioms lookup2_credited_rejection
#print axioms lookup1_credited_rejection
#print axioms subLookup_credited_rejection
#print axioms distLookup_credited_rejection
#print axioms credited_query_word
#print axioms credited_drop_ledger
#print axioms lookupBoundary_credited_rejection
#print axioms DIST_rejected_finish_cut
end Zlib.Inflate.Proofs.SlowCreditedDistance
