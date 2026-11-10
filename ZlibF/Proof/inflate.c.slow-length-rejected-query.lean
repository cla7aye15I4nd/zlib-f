import ZlibF.Proof.«inflate.c.slow-arbitrary-length»
import ZlibF.Proof.«inftrees.c.decode.stability-rejection»

namespace Zlib.Inflate.Proofs.SlowRejectedLength
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec
open Zlib.Inflate.Proofs Zlib.Inftrees Zlib.Inffast.Proofs Zlib.Inffast.Spec
open Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness
open Zlib.Inftrees.Spec.DecodeTableInvariant Zlib.Inftrees.Spec.DecodeTableStability
open SlowArbitraryLength SlowSubtablePath
set_option autoImplicit false

def credited (l : IL) (bs : List UInt8) (used : Nat) : List Bool :=
  natBits l.bits.toNat l.hold.toNat ++ bytesBits (bs.take used)

 theorem held_credit {l regs : IL} {bs : List UInt8} {used : Nat}
    (source : stream regs (bs.drop used) = stream l bs) :
    natBits regs.bits.toNat regs.hold.toNat = credited l bs used := by
  have split : bytesBits bs = bytesBits (bs.take used) ++ bytesBits (bs.drop used) := by
    rw [← bytesBits_append, List.take_append_drop]
  change natBits regs.bits.toNat regs.hold.toNat ++ bytesBits (bs.drop used) =
    natBits l.bits.toNat l.hold.toNat ++ bytesBits bs at source
  rw [split, ← List.append_assoc] at source
  exact List.append_cancel_right source

 theorem credit_compose {l regs : IL} {bs : List UInt8} {used more : Nat}
    (source : stream regs (bs.drop used) = stream l bs) :
    credited l bs (used + more) = credited regs (bs.drop used) more := by
  unfold credited
  rw [List.take_add, bytesBits_append, ← List.append_assoc]
  have held := held_credit source
  dsimp only [credited] at held
  rw [← held]

 theorem query_rejects_credit
    {type : UInt32} {ca : Array Code} {offset root extent : Nat} {alphabet : List Nat}
    {l regs : IL} {bs : List UInt8} {used consumed : Nat} {entry : Code}
    (meaning : Inv type ca offset root extent alphabet) (stable : StableQuery type ca offset root)
    (source : stream regs (bs.drop used) = stream l bs)
    (query : tableRead type ca offset root
      (Zlib.Inftrees.Spec.DecodeShort.padded (bitsOfNat regs.hold.toNat regs.bits.toNat)) = some (entry, consumed))
    (fits : consumed ≤ regs.bits.toNat) (rejected : ¬ LeafAccepted type entry) :
    ∀ future : List Bool, ¬ ∃ symbol rest,
      decodeSym alphabet (credited l bs used ++ future) = some (symbol, rest) ∧ ValidSymbol type symbol := by
  have invalid := Zlib.Inftrees.Proofs.short_rejected_leaf_stays_invalid type ca offset root extent alphabet
    meaning stable _ entry consumed query (by simpa only [bitsOfNat_length] using fits) rejected
  have word : bitsOfNat regs.hold.toNat regs.bits.toNat = credited l bs used := by
    rw [← held_credit source]
    simp only [natBits_testBit, bitsOfNat]
  rwa [word] at invalid

#print axioms held_credit
#print axioms credit_compose
#print axioms query_rejects_credit
end Zlib.Inflate.Proofs.SlowRejectedLength

namespace Zlib.Inflate.Proofs.SlowRejectedLength
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec
open Zlib.Inflate.Proofs Zlib.Inftrees Zlib.Inffast.Proofs Zlib.Inffast.Spec
open Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness
open Zlib.Inftrees.Spec.DecodeTableInvariant Zlib.Inftrees.Spec.DecodeTableStability
open SlowArbitraryLength SlowSubtablePath
set_option autoImplicit false
theorem lookup1_rejected_query
    {c : Ctx} {h : Heap} {zs : Nat} {s : InflateState}
    {ref : CodeRef} {offset usedExtent : Nat} {ca : Array Code} {alphabet : List Nat}
    {l : IL} {bs : List UInt8}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (pointer : s.lencode = .ref ref offset) (get : Space.get h ref = some ca)
    (meaning : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS ca offset s.lenbits.toNat usedExtent alphabet)
    (stable : StableQuery LENS ca offset s.lenbits.toNat) (B : BitInv h l bs) :
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
            some (symbol, (stream l bs).drop regs.here.bits.toNat)) ∧
      (result = .ok () → ¬ SlowLenLink regs.here → ¬ LeafAccepted LENS regs.here →
        ∀ future, ¬ ∃ symbol rest, decodeSym alphabet (credited l bs used ++ future) = some (symbol, rest) ∧ ValidSymbol LENS symbol) := by
  obtain ⟨result, regs, used, actual, two, bound, inv, source, shape, selected, cursor, width,
    fits, kinds, empty, count, bitBound, accepted⟩ := lookup1_actual_meaning hc hs pointer get meaning B
  refine ⟨result, regs, used, actual, two, bound, inv, source, shape, selected, cursor, width,
    fits, kinds, empty, count, bitBound, accepted, ?_⟩
  intro normal nonlink rejected
  obtain ⟨suffix, query⟩ := ZlibF.Math.InflateHeldBits.padded_query inv.hold_lt meaning.rootTable.2.1
  have inside : offset + regs.hold.toNat % 2 ^ s.lenbits.toNat < ca.size := by
    have root := meaning.rootTable.2.2.1
    have index := Nat.mod_lt regs.hold.toNat (Nat.two_pow_pos s.lenbits.toNat)
    omega
  have cell : ca[offset + regs.hold.toNat % 2 ^ s.lenbits.toNat]? = some regs.here := by
    rw [selected, codeLookupValue, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem inside, Option.getD_some]
  have mathRead : tableRead LENS ca offset s.lenbits.toNat
      (Zlib.Inftrees.Spec.DecodeShort.padded (bitsOfNat regs.hold.toNat regs.bits.toNat)) =
      some (regs.here, regs.here.bits.toNat) := by
    simp [tableRead, query, cell]
    intro nonzero high
    exact False.elim (nonlink ⟨nonzero, high⟩)
  exact query_rejects_credit meaning stable source mathRead (fits normal) rejected

#print axioms lookup1_rejected_query
end Zlib.Inflate.Proofs.SlowRejectedLength

namespace Zlib.Inflate.Proofs.SlowRejectedLength
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec
open Zlib.Inflate.Proofs Zlib.Inftrees Zlib.Inffast.Proofs Zlib.Inffast.Spec
open Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness
open Zlib.Inftrees.Spec.DecodeTableInvariant Zlib.Inftrees.Spec.DecodeTableStability
open SlowArbitraryLength SlowSubtablePath
set_option autoImplicit false
theorem lenSubLookup_rejected_query {c : Ctx} {h : Heap} {zs : Nat} {s : InflateState}
    {ref : CodeRef} {offset extent : Nat} {ca : Array Code} {alphabet : List Nat} {l : IL} {bs : List UInt8}
    (root : Code) (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (pointer : s.lencode = .ref ref offset) (tableGet : Space.get h ref = some ca)
    (link : LinkOK LenLeaf ca offset root) (back : s.back = 0) (B : BitInv h l bs)
    (meaning : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS ca offset s.lenbits.toNat extent alphabet)
    (stable : StableQuery LENS ca offset s.lenbits.toNat)
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
      (result = .error Ex.leave → regs.bits.toNat < root.bits.toNat + regs.here.bits.toNat) ∧
      (result = .ok () → ¬ LeafAccepted LENS regs.here →
        ∀ future, ¬ ∃ symbol rest, decodeSym alphabet (credited l bs used ++ future) = some (symbol, rest) ∧ ValidSymbol LENS symbol) := by
  let start := { l with last := root }
  have startInv : BitInv h start bs := ⟨B.have_eq, B.next, B.hold_lt⟩
  obtain ⟨result, current, used, run, usedTwo, usedBound, currentInv, sameStream, shape,
    lastRemembered, cursor, count, bitBound, selected, heldQuery, kinds, enough, empty, semantic⟩ :=
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
      symbolShape, lastEq, bitBound, Or.inr rfl, ?_, ?_, cursor, ?_, ?_, ?_⟩
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
    · intro impossible; cases impossible
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

    · intro _ rejected
      have sameSource : stream current (bs.drop used) = stream l bs := by
        simpa only [stream, start] using sameStream
      exact query_rejects_credit meaning stable sameSource heldQuery (enough rfl) rejected

#print axioms lenSubLookup_rejected_query
end Zlib.Inflate.Proofs.SlowRejectedLength

namespace Zlib.Inflate.Proofs.SlowRejectedLength
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec
open Zlib.Inflate.Proofs Zlib.Inftrees Zlib.Inffast.Proofs Zlib.Inffast.Spec
open Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness
open Zlib.Inftrees.Spec.DecodeTableInvariant Zlib.Inftrees.Spec.DecodeTableStability
open SlowArbitraryLength SlowSubtablePath
set_option autoImplicit false
theorem lenLookup_rejected_query {c : Ctx} {h : Heap} {zs : Nat} {s : InflateState}
    {ref : CodeRef} {offset extent : Nat} {ca : Array Code} {alphabet : List Nat} {l : IL} {bs : List UInt8}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (pointer : s.lencode = .ref ref offset) (tableGet : Space.get h ref = some ca)
    (safe : LenTableSafe ca offset s.lenbits.toNat) (back : s.back = 0) (B : BitInv h l bs)
    (meaning : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS ca offset s.lenbits.toNat extent alphabet)
    (stable : StableQuery LENS ca offset s.lenbits.toNat) :
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
            (stream l bs).drop (dropped + regs.here.bits.toNat))) ∧
      (result = .ok () → ¬ LeafAccepted LENS regs.here →
        ∀ future, ¬ ∃ symbol rest, decodeSym alphabet (credited l bs used ++ future) = some (symbol, rest) ∧ ValidSymbol LENS symbol) := by
  obtain ⟨first, current, used, run, usedTwo, usedBound, inv, sameStream, shape,
    selected, cursor, entryBound, enough, kinds, empty, count, bitBound, rootMeaning, rootRejected⟩ :=
    lookup1_rejected_query hc hs pointer tableGet meaning stable B
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
      bitBound, Or.inr rfl, ?_, fun _ => ⟨rfl, (empty rfl).1, sameStream⟩, cursor, ?_, ?_⟩
    · unfold lenLookup
      rw [runX_bind, run]
    · intro impossible
      cases impossible
    · intro impossible; cases impossible
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
        _, finalBound, kinds2, done, leave, subCursor, subMeaning, _short, subRejected⟩ :=
        lenSubLookup_rejected_query current.here hc hs pointer tableGet classification back inv meaning stable
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
        have invalid := subRejected success rejected
        rw [← credit_compose sameStream] at invalid
        exact invalid
    · have notLink : ¬ LenLink current.here := by
        intro link
        have table := classification
        rw [ite_eq_left link] at table
        exact slow (lenLink_slow link table)
      rw [ite_eq_right notLink] at classification
      refine ⟨.ok (), current, used, h, ?_, by omega, usedBound, inv, shape.symbol,
        bitBound, Or.inl rfl, ?_, ?_, cursor, ?_, ?_⟩
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

      · intro _ rejected
        exact rootRejected rfl slow rejected

#print axioms lenLookup_rejected_query
end Zlib.Inflate.Proofs.SlowRejectedLength

namespace Zlib.Inflate.Proofs.SlowRejectedLength
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec
open Zlib.Inflate.Proofs Zlib.Inftrees Zlib.Inffast.Proofs Zlib.Inffast.Spec
open Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness
open Zlib.Inftrees.Spec.DecodeTableInvariant Zlib.Inftrees.Spec.DecodeTableStability
open SlowArbitraryLength SlowSubtablePath
set_option autoImplicit false
theorem LEN_rejected_lookup_boundary {c : Ctx} {l : IL} {h : Heap}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8}
    {ref : CodeRef} {offset extent : Nat} {ca : Array Code} {alphabet : List Nat}
    (hc : c.st = some (.tab zs)) (good : Good h r zs z s)
    (tables : DataTablesSafe h s) (B : BitInv h l bs)
    (pointer : s.lencode = .ref ref offset) (tableGet : Space.get h ref = some ca)
    (safe : LenTableSafe ca offset s.lenbits.toNat)
    (meaning : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS ca offset s.lenbits.toNat extent alphabet)
    (stable : StableQuery LENS ca offset s.lenbits.toNat)
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
            (stream l bs).drop (dropped + regs.here.bits.toNat))) ∧
      (¬ LeafAccepted LENS regs.here → ∀ future, ¬ ∃ symbol rest,
        decodeSym alphabet (credited l bs used ++ future) = some (symbol, rest) ∧ ValidSymbol LENS symbol)) := by
  let reset := { s with back := 0 }
  let heap := setI h zs reset
  have resetGood : Good heap r zs z reset := good.decode_update rfl good.live.mode
  have resetTables : DataTablesSafe heap reset := tables.decode_update good.live.hs rfl
  have getReset : Space.get heap ref = some ca := by
    rw [decode_code_views good.live.hs (after := reset) rfl]
    exact tableGet
  obtain ⟨result, regs, used, after, run, usedFour, usedBound, inv, shape, bitBound, kinds, done, leave, cursor, semantic, rejected⟩ :=
    lenLookup_rejected_query hc resetGood.live.hs pointer getReset safe rfl (B.decode_update zs reset) meaning stable
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
      ?_, finalGood, finalTables, inv, leaf, enough, rfl, bits, shape, rfl, count, bitBound, by simp [heap], cursor, ?_, ?_⟩
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

    intro invalid
    exact rejected rfl invalid

#print axioms LEN_rejected_lookup_boundary
end Zlib.Inflate.Proofs.SlowRejectedLength


namespace Zlib.Inflate.Proofs.SlowRejectedLength
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec
open Zlib.Inflate.Proofs Zlib.Inftrees Zlib.Inffast.Proofs Zlib.Inffast.Spec
open Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness
open Zlib.Inftrees.Spec.DecodeTableInvariant Zlib.Inftrees.Spec.DecodeTableStability
open SlowArbitraryLength SlowSubtablePath
set_option autoImplicit false
theorem LEN_rejected_finish_cut
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {ref : CodeRef} {offset extent : Nat} {ca : Array Code} {L : List Nat}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s) (B : BitInv h l bs)
    (pointer : s.lencode = .ref ref offset) (tableGet : Space.get h ref = some ca)
    (safe : LenTableSafe ca offset s.lenbits.toNat)
    (meaning : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS ca offset s.lenbits.toNat extent L)
    (stable : StableQuery LENS ca offset s.lenbits.toNat)
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
        consumed = L.getD symbol 0 ∧ decodeSym L (stream l bs) = some (symbol, stream regs (bs.drop used))) ∧
      (¬ LeafAccepted LENS entry → ∀ future, ¬ ∃ symbol rest,
        decodeSym L (credited l bs used ++ future) = some (symbol, rest) ∧ ValidSymbol LENS symbol)) := by
  rcases LEN_rejected_lookup_boundary E.st good tables B pointer tableGet safe meaning stable slow with wait | reached
  · obtain ⟨regs, after, state, used, four, bound, run, current, currentTables, bits, empty,
      source, shape, frame, _bitsBound, cursor, heap, mode⟩ := wait
    exact Or.inl ⟨regs, after, state, used, four, bound, run, current, currentTables, bits,
      empty, source, shape, frame, cursor, heap, mode⟩
  · obtain ⟨looked, heap, lookupState, used, dropped, four, bound, droppedBound, cut, current,
      currentTables, bits, leaf, enough, back, source, shape, frame, _count, _bitsBound, heapEq, cursor, semantic, rejected⟩ := reached
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
      sourceFinal, ?_, leaf0, ?_, ?_⟩
    · rw [finalHeap, heapEq, setI_setI]
    · intro accepted
      obtain ⟨symbol, valid, fields, width, decoded⟩ := semantic accepted
      exact ⟨symbol, valid, fields, width, by rwa [sourceFinal]⟩

    · intro invalid
      exact rejected invalid

#print axioms LEN_rejected_finish_cut
end Zlib.Inflate.Proofs.SlowRejectedLength
