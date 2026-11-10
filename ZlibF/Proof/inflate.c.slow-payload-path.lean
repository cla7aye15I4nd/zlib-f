import ZlibF.Proof.«inftrees.c.decode.forward»
import ZlibF.Proof.«inftrees.c.decode.stability»
import ZlibF.Proof.«inflate.c.length-finish»
import ZlibF.Proof.«inflate.c.literal-step»
import ZlibF.Spec.InflateDecodeTableInvariant
import ZlibF.Math.InflateHeldBits
import ZlibF.Proof.Format.Token

namespace Zlib.Inflate.Proofs.SlowPayloadPath
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec
open Zlib.Inflate.Proofs Zlib.Inftrees
open Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness
open Zlib.Inffast.Proofs Zlib.Inffast.Spec
set_option autoImplicit false

/-- A literal table entry cannot stand for EOB or a length symbol. -/
theorem symbolEntry_literal {entry : Code} {symbol : Nat}
    (meaning : SymbolEntry LENS symbol entry) (ordinary : entry.op = 0) :
    symbol < 256 ∧ entry.val.toNat = symbol := by
  simp only [SymbolEntry, ↓reduceIte] at meaning
  split at meaning
  · exact ⟨by assumption, meaning.2⟩
  · split at meaning
    · have same := meaning.1
      rw [ordinary] at same
      cases same
    · split at meaning
      · have bound := meaning.1
        rw [ordinary] at bound
        change 0 = 16 + _ at bound
        omega
      · simp [ordinary] at meaning

/-- Every accepted actual non-link root leaf agrees with independent
symbol decoding, including EOB and length entries. -/
theorem lookup1_nonlink_meaning
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
  obtain ⟨result, regs, used, run, two, bound, inv, source, shape, _count,
    _bitBound, selected, _entryWidth, _kinds, enough, _empty, _cursor⟩ :=
    lookup1_data_readable_run_cursor false hc hs pointer get readable B
  change regs.here = codeLookupValue ca offset s.lenbits.toNat regs at selected
  refine ⟨result, regs, used, run, two, bound, inv, source, shape, selected, _cursor, _entryWidth, enough, ?_⟩
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
    exact enough normal
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

/-- The actual root lookup identifies an ordinary leaf with an independent
literal on the original source. Padding never supplies consumed bits. -/
theorem lookup1_literal_meaning
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
      (result = .ok () → regs.here.op = 0 →
        ∃ symbol, symbol < 256 ∧ regs.here.val.toNat = symbol ∧
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
  obtain ⟨result, regs, used, run, two, bound, inv, source, shape, _count,
    _bitBound, selected, _entryWidth, _kinds, enough, _empty, _cursor⟩ :=
    lookup1_data_readable_run_cursor false hc hs pointer get readable B
  change regs.here = codeLookupValue ca offset s.lenbits.toNat regs at selected
  refine ⟨result, regs, used, run, two, bound, inv, source, shape, selected, _cursor, _entryWidth, enough, ?_⟩
  intro normal ordinary
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
    simp [tableRead, query, cell, ordinary]
  have fitted : regs.here.bits.toNat ≤ (bitsOfNat regs.hold.toNat regs.bits.toNat).length := by
    rw [bitsOfNat_length]
    exact enough normal
  have accepted : LeafAccepted LENS regs.here := by simp [LeafAccepted, ordinary]
  obtain ⟨symbol, _valid, symbolMeaning, width, _decoded, continued⟩ :=
    meaning.short _ _ _ mathRead fitted accepted
  obtain ⟨literal, value⟩ := symbolEntry_literal symbolMeaning ordinary
  have extended := continued (bytesBits (bs.drop used))
  have streamEq : bitsOfNat regs.hold.toNat regs.bits.toNat ++ bytesBits (bs.drop used) =
      stream l bs := by
    simpa only [stream, natBits_testBit, bitsOfNat] using source
  have residual : (bitsOfNat regs.hold.toNat regs.bits.toNat).drop regs.here.bits.toNat ++
      bytesBits (bs.drop used) = (stream l bs).drop regs.here.bits.toNat := by
    rw [← streamEq, List.drop_append_of_le_length fitted]
  rw [streamEq, residual] at extended
  exact ⟨symbol, literal, value, width, extended⟩

/-- A real exhausted lookup retains the strict missing-bit inequality.
This exact source guard is needed to rule out input exhaustion from a
complete independent token; the existing safety projection omits it. -/
theorem lookupLoop_run_cursor_short {body : X Bool} {h : Heap} {l : IL} {bs : List UInt8}
    (query : IL → Code) (need : Code → UInt32)
    (stable : ∀ current, query { current with here := query current } = query current)
    (bound : ∀ current, (need (query current)).toNat ≤ 15)
    (bodyRun : ∀ current, LookupRegShape l current →
      runX body current h =
        if need (query current) ≤ current.bits then
          .ok ((.ok true, { current with here := query current }), h)
        else runX (do PULLBYTE; pure false : X Bool) { current with here := query current } h)
    (B : BitInv h l bs) :
    ∃ result regs used,
      runX (xloopBrk body) l h = .ok ((result, regs), h) ∧
      used ≤ 2 ∧ used ≤ bs.length ∧ BitInv h regs (bs.drop used) ∧
      stream regs (bs.drop used) = stream l bs ∧ LookupRegShape l regs ∧
      regs.bits.toNat = l.bits.toNat + 8 * used ∧
      regs.bits.toNat ≤ max l.bits.toNat 22 ∧
      regs.here = query regs ∧ (need regs.here).toNat ≤ 15 ∧
      (result = .ok () ∨ result = .error Ex.leave) ∧
      (result = .ok () → (need regs.here).toNat ≤ regs.bits.toNat) ∧
      (result = .error Ex.leave → regs.have_ = 0 ∧ regs.bits.toNat < (need regs.here).toNat) ∧ regs.next = inputAdvance l.next used := by
  let P : IL → Heap → Prop := fun regs heap =>
    heap = h ∧ ∃ used, used ≤ bs.length ∧ BitInv h regs (bs.drop used) ∧
      stream regs (bs.drop used) = stream l bs ∧ LookupRegShape l regs ∧
      regs.bits.toNat = l.bits.toNat + 8 * used ∧ regs.bits.toNat ≤ max l.bits.toNat 22 ∧
      regs.next = inputAdvance l.next used
  let Q : Except Ex Unit → IL → Heap → Prop := fun result regs heap =>
    P regs heap ∧ regs.here = query regs ∧
      (need regs.here).toNat ≤ 15 ∧ (result = .ok () ∨ result = .error Ex.leave) ∧
      (result = .ok () → (need regs.here).toNat ≤ regs.bits.toNat) ∧
      (result = .error Ex.leave → regs.have_ = 0 ∧ regs.bits.toNat < (need regs.here).toNat)
  have step : ∀ current heap, P current heap → ∃ test regs heap1,
      runX (pure true : X Bool) current heap = .ok ((test, regs), heap1) ∧
      (match test with
       | .error fault => Q (.error fault) regs heap1
       | .ok false => Q (.ok ()) regs heap1
       | .ok true => ∃ result final heap2,
           runX body regs heap1 = .ok ((result, final), heap2) ∧
           (match result with
            | .error fault => Q (.error fault) final heap2
            | .ok true => Q (.ok ()) final heap2
            | .ok false => P final heap2 ∧ 15 - final.bits.toNat < 15 - current.bits.toNat)) := by
    rintro current heap ⟨heapEq, used, usedBound, inv, sameStream, shape, count, bitBound, cursor⟩
    subst heap
    refine ⟨.ok true, current, h, rfl, ?_⟩
    let entry := query current
    let read := { current with here := entry }
    have entryBound : (need entry).toNat ≤ 15 := bound current
    have readInv : BitInv h read (bs.drop used) := ⟨inv.have_eq, inv.next, inv.hold_lt⟩
    have readShape : LookupRegShape l read := shape.trans (by rfl)
    have actual := bodyRun current shape
    change runX body current h =
      if need entry ≤ current.bits then .ok ((.ok true, read), h)
      else runX (do PULLBYTE; pure false : X Bool) read h at actual
    by_cases fits : need entry ≤ current.bits
    · rw [ite_eq_left fits] at actual
      refine ⟨.ok true, read, h, actual, ⟨rfl, used, usedBound, readInv, sameStream, readShape, count, bitBound, cursor⟩,
        (stable current).symm, entryBound, Or.inl rfl, ?_, ?_⟩
      · intro _
        have bound := UInt32.le_iff_toNat_le.mp fits
        exact bound
      · intro impossible
        cases impossible
    · rw [ite_eq_right fits] at actual
      have short : current.bits.toNat < (need entry).toNat := by
        have := (not_congr UInt32.le_iff_toNat_le).mp fits
        omega
      cases remaining : bs.drop used with
      | nil =>
        have empty : read.have_ = 0 := by
          apply UInt32.toNat_inj.mp
          have len := inv.have_eq
          rw [remaining] at len
          exact len
        rw [runX_bind, PULLBYTE_zero empty] at actual
        refine ⟨.error Ex.leave, read, h, actual,
          ⟨rfl, used, usedBound, readInv, sameStream, readShape, count, bitBound, cursor⟩,
          (stable current).symm, entryBound, Or.inr rfl, ?_, fun _ => ⟨empty, short⟩⟩
        intro impossible
        cases impossible
      | cons byte rest =>
        have readCons : BitInv h read (byte :: rest) := by rwa [remaining] at readInv
        obtain ⟨next, pull, nextInv, nextStream, nextBits, nextCursor⟩ := PULLBYTE_succ_cursor readCons
          (by change current.bits.toNat ≤ 56; omega)
        let final := pulled read byte next
        have restEq : bs.drop (used + 1) = rest := by
          have eq : (bs.drop used).drop 1 = rest := by rw [remaining]; rfl
          simpa only [List.drop_drop, Nat.add_comm] using eq
        have usedNext : used + 1 ≤ bs.length := by
          have len := congrArg List.length remaining
          simp only [List.length_drop, List.length_cons] at len
          omega
        have finalInv : BitInv h final (bs.drop (used + 1)) := by rwa [restEq]
        have finalStream : stream final (bs.drop (used + 1)) = stream l bs := by
          rw [restEq, nextStream, ← remaining]
          exact sameStream
        have finalCount : final.bits.toNat = l.bits.toNat + 8 * (used + 1) := by
          rw [nextBits]
          change current.bits.toNat + 8 = _
          rw [count, Nat.mul_add]
          omega
        have finalBound : final.bits.toNat ≤ max l.bits.toNat 22 := by
          rw [nextBits]
          change current.bits.toNat + 8 ≤ _
          omega
        rw [runX_bind, pull] at actual
        simp only [runX_pure] at actual
        refine ⟨.ok false, final, h, actual,
          ⟨rfl, used + 1, usedNext, finalInv, finalStream, readShape.trans (by rfl), finalCount, finalBound, ?_⟩, ?_⟩
        · change next = inputAdvance l.next (used + 1)
          rw [nextCursor]
          change inputAdvance current.next 1 = _
          rw [cursor, inputAdvance_add]
        · rw [nextBits]
          change 15 - (current.bits.toNat + 8) < 15 - current.bits.toNat
          omega
  have initial : P l h := ⟨rfl, 0, by omega, by simpa using B, rfl, LookupRegShape.refl l, by simp, by omega, (inputAdvance_zero l.next).symm⟩
  have fuelBound : 17 < fuel := by decide
  obtain ⟨result, regs, after, run, post, selected, entryBits, kinds, enough, empty⟩ :=
    xwhileBrk_rank P (fun regs _ => 15 - regs.bits.toNat) Q step initial (by change 15 - l.bits.toNat + 2 < fuel; omega)
  obtain ⟨heapEq, used, usedBound, inv, sameStream, shape, count, bitBound, cursor⟩ := post
  subst after
  have atMostTwo : used ≤ 2 := by omega
  exact ⟨result, regs, used, run, atMostTwo, usedBound, inv, sameStream, shape, count, bitBound,
    selected, entryBits, kinds, enough, empty, cursor⟩

/-- A complete independent literal forces every real non-link root
lookup to return normally and select that literal. Constructor-proved
query stability covers even a provisional rejected zero-padded query. -/
theorem lookup1_token_nonlink
    {c : Ctx} {h : Heap} {zs : Nat} {s : InflateState}
    {ref : CodeRef} {offset usedExtent : Nat} {ca : Array Code} {alphabet : List Nat}
    {l : IL} {bs : List UInt8} {symbol : Nat} {rest : List Bool}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (pointer : s.lencode = .ref ref offset) (get : Space.get h ref = some ca)
    (meaning : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS ca offset s.lenbits.toNat usedExtent alphabet)
    (stable : Zlib.Inftrees.Spec.DecodeTableStability.StableQuery LENS ca offset s.lenbits.toNat)
    (B : BitInv h l bs)
    (decoded : decodeSym alphabet (stream l bs) = some (symbol, rest)) (small : symbol < 256) :
    ∃ result regs used,
      runX (lookup1 c false) l h = .ok ((result, regs), h) ∧
      used ≤ 2 ∧ used ≤ bs.length ∧ BitInv h regs (bs.drop used) ∧
      stream regs (bs.drop used) = stream l bs ∧ LookupRegShape l regs ∧
      regs.next = inputAdvance l.next used ∧
      (¬ SlowLenLink regs.here → result = .ok () ∧ regs.here.op = 0 ∧
        regs.here.val.toNat = symbol ∧ regs.here.bits.toNat = alphabet.getD symbol 0 ∧
        rest = (stream l bs).drop regs.here.bits.toNat) := by
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
      (by simp only [ValidSymbol, ite_true]; omega)
  obtain ⟨result, regs, used, run, two, bound, inv, source, shape, count,
    bitBound, selected, entryBound, kinds, enough, exhausted, cursor⟩ :=
    lookupLoop_run_cursor_short (query := codeLookupValue ca offset s.lenbits.toNat)
      (need := fun entry => entry.bits.toUInt32) (fun _ => rfl)
      (by intro current; rw [UInt8.toNat_toUInt32]; exact readable.2.2 _ (Nat.mod_lt _ (Nat.two_pow_pos _)))
      (by intro current _; exact dataLookupBody_run false current hc hs pointer get readable) B
  have actual : runX (lookup1 c false) l h = .ok ((result, regs), h) := by
    rw [lookup1_data_eq]
    exact run
  refine ⟨result, regs, used, actual, two, bound, inv, source, shape, cursor, ?_⟩
  intro nonlink
  obtain ⟨suffix, query⟩ := ZlibF.Math.InflateHeldBits.padded_query inv.hold_lt meaning.rootTable.2.1
  have inside : offset + regs.hold.toNat % 2 ^ s.lenbits.toNat < ca.size := by
    have extent := meaning.rootTable.2.2.1
    have index := Nat.mod_lt regs.hold.toNat (Nat.two_pow_pos s.lenbits.toNat)
    omega
  have cell : ca[offset + regs.hold.toNat % 2 ^ s.lenbits.toNat]? = some regs.here := by
    rw [selected, codeLookupValue, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem inside, Option.getD_some]
  have heldQuery : tableRead LENS ca offset s.lenbits.toNat
      (Zlib.Inftrees.Spec.DecodeShort.padded (bitsOfNat regs.hold.toNat regs.bits.toNat)) =
      some (regs.here, regs.here.bits.toNat) := by
    simp [tableRead, query, cell]
    intro nonzero high
    exact False.elim (nonlink ⟨nonzero, high⟩)
  have normal : result = .ok () := by
    rcases kinds with normal | leave
    · exact normal
    · obtain ⟨empty, short⟩ := exhausted leave
      have noBytes : bs.drop used = [] := List.length_eq_zero_iff.mp
        (inv.have_eq.symm.trans (by rw [empty]; rfl))
      have sourceEq : bitsOfNat regs.hold.toNat regs.bits.toNat = stream l bs := by
        simpa only [noBytes, stream, bytesBits, List.flatMap_nil, List.append_nil, natBits_testBit, bitsOfNat] using source
      have fullQuery : tableRead LENS ca offset s.lenbits.toNat
          (Zlib.Inftrees.Spec.DecodeShort.padded (stream l bs)) =
          some (regs.here, regs.here.bits.toNat) := by
        simpa only [sourceEq] using heldQuery
      have same := Prod.mk.inj (Option.some.inj (fullQuery.symm.trans forward))
      have fits : regs.here.bits.toNat ≤ regs.bits.toNat := by
        have sizeEq : (stream l bs).length = regs.bits.toNat := by rw [← sourceEq, bitsOfNat_length]
        omega
      rw [UInt8.toNat_toUInt32] at short
      omega
  have fullQuery := stable _ _ _ heldQuery
    (by rw [bitsOfNat_length]; simpa only [UInt8.toNat_toUInt32] using enough normal)
    (bytesBits (bs.drop used))
  have sourceEq : bitsOfNat regs.hold.toNat regs.bits.toNat ++ bytesBits (bs.drop used) = stream l bs := by
    simpa only [stream, natBits_testBit, bitsOfNat] using source
  rw [sourceEq] at fullQuery
  obtain ⟨entries, widths⟩ := Prod.mk.inj (Option.some.inj (fullQuery.symm.trans forward))
  have literal : regs.here.op = 0 ∧ regs.here.val.toNat = symbol := by
    rw [← entries] at symbolMeaning
    simpa only [SymbolEntry, ↓reduceIte, small] using symbolMeaning
  exact ⟨normal, literal.1, literal.2, widths.trans width, by rwa [← widths] at restEq⟩

/-- The ordinary root-leaf branch of actual slow LEN establishes LIT and
its exact independent symbol/bit suffix. The lookup is produced here; its
normal/literal guard is an explicit source branch, never an assumed run. -/
theorem slow_LEN_literal_branch
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {ref : CodeRef} {offset usedExtent : Nat} {ca : Array Code} {alphabet : List Nat}
    {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (pointer : s.lencode = .ref ref offset) (get : Space.get h ref = some ca)
    (meaning : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS ca offset s.lenbits.toNat usedExtent alphabet)
    (B : BitInv h l bs)
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    ∃ result looked used,
      runX (lookup1 c false) l (setI h zs {s with back := 0}) =
        .ok ((result, looked), setI h zs {s with back := 0}) ∧
      used ≤ 2 ∧ used ≤ bs.length ∧
      (result = .ok () → looked.here.op = 0 →
        ∃ regs after state symbol,
          runX (inflate_LEN c) l h = .ok ((.ok (), regs), after) ∧
          Good after r zs z state ∧ DataTablesSafe after state ∧
          BitInv after regs (bs.drop used) ∧ state.mode = LIT ∧
          state.length.toNat = symbol ∧ symbol < 256 ∧ looked.here.val.toNat = symbol ∧
          decodeSym alphabet (stream l bs) = some (symbol, stream regs (bs.drop used)) ∧
          stream regs (bs.drop used) = (stream l bs).drop looked.here.bits.toNat ∧
          after = setI h zs state ∧
          regs.next = inputAdvance l.next used ∧ regs.put = l.put ∧ regs.left = l.left) := by
  let reset := {s with back := (0 : Int32)}
  let h0 := setI h zs reset
  have good0 : Good h0 r zs z reset := good.decode_update rfl good.live.mode
  have table0 : DataTablesSafe h0 reset := tables.decode_update good.live.hs rfl
  have get0 : Space.get h0 ref = some ca := by
    rw [decode_code_views good.live.hs (after := reset) rfl]; exact get
  obtain ⟨result, looked, used, lookup, two, bound, B0, source, shape, selected, lookupCursor,
    entryBound, enough, semantic⟩ :=
    lookup1_literal_meaning E.st good0.live.hs pointer get0 meaning (B.decode_update zs reset)
  refine ⟨result, looked, used, lookup, two, bound, ?_⟩
  intro normal ordinary
  obtain ⟨symbol, small, value, width, decoded⟩ := semantic normal ordinary
  have leaf : LenLeaf 0 looked.here := ⟨by omega, Or.inl ordinary⟩
  obtain ⟨regs, after, state, finish, good1, tables1, B1, frame, regshape,
    length, back, suffix, bitcount, here, heap, next⟩ :=
    lenFinish_consume_cursor 0 E.st good0 table0 leaf (by rfl) (enough normal) B0
  let final := {state with mode := LIT}
  let h1 := setI after zs final
  have env1 : Env c after r zs z state := ⟨E.strm, E.st, good1.live.hz, good1.live.hs⟩
  have tail : runX (lenLeafTail c looked.here) regs after = .ok ((.ok (), regs), h1) := by
    unfold lenLeafTail
    simp only [ordinary, UInt8.toNat_zero, beq_self_eq_true, ite_true,
      runX_bind, runX_setMode env1, runX_pure]
    rfl
  have literalLookup : runX (lenLookup c) l h0 = .ok ((.ok (), looked), h0) := by
    unfold lenLookup
    rw [runX_bind, lookup, normal]
    simp only [runX_bind, runX_get]
    rw [lenRootTail_leaf c looked.here (by simp [SlowLenLink, ordinary])]
    rfl
  have actual : runX (inflate_LEN c) l h = .ok ((.ok (), regs), h1) := by
    rw [inflate_LEN_slow_cut slow, lenSlow_split]
    rw [runX_bind, runX_wrS E]
    change runX (do lenLookup c; lenFinish c) l h0 = _
    rw [runX_bind, literalLookup]
    exact finish.trans tail
  have valueSmall := UInt16.toNat_lt looked.here.val
  have lengthNat : final.length.toNat = symbol := by
    change state.length.toNat = symbol
    rw [length, UInt16.toNat_toUInt32, value]
  have afterSource : stream regs (bs.drop used) = (stream l bs).drop looked.here.bits.toNat := by
    rw [suffix, source]
  have putShape : regs.put = l.put := by
    rw [regshape, shape]
  have leftShape : regs.left = l.left := by
    rw [regshape, shape]
  refine ⟨regs, h1, final, symbol, actual,
    good1.decode_update rfl (by change HEAD ≤ LIT ∧ LIT ≤ SYNC; decide),
    tables1.decode_update good1.live.hs rfl, B1.decode_update zs final,
    rfl, lengthNat, small, value, ?_, afterSource, ?_, next.trans lookupCursor, putShape, leftShape⟩
  · rw [afterSource]
    exact decoded
  · dsimp only [h1]
    rw [heap]
    dsimp only [h0]
    rw [setI_setI, setI_setI]

/-- A pending literal is emitted through the actual generic byte-view
write. Public Separate permits one allocation with disjoint intervals.
The emitted byte is the same independent Symbols token, and the unread
source survives the write. -/
theorem literal_emit_semantics
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {dest : BRef} {off : Nat} {array : Array UInt8}
    {L D : List Nat} {dict history : List UInt8} {input : List Bool} {symbol : Nat}
    (E : Env c h r zs z s) (B : BitInv h l bs)
    (left : l.left ≠ 0) (put : l.put = .ref dest off)
    (get : Space.get h dest = some array) (write : Space.ro h dest = false)
    (fit : off < array.size)
    (separate : ZlibF.Spec.Public.Separate l.next l.have_.toNat l.put l.left.toNat)
    (length : s.length.toNat = symbol) (small : symbol < 256)
    (decoded : decodeSym L input = some (symbol, stream l bs)) :
    let regs := {l with put := .ref dest (off + 1), left := l.left - 1}
    let after := setI (Space.put h dest (array.set! off symbol.toUInt8)) zs {s with mode := LEN}
    runX (inflate_LIT c) l h = .ok ((.ok (), regs), after) ∧
      BitInv after regs bs ∧ stream regs bs = stream l bs ∧
      ZlibF.Spec.Public.Bytes after l.put 1 [symbol.toUInt8] ∧
      Token.Step L D dict history input (stream regs bs) (history ++ [symbol.toUInt8]) false ∧
      (∀ tail output, Symbols L D dict (history ++ [symbol.toUInt8]) (stream regs bs) tail output →
        Symbols L D dict history input tail output) := by
  dsimp only
  have byte : s.length.toUInt8 = symbol.toUInt8 := by
    rw [← length]
    rfl
  have run := inflate_LIT_view_run E left put get write fit
  rw [byte] at run
  have positions : bs = [] ∨ ∀ i, l.next = .ref dest i → i + bs.length ≤ off ∨ off + 1 ≤ i := by
    rcases B.output_positions put left separate with empty | positions
    · exact Or.inl empty
    · right
      intro i pointer
      rcases positions i pointer with before | later
      · exact Or.inl before
      · have positive : 0 < l.left.toNat := by
          have nonzero : l.left.toNat ≠ 0 := by
            intro zero
            exact left (UInt32.toNat_inj.mp zero)
          omega
        exact Or.inr (by omega)
  have inv := (B.store_byte get write symbol.toUInt8 positions).decode_update zs {s with mode := LEN}
  have bits : BitInv
      (setI (Space.put h dest (array.set! off symbol.toUInt8)) zs {s with mode := LEN})
      {l with put := .ref dest (off + 1), left := l.left - 1} bs :=
    ⟨inv.have_eq, inv.next, inv.hold_lt⟩
  have outputGet : Space.get
      (setI (Space.put h dest (array.set! off symbol.toUInt8)) zs {s with mode := LEN}) dest =
      some (array.set! off symbol.toUInt8) := by
    rw [byte_view_get_setI]
    exact byte_view_get_put get write _
  have slice : ((array.set! off symbol.toUInt8).toList.drop off).take 1 = [symbol.toUInt8] := by
    rw [take_succ_drop (array.set! off symbol.toUInt8) off 0 (by simp; omega)]
    simp
  have observed : ZlibF.Spec.Public.Bytes
      (setI (Space.put h dest (array.set! off symbol.toUInt8)) zs {s with mode := LEN})
      l.put 1 [symbol.toUInt8] :=
    Or.inr ⟨dest, off, array.set! off symbol.toUInt8, put, outputGet, by simp; omega, slice.symm⟩
  have token : Token.Step L D dict history input (stream l bs) (history ++ [symbol.toUInt8]) false :=
    Token.Step.literal decoded small
  exact ⟨run, bits, rfl, observed, token,
    fun tail output continuation =>
      (Token.step_composes_symbols L D dict history input (stream l bs)
        (history ++ [symbol.toUInt8]) false token).2 rfl tail output continuation⟩

/-- Compositional actual LEN then LIT execution for its ordinary root
branch. The same selected literal is read from the independent bitstream
and written to the caller byte view; no caller run is an assumption. -/
theorem slow_literal_token_output
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {ref : CodeRef} {offset usedExtent : Nat} {ca : Array Code} {alphabet D : List Nat}
    {l : IL} {bs dict history : List UInt8} {dest : BRef} {off : Nat} {array : Array UInt8}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (pointer : s.lencode = .ref ref offset) (get : Space.get h ref = some ca)
    (meaning : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS ca offset s.lenbits.toNat usedExtent alphabet)
    (B : BitInv h l bs)
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true)
    (left : l.left ≠ 0) (put : l.put = .ref dest off)
    (outputGet : Space.get h dest = some array) (write : Space.ro h dest = false)
    (fit : off < array.size)
    (separate : ZlibF.Spec.Public.Separate l.next l.have_.toNat l.put l.left.toNat) :
    ∃ result looked used,
      runX (lookup1 c false) l (setI h zs {s with back := 0}) =
        .ok ((result, looked), setI h zs {s with back := 0}) ∧
      used ≤ 2 ∧ used ≤ bs.length ∧
      (result = .ok () → looked.here.op = 0 →
        ∃ regs after symbol,
          runX (do inflate_LEN c; inflate_LIT c) l h = .ok ((.ok (), regs), after) ∧
          BitInv after regs (bs.drop used) ∧
          decodeSym alphabet (stream l bs) = some (symbol, stream regs (bs.drop used)) ∧
          ZlibF.Spec.Public.Bytes after l.put 1 [symbol.toUInt8] ∧ symbol < 256 ∧
          looked.here.val.toNat = symbol ∧
          Token.Step alphabet D dict history (stream l bs) (stream regs (bs.drop used))
            (history ++ [symbol.toUInt8]) false ∧
          (∀ tail output, Symbols alphabet D dict (history ++ [symbol.toUInt8])
            (stream regs (bs.drop used)) tail output →
            Symbols alphabet D dict history (stream l bs) tail output)) := by
  obtain ⟨result, looked, used, lookup, two, bound, branch⟩ :=
    slow_LEN_literal_branch E good tables pointer get meaning B slow
  refine ⟨result, looked, used, lookup, two, bound, ?_⟩
  intro normal ordinary
  obtain ⟨middle, heap, state, symbol, lenRun, current, currentTables, currentBits,
    mode, length, small, value, decoded, suffix, heapEq, cursor, putEq, leftEq⟩ := branch normal ordinary
  have env : Env c heap r zs z state := ⟨E.strm, E.st, current.live.hz, current.live.hs⟩
  have currentGet : Space.get heap dest = some array := by
    rw [heapEq, byte_view_get_setI]; exact outputGet
  have currentWrite : Space.ro heap dest = false := by
    rw [heapEq, byte_view_ro_setI]; exact write
  have currentLeft : middle.left ≠ 0 := by rw [leftEq]; exact left
  have currentPut : middle.put = .ref dest off := putEq.trans put
  have currentSeparate : ZlibF.Spec.Public.Separate middle.next middle.have_.toNat middle.put middle.left.toNat := by
    have advanced := inputAdvance_separate l.next l.put l.have_.toNat l.left.toNat used
      (by rw [B.have_eq]; exact bound) separate
    rw [cursor, putEq, leftEq]
    have count : middle.have_.toNat = l.have_.toNat - used := by
      rw [currentBits.have_eq, B.have_eq, List.length_drop]
    rw [count]
    exact advanced
  obtain ⟨litRun, finalBits, finalStream, bytes, token, continuation⟩ :=
    literal_emit_semantics (L := alphabet) (D := D) (dict := dict) (history := history)
      env currentBits currentLeft currentPut currentGet currentWrite fit currentSeparate length small decoded
  let regs := {middle with put := .ref dest (off + 1), left := middle.left - 1}
  let after := setI (Space.put heap dest (array.set! off symbol.toUInt8)) zs {state with mode := LEN}
  refine ⟨regs, after, symbol, ?_, finalBits, ?_, ?_, small, value, token, continuation⟩
  · rw [runX_bind, lenRun]
    exact litRun
  · rw [finalStream]
    exact decoded
  · rw [← putEq]
    exact bytes

/-- An independent literal drives the actual slow LEN/LIT execution on
the non-link root path. Both the normal-return and literal-entry guards
are proved here. No lookahead lower bound or desired run is a premise. -/
theorem slow_literal_from_token_output
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {ref : CodeRef} {offset usedExtent : Nat} {ca : Array Code} {alphabet D : List Nat}
    {l : IL} {bs dict history : List UInt8} {dest : BRef} {off : Nat} {array : Array UInt8}
    {symbol : Nat} {rest : List Bool}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (pointer : s.lencode = .ref ref offset) (get : Space.get h ref = some ca)
    (meaning : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS ca offset s.lenbits.toNat usedExtent alphabet)
    (stable : Zlib.Inftrees.Spec.DecodeTableStability.StableQuery LENS ca offset s.lenbits.toNat)
    (B : BitInv h l bs)
    (decoded : decodeSym alphabet (stream l bs) = some (symbol, rest)) (small : symbol < 256)
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true)
    (left : l.left ≠ 0) (put : l.put = .ref dest off)
    (outputGet : Space.get h dest = some array) (write : Space.ro h dest = false)
    (fit : off < array.size)
    (separate : ZlibF.Spec.Public.Separate l.next l.have_.toNat l.put l.left.toNat) :
    ∃ result looked used,
      runX (lookup1 c false) l (setI h zs {s with back := 0}) =
        .ok ((result, looked), setI h zs {s with back := 0}) ∧
      used ≤ 2 ∧ used ≤ bs.length ∧
      (¬ SlowLenLink looked.here →
        ∃ regs after,
          runX (do inflate_LEN c; inflate_LIT c) l h = .ok ((.ok (), regs), after) ∧
          BitInv after regs (bs.drop used) ∧ stream regs (bs.drop used) = rest ∧
          ZlibF.Spec.Public.Bytes after l.put 1 [symbol.toUInt8] ∧
          Token.Step alphabet D dict history (stream l bs) rest
            (history ++ [symbol.toUInt8]) false ∧
          (∀ tail output, Symbols alphabet D dict (history ++ [symbol.toUInt8]) rest tail output →
            Symbols alphabet D dict history (stream l bs) tail output)) := by
  obtain ⟨result, looked, used, lookup, two, bound, branch⟩ :=
    slow_literal_token_output (D := D) (dict := dict) (history := history)
      E good tables pointer get meaning B slow left put outputGet write fit separate
  let reset := {s with back := (0 : Int32)}
  have current : Good (setI h zs reset) r zs z reset := good.decode_update rfl good.live.mode
  have currentGet : Space.get (setI h zs reset) ref = some ca := by
    rw [decode_code_views good.live.hs (after := reset) rfl]; exact get
  obtain ⟨otherResult, otherLooked, otherUsed, otherRun, _, _, _, _, _, _, tokenBranch⟩ :=
    lookup1_token_nonlink E.st current.live.hs pointer currentGet meaning stable
      (B.decode_update zs reset) decoded small
  have same := Prod.mk.inj (Prod.mk.inj (Except.ok.inj (lookup.symm.trans otherRun))).1
  obtain ⟨rfl, rfl⟩ := same
  refine ⟨result, looked, used, lookup, two, bound, ?_⟩
  intro nonlink
  obtain ⟨normal, ordinary, expectedValue, _, _⟩ := tokenBranch nonlink
  obtain ⟨regs, after, emitted, actual, bits, selectedDecode, bytes, _, actualValue, token, continuation⟩ :=
    branch normal ordinary
  have symbolEq : emitted = symbol := actualValue.symm.trans expectedValue
  rw [symbolEq] at bytes token continuation selectedDecode
  have restEq : stream regs (bs.drop used) = rest :=
    (Prod.mk.inj (Option.some.inj (selectedDecode.symm.trans decoded))).2
  refine ⟨regs, after, actual, bits, restEq, bytes, ?_, ?_⟩
  · rwa [restEq] at token
  · rwa [restEq] at continuation

#print axioms symbolEntry_literal
#print axioms lookup1_literal_meaning
#print axioms lookup1_nonlink_meaning
#print axioms lookupLoop_run_cursor_short
#print axioms lookup1_token_nonlink
#print axioms slow_LEN_literal_branch
#print axioms literal_emit_semantics
#print axioms slow_literal_token_output
#print axioms slow_literal_from_token_output
end Zlib.Inflate.Proofs.SlowPayloadPath
