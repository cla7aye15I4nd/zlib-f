import ZlibF.Proof.«inflate.c.code-length-classified»
import ZlibF.Proof.«inflate.c.code-length-body-prefix»
import ZlibF.Math.InflateHeldBits

namespace Zlib.Inflate.Proofs.CodeLensCompletion
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec
open Zlib.Inflate.Proofs Zlib.Inffast.Proofs
set_option autoImplicit false

/-- A single actual lookup trip returns its selected entry immediately. -/
theorem loop_stop {body : X Bool} {l l' : IL} {h : Heap}
    (run : runX body l h = .ok ((.ok true, l'), h)) :
    runX (xloopBrk body) l h = .ok ((.ok (), l'), h) := by
  have rule := xwhileBrk_run (cond := pure true) (body := body)
    (fun k current heap => k = 1 ∧ current = l ∧ heap = h)
    (fun result current heap => result = .ok () ∧ current = l' ∧ heap = h)
    (by
      intro k current heap inv
      obtain ⟨count, currentEq, heapEq⟩ := inv
      subst current heap
      exact ⟨l, h, rfl, .ok true, l', h, run, rfl, rfl, rfl⟩)
    (by intro current heap inv; have := inv.1 <;> omega)
    (k := 1) ⟨rfl, rfl, rfl⟩ (by decide)
  obtain ⟨result, current, heap, actual, rfl, rfl, rfl⟩ := rule
  exact actual

/-- One actual pull followed by the next selected entry is the whole lookup. -/
theorem loop_pull_stop {body : X Bool} {l middle final : IL} {h : Heap}
    (first : runX body l h = .ok ((.ok false, middle), h))
    (second : runX body middle h = .ok ((.ok true, final), h)) :
    runX (xloopBrk body) l h = .ok ((.ok (), final), h) := by
  have rule := xwhileBrk_run (cond := pure true) (body := body)
    (fun k current heap => heap = h ∧ ((k = 2 ∧ current = l) ∨ (k = 1 ∧ current = middle)))
    (fun result current heap => result = .ok () ∧ current = final ∧ heap = h)
    (by
      intro k current heap inv
      obtain ⟨heapEq, two | one⟩ := inv
      · subst heap
        obtain ⟨count, currentEq⟩ := two
        subst current
        have zero : k = 1 := by omega
        subst k
        exact ⟨l, h, rfl, .ok false, middle, h, first, rfl, Or.inr ⟨rfl, rfl⟩⟩
      · subst heap
        obtain ⟨count, currentEq⟩ := one
        subst current
        exact ⟨middle, h, rfl, .ok true, final, h, second, rfl, rfl, rfl⟩)
    (by intro current heap inv; rcases inv.2 with inv | inv <;> have := inv.1 <;> omega)
    (k := 2) ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩ (by decide)
  obtain ⟨result, current, heap, actual, rfl, rfl, rfl⟩ := rule
  exact actual

/-- Every actual CODES cell has its selected positive, bounded width. -/
theorem selected_width {ca : Array Code} {offset root : Nat} (l : IL)
    (safe : Zlib.Inftrees.Spec.CodeLengthTableSafe ca offset root) :
    1 ≤ (codeLookupValue ca offset root l).bits.toNat ∧
      (codeLookupValue ca offset root l).bits.toNat ≤ root := by
  have entry := safe.2.2.2 (l.hold.toNat % 2 ^ root) (Nat.mod_lt _ (Nat.two_pow_pos _))
  exact ⟨entry.1, entry.2.1⟩

/-- A valid independent symbol forces the actual lookup to return normally.
The source tests the selected entry width, not a forced root-width fill. -/
theorem valid_lookup_normal
    {c : Ctx} {h : Heap} {zs : Nat} {s : InflateState}
    {ref : CodeRef} {offset : Nat} {ca : Array Code} {alphabet : List Nat}
    {l : IL} {bs : List UInt8} {symbol : Nat} {rest : List Bool}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (pointer : s.lencode = .ref ref offset) (get : Space.get h ref = some ca)
    (meaning : Zlib.Inftrees.Proofs.CodeLengthMeaning ca offset s.lenbits.toNat alphabet)
    (B : BitInv h l bs) (decoded : decodeSym alphabet (stream l bs) = some (symbol, rest)) :
    ∃ regs used, runX (lookup1 c false) l h = .ok ((.ok (), regs), h) ∧
      used ≤ 1 ∧ used ≤ bs.length ∧ BitInv h regs (bs.drop used) ∧
      stream regs (bs.drop used) = stream l bs ∧
      1 ≤ regs.here.bits.toNat ∧ regs.here.bits.toNat ≤ s.lenbits.toNat ∧
      regs.here.bits.toNat ≤ regs.bits.toNat := by
  let entry := codeLookupValue ca offset s.lenbits.toNat l
  let read := { l with here := entry }
  have widths := selected_width l meaning.safe
  change 1 ≤ entry.bits.toNat ∧ entry.bits.toNat ≤ s.lenbits.toNat at widths
  have readB : BitInv h read bs := ⟨B.have_eq, B.next, B.hold_lt⟩
  have body := codesLookupBody_run l hc hs pointer get meaning.safe
  change runX (codesLookupBody c) l h =
    if entry.bits.toUInt32 ≤ l.bits then .ok ((.ok true, read), h)
    else runX (do PULLBYTE; pure false : X Bool) read h at body
  have normalExists : ∃ regs, runX (lookup1 c false) l h = .ok ((.ok (), regs), h) := by
    by_cases fit : entry.bits.toUInt32 ≤ l.bits
    · rw [ite_eq_left fit] at body
      exact ⟨read, by rw [lookup1_codes_eq]; exact loop_stop body⟩
    · have short : l.bits.toNat < entry.bits.toNat := by
        have failed := (not_congr UInt32.le_iff_toNat_le).mp fit
        simp only [UInt8.toNat_toUInt32] at failed
        omega
      rw [ite_eq_right fit] at body
      have root : s.lenbits.toNat ≤ 7 := meaning.safe.2.1
      cases bs with
      | nil =>
        obtain ⟨value, suffix, forwardEntry, query, cell, _op, _value, _width, fitted, _rest⟩ :=
          meaning.forward (stream l []) rest symbol decoded
        have held : stream l [] = bitsOfNat l.hold.toNat l.bits.toNat := by
          simp only [stream, bytesBits, List.flatMap_nil, List.append_nil, natBits_testBit]
          rfl
        obtain ⟨lookahead, actualQuery⟩ := ZlibF.Math.InflateHeldBits.padded_query (root := s.lenbits.toNat) B.hold_lt (by omega)
        rw [← held] at actualQuery
        have valueEq : value = l.hold.toNat % 2 ^ s.lenbits.toNat :=
          congrArg Prod.fst (Option.some.inj (query.symm.trans actualQuery))
        have inside : offset + l.hold.toNat % 2 ^ s.lenbits.toNat < ca.size := by
          have capacity := meaning.safe.2.2.1
          have index := Nat.mod_lt l.hold.toNat (Nat.two_pow_pos s.lenbits.toNat)
          omega
        have actualCell : ca[offset + l.hold.toNat % 2 ^ s.lenbits.toNat]? = some entry := by
          dsimp only [entry, codeLookupValue]
          rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem inside, Option.getD_some]
        rw [valueEq] at cell
        have sameEntry : forwardEntry = entry := Option.some.inj (cell.symm.trans actualCell)
        rw [sameEntry, held, bitsOfNat_length] at fitted
        exact False.elim (by omega)
      | cons b tail =>
        obtain ⟨next, pull, inv, sameStream, bitCount, _cursor⟩ :=
          PULLBYTE_succ_cursor readB (by change l.bits.toNat ≤ 56; omega)
        let middle := pulled read b next
        let finalEntry := codeLookupValue ca offset s.lenbits.toNat middle
        let final := { middle with here := finalEntry }
        have finalWidths := selected_width middle meaning.safe
        change 1 ≤ finalEntry.bits.toNat ∧ finalEntry.bits.toNat ≤ s.lenbits.toNat at finalWidths
        have fits : finalEntry.bits.toUInt32 ≤ middle.bits := by
          apply UInt32.le_iff_toNat_le.mpr
          rw [UInt8.toNat_toUInt32]
          change finalEntry.bits.toNat ≤ (pulled read b next).bits.toNat
          rw [bitCount]
          change finalEntry.bits.toNat ≤ l.bits.toNat + 8
          omega
        have second := codesLookupBody_run middle hc hs pointer get meaning.safe
        change runX (codesLookupBody c) middle h =
          if finalEntry.bits.toUInt32 ≤ middle.bits then .ok ((.ok true, final), h)
          else runX (do PULLBYTE; pure false : X Bool) final h at second
        rw [ite_eq_left fits] at second
        rw [runX_bind, pull] at body
        simp only [runX_pure] at body
        exact ⟨final, by rw [lookup1_codes_eq]; exact loop_pull_stop body second⟩
  obtain ⟨regs0, normal⟩ := normalExists
  obtain ⟨result, regs, used, actual, one, bound, inv, source, _shape, _bits, lower, upper,
    _kinds, full, _empty, _cursor, _count⟩ := lookup1_codes_run_cursor hc hs pointer get meaning.safe B
  rw [normal] at actual
  cases actual
  exact ⟨regs0, used, normal, one, bound, inv, source, lower, upper, full rfl⟩

#print axioms loop_stop
#print axioms loop_pull_stop
#print axioms selected_width
#print axioms valid_lookup_normal

/-- A valid independent symbol excludes the constructor's empty table;
the ordinary flat-root classification is therefore derived from contents. -/
theorem decoded_root_ordinary {ca : Array Code} {offset root : Nat} {alphabet : List Nat}
    {input rest : List Bool} {symbol : Nat}
    (contents : Zlib.Inftrees.Proofs.CodeLengthContents ca offset root alphabet)
    (decoded : decodeSym alphabet input = some (symbol, rest)) :
    ∀ index, index < 2 ^ root → ∃ entry, ca[offset + index]? = some entry ∧ entry.op = 0 := by
  rcases contents.layout with ⟨_root, zeros, _first, _second⟩ | ordinary
  · obtain ⟨inside, nonzero, _code, _rest⟩ := Zlib.Inftrees.Proofs.decoded_symbol_prefix decoded
    have member : alphabet.getD symbol 0 ∈ alphabet := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inside, Option.getD_some]
      exact List.getElem_mem inside
    exact False.elim (nonzero (zeros _ member))
  · exact ordinary

/-- Actual lookup returns precisely the symbol already decoded by the
independent alphabet, without a root-width availability precondition. -/
theorem valid_lookup_decoded
    {c : Ctx} {h : Heap} {zs : Nat} {s : InflateState}
    {ref : CodeRef} {offset : Nat} {ca : Array Code} {alphabet : List Nat}
    {l : IL} {bs : List UInt8} {symbol : Nat} {rest : List Bool}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (pointer : s.lencode = .ref ref offset) (get : Space.get h ref = some ca)
    (contents : Zlib.Inftrees.Proofs.CodeLengthContents ca offset s.lenbits.toNat alphabet)
    (B : BitInv h l bs) (decoded : decodeSym alphabet (stream l bs) = some (symbol, rest)) :
    ∃ regs used, runX (lookup1 c false) l h = .ok ((.ok (), regs), h) ∧
      used ≤ 1 ∧ used ≤ bs.length ∧ BitInv h regs (bs.drop used) ∧
      stream regs (bs.drop used) = stream l bs ∧
      regs.here.op = 0 ∧ regs.here.val.toNat = symbol ∧
      regs.here.bits.toNat = alphabet.getD symbol 0 ∧
      regs.here.bits.toNat ≤ 7 ∧ regs.here.bits.toNat ≤ regs.bits.toNat ∧
      rest = (stream l bs).drop regs.here.bits.toNat := by
  obtain ⟨regs, used, run, one, bound, inv, source, _lower, upper, full⟩ :=
    valid_lookup_normal hc hs pointer get contents.toCodeLengthMeaning B decoded
  have ordinaryRoot := decoded_root_ordinary contents decoded
  obtain ⟨_sameHeap, cell, _fields⟩ := lookup1_codes_contents hc hs pointer get contents B run
  obtain ⟨entry, entryGet, entryOp⟩ := ordinaryRoot _ (Nat.mod_lt _ (Nat.two_pow_pos _))
  have sameEntry : entry = regs.here := Option.some.inj (entryGet.symm.trans cell)
  have ordinary : regs.here.op = 0 := by rw [← sameEntry]; exact entryOp
  obtain ⟨sym, _small, value, width, actualDecoded⟩ :=
    lookup1_codes_symbol hc hs pointer get contents.toCodeLengthMeaning B run ordinary
  have sameSymbol : sym = symbol := congrArg Prod.fst (Option.some.inj (actualDecoded.symm.trans decoded))
  rw [sameSymbol] at value width actualDecoded
  obtain ⟨_inside, _nonzero, _prefix, remaining⟩ := Zlib.Inftrees.Proofs.decoded_symbol_prefix decoded
  refine ⟨regs, used, run, one, bound, inv, source, ordinary, value, width, ?_, full, ?_⟩
  · have root := contents.safe.2.1
    omega
  · rw [width]
    exact remaining

#print axioms decoded_root_ordinary
#print axioms valid_lookup_decoded

/-- Available real stream bits rule out the actual NEEDBITS exhausted exit. -/
theorem needbits_normal_of_available {h : Heap} {l : IL} {bs : List UInt8}
    (B : BitInv h l bs) (n : UInt32) (small : n.toNat ≤ 49)
    (available : n.toNat ≤ (stream l bs).length) :
    ∃ regs used, runX (NEEDBITS n) l h = .ok ((.ok (), regs), h) ∧
      used ≤ bs.length ∧ BitInv h regs (bs.drop used) ∧ stream regs (bs.drop used) = stream l bs ∧
      n.toNat ≤ regs.bits.toNat ∧ regs.bits.toNat = l.bits.toNat + 8 * used ∧
      regs.bits.toNat ≤ max l.bits.toNat (n.toNat + 7) ∧
      (n.toNat ≤ l.bits.toNat → regs = l) := by
  obtain ⟨result, regs, used, run, bound, inv, source, count, _shape, upper, same,
    full, wait, kinds, _cursor⟩ := NEEDBITS_run_cursor B n small
  have normal : result = .ok () := by
    rcases kinds with normal | waiting
    · exact normal
    · obtain ⟨allUsed, _empty, below⟩ := wait waiting
      rw [tcStream_length B] at available
      rw [allUsed] at count
      omega
  exact ⟨regs, used, by rwa [normal] at run, bound, inv, source, full normal, count, upper, same⟩

/-- A selected code and the independently available repeat extra bits
complete the actual NEEDBITS/drop prefix with at most one new byte. -/
theorem need_drop_complete {h : Heap} {l : IL} {bs : List UInt8}
    (B : BitInv h l bs) (here : Code) (extra : UInt32)
    (width : here.bits.toNat ≤ 7) (extraBound : extra.toNat ≤ 7)
    (fitted : here.bits.toNat ≤ l.bits.toNat)
    (available : here.bits.toNat + extra.toNat ≤ (stream l bs).length) :
    ∃ regs used, runX (clNeedDrop here extra) l h = .ok ((.ok (), regs), h) ∧
      used ≤ 1 ∧ used ≤ bs.length ∧ BitInv h regs (bs.drop used) ∧
      stream regs (bs.drop used) = (stream l bs).drop here.bits.toNat ∧
      extra.toNat ≤ regs.bits.toNat := by
  have total : (here.bits.toUInt32 + extra).toNat = here.bits.toNat + extra.toNat := by
    rw [UInt32.toNat_add, UInt8.toNat_toUInt32, Nat.mod_eq_of_lt (by omega)]
  obtain ⟨pulled, used, run, bound, inv, source, enough, count, upper, same⟩ :=
    needbits_normal_of_available B (here.bits.toUInt32 + extra) (by rw [total]; omega) (by rwa [total])
  rw [total] at enough upper same
  have one : used ≤ 1 := by
    by_cases old : here.bits.toNat + extra.toNat ≤ l.bits.toNat
    · rw [same old] at count
      omega
    · omega
  have small : here.bits.toUInt32.toNat < 64 := by rw [UInt8.toNat_toUInt32]; omega
  obtain ⟨afterInv, afterStream, afterCount⟩ := DROPBITS_inv inv here.bits.toUInt32
    (by rw [UInt8.toNat_toUInt32]; omega) small
  let regs := { pulled with hold := pulled.hold >>> here.bits.toUInt32.toUInt64, bits := pulled.bits - here.bits.toUInt32 }
  refine ⟨regs, used, ?_, one, bound, afterInv, ?_, ?_⟩
  · unfold clNeedDrop
    rw [runX_bind, run]
    exact DROPBITS_run pulled h here.bits.toUInt32 small
  · simpa only [UInt8.toNat_toUInt32, source] using afterStream
  · rw [UInt8.toNat_toUInt32] at afterCount
    change regs.bits.toNat = pulled.bits.toNat - here.bits.toNat at afterCount
    omega

#print axioms needbits_normal_of_available
#print axioms need_drop_complete

/-- An independent extra-bit read supplies exactly the availability needed
by the real zero-repeat setup. Its extra read pulls at most one new byte. -/
theorem zero_setup_complete
    {h : Heap} {l : IL} {bs : List UInt8} {value : Nat} {rest : List Bool}
    (B : BitInv h l bs) (here : Code) (extra base : UInt32)
    (width : here.bits.toNat ≤ 7) (extraBound : extra.toNat ≤ 7)
    (baseLo : 3 ≤ base.toNat) (baseHi : base.toNat ≤ 11)
    (fitted : here.bits.toNat ≤ l.bits.toNat)
    (readExtra : readBits extra.toNat ((stream l bs).drop here.bits.toNat) = some (value, rest)) :
    ∃ regs used, runX (clZeroSetup here extra base) l h = .ok ((.ok (), regs), h) ∧
      used ≤ 1 ∧ used ≤ bs.length ∧ BitInv h regs (bs.drop used) ∧
      stream regs (bs.drop used) = rest ∧ regs.len = 0 ∧ regs.copy.toNat = base.toNat + value := by
  obtain ⟨_valueBound, extraWord⟩ := ZlibF.Math.CodeLengthPrefix.read_word readExtra
  have wordLength := congrArg List.length extraWord
  simp only [List.length_drop, List.length_append, bitsOfNat_length] at wordLength
  have streamLength := tcStream_length B
  have available : here.bits.toNat + extra.toNat ≤ (stream l bs).length := by omega
  have total : (here.bits.toUInt32 + extra).toNat = here.bits.toNat + extra.toNat := by
    rw [UInt32.toNat_add, UInt8.toNat_toUInt32, Nat.mod_eq_of_lt (by omega)]
  obtain ⟨pulled, pulledUsed, needRun, needBound, needInv, _needSource, enough, bitCount, upper, same⟩ :=
    needbits_normal_of_available B (here.bits.toUInt32 + extra) (by rw [total]; omega) (by rwa [total])
  rw [total] at enough upper same
  have one : pulledUsed ≤ 1 := by
    by_cases old : here.bits.toNat + extra.toNat ≤ l.bits.toNat
    · rw [same old] at bitCount
      omega
    · omega
  let dropped : IL := { pulled with hold := pulled.hold >>> here.bits.toUInt32.toUInt64, bits := pulled.bits - here.bits.toUInt32 }
  let bits := dropped.hold.toUInt32 &&& ((1 : UInt32) <<< extra - 1)
  let prepared : IL := { dropped with len := 0, copy := base + bits }
  let final : IL := { prepared with hold := prepared.hold >>> extra.toUInt64, bits := prepared.bits - extra }
  have normal : runX (clZeroSetup here extra base) l h = .ok ((.ok (), final), h) := by
    unfold clZeroSetup
    rw [runX_bind, needRun]
    simp only []
    rw [runX_bind, DROPBITS_run pulled h here.bits.toUInt32 (by rw [UInt8.toNat_toUInt32]; omega)]
    simp only []
    rw [runX_bind, BITS_run dropped h extra (by omega)]
    simp only []
    rw [runX_bind, runX_modify]
    exact DROPBITS_run prepared h extra (by omega)
  obtain ⟨outcome, regs, used, actual, bound, inv, semantic⟩ :=
    clZeroSetup_read B here extra base width extraBound baseLo baseHi
  rw [normal] at actual
  cases actual
  obtain ⟨actualValue, parsed, zero, count⟩ := semantic rfl
  have sameValue : actualValue = value := congrArg Prod.fst (Option.some.inj (parsed.symm.trans readExtra))
  have sameRest : stream final (bs.drop used) = rest := congrArg Prod.snd (Option.some.inj (parsed.symm.trans readExtra))
  have sameUsed : pulledUsed = used := by
    have a := needInv.have_eq
    have b := inv.have_eq
    change pulled.have_.toNat = (bs.drop used).length at b
    simp only [List.length_drop] at a b
    omega
  refine ⟨final, used, normal, by omega, bound, inv, sameRest, zero, ?_⟩
  rw [sameValue] at count
  exact count

#print axioms zero_setup_complete

/-- A valid zero-repeat count passes the actual bounds check and writes
exactly the independently requested zero lengths. -/
theorem zero_repeat_complete
    {c : Ctx} {h : Heap} {zs : Nat} {s : InflateState} {l : IL} {bs : List UInt8}
    {value : Nat} {rest : List Bool}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (size : s.lens.size = 320) (nlen : s.nlen.toNat ≤ 286) (ndist : s.ndist.toNat ≤ 30)
    (haveBound : s.«have».toNat ≤ s.nlen.toNat + s.ndist.toNat)
    (B : BitInv h l bs) (here : Code) (extra base : UInt32)
    (width : here.bits.toNat ≤ 7) (extraBound : extra.toNat ≤ 7)
    (baseLo : 3 ≤ base.toNat) (baseHi : base.toNat ≤ 11)
    (fitted : here.bits.toNat ≤ l.bits.toNat)
    (readExtra : readBits extra.toNat ((stream l bs).drop here.bits.toNat) = some (value, rest))
    (room : s.«have».toNat + (base.toNat + value) ≤ s.nlen.toNat + s.ndist.toNat) :
    ∃ regs state used,
      runX (do clZeroSetup here extra base; clRepeatFinish c) l h =
        .ok ((.ok false, regs), setI h zs state) ∧
      used ≤ 1 ∧ used ≤ bs.length ∧ BitInv (setI h zs state) regs (bs.drop used) ∧
      stream regs (bs.drop used) = rest ∧
      state = { s with lens := state.lens, «have» := state.«have» } ∧
      state.lens.size = 320 ∧ state.«have».toNat = s.«have».toNat + (base.toNat + value) ∧
      actualLengthPrefix state = actualLengthPrefix s ++ List.replicate (base.toNat + value) 0 := by
  obtain ⟨prepared, used, setup, one, bound, inv, source, zero, count⟩ :=
    zero_setup_complete B here extra base width extraBound baseLo baseHi fitted readExtra
  have valueBound := (ZlibF.Math.CodeLengthPrefix.read_word readExtra).1
  have power : 2 ^ extra.toNat ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) extraBound
  have copyBound : prepared.copy.toNat ≤ 138 := by omega
  obtain ⟨state, finish, frame, stateSize, stateCount, prefixEq⟩ :=
    clRepeatFinish_contents hc hs size nlen ndist haveBound copyBound (by omega)
  let regs := { prepared with copy := 0xffffffff }
  have finalInv : BitInv (setI h zs state) regs (bs.drop used) :=
    (show BitInv h regs (bs.drop used) from ⟨inv.have_eq, inv.next, inv.hold_lt⟩).setI zs state
  have castZero : prepared.len.toUInt16.toNat = 0 := by rw [zero]; rfl
  refine ⟨regs, state, used, ?_, one, bound, finalInv, source, frame, stateSize, ?_, ?_⟩
  · rw [runX_bind, setup]
    exact finish
  · rw [stateCount, count]
  · rw [prefixEq, count, castZero]

/-- A valid symbol-16 extra read supplies the missing bits, proves the
prefix nonempty and passes the actual repeat-range check. -/
theorem previous_repeat_complete
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {value : Nat} {rest : List Bool}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (hz : r.get h = some z) (hs : h.istates zs = some s)
    (size : s.lens.size = 320) (nlen : s.nlen.toNat ≤ 286) (ndist : s.ndist.toNat ≤ 30)
    (haveBound : s.«have».toNat ≤ s.nlen.toNat + s.ndist.toNat) (nonempty : 1 ≤ s.«have».toNat)
    (B : BitInv h l bs) (here : Code) (width : here.bits.toNat ≤ 7)
    (fitted : here.bits.toNat ≤ l.bits.toNat)
    (readExtra : readBits 2 ((stream l bs).drop here.bits.toNat) = some (value, rest))
    (room : s.«have».toNat + (3 + value) ≤ s.nlen.toNat + s.ndist.toNat) :
    ∃ regs state used,
      runX (clRepeat16 c here) l h = .ok ((.ok false, regs), setI h zs state) ∧
      used ≤ 1 ∧ used ≤ bs.length ∧ BitInv (setI h zs state) regs (bs.drop used) ∧
      stream regs (bs.drop used) = rest ∧
      state = { s with lens := state.lens, «have» := state.«have» } ∧
      state.lens.size = 320 ∧ state.«have».toNat = s.«have».toNat + (3 + value) ∧
      actualLengthPrefix state = actualLengthPrefix s ++ List.replicate (3 + value) ((actualLengthPrefix s).getLastD 0) := by
  obtain ⟨_valueBound, extraWord⟩ := ZlibF.Math.CodeLengthPrefix.read_word readExtra
  have wordLength := congrArg List.length extraWord
  simp only [List.length_drop, List.length_append, bitsOfNat_length] at wordLength
  have streamLength := tcStream_length B
  have available : here.bits.toNat + (2 : UInt32).toNat ≤ (stream l bs).length := by
    change here.bits.toNat + 2 ≤ _
    omega
  obtain ⟨dropped, prefixUsed, prefixRun, one, prefixBound, prefixInv, prefixSource, extraHeld⟩ :=
    need_drop_complete B here 2 width (by decide) fitted available
  obtain ⟨prepared, actualValue, previousRun, preparedInv, _previous, parsed, count⟩ :=
    clPrevBits_read hc hs size nonempty (by omega) prefixInv extraHeld
  rw [prefixSource] at parsed
  have sameValue : actualValue = value := congrArg Prod.fst (Option.some.inj (parsed.symm.trans readExtra))
  rw [sameValue] at count
  have copyBound : prepared.copy.toNat ≤ 138 := by
    have small := (ZlibF.Math.CodeLengthPrefix.read_word readExtra).1
    change value < 4 at small
    omega
  obtain ⟨state, finish, _frame, _stateSize, _stateCount, _prefixEq⟩ :=
    clRepeatFinish_contents hc hs size nlen ndist haveBound copyBound (by omega)
  have notEmpty : s.«have» ≠ 0 := by intro empty; rw [empty] at nonempty; contradiction
  have cut : runX (clRepeat16 c here) l h = runX (do clPrevBits c s.«have»; clRepeatFinish c) dropped h := by
    unfold clRepeat16
    rw [runX_bind, prefixRun, hc]
    simp [runX_bind, runX_lift, ldI_eq, hs, notEmpty]
  have actual : runX (clRepeat16 c here) l h =
      .ok ((.ok false, { prepared with copy := 0xffffffff }), setI h zs state) := by
    rw [cut, runX_bind, previousRun]
    exact finish
  obtain ⟨used, observedState, observedValue, bound, heapEq, inv, _nonempty, frame,
    stateSize, stateCount, _upper, read, prefixEq⟩ :=
    clPreviousRepeat_contents_of_run hr hc hz hs size nlen ndist haveBound B here width actual
  have sameState : state = observedState := by
    have get := congrArg (fun heap : Heap => heap.istates zs) heapEq
    simp only [setI_istates_same] at get
    exact Option.some.inj get
  subst observedState
  have valueEq : observedValue = value := congrArg Prod.fst (Option.some.inj (read.symm.trans readExtra))
  have restEq : stream { prepared with copy := 0xffffffff } (bs.drop used) = rest :=
    congrArg Prod.snd (Option.some.inj (read.symm.trans readExtra))
  rw [valueEq] at stateCount prefixEq
  have sameUsed : prefixUsed = used := by
    have a := preparedInv.have_eq
    have b := inv.have_eq
    change prepared.have_.toNat = (bs.drop used).length at b
    simp only [List.length_drop] at a b
    omega
  refine ⟨{ prepared with copy := 0xffffffff }, state, used, actual, by omega, bound, ?_, restEq,
    frame, stateSize, stateCount, prefixEq⟩
  rw [← heapEq]
  exact inv

#print axioms zero_repeat_complete
#print axioms previous_repeat_complete

/-- An observed, closed lookup and its closed suffix compose without
reloading registers or losing the actual source cursor. -/
theorem lookup_suffix_compose
    {c : Ctx} {h : Heap} {zs : Nat} {state : InflateState}
    {l looked regs : IL} {bs : List UInt8} {used1 used2 : Nat}
    (lookupRun : runX (lookup1 c false) l h = .ok ((.ok (), looked), h))
    (firstBound : used1 ≤ bs.length)
    (suffixRun : runX (clAfterLookup c looked.here) looked h = .ok ((.ok false, regs), setI h zs state))
    (secondBound : used2 ≤ (bs.drop used1).length)
    (inv : BitInv (setI h zs state) regs ((bs.drop used1).drop used2)) :
    runX (clReadBody c) l h = .ok ((.ok false, regs), setI h zs state) ∧
    used1 + used2 ≤ bs.length ∧ BitInv (setI h zs state) regs (bs.drop (used1 + used2)) := by
  refine ⟨?_, by simp only [List.length_drop] at secondBound; omega, ?_⟩
  · rw [clReadBody_eq, runX_bind, lookupRun]
    simpa only [runX_bind, runX_get] using suffixRun
  · simpa only [List.drop_drop, Nat.add_comm] using inv

/-- Each independent nonfinal grammar constructor drives one actual normal
CODELENS iteration and supplies its exact remaining valid derivation. -/
theorem body_forward
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {alphabet out : List Nat} {rest : List Bool}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (hz : r.get h = some z) (hs : h.istates zs = some s)
    (size : s.lens.size = 320) (mode : s.mode = CODELENS) (stateInv : CodeLengthInvariant zs s)
    (contents : Zlib.Inftrees.Proofs.CodeLengthContents s.codes 0 s.lenbits.toNat alphabet)
    (more : s.«have».toNat < s.nlen.toNat + s.ndist.toNat) (B : BitInv h l bs)
    (parsed : CodeLens alphabet (s.nlen.toNat + s.ndist.toNat) (actualLengthPrefix s) (stream l bs) rest out) :
    ∃ regs state used,
      runX (clReadBody c) l h = .ok ((.ok false, regs), setI h zs state) ∧
      used ≤ bs.length ∧ BitInv (setI h zs state) regs (bs.drop used) ∧
      ClWriteResult s state ∧
      CodeLens alphabet (s.nlen.toNat + s.ndist.toNat) (actualLengthPrefix state) (stream regs (bs.drop used)) rest out := by
  obtain ⟨pointer, _table, nlen, ndist, haveBound, initialized⟩ := stateInv mode
  have get := CodeRef.get_istate_codes hs
  have prefixLength : (actualLengthPrefix s).length = s.«have».toNat := Zlib.Inftrees.Proofs.lensOf_length _ _
  have witness : ∃ regs state used,
      runX (clReadBody c) l h = .ok ((.ok false, regs), setI h zs state) ∧
      used ≤ bs.length ∧ BitInv (setI h zs state) regs (bs.drop used) ∧
      CodeLens alphabet (s.nlen.toNat + s.ndist.toNat) (actualLengthPrefix state) (stream regs (bs.drop used)) rest out := by
    cases parsed with
    | done full => omega
    | len _ decoded literal tail =>
      obtain ⟨looked, used1, lookupRun, _one, bound1, _inv1, _source1, ordinary, value, _width, _seven, _fitted, _remaining⟩ :=
        valid_lookup_decoded hc hs pointer get contents B decoded
      obtain ⟨used, _one, bound, run, inv, _source, actualDecode, written⟩ :=
        clReadBody_literal_symbol hc hs pointer get contents.toCodeLengthMeaning size (by omega) initialized B lookupRun ordinary (by omega)
      have remaining := congrArg Prod.snd (Option.some.inj (actualDecode.symm.trans decoded))
      dsimp only at remaining
      change actualLengthPrefix (clWrite s looked.here.val) = actualLengthPrefix s ++ [looked.here.val.toNat] at written
      refine ⟨_, clWrite s looked.here.val, used, run, bound, inv, ?_⟩
      rw [written, value, remaining]
      exact tail
    | rep16 _ decoded nonempty readExtra room tail =>
      obtain ⟨looked, used1, lookupRun, _one, bound1, inv1, source1, _ordinary, value, _width, seven, fitted, remaining⟩ :=
        valid_lookup_decoded hc hs pointer get contents B decoded
      have symbol : looked.here.val = 16 := UInt16.toNat_inj.mp value
      have notEmpty : 1 ≤ s.«have».toNat := by
        by_cases positive : 1 ≤ s.«have».toNat
        · exact positive
        · have empty : actualLengthPrefix s = [] := List.eq_nil_of_length_eq_zero (by omega)
          exact False.elim (nonempty empty)
      have readSelected := readExtra
      rw [remaining, ← source1] at readSelected
      obtain ⟨regs, state, used2, suffixRun, _one, bound2, inv2, source2, _frame, _size, _count, written⟩ :=
        previous_repeat_complete hr hc hz hs size nlen ndist haveBound notEmpty inv1 looked.here seven fitted readSelected (by omega)
      rw [← clAfterLookup_repeat16 c looked.here symbol] at suffixRun
      obtain ⟨run, bound, inv⟩ := lookup_suffix_compose lookupRun bound1 suffixRun bound2 inv2
      refine ⟨regs, state, used1 + used2, run, bound, inv, ?_⟩
      rw [written]
      rw [← source2] at tail
      simpa only [List.drop_drop, Nat.add_comm, show (3 : UInt32).toNat = 3 by decide, show (11 : UInt32).toNat = 11 by decide] using tail
    | rep17 _ decoded readExtra room tail =>
      obtain ⟨looked, used1, lookupRun, _one, bound1, inv1, source1, _ordinary, value, _width, seven, fitted, remaining⟩ :=
        valid_lookup_decoded hc hs pointer get contents B decoded
      have symbol : looked.here.val = 17 := UInt16.toNat_inj.mp value
      have readSelected := readExtra
      rw [remaining, ← source1] at readSelected
      obtain ⟨regs, state, used2, suffixRun, _one, bound2, inv2, source2, _frame, _size, _count, written⟩ :=
        zero_repeat_complete hc hs size nlen ndist haveBound inv1 looked.here 3 3 seven (by decide) (by decide) (by decide) fitted readSelected (by simpa only [prefixLength, show (3 : UInt32).toNat = 3 by decide, show (11 : UInt32).toNat = 11 by decide] using room)
      rw [← clAfterLookup_zero17 c looked.here symbol] at suffixRun
      obtain ⟨run, bound, inv⟩ := lookup_suffix_compose lookupRun bound1 suffixRun bound2 inv2
      refine ⟨regs, state, used1 + used2, run, bound, inv, ?_⟩
      rw [written]
      rw [← source2] at tail
      simpa only [List.drop_drop, Nat.add_comm, show (3 : UInt32).toNat = 3 by decide, show (11 : UInt32).toNat = 11 by decide] using tail
    | rep18 _ decoded readExtra room tail =>
      obtain ⟨looked, used1, lookupRun, _one, bound1, inv1, source1, _ordinary, value, _width, seven, fitted, remaining⟩ :=
        valid_lookup_decoded hc hs pointer get contents B decoded
      have symbol : looked.here.val = 18 := UInt16.toNat_inj.mp value
      have notLiteral : ¬ looked.here.val < 16 := by rw [symbol]; decide
      have not16 : looked.here.val ≠ 16 := by rw [symbol]; decide
      have not17 : looked.here.val ≠ 17 := by rw [symbol]; decide
      have readSelected := readExtra
      rw [remaining, ← source1] at readSelected
      obtain ⟨regs, state, used2, suffixRun, _one, bound2, inv2, source2, _frame, _size, _count, written⟩ :=
        zero_repeat_complete hc hs size nlen ndist haveBound inv1 looked.here 7 11 seven (by decide) (by decide) (by decide) fitted readSelected (by simpa only [prefixLength, show (3 : UInt32).toNat = 3 by decide, show (11 : UInt32).toNat = 11 by decide] using room)
      rw [← clAfterLookup_zero18 c looked.here notLiteral not16 not17] at suffixRun
      obtain ⟨run, bound, inv⟩ := lookup_suffix_compose lookupRun bound1 suffixRun bound2 inv2
      refine ⟨regs, state, used1 + used2, run, bound, inv, ?_⟩
      rw [written]
      rw [← source2] at tail
      simpa only [List.drop_drop, Nat.add_comm, show (3 : UInt32).toNat = 3 by decide, show (11 : UInt32).toNat = 11 by decide] using tail
  obtain ⟨regs, state, used, actual, bound, inv, tail⟩ := witness
  obtain ⟨result2, regs2, after2, used2, run2, _bound2, _inv2, _shape, _bits, post, _cursor, _budget⟩ :=
    clReadBody_run_cursor hr hc hz hs size mode stateInv more B
  rw [actual] at run2
  cases run2
  obtain ⟨observedState, heapEq, write⟩ := post
  have stateEq : state = observedState := by
    have getEq := congrArg (fun heap : Heap => heap.istates zs) heapEq
    simp only [setI_istates_same] at getEq
    exact Option.some.inj getEq
  rw [← stateEq] at write
  exact ⟨regs, state, used, actual, bound, inv, write, tail⟩

#print axioms lookup_suffix_compose
#print axioms body_forward


/-- A valid grammar cannot consume another code when its prefix is full. -/
theorem parsed_full {alphabet acc out : List Nat} {total : Nat} {input rest : List Bool}
    (parsed : CodeLens alphabet total acc input rest out) (full : acc.length = total) :
    input = rest ∧ acc = out := by
  cases parsed <;> first | exact ⟨rfl, rfl⟩ | omega

/-- Independent valid CodeLens input drives the actual reader to normal
completion, with exactly the requested real lens prefix and remaining bits.
The live IL is used directly; selected-cell lookup needs no root-width fill. -/
theorem clRead_forward_complete
    {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {bs : List UInt8} {alphabet out : List Nat} {rest : List Bool}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (hz : r.get h = some z) (hs : h.istates zs = some s)
    (size : s.lens.size = 320) (mode : s.mode = CODELENS) (stateInv : CodeLengthInvariant zs s)
    (contents : Zlib.Inftrees.Proofs.CodeLengthContents s.codes 0 s.lenbits.toNat alphabet)
    (B : BitInv h l bs)
    (parsed : CodeLens alphabet (s.nlen.toNat + s.ndist.toNat) (actualLengthPrefix s) (stream l bs) rest out) :
    ∃ regs state used,
      runX (clRead c) l h = .ok ((.ok (), regs), setI h zs state) ∧
      state = { s with lens := state.lens, «have» := state.«have» } ∧
      state.lens.size = 320 ∧ state.«have».toNat = s.nlen.toNat + s.ndist.toNat ∧
      (∀ k, k < state.«have».toNat → (state.lens.getD k 0).toNat ≤ 15) ∧
      used ≤ bs.length ∧ BitInv (setI h zs state) regs (bs.drop used) ∧
      stream regs (bs.drop used) = rest ∧ actualLengthPrefix state = out := by
  obtain ⟨pointer, table, nlen, ndist, haveBound, initialized⟩ := stateInv mode
  let total := s.nlen.toNat + s.ndist.toNat
  let P : IL → Heap → Prop := fun regs heap => ∃ state used,
    heap = setI h zs state ∧ state = { s with lens := state.lens, «have» := state.«have» } ∧
    state.lens.size = 320 ∧ state.«have».toNat ≤ total ∧
    (∀ k, k < state.«have».toNat → (state.lens.getD k 0).toNat ≤ 15) ∧
    used ≤ bs.length ∧ BitInv heap regs (bs.drop used) ∧
    CodeLens alphabet total (actualLengthPrefix state) (stream regs (bs.drop used)) rest out
  let rank : IL → Heap → Nat := fun _ heap => total - ((heap.istates zs).getD default).«have».toNat
  let Q : Except Ex Unit → IL → Heap → Prop := fun outcome regs after =>
    outcome = .ok () ∧ ∃ state used,
      after = setI h zs state ∧ state = { s with lens := state.lens, «have» := state.«have» } ∧
      state.lens.size = 320 ∧ state.«have».toNat = total ∧
      (∀ k, k < state.«have».toNat → (state.lens.getD k 0).toNat ≤ 15) ∧
      used ≤ bs.length ∧ BitInv after regs (bs.drop used) ∧
      stream regs (bs.drop used) = rest ∧ actualLengthPrefix state = out
  have loop := xwhileBrk_rank (cond := clReadCond c) (body := clReadBody c) P rank Q ?_ (l := l) (h := h) ?_ ?_
  · obtain ⟨outcome, regs, after, run, normal, state, used, heapEq, frame, sz, count, values, bound, inv, source, lens⟩ := loop
    subst outcome after
    exact ⟨regs, state, used, by rw [clRead_eq]; exact run, frame, sz, count, values, bound, inv, source, lens⟩
  · intro regs heap inv
    obtain ⟨state, used, heapEq, frame, sz, count, prefixValues, usedBound, bitInv, remainingParsed⟩ := inv
    subst heap
    have get : (setI h zs state).istates zs = some state := by simp
    have currentStream : r.get (setI h zs state) = some z := by simpa using hz
    have fields : state.nlen = s.nlen ∧ state.ndist = s.ndist ∧ state.mode = CODELENS := by
      rw [frame]
      exact ⟨rfl, rfl, mode⟩
    have totalEq : state.nlen.toNat + state.ndist.toNat = total := by rw [fields.1, fields.2.1]
    have sum : (state.nlen + state.ndist).toNat = total := by
      rw [fields.1, fields.2.1, UInt32.toNat_add, Nat.mod_eq_of_lt (by omega)]
    have currentInv : CodeLengthInvariant zs state := by
      intro _
      refine ⟨?_, ?_, ?_, ?_, ?_, prefixValues⟩
      · rw [frame]; exact pointer
      · rw [frame]; exact table
      · rw [fields.1]; exact nlen
      · rw [fields.2.1]; exact ndist
      · rw [totalEq]; exact count
    have currentContents : Zlib.Inftrees.Proofs.CodeLengthContents state.codes 0 state.lenbits.toNat alphabet := by
      rw [frame]
      exact contents
    have condRun : runX (clReadCond c) regs (setI h zs state) =
        .ok ((.ok (decide (state.«have» < state.nlen + state.ndist)), regs), setI h zs state) := by
      unfold clReadCond
      rw [hc]
      simp [runX_bind, runX_lift, ldI_eq, get, runX_pure]
    by_cases more : state.«have» < state.nlen + state.ndist
    · have moreNat : state.«have».toNat < state.nlen.toNat + state.ndist.toNat := by
        have less := UInt32.lt_iff_toNat_lt.mp more
        rw [sum] at less
        rw [totalEq]
        exact less
      rw [← totalEq] at remainingParsed
      obtain ⟨nextRegs, nextState, consumed, bodyRun, consumedBound, nextInv, writeFrame, nextParsed⟩ :=
        body_forward hr hc currentStream get sz fields.2.2 currentInv currentContents moreNat bitInv remainingParsed
      obtain ⟨writeFrame, nextSize, nextCount, progress, nextPrefix⟩ := writeFrame
      refine ⟨.ok true, regs, setI h zs state, by simpa only [more, decide_true] using condRun,
        .ok false, nextRegs, setI (setI h zs state) zs nextState, bodyRun, ?_⟩
      have consumedTotal : used + consumed ≤ bs.length := by
        simp only [List.length_drop] at consumedBound
        omega
      have remainder : (bs.drop used).drop consumed = bs.drop (used + consumed) := by simp only [List.drop_drop]
      rw [totalEq, remainder] at nextParsed
      rw [remainder] at nextInv
      constructor
      · refine ⟨nextState, used + consumed, by simp, ?_, nextSize, ?_, nextPrefix, consumedTotal, nextInv, nextParsed⟩
        · rw [writeFrame, frame]
        · rw [totalEq] at nextCount
          exact nextCount
      · dsimp only [rank]
        simp only [setI_istates_same, Option.getD_some]
        rw [totalEq] at nextCount
        omega
    · have full : state.«have».toNat = total := by
        have notLess := (not_congr UInt32.lt_iff_toNat_lt).mp more
        rw [sum] at notLess
        omega
      have prefixFull : (actualLengthPrefix state).length = total := by
        exact (Zlib.Inftrees.Proofs.lensOf_length _ _).trans full
      obtain ⟨source, lens⟩ := parsed_full remainingParsed prefixFull
      refine ⟨.ok false, regs, setI h zs state, by simpa only [more, decide_false] using condRun, ?_⟩
      exact ⟨rfl, state, used, rfl, frame, sz, full, prefixValues, usedBound, bitInv, source, lens⟩
  · exact ⟨s, 0, (tcSetI_same hs).symm, rfl, size, haveBound, initialized, by omega,
      by simpa only [List.drop_zero] using B, by simpa only [List.drop_zero] using parsed⟩
  · dsimp only [rank]
    rw [hs]
    simp only [Option.getD_some]
    unfold fuel total
    omega

#print axioms parsed_full
#print axioms clRead_forward_complete


/-- The same successful actual reader run retains all existing frame,
array-safety and exact input-cursor facts, alongside forward semantics. -/
theorem clRead_forward_full
    {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {bs : List UInt8} {alphabet out : List Nat} {rest : List Bool}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (hz : r.get h = some z) (hs : h.istates zs = some s)
    (size : s.lens.size = 320) (mode : s.mode = CODELENS) (stateInv : CodeLengthInvariant zs s)
    (contents : Zlib.Inftrees.Proofs.CodeLengthContents s.codes 0 s.lenbits.toNat alphabet)
    (B : BitInv h l bs)
    (parsed : CodeLens alphabet (s.nlen.toNat + s.ndist.toNat) (actualLengthPrefix s) (stream l bs) rest out) :
    ∃ regs state used,
      runX (clRead c) l h = .ok ((.ok (), regs), setI h zs state) ∧
      ClReadResultFull h r z zs s l bs (.ok ()) regs (setI h zs state) ∧
      state = { s with lens := state.lens, «have» := state.«have» } ∧
      state.lens.size = 320 ∧ state.«have».toNat = s.nlen.toNat + s.ndist.toNat ∧
      (∀ k, k < state.«have».toNat → (state.lens.getD k 0).toNat ≤ 15) ∧
      used ≤ bs.length ∧ BitInv (setI h zs state) regs (bs.drop used) ∧
      regs.next = inputAdvance l.next used ∧ regs.bits.toNat ≤ l.bits.toNat + 8 * used ∧
      stream regs (bs.drop used) = rest ∧ actualLengthPrefix state = out := by
  obtain ⟨regs, state, used, actual, frame, sz, count, values, bound, inv, source, lens⟩ :=
    clRead_forward_complete hr hc hz hs size mode stateInv contents B parsed
  obtain ⟨outcome2, regs2, after2, run2, full, used2, bound2, inv2, cursor, budget⟩ :=
    clRead_run_full_cursor hr hc hz hs size mode stateInv B
  rw [actual] at run2
  cases run2
  have sameUsed : used2 = used := by
    have first := inv.have_eq
    have second := inv2.have_eq
    simp only [List.length_drop] at first second
    omega
  subst used2
  exact ⟨regs, state, used, actual, full, frame, sz, count, values, bound, inv, cursor, budget, source, lens⟩

/-- Exact completed-prefix equality supplies each actual stored lens cell
needed by the following literal/length and distance table constructors. -/
theorem completed_lens_cell {state : InflateState} {out : List Nat} {k : Nat}
    (lens : actualLengthPrefix state = out) (inside : k < state.«have».toNat) :
    (state.lens.getD k 0).toNat = out.getD k 0 := by
  rw [← lens]
  exact (Zlib.Inftrees.Proofs.lensOf_getD (fun j => (state.lens.getD j 0).toNat) inside).symm

#print axioms clRead_forward_full
#print axioms completed_lens_cell

end Zlib.Inflate.Proofs.CodeLensCompletion
