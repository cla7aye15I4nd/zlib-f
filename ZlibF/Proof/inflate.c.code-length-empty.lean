import ZlibF.Proof.«inflate.c.code-length-body-prefix»
import ZlibF.Proof.«inflate.c.code-length-body-wait»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

/-- The real empty root's invalid opcode is not tested by clRead.
Each completed iteration writes a literal zero; exhaustion waits safely. -/
theorem clReadBody_empty_root {c : Ctx} {l : IL} {h : Heap}
    {zs : Nat} {s : InflateState} {bs : List UInt8}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (size : s.lens.size = 320) (mode : s.mode = CODELENS) (stateInv : CodeLengthInvariant zs s)
    (root : s.lenbits.toNat = 1) (first : s.codes[0]? = some (⟨64, 1, 0⟩ : Code))
    (second : s.codes[1]? = some (⟨64, 1, 0⟩ : Code))
    (more : s.«have».toNat < s.nlen.toNat + s.ndist.toNat) (B : BitInv h l bs) :
    ∃ outcome regs after used, runX (clReadBody c) l h = .ok ((outcome, regs), after) ∧
      used ≤ bs.length ∧ BitInv after regs (bs.drop used) ∧
      ((outcome = .error Ex.leave ∧ after = h) ∨
       (outcome = .ok false ∧ after = setI h zs (clWrite s 0))) := by
  obtain ⟨pointer, table, nlen, ndist, _have, initialized⟩ := stateInv mode
  have arrayGet := CodeRef.get_istate_codes hs
  obtain ⟨outcome, looked, used, lookupRun, _one, bound, inv, _stream, _shape, _bits,
    _lower, width, kinds, enough, _empty, _cursor, _count⟩ :=
    lookup1_codes_run_cursor hc hs pointer arrayGet table B
  obtain ⟨_heap, selected⟩ := lookup1_codes_selected hc hs pointer arrayGet table B lookupRun
  have indexBound : looked.hold.toNat % 2 ^ s.lenbits.toNat < 2 := by
    have inside := Nat.mod_lt looked.hold.toNat (Nat.two_pow_pos s.lenbits.toNat)
    rw [root] at inside ⊢
    exact inside
  have casesIndex : looked.hold.toNat % 2 ^ s.lenbits.toNat = 0 ∨ looked.hold.toNat % 2 ^ s.lenbits.toNat = 1 := by omega
  have here : looked.here = (⟨64, 1, 0⟩ : Code) := by
    rw [selected, codeLookupValue, Array.getD_eq_getD_getElem?]
    rcases casesIndex with zero | one
    · simp only [zero, Nat.zero_add, first, Option.getD_some]
    · simp only [one, Nat.zero_add, second, Option.getD_some]
  cases outcome with
  | error exit =>
    have exitEq : exit = Ex.leave := by
      rcases kinds with impossible | same
      · cases impossible
      · exact Except.error.inj same
    subst exit
    refine ⟨.error Ex.leave, looked, h, used, ?_, bound, inv, Or.inl ⟨rfl, rfl⟩⟩
    rw [clReadBody_eq, runX_bind, lookupRun]
  | ok done =>
    cases done
    obtain ⟨literalRun, afterInv, _remaining, _newCount, _values⟩ := clAfterLookup_literal_run hc hs size
      (by omega) (by simpa only [here] using (by decide : (0 : UInt16).toNat < 16)) (by simpa only [here] using (by decide : (1 : UInt8).toNat ≤ 7)) (enough rfl) inv initialized
    have storedZero : looked.here.val = 0 := by rw [here]
    rw [storedZero] at literalRun afterInv
    refine ⟨.ok false, _, setI h zs (clWrite s 0), used, ?_, bound, afterInv, Or.inr ⟨rfl, rfl⟩⟩
    rw [clReadBody_eq, runX_bind, lookupRun]
    simp only [runX_bind, runX_get]
    exact literalRun


/-- The actual empty-root reader only appends zeros. A normal return reaches its count bound. -/
theorem clRead_empty_root {c : Ctx} {l : IL} {h : Heap}
    {zs : Nat} {s : InflateState} {bs : List UInt8}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (size : s.lens.size = 320) (mode : s.mode = CODELENS) (stateInv : CodeLengthInvariant zs s)
    (root : s.lenbits.toNat = 1) (first : s.codes[0]? = some (⟨64, 1, 0⟩ : Code))
    (second : s.codes[1]? = some (⟨64, 1, 0⟩ : Code))
    (zeros : actualLengthPrefix s = List.replicate s.«have».toNat 0) (B : BitInv h l bs) :
    ∃ outcome regs after state used, runX (clRead c) l h = .ok ((outcome, regs), after) ∧
      after.istates zs = some state ∧ used ≤ bs.length ∧ BitInv after regs (bs.drop used) ∧
      state.mode = CODELENS ∧
      actualLengthPrefix state = List.replicate state.«have».toNat 0 ∧
      (outcome = .ok () → state.«have».toNat = s.nlen.toNat + s.ndist.toNat) := by
  obtain ⟨pointer, table, nlen, ndist, haveBound, initialized⟩ := stateInv mode
  let total := s.nlen.toNat + s.ndist.toNat
  let P : IL → Heap → Prop := fun regs heap => ∃ state used,
    heap = setI h zs state ∧ state = { s with lens := state.lens, «have» := state.«have» } ∧
    state.lens.size = 320 ∧ state.«have».toNat ≤ total ∧
    (∀ k, k < state.«have».toNat → (state.lens.getD k 0).toNat ≤ 15) ∧
    used ≤ bs.length ∧ BitInv heap regs (bs.drop used) ∧
    actualLengthPrefix state = List.replicate state.«have».toNat 0
  let rank : IL → Heap → Nat := fun _ heap => total - ((heap.istates zs).getD default).«have».toNat
  let Q : Except Ex Unit → IL → Heap → Prop := fun outcome regs after =>
    ∃ state used, after.istates zs = some state ∧ used ≤ bs.length ∧ BitInv after regs (bs.drop used) ∧
      state.mode = CODELENS ∧ actualLengthPrefix state = List.replicate state.«have».toNat 0 ∧
      (outcome = .ok () → state.«have».toNat = total)
  have loop := xwhileBrk_rank (cond := clReadCond c) (body := clReadBody c) P rank Q ?_ (l := l) (h := h) ?_ ?_
  · obtain ⟨outcome, regs, after, run, state, used, post⟩ := loop
    refine ⟨outcome, regs, after, state, used, ?_, post⟩
    rw [clRead_eq]
    exact run
  · intro regs heap inv
    obtain ⟨state, used, heapEq, frame, sz, count, prefixValues, usedBound, bitInv, prefixZero⟩ := inv
    subst heap
    have arrayGet : (setI h zs state).istates zs = some state := by simp
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
    have currentRoot : state.lenbits.toNat = 1 := by rw [frame]; exact root
    have currentFirst : state.codes[0]? = some (⟨64, 1, 0⟩ : Code) := by rw [frame]; exact first
    have currentSecond : state.codes[1]? = some (⟨64, 1, 0⟩ : Code) := by rw [frame]; exact second
    have condRun : runX (clReadCond c) regs (setI h zs state) =
        .ok ((.ok (decide (state.«have» < state.nlen + state.ndist)), regs), setI h zs state) := by
      unfold clReadCond
      rw [hc]
      simp [runX_bind, runX_lift, ldI_eq, arrayGet, runX_pure]
    by_cases more : state.«have» < state.nlen + state.ndist
    · have moreNat : state.«have».toNat < state.nlen.toNat + state.ndist.toNat := by
        have less := UInt32.lt_iff_toNat_lt.mp more
        rw [sum] at less
        rw [totalEq]
        exact less
      obtain ⟨result, nextRegs, after, consumed, bodyRun, consumedBound, nextInv, post⟩ :=
        clReadBody_empty_root hc arrayGet sz fields.2.2 currentInv currentRoot currentFirst currentSecond moreNat bitInv
      refine ⟨.ok true, regs, setI h zs state, by simpa only [more, decide_true] using condRun,
        result, nextRegs, after, bodyRun, ?_⟩
      have consumedTotal : used + consumed ≤ bs.length := by
        simp only [List.length_drop] at consumedBound
        omega
      have remainder : (bs.drop used).drop consumed = bs.drop (used + consumed) := by simp only [List.drop_drop]
      rw [remainder] at nextInv
      rcases post with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨state, used + consumed, arrayGet, consumedTotal, nextInv, fields.2.2, prefixZero, by intro impossible; cases impossible⟩
      · have inside : state.«have».toNat < 320 := by omega
        obtain ⟨nextSize, nextCount, nextPrefix⟩ := clWrite_initialized (value := 0) sz inside (by decide) prefixValues
        have writePrefix := clWrite_lens_prefix (s := state) (value := 0) inside (by omega)
        change actualLengthPrefix (clWrite state 0) = actualLengthPrefix state ++ [0] at writePrefix
        have writeZero : actualLengthPrefix (clWrite state 0) = List.replicate (clWrite state 0).«have».toNat 0 := by
          rw [writePrefix, prefixZero, nextCount, List.replicate_succ']
        constructor
        · refine ⟨clWrite state 0, used + consumed, by simp, ?_, nextSize, ?_, nextPrefix, consumedTotal, nextInv, writeZero⟩
          · unfold clWrite
            rw [frame]
          · rw [nextCount]
            omega
        · dsimp only [rank]
          simp only [setI_istates_same, Option.getD_some]
          rw [nextCount]
          omega
    · have full : state.«have».toNat = total := by
        have notLess := (not_congr UInt32.lt_iff_toNat_lt).mp more
        rw [sum] at notLess
        omega
      refine ⟨.ok false, regs, setI h zs state, by simpa only [more, decide_false] using condRun,
        state, used, arrayGet, usedBound, bitInv, fields.2.2, prefixZero, by intro _; exact full⟩
  · exact ⟨s, 0, (tcSetI_same hs).symm, rfl, size, haveBound, initialized, by omega,
      by simpa only [List.drop_zero] using B, zeros⟩
  · dsimp only [rank]
    rw [hs]
    simp only [Option.getD_some]
    unfold fuel total
    omega


/-- A zero prefix containing the end-of-block cell takes the actual
missing-end-of-block branch before either payload table is built. -/
theorem clTail_zero_prefix {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs))
    (hz : r.get h = some z) (hs : h.istates zs = some s)
    (size : s.lens.size = 320) (mode : s.mode = CODELENS)
    (count : 256 < s.«have».toNat)
    (zeros : actualLengthPrefix s = List.replicate s.«have».toNat 0) :
    ∃ i, runX (clTail c) l h = .ok ((.ok (), l), tcBadHeap h r zs z s i) := by
  have prefixCell := Zlib.Inftrees.Proofs.lensOf_getD (fun k => (s.lens.getD k 0).toNat) count
  change (actualLengthPrefix s).getD 256 0 = (s.lens.getD 256 0).toNat at prefixCell
  rw [zeros] at prefixCell
  have natZero : (s.lens.getD 256 0).toNat = 0 := by
    rw [← prefixCell]
    simp [List.getD_eq_getElem?_getD, count]
  have cellZero : s.lens.getD 256 0 = (0 : UInt16) := UInt16.toNat_inj.mp natZero
  have inside : 0 + 256 < s.lens.size := by omega
  have read := Ptr.index_ok (off := 0) (i := 256) (WRef.get_istate_lens hs) inside
  have read' : Ptr.index (lensP c.st) 256 h = .ok ((0 : UInt16), h) := by
    rw [hc]
    change OkOn h ((Ptr.ref (WRef.istate_lens zs) 0).index 256) (0 : UInt16)
    have zeroValue : s.lens[0 + 256] = 0 := by simpa [Array.getD, inside] using cellZero
    simpa [zeroValue] using read
  have modeRead : rdS c.st (·.mode) h = .ok (CODELENS, h) := by
    rw [hc, rdI_eq, hs]
    simp only [mode]
  obtain ⟨i, _, badRun⟩ := tcBadMode_run (c := c) "invalid code -- missing end-of-block"
    lit_missing_eob hr hc hz hs
  refine ⟨i, ?_⟩
  have distinct : CODELENS ≠ BAD := by decide
  simp [clTail, runX_bind, runX_lift_ok modeRead, distinct, runX_lift_ok read', runX_lift_ok badRun, runX_pure]

/-- Normal returns from the real empty-root CODELENS mode enter BAD.
Nonnormal outcomes remain unconstrained in this statement.
The explicit count lower bound is a header-origin fact to be derived. -/
theorem inflate_CODELENS_empty_root_rejects {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs))
    (hz : r.get h = some z) (hs : h.istates zs = some s)
    (size : s.lens.size = 320) (mode : s.mode = CODELENS) (stateInv : CodeLengthInvariant zs s)
    (root : s.lenbits.toNat = 1) (first : s.codes[0]? = some (⟨64, 1, 0⟩ : Code))
    (second : s.codes[1]? = some (⟨64, 1, 0⟩ : Code))
    (lower : 257 ≤ s.nlen.toNat + s.ndist.toNat)
    (zeros : actualLengthPrefix s = List.replicate s.«have».toNat 0) (B : BitInv h l bs) :
    ∃ outcome regs after, runX (inflate_CODELENS c) l h = .ok ((outcome, regs), after) ∧
      ∀ state, after.istates zs = some state → outcome = .ok () → state.mode = BAD := by
  obtain ⟨outcome, regs, after, state, used, readRun, stateGet, _bound, _inv, currentMode, prefixZero, fullCount⟩ :=
    clRead_empty_root hc hs size mode stateInv root first second zeros B
  obtain ⟨other, otherRegs, otherHeap, sameRun, full, _cursor⟩ :=
    clRead_run_full_cursor hr hc hz hs size mode stateInv B
  rw [readRun] at sameRun
  cases sameRun
  cases outcome with
  | error exit =>
    refine ⟨.error exit, regs, after, ?_, ?_⟩
    · rw [inflate_CODELENS_eq, runX_bind, readRun]
    · intro _ _ impossible
      cases impossible
  | ok done =>
    cases done
    obtain ⟨finalState, _used, finalGet, _bound, _inv, _shape, _bits, _frame, finalSize, _count, _prefix, _modes, _full⟩ := full.1
    have sameState : finalState = state := Option.some.inj (finalGet.symm.trans stateGet)
    subst finalState
    obtain ⟨currentStream, streamGet, _streamFrame, _heapFrame⟩ := full.2
    have count : 256 < state.«have».toNat := by have countEq := fullCount rfl; omega
    obtain ⟨i, tailRun⟩ := clTail_zero_prefix hr hc streamGet stateGet finalSize currentMode count prefixZero
    refine ⟨.ok (), regs, tcBadHeap after r zs currentStream state i, ?_, ?_⟩
    · rw [inflate_CODELENS_eq, runX_bind, readRun]
      exact tailRun
    · intro final finalGet _
      have badGet : (tcBadHeap after r zs currentStream state i).istates zs = some { state with mode := BAD } := by simp [tcBadHeap]
      have same : final = { state with mode := BAD } := Option.some.inj (finalGet.symm.trans badGet)
      rw [same]



/-- The real count writes cannot wrap the five-bit field additions. -/
theorem tableCounts_symbol_lower (s : InflateState) (hold : UInt64) :
    257 ≤ (tableCounts s hold).nlen.toNat ∧
    1 ≤ (tableCounts s hold).ndist.toNat := by
  have first : (hold.toUInt32 &&& 31).toNat ≤ 31 := by
    rw [UInt32.toNat_and]
    exact Nat.and_le_right
  have second : ((hold >>> 5).toUInt32 &&& 31).toNat ≤ 31 := by
    rw [UInt32.toNat_and]
    exact Nat.and_le_right
  constructor
  · change 257 ≤ ((hold.toUInt32 &&& 31) + 257).toNat
    rw [UInt32.toNat_add]
    change 257 ≤ (_ + 257) % 2 ^ 32
    omega
  · change 1 ≤ (((hold >>> 5).toUInt32 &&& 31) + 1).toNat
    rw [UInt32.toNat_add]
    change 1 ≤ (_ + 1) % 2 ^ 32
    omega



/-- The actual successful constructor record starts with an empty prefix;
its header-count expressions also supply the needed EOB index lower bound. -/
theorem llOkSt_tableCounts_empty_prefix (zs : Nat) (s : InflateState) (hold : UInt64)
    (used : Nat) (root : UInt32) (work : Array UInt16) (codes : Array Code) :
    let state := llOkSt zs (tableCounts s hold) used root work codes
    257 ≤ state.nlen.toNat + state.ndist.toNat ∧
    actualLengthPrefix state = List.replicate state.«have».toNat 0 := by
  dsimp only
  constructor
  · have lower := tableCounts_symbol_lower s hold
    change 257 ≤ (tableCounts s hold).nlen.toNat + (tableCounts s hold).ndist.toNat
    omega
  · simp [actualLengthPrefix, llOkSt, Zlib.Inftrees.Proofs.lensOf]



#print axioms clReadBody_empty_root
#print axioms clRead_empty_root
#print axioms clTail_zero_prefix
#print axioms inflate_CODELENS_empty_root_rejects
#print axioms tableCounts_symbol_lower
#print axioms llOkSt_tableCounts_empty_prefix
end Zlib.Inflate.Proofs
