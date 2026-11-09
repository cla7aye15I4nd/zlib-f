import ZlibF.Proof.«inflate.c.code-length-body-meaning»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec
set_option autoImplicit false

/-- The complete actual ordinary-root reading loop terminates. A normal
non-BAD result has an independent CodeLens derivation from the incoming
prefix and input to the returned prefix and remaining real bits. Waiting
and BAD results remain actual outcomes; this theorem makes no completed
parse claim about them. -/
theorem clRead_ordinary_parser_complete {c : Ctx} {l : IL} {h : Heap}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8} {alphabet : List Nat}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs))
    (hz : r.get h = some z) (hs : h.istates zs = some s)
    (size : s.lens.size = 320) (mode : s.mode = CODELENS) (stateInv : CodeLengthInvariant zs s)
    (contents : Zlib.Inftrees.Proofs.CodeLengthContents s.codes 0 s.lenbits.toNat alphabet)
    (ordinaryRoot : ∀ index, index < 2 ^ s.lenbits.toNat →
      ∃ entry, s.codes[index]? = some entry ∧ entry.op = 0)
    (B : BitInv h l bs) :
    ∃ outcome regs after, runX (clRead c) l h = .ok ((outcome, regs), after) ∧
      ∀ state, outcome = .ok () → after.istates zs = some state → state.mode ≠ BAD →
        ∃ used, used ≤ bs.length ∧ BitInv after regs (bs.drop used) ∧
          CodeLens alphabet (s.nlen.toNat + s.ndist.toNat) (actualLengthPrefix s) (stream l bs)
            (stream regs (bs.drop used)) (actualLengthPrefix state) := by
  obtain ⟨pointer, table, nlen, ndist, haveBound, initialized⟩ := stateInv mode
  let total := s.nlen.toNat + s.ndist.toNat
  let P : IL → Heap → Prop := fun regs heap => ∃ state used,
    heap = setI h zs state ∧ state = { s with lens := state.lens, «have» := state.«have» } ∧
    state.lens.size = 320 ∧ state.«have».toNat ≤ total ∧
    (∀ k, k < state.«have».toNat → (state.lens.getD k 0).toNat ≤ 15) ∧
    used ≤ bs.length ∧ BitInv heap regs (bs.drop used) ∧
    LengthParserStep alphabet total s (stream l bs) state (stream regs (bs.drop used))
  let rank : IL → Heap → Nat := fun _ heap => total - ((heap.istates zs).getD default).«have».toNat
  let Q : Except Ex Unit → IL → Heap → Prop := fun outcome regs after =>
    ∀ state, outcome = .ok () → after.istates zs = some state → state.mode ≠ BAD →
      ∃ used, used ≤ bs.length ∧ BitInv after regs (bs.drop used) ∧
        CodeLens alphabet total (actualLengthPrefix s) (stream l bs)
          (stream regs (bs.drop used)) (actualLengthPrefix state)
  have loop := xwhileBrk_rank (cond := clReadCond c) (body := clReadBody c) P rank Q ?_ (l := l) (h := h) ?_ ?_
  · rw [clRead_eq]
    exact loop
  · intro regs heap inv
    obtain ⟨state, used, heapEq, frame, sz, count, prefixValues, usedBound, bitInv, parsed⟩ := inv
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
    have currentRoot : ∀ index, index < 2 ^ state.lenbits.toNat →
        ∃ entry, state.codes[index]? = some entry ∧ entry.op = 0 := by
      rw [frame]
      exact ordinaryRoot
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
      obtain ⟨result, nextRegs, after, consumed, bodyRun, consumedBound, nextInv, _shape, _bits, post, _cursor, _budget⟩ :=
        clReadBody_run_cursor hr hc currentStream get sz fields.2.2 currentInv moreNat bitInv
      refine ⟨.ok true, regs, setI h zs state, by simpa only [more, decide_true] using condRun,
        result, nextRegs, after, bodyRun, ?_⟩
      cases result with
      | error exit =>
        intro final impossible
        cases impossible
      | ok decision =>
        cases decision with
        | true =>
          obtain ⟨index, _literal, rejected⟩ := post
          intro final _ getFinal notBad
          have badGet : after.istates zs = some { state with mode := BAD } := by rw [rejected]; simp [tcBadHeap]
          have same : final = { state with mode := BAD } := Option.some.inj (getFinal.symm.trans badGet)
          exact False.elim (notBad (by rw [same]))
        | false =>
          obtain ⟨nextState, afterEq, writeFrame, nextSize, nextCount, progress, nextPrefix⟩ := post
          obtain ⟨semanticUsed, semanticState, semanticBound, semanticHeap, semanticInv, step⟩ :=
            clReadBody_parser_step hr hc currentStream get sz fields.2.2 currentInv currentContents currentRoot moreNat bitInv bodyRun
          have semanticGet : after.istates zs = some semanticState := by rw [semanticHeap]; simp
          have nextGet : after.istates zs = some nextState := by rw [afterEq]; simp
          have sameState : semanticState = nextState := Option.some.inj (semanticGet.symm.trans nextGet)
          subst semanticState
          have sameUsed : semanticUsed = consumed := by
            have a := semanticInv.have_eq
            have b := nextInv.have_eq
            simp only [List.length_drop] at a b semanticBound consumedBound
            omega
          subst semanticUsed
          have consumedTotal : used + consumed ≤ bs.length := by
            simp only [List.length_drop] at consumedBound
            omega
          have remainder : (bs.drop used).drop consumed = bs.drop (used + consumed) := by simp only [List.drop_drop]
          rw [totalEq, remainder] at step
          have nextParsed := parsed.trans step
          rw [remainder] at nextInv
          subst after
          constructor
          · refine ⟨nextState, used + consumed, by simp, ?_, nextSize, ?_, nextPrefix,
              consumedTotal, ?_, nextParsed⟩
            · rw [writeFrame, frame]
            · rw [totalEq] at nextCount
              exact nextCount
            · simpa only [setI_setI] using nextInv
          · dsimp only [rank]
            simp only [setI_istates_same, Option.getD_some]
            rw [totalEq] at nextCount
            omega
    · have full : state.«have».toNat = total := by
        have notLess := (not_congr UInt32.lt_iff_toNat_lt).mp more
        rw [sum] at notLess
        omega
      refine ⟨.ok false, regs, setI h zs state, by simpa only [more, decide_false] using condRun, ?_⟩
      intro final _ getFinal _
      have same : final = state := Option.some.inj (getFinal.symm.trans get)
      subst final
      exact ⟨used, usedBound, bitInv, parsed.complete full⟩
  · exact ⟨s, 0, (tcSetI_same hs).symm, rfl, size, haveBound, initialized, by omega,
      by simpa only [List.drop_zero] using B, by simpa only [List.drop_zero] using LengthParserStep.refl alphabet total s (stream l bs)⟩
  · dsimp only [rank]
    rw [hs]
    simp only [Option.getD_some]
    unfold fuel total
    omega

/-- The actual complete reader retains its original safety/frame/cursor
result and the independent normal-completion meaning on that same run.
The final state and input cursor are supplied by the actual callee result. -/
theorem clRead_ordinary_format {c : Ctx} {l : IL} {h : Heap}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8} {alphabet : List Nat}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs))
    (hz : r.get h = some z) (hs : h.istates zs = some s)
    (size : s.lens.size = 320) (mode : s.mode = CODELENS) (stateInv : CodeLengthInvariant zs s)
    (contents : Zlib.Inftrees.Proofs.CodeLengthContents s.codes 0 s.lenbits.toNat alphabet)
    (ordinaryRoot : ∀ index, index < 2 ^ s.lenbits.toNat →
      ∃ entry, s.codes[index]? = some entry ∧ entry.op = 0)
    (B : BitInv h l bs) :
    ∃ outcome regs after state used,
      runX (clRead c) l h = .ok ((outcome, regs), after) ∧
      ClReadResultFull h r z zs s l bs outcome regs after ∧
      after.istates zs = some state ∧ used ≤ bs.length ∧ BitInv after regs (bs.drop used) ∧
      (outcome = .ok () → state.mode ≠ BAD →
        CodeLens alphabet (s.nlen.toNat + s.ndist.toNat) (actualLengthPrefix s) (stream l bs)
          (stream regs (bs.drop used)) (actualLengthPrefix state)) := by
  obtain ⟨outcome, regs, after, run, full, _cursor⟩ :=
    clRead_run_full_cursor hr hc hz hs size mode stateInv B
  obtain ⟨outcome2, regs2, after2, run2, semantic⟩ :=
    clRead_ordinary_parser_complete hr hc hz hs size mode stateInv contents ordinaryRoot B
  rw [run] at run2
  cases run2
  obtain ⟨state, used, get, bound, inv, _shape, _bits, _frame, _size, _count, _prefix, _modes, _complete⟩ := full.1
  refine ⟨outcome, regs, after, state, used, run, full, get, bound, inv, ?_⟩
  intro normal notBad
  obtain ⟨used2, bound2, inv2, parsed⟩ := semantic state normal get notBad
  have uses : used2 = used := by
    have a := inv.have_eq
    have b := inv2.have_eq
    simp only [List.length_drop] at a b
    omega
  subst used2
  exact parsed

#print axioms clRead_ordinary_format
#print axioms clRead_ordinary_parser_complete
end Zlib.Inflate.Proofs
