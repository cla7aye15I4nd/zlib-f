import ZlibF.Proof.«uncompr.c.inflate-pause-basic»
import ZlibF.Proof.«uncompr.c.inflate-pause-data»

namespace Zlib.Uncompr.Proof.InflatePause
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

private def ClReadPause (h : Heap) (r : ZStreamRef) (z : ZStream) (zs : Nat)
    (s : InflateState) (l : IL) (bs : List UInt8)
    (outcome : Except Ex Unit) (regs : IL) (after : Heap) : Prop :=
  ClReadResultFull h r z zs s l bs outcome regs after ∧
  (outcome = .error Ex.leave → ∃ state, after.istates zs = some state ∧ state.mode = CODELENS)

/-- The actual code-length reader can leave only while retaining CODELENS.
Malformed-repeat BAD writes break the loop normally. -/
private theorem clRead_pause_cursor {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs))
    (hz : r.get h = some z) (hs : h.istates zs = some s)
    (size : s.lens.size = 320) (mode : s.mode = CODELENS)
    (stateInv : CodeLengthInvariant zs s) (B : BitInv h l bs) :
    ∃ outcome regs after, runX (clRead c) l h = .ok ((outcome, regs), after) ∧
      ClReadPause h r z zs s l bs outcome regs after ∧
      ∃ used, used ≤ bs.length ∧ BitInv after regs (bs.drop used) ∧
        regs.next = inputAdvance l.next used ∧ regs.bits.toNat ≤ l.bits.toNat + 8 * used := by
  obtain ⟨pointer, table, nlen, ndist, haveBound, initialized⟩ := stateInv mode
  let total := s.nlen.toNat + s.ndist.toNat
  let P : IL → Heap → Prop := fun regs heap => ∃ state used,
    heap = setI h zs state ∧
    state = { s with lens := state.lens, «have» := state.«have» } ∧
    state.lens.size = 320 ∧ state.«have».toNat ≤ total ∧
    (∀ k, k < state.«have».toNat → (state.lens.getD k 0).toNat ≤ 15) ∧
    used ≤ bs.length ∧ BitInv heap regs (bs.drop used) ∧ ClRegShape l regs ∧
    regs.bits.toNat ≤ max l.bits.toNat 21 ∧ regs.next = inputAdvance l.next used ∧
      regs.bits.toNat ≤ l.bits.toNat + 8 * used
  let rank : IL → Heap → Nat := fun _ heap => total - ((heap.istates zs).getD default).«have».toNat
  have loop := xwhileBrk_rank (cond := clReadCond c) (body := clReadBody c) P rank
    (fun outcome regs after => ClReadPause h r z zs s l bs outcome regs after ∧
      ∃ used, used ≤ bs.length ∧ BitInv after regs (bs.drop used) ∧
        regs.next = inputAdvance l.next used ∧ regs.bits.toNat ≤ l.bits.toNat + 8 * used) ?_ (l := l) (h := h) ?_ ?_
  · rw [clRead_eq]
    exact loop
  · intro regs heap inv
    obtain ⟨state, used, heapEq, frame, sz, count, prefixValues, usedBound, bitInv, regFrame, bitBound, cursor, budget⟩ := inv
    subst heap
    have get : (setI h zs state).istates zs = some state := by simp
    have stream : r.get (setI h zs state) = some z := by simpa using hz
    have fields : state.nlen = s.nlen ∧ state.ndist = s.ndist ∧ state.mode = CODELENS := by
      rw [frame]
      exact ⟨rfl, rfl, mode⟩
    have sum : (state.nlen + state.ndist).toNat = total := by
      rw [fields.1, fields.2.1, UInt32.toNat_add, Nat.mod_eq_of_lt (by omega)]
    have currentInv : CodeLengthInvariant zs state := by
      intro _
      refine ⟨?_, ?_, ?_, ?_, ?_, prefixValues⟩
      · rw [frame]; exact pointer
      · rw [frame]; exact table
      · rw [fields.1]; exact nlen
      · rw [fields.2.1]; exact ndist
      · rw [fields.1, fields.2.1]; exact count
    have condRun : runX (clReadCond c) regs (setI h zs state) =
        .ok ((.ok (decide (state.«have» < state.nlen + state.ndist)), regs), setI h zs state) := by
      unfold clReadCond
      rw [hc]
      simp [runX_bind, runX_lift, ldI_eq, get, runX_pure]
    by_cases more : state.«have» < state.nlen + state.ndist
    · have moreNat : state.«have».toNat < state.nlen.toNat + state.ndist.toNat := by
        have := UInt32.lt_iff_toNat_lt.mp more
        rw [sum] at this
        rw [fields.1, fields.2.1]
        exact this
      obtain ⟨result, nextRegs, after, consumed, bodyRun, consumedBound, nextInv, nextFrame, nextBits, post, stepCursor, stepBudget⟩ :=
        clReadBody_run_cursor hr hc stream get sz fields.2.2 currentInv moreNat bitInv
      refine ⟨.ok true, regs, setI h zs state, by simpa only [more, decide_true] using condRun,
        result, nextRegs, after, bodyRun, ?_⟩
      have consumedTotal : used + consumed ≤ bs.length := by
        simp only [List.length_drop] at consumedBound
        omega
      have nextInput : BitInv after nextRegs (bs.drop (used + consumed)) := by
        simpa only [List.drop_drop, Nat.add_comm] using nextInv
      have nextCursor : nextRegs.next = inputAdvance l.next (used + consumed) := by
        rw [stepCursor, cursor, inputAdvance_add]
      have nextBudget : nextRegs.bits.toNat ≤ l.bits.toNat + 8 * (used + consumed) := by omega
      have nextShape := regFrame.trans nextFrame
      have nextBound : nextRegs.bits.toNat ≤ max l.bits.toNat 21 := by omega
      cases result with
      | error fault =>
        have same : after = setI h zs state := post
        subst after
        refine ⟨?_, used + consumed, consumedTotal, nextInput, nextCursor, nextBudget⟩
        constructor
        ·
          constructor
          · refine ⟨state, used + consumed, get, consumedTotal, nextInput, nextShape, nextBound,
              ?_, sz, count, prefixValues, Or.inl fields.2.2, ?_⟩
            · rw [frame]
            · intro impossible; cases impossible
          · exact ⟨z, stream, rfl, state, by rw [ZStreamRef.put_self hz]⟩
        · intro _
          exact ⟨state, get, fields.2.2⟩
      | ok decision =>
        cases decision with
        | false =>
          obtain ⟨nextState, afterEq, writeFrame, nextSize, nextCount, progress, nextPrefix⟩ := post
          subst after
          constructor
          · refine ⟨nextState, used + consumed, by simp, ?_, nextSize, ?_, nextPrefix,
              consumedTotal, ?_, nextShape, nextBound, nextCursor, nextBudget⟩
            · rw [writeFrame, frame]
            · rw [fields.1, fields.2.1] at nextCount
              exact nextCount
            · simpa only [setI_setI] using nextInput
          · dsimp only [rank]
            simp only [setI_istates_same, Option.getD_some]
            rw [fields.1, fields.2.1] at nextCount
            omega
        | true =>
          obtain ⟨i, _, afterEq⟩ := post
          subst after
          have badGet : (tcBadHeap (setI h zs state) r zs z state i).istates zs =
              some { state with mode := BAD } := by simp [tcBadHeap]
          refine ⟨?_, used + consumed, consumedTotal, nextInput, nextCursor, nextBudget⟩
          constructor
          ·
            constructor
            · refine ⟨{ state with mode := BAD }, used + consumed, badGet, consumedTotal,
                nextInput, nextShape, nextBound, ?_, sz, count, prefixValues, Or.inr rfl,
                fun _ => Or.inl rfl⟩
              rw [frame]
            · refine ⟨{ z with msg := .ref (.str i) 0 }, ?_, rfl, { state with mode := BAD }, ?_⟩
              · simp [tcBadHeap, hz]
              · simp [tcBadHeap, ZStreamRef.put_setI, setI_setI]
          · intro impossible
            cases impossible
    · have full : state.«have».toNat = total := by
        have notLess := (not_congr UInt32.lt_iff_toNat_lt).mp more
        rw [sum] at notLess
        omega
      refine ⟨.ok false, regs, setI h zs state,
        by simpa only [more, decide_false] using condRun, ?_⟩
      refine ⟨?_, used, usedBound, bitInv, cursor, budget⟩
      constructor
      ·
        constructor
        · refine ⟨state, used, get, usedBound, bitInv, regFrame, bitBound, ?_, sz, count,
            prefixValues, Or.inl fields.2.2, fun _ => Or.inr full⟩
          rw [frame]
        · exact ⟨z, stream, rfl, state, by rw [ZStreamRef.put_self hz]⟩
      · intro impossible
        cases impossible
  · exact ⟨s, 0, (tcSetI_same hs).symm, rfl, size, haveBound, initialized, by omega,
      by simpa only [List.drop_zero] using B, ClRegShape.refl l, by omega, (inputAdvance_zero l.next).symm, by omega⟩
  · dsimp only [rank]
    rw [hs]
    simp only [Option.getD_some]
    unfold fuel total
    omega



/-- An actual construction leave either already has a resumable private
mode, or reaches the real LEN_ continuation with its proved live packet. -/
def ConstructionLeaveCut (c : Ctx) (r : ZStreamRef) (zs : Nat)
    (returned : InflateState) (regs : IL) (after : Heap) : Prop :=
  PauseGood returned ∨ ∃ heap stream state before remaining,
    Env c heap r zs stream state ∧ DefaultStateJ heap r zs stream state ∧
    DispatchBuffers heap r before remaining ∧ state.mode = LEN_ ∧
    runX (inflate_LEN_ c) before heap = .ok ((.error Ex.leave, regs), after)

/-- CODELENS ordinary leaves are actual input waits or the real data
continuation. Rejected code sets and malformed repeats return normally
in BAD; they are not ordinary-leave witnesses. -/
theorem codelens_leave_cut
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = CODELENS)
    (run : runX (inflate_CODELENS c) l h = .ok ((.error Ex.leave, regs), after))
    (get : after.istates zs = some returned) : ConstructionLeaveCut c r zs returned regs after := by
  obtain ⟨outcome, current, middle, zm, sm, used, _bound, read, nextJ, config, packet,
      _sizes, _cursor, _count, _put, _left, _total, _bits, _budget, modes, complete⟩ :=
    clRead_default_state_complete E invariant buffers mode
  cases outcome with
  | error exit =>
    have actual : runX (clRead c) l h = .ok ((.error Ex.leave, regs), after) := by
      have source := run
      rw [inflate_CODELENS_eq, runX_bind] at source
      rw [show runX (clRead c) l h = .ok ((.error exit, current), middle) from read] at source
      cases source
      assumption
    obtain ⟨observed, re, he, source, post, _rest⟩ := clRead_pause_cursor E.strm E.st E.hz E.hs
      invariant.good.inv.wf.1 mode invariant.lengths buffers.bits
    have same := Except.ok.inj (source.symm.trans actual)
    cases same
    obtain ⟨state, live, code⟩ := post.2 rfl
    have same : state = returned := Option.some.inj (live.symm.trans get)
    left
    rw [←same]
    simp only [PauseGood, code]
    decide +kernel
  | ok done =>
    cases done
    have source : runX (inflate_CODELENS c) l h = runX (clTail c) current middle := by
      rw [inflate_CODELENS_eq, runX_bind, read]
    have env : Env c middle r zs zm sm := ⟨E.strm, E.st, nextJ.good.live.hz, nextJ.good.live.hs⟩
    have done : sm.mode = CODELENS → sm.«have».toNat = sm.nlen.toNat + sm.ndist.toNat := by
      intro code
      rcases complete rfl with bad | full
      · rw [code] at bad; cases bad
      · exact full
    have format : sm.wrap = 0 ∨ sm.flags = 0 := by
      rw [config.2.2.1, config.2.2.2]
      exact invariant.construction_format (Or.inr (Or.inr mode))
    rcases clTail_default_state env nextJ packet modes.symm done format with bad | ready
    · obtain ⟨ret, heap, stream, state, stopped, _rest⟩ := bad
      have impossible := xrun_outcome_eq (source.trans stopped) run
      cases impossible
    · obtain ⟨heap, state, finalJ, _config, active, finalPacket, _sizes, _static, tail⟩ := ready
      by_cases trees : c.flush = Z_TREES
      · rw [ite_eq_left trees] at tail
        have same := xrun_state_eq (source.trans tail) run finalJ.good.live.hs get
        left
        rw [←same]
        simp only [PauseGood, active]
        decide +kernel
      · rw [ite_eq_right trees] at tail
        right
        exact ⟨heap, zm, state, { current with ret := 0 }, bs.drop used,
          ⟨E.strm, E.st, finalJ.good.live.hz, finalJ.good.live.hs⟩, finalJ,
          finalPacket, active, (source.trans tail).symm.trans run⟩

/-- The actual length header pauses only before its CODES constructor. -/
private theorem lenlens_pause_entry {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = LENLENS) :
    ∃ regs after stream state used, used ≤ bs.length ∧ DefaultStateJ after r zs stream state ∧
      DefaultConfigFrame s state ∧
      DispatchBuffers after r regs (bs.drop used) ∧ ByteViewSizes h after ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = l.put ∧ regs.left = l.left ∧ regs.out_ = l.out_ ∧
      regs.bits.toNat ≤ max l.bits.toNat 10 ∧ regs.bits.toNat ≤ l.bits.toNat + 8 * used ∧
      ((∃ outcome, runX (inflate_LENLENS c) l h = .ok ((outcome, regs), after) ∧
          ((outcome = .error Ex.leave ∧ state.mode = LENLENS) ∨ (outcome = .ok () ∧ state.mode = BAD))) ∨
       (state.mode = CODELENS ∧ runX (inflate_LENLENS c) l h = runX (inflate_CODELENS c) regs after)) := by
  have format := invariant.construction_format (Or.inr (Or.inl mode))
  obtain ⟨ncode, haveBound, nlen, ndist, prefixValues⟩ := invariant.headerLengths mode
  obtain ⟨regs, used, bound, inv, streamBits, shape, wait, full, cursor, bits, prefixExit, read⟩ :=
    inflate_LENLENS_table_cursor E.strm E.st E.hz E.hs invariant.good.inv.wf ncode haveBound prefixValues buffers.bits
  let m := min (s.ncode.toNat - s.«have».toNat) ((Zlib.Inflate.Proofs.stream l bs).length / 3)
  have mBound : m ≤ s.ncode.toNat - s.«have».toNat := Nat.min_le_left _ _
  have count : regs.have_.toNat + used = l.have_.toNat := by
    rw [inv.have_eq, buffers.bits.have_eq, List.length_drop]
    omega
  have put : regs.put = l.put := by rw [shape]
  have left : regs.left = l.left := by rw [shape]
  have total : regs.out_ = l.out_ := by rw [shape]
  have budget : regs.bits.toNat ≤ l.bits.toNat + 8 * used := by
    have shorter : (Zlib.Inflate.Proofs.stream regs (bs.drop used)).length ≤
        (Zlib.Inflate.Proofs.stream l bs).length := by rw [streamBits, List.length_drop]; omega
    rw [tcStream_length inv, tcStream_length buffers.bits, List.length_drop] at shorter
    omega
  by_cases short : m < s.ncode.toNat - s.«have».toNat
  · obtain ⟨_, _, _, run⟩ := wait short
    obtain ⟨exit2, regs2, heap2, state2, used2, bound2, read2, nextJ,
      packet, sizes, _, count2, _, _, _, _, _⟩ := ll1_default_J E invariant.toDefaultDecodeJ buffers mode
    rw [read] at read2
    cases read2
    have sameUse : used2 = used := by omega
    subst used2
    have config : DefaultConfigFrame s state2 := by
      have get := nextJ.good.live.hs
      rw [setI_istates_same] at get
      rw [← Option.some.inj get]
      simp only [DefaultConfigFrame, llSt, and_self, eq_self]
    have nextState := invariant.config_update nextJ config format
    have sameMode : state2.mode = LENLENS := by
      have get := nextJ.good.live.hs
      rw [setI_istates_same] at get
      rw [← Option.some.inj get]
      exact mode
    exact ⟨regs, _, z, state2, used, bound, nextState, config, packet, sizes, cursor, count,
      put, left, total, bits, budget, Or.inl ⟨.error Ex.leave, run, Or.inl ⟨rfl, sameMode⟩⟩⟩
  · have complete : m = s.ncode.toNat - s.«have».toNat := by omega
    obtain ⟨ret, work, codes, workSize, codeSize, _, _, kinds, _, accepted, rejected⟩ := full complete
    let filled := llDone s (Zlib.Inflate.Proofs.stream l bs)
    have lensSize : filled.lens.size = 320 := by
      simp only [filled, llDone, lzSt, llSt, lensZero_size, lensRead_size]
      exact invariant.good.inv.wf.1
    rcases kinds with success | failure
    · obtain ⟨usedCodes, root, capacity, safe, run⟩ := accepted success
      let state := llOkSt zs filled usedCodes root work codes
      have frame : LengthTableFrame s state := by
        simp only [LengthTableFrame, state, llOkSt, llPre, filled, llDone, lzSt, llSt]
      have wf : state.WellFormed := ⟨lensSize, workSize, codeSize⟩
      have pointers : PtrInv zs state :=
        ⟨⟨usedCodes, rfl, by omega⟩, Or.inl ⟨0, 0, rfl, rfl, by decide, by decide⟩⟩
      have codeInv : CodeLengthInvariant zs state :=
        llOkSt_codeLengthInvariant zs filled usedCodes root work codes safe nlen ndist
      have bitInv : BitInv h { regs with ret := 0 } (bs.drop used) := ⟨inv.have_eq, inv.next, inv.hold_lt⟩
      obtain ⟨nextJ, packet, sizes⟩ := invariant.toDefaultDecodeJ.length_table_packet buffers frame
        (stream := z) (by rfl) wf pointers (Or.inr rfl) codeInv bitInv cursor count put left total
      rw [ZStreamRef.put_self E.hz] at nextJ packet sizes
      have config : DefaultConfigFrame s state := by rw [frame]; exact ⟨rfl, rfl, rfl, rfl⟩
      have nextState := invariant.config_update nextJ config format
      exact ⟨{ regs with ret := 0 }, _, z, state, used, bound, nextState, config, packet, sizes,
        cursor, count, put, left, total, bits, budget, Or.inr ⟨rfl, run⟩⟩
    · obtain ⟨i, _, run⟩ := rejected failure
      let state := { llBadSt zs filled work codes with mode := BAD }
      let stream := { z with msg := .ref (.str i) 0 }
      have frame : LengthTableFrame s state := by
        simp only [LengthTableFrame, state, llBadSt, llPre, filled, llDone, lzSt, llSt]
      have wf : state.WellFormed := ⟨lensSize, workSize, codeSize⟩
      have pointers : PtrInv zs state :=
        ⟨⟨0, rfl, by decide⟩, Or.inl ⟨0, 0, rfl, rfl, by decide, by decide⟩⟩
      have codeInv : CodeLengthInvariant zs state := by
        intro active
        change BAD = CODELENS at active
        exact False.elim ((by decide : BAD ≠ CODELENS) active)
      have bitInv : BitInv h { regs with ret := -1 } (bs.drop used) := ⟨inv.have_eq, inv.next, inv.hold_lt⟩
      obtain ⟨nextJ, packet, sizes⟩ := invariant.toDefaultDecodeJ.length_table_packet buffers frame
        (stream := stream) (by rfl) wf pointers (Or.inl rfl) codeInv bitInv cursor count put left total
      have config : DefaultConfigFrame s state := by rw [frame]; exact ⟨rfl, rfl, rfl, rfl⟩
      have nextState := invariant.config_update nextJ config format
      refine ⟨{ regs with ret := -1 }, _, stream, state, used, bound, nextState, config, packet, sizes,
        cursor, count, put, left, total, bits, budget, Or.inl ⟨.ok (), ?_, Or.inr ⟨rfl, rfl⟩⟩⟩
      simpa only [tcBadHeap, ZStreamRef.put_setI, setI_setI] using run




/-- The actual count header pauses only before its count-field writes. -/
private theorem table_pause_entry {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = TABLE) :
    ∃ regs after stream state used, used ≤ bs.length ∧ DefaultStateJ after r zs stream state ∧
      DefaultConfigFrame s state ∧
      DispatchBuffers after r regs (bs.drop used) ∧ ByteViewSizes h after ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = l.put ∧ regs.left = l.left ∧ regs.out_ = l.out_ ∧
      regs.bits.toNat ≤ max l.bits.toNat 21 ∧ regs.bits.toNat ≤ l.bits.toNat + 8 * used ∧
      ((∃ outcome, runX (inflate_TABLE c) l h = .ok ((outcome, regs), after) ∧
          ((outcome = .error Ex.leave ∧ state.mode = TABLE) ∨ (outcome = .ok () ∧ state.mode = BAD))) ∨
       (state.mode = LENLENS ∧ runX (inflate_TABLE c) l h = runX (inflate_LENLENS c) regs after)) := by
  have format := invariant.construction_format (Or.inl mode)
  obtain ⟨outcome, current, used, pull, bound, inv, _, wait, full⟩ :=
    inflate_TABLE_run E.strm E.st E.hz E.hs buffers.bits
  obtain ⟨outcome2, current2, used2, pull2, bound2, inv2, _, bitCount, shape, bitBound, _, _, _, kinds, cursor⟩ :=
    NEEDBITS_run_cursor buffers.bits 14 (by decide)
  rw [pull] at pull2
  cases pull2
  have sameUse : used2 = used := by
    have one := inv.have_eq
    have two := inv2.have_eq
    rw [List.length_drop] at one two
    omega
  subst used2
  change current.bits.toNat ≤ max l.bits.toNat 21 at bitBound
  have count : current.have_.toNat + used = l.have_.toNat := by
    rw [inv.have_eq, buffers.bits.have_eq, List.length_drop]
    omega
  have put : current.put = l.put := by rw [shape]
  have left : current.left = l.left := by rw [shape]
  have total : current.out_ = l.out_ := by rw [shape]
  rcases kinds with normal | leaves
  · obtain ⟨enough, dropInv, _, badRun, readyRun⟩ := full normal
    have dropCount : (tableRegs current).bits.toNat = current.bits.toNat - 14 := by
      change (current.bits - 14).toNat = _
      exact UInt32.toNat_sub_of_le _ _ (by apply UInt32.le_iff_toNat_le.mpr; exact enough)
    have bits : (tableRegs current).bits.toNat ≤ max l.bits.toNat 21 := by rw [dropCount]; omega
    have budget : (tableRegs current).bits.toNat ≤ l.bits.toNat + 8 * used := by rw [dropCount]; omega
    by_cases invalid : (tableCounts s current.hold).nlen > 286 ∨ (tableCounts s current.hold).ndist > 30
    · obtain ⟨i, _, run⟩ := badRun invalid
      let state := { tableCounts s current.hold with mode := BAD }
      let stream := { z with msg := .ref (.str i) 0 }
      have frame : TableCountsFrame s state := by rfl
      have lengths : LengthHeaderInvariant state := by
        intro active
        change BAD = LENLENS at active
        exact False.elim ((by decide : BAD ≠ LENLENS) active)
      have nextJ := invariant.toDefaultDecodeJ.counts_update frame (stream := stream) (by rfl) (Or.inl rfl) lengths
      obtain ⟨packet, sizes⟩ := buffers.metadata_advance invariant.good nextJ.good rfl dropInv
        cursor count put left total
      have config : DefaultConfigFrame s state := by rw [frame]; exact ⟨rfl, rfl, rfl, rfl⟩
      have nextState := invariant.config_update nextJ config format
      refine ⟨tableRegs current, _, stream, state, used, bound, nextState, config, packet, sizes,
        cursor, count, put, left, total, bits, budget, Or.inl ⟨.ok (), ?_, Or.inr ⟨rfl, rfl⟩⟩⟩
      exact run
    · let state := { tableCounts s current.hold with «have» := 0, mode := LENLENS }
      have frame : TableCountsFrame s state := by rfl
      have lengths : LengthHeaderInvariant state := tableCounts_header_invariant s current.hold invalid
      have nextJ := invariant.toDefaultDecodeJ.counts_update frame (stream := z) (by rfl) (Or.inr rfl) lengths
      obtain ⟨packet, sizes⟩ := buffers.metadata_advance invariant.good nextJ.good rfl dropInv
        cursor count put left total
      rw [ZStreamRef.put_self E.hz] at nextJ packet sizes
      have config : DefaultConfigFrame s state := by rw [frame]; exact ⟨rfl, rfl, rfl, rfl⟩
      have nextState := invariant.config_update nextJ config format
      exact ⟨tableRegs current, _, z, state, used, bound, nextState, config, packet, sizes,
        cursor, count, put, left, total, bits, budget, Or.inr ⟨rfl, readyRun invalid⟩⟩
  · obtain ⟨_, _, _, run⟩ := wait leaves
    have packet : DispatchBuffers h r current (bs.drop used) :=
      buffers.consume invariant.good invariant.good rfl (fun _ => rfl) (fun _ => rfl)
        (by rw [shape]; rfl) cursor bound inv
    exact ⟨current, h, z, s, used, bound, invariant, ⟨rfl, rfl, rfl, rfl⟩, packet, ByteViewSizes.refl h,
      cursor, count, put, left, total, bitBound, by omega, Or.inl ⟨.error Ex.leave, run, Or.inl ⟨rfl, mode⟩⟩⟩



/-- The actual LENLENS wait retains that mode; successful construction
continues through the actual CODELENS source on its proved returned state. -/
theorem lenlens_leave_cut
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = LENLENS)
    (run : runX (inflate_LENLENS c) l h = .ok ((.error Ex.leave, regs), after))
    (get : after.istates zs = some returned) : ConstructionLeaveCut c r zs returned regs after := by
  obtain ⟨current, middle, zm, sm, used, _bound, nextJ, _config, packet,
      _sizes, _cursor, _count, _put, _left, _total, _bits, _budget, cases⟩ :=
    lenlens_pause_entry E invariant buffers mode
  rcases cases with ⟨outcome, source, selected⟩ | ⟨active, source⟩
  · have outcomeEq := xrun_outcome_eq source run
    rcases selected with ⟨_leave, paused⟩ | ⟨normal, _bad⟩
    · have same := xrun_state_eq source run nextJ.good.live.hs get
      left
      rw [←same]
      simp only [PauseGood, paused]
      decide +kernel
    · cases normal.symm.trans outcomeEq
  · exact codelens_leave_cut ⟨E.strm, E.st, nextJ.good.live.hz, nextJ.good.live.hs⟩
      nextJ packet active (source.symm.trans run) get

/-- The actual TABLE wait retains that mode; accepted counts continue
through both real dynamic alphabet constructors. -/
theorem table_leave_cut
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = TABLE)
    (run : runX (inflate_TABLE c) l h = .ok ((.error Ex.leave, regs), after))
    (get : after.istates zs = some returned) : ConstructionLeaveCut c r zs returned regs after := by
  obtain ⟨current, middle, zm, sm, used, _bound, nextJ, _config, packet,
      _sizes, _cursor, _count, _put, _left, _total, _bits, _budget, cases⟩ :=
    table_pause_entry E invariant buffers mode
  rcases cases with ⟨outcome, source, selected⟩ | ⟨active, source⟩
  · have outcomeEq := xrun_outcome_eq source run
    rcases selected with ⟨_leave, paused⟩ | ⟨normal, _bad⟩
    · have same := xrun_state_eq source run nextJ.good.live.hs get
      left
      rw [←same]
      simp only [PauseGood, paused]
      decide +kernel
    · cases normal.symm.trans outcomeEq
  · exact lenlens_leave_cut ⟨E.strm, E.st, nextJ.good.live.hz, nextJ.good.live.hs⟩
      nextJ packet active (source.symm.trans run) get

/-- Every actual construction dispatch leave has a resumable prefix mode
or a proved concrete LEN_ continuation. No data-callee contract is assumed. -/
theorem construction_leave_cut
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs)
    (mode : s.mode = TABLE ∨ s.mode = LENLENS ∨ s.mode = CODELENS)
    (run : runX (inflate_dispatch c) l h = .ok ((.error Ex.leave, regs), after))
    (get : after.istates zs = some returned) : ConstructionLeaveCut c r zs returned regs after := by
  rcases mode with table | lengths | codes
  · rw [inflate_dispatch_TABLE E l table] at run
    exact table_leave_cut E invariant buffers table run get
  · rw [inflate_dispatch_LENLENS E l lengths] at run
    exact lenlens_leave_cut E invariant buffers lengths run get
  · rw [inflate_dispatch_CODELENS E l codes] at run
    exact codelens_leave_cut E invariant buffers codes run get

/-- The actual dynamic-construction chain leaves only in resumable modes.
Input waits retain TABLE, LENLENS or CODELENS. A completed alphabet uses
the proved actual LEN_ data continuation. No callee contract is assumed;
BAD constructor and repeat branches return normally before dispatch. -/
theorem construction_leave_pause
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs)
    (mode : s.mode = TABLE ∨ s.mode = LENLENS ∨ s.mode = CODELENS)
    (run : runX (inflate_dispatch c) l h = .ok ((.error Ex.leave, regs), after))
    (get : after.istates zs = some returned) : PauseGood returned := by
  rcases construction_leave_cut E invariant buffers mode run get with paused | continued
  · exact paused
  · obtain ⟨heap, stream, state, before, remaining, env, current, packet, active, actual⟩ := continued
    exact len_start_leave_pause env current packet active actual get

end Zlib.Uncompr.Proof.InflatePause
