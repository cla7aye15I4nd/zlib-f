import ZlibF.Proof.«inflate.c.code-length-body-prefix»
import ZlibF.Proof.«inflate.c.code-length-body-wait»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec
set_option autoImplicit false

/-- The actual ordinary-root reader retains a causal consumed-bit trace on
both completion and waiting. Its trace is valid for every future suffix,
so it does not depend on retaining unread bytes from one caller buffer.
BAD remains an actual outcome with no accepted-parse claim. -/
theorem clRead_ordinary_prefix_trace {c : Ctx} {l : IL} {h : Heap}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8} {alphabet : List Nat}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (hz : r.get h = some z) (hs : h.istates zs = some s)
    (size : s.lens.size = 320) (mode : s.mode = CODELENS) (stateInv : CodeLengthInvariant zs s)
    (contents : Zlib.Inftrees.Proofs.CodeLengthContents s.codes 0 s.lenbits.toNat alphabet)
    (ordinaryRoot : ∀ index, index < 2 ^ s.lenbits.toNat → ∃ entry, s.codes[index]? = some entry ∧ entry.op = 0)
    (B : BitInv h l bs) :
    ∃ outcome regs after state used,
      runX (clRead c) l h = .ok ((outcome, regs), after) ∧
      after.istates zs = some state ∧ used ≤ bs.length ∧ BitInv after regs (bs.drop used) ∧
      (state.mode ≠ BAD → ∃ consumed, stream l bs = consumed ++ stream regs (bs.drop used) ∧
        ZlibF.Math.CodeLengthPrefix.Trace alphabet (s.nlen.toNat + s.ndist.toNat)
          (actualLengthPrefix s) consumed (actualLengthPrefix state)) := by
  obtain ⟨pointer, table, nlen, ndist, haveBound, initialized⟩ := stateInv mode
  let total := s.nlen.toNat + s.ndist.toNat
  let P : IL → Heap → Prop := fun regs heap => ∃ state used consumed,
    heap = setI h zs state ∧ state = { s with lens := state.lens, «have» := state.«have» } ∧
    state.lens.size = 320 ∧ state.«have».toNat ≤ total ∧
    (∀ k, k < state.«have».toNat → (state.lens.getD k 0).toNat ≤ 15) ∧
    used ≤ bs.length ∧ BitInv heap regs (bs.drop used) ∧
    stream l bs = consumed ++ stream regs (bs.drop used) ∧
    ZlibF.Math.CodeLengthPrefix.Trace alphabet total (actualLengthPrefix s) consumed (actualLengthPrefix state)
  let rank : IL → Heap → Nat := fun _ heap => total - ((heap.istates zs).getD default).«have».toNat
  let Q : Except Ex Unit → IL → Heap → Prop := fun _ regs after => ∃ state used,
    after.istates zs = some state ∧ used ≤ bs.length ∧ BitInv after regs (bs.drop used) ∧
    (state.mode ≠ BAD → ∃ consumed, stream l bs = consumed ++ stream regs (bs.drop used) ∧
      ZlibF.Math.CodeLengthPrefix.Trace alphabet total (actualLengthPrefix s) consumed (actualLengthPrefix state))
  have loop := xwhileBrk_rank (cond := clReadCond c) (body := clReadBody c) P rank Q ?_ (l := l) (h := h) ?_ ?_
  · obtain ⟨outcome, regs, after, run, state, used, get, bound, inv, trace⟩ := loop
    exact ⟨outcome, regs, after, state, used, by rw [clRead_eq]; exact run, get, bound, inv, trace⟩
  · intro regs heap inv
    obtain ⟨state, used, consumed, heapEq, frame, sz, count, prefixValues, usedBound, bitInv, source, trace⟩ := inv
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
    have currentContents : Zlib.Inftrees.Proofs.CodeLengthContents state.codes 0 state.lenbits.toNat alphabet := by rw [frame]; exact contents
    have currentRoot : ∀ index, index < 2 ^ state.lenbits.toNat → ∃ entry, state.codes[index]? = some entry ∧ entry.op = 0 := by
      rw [frame]; exact ordinaryRoot
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
      obtain ⟨result, nextRegs, after, usedStep, bodyRun, stepBound, nextInv, _shape, _bits, post, _cursor, _budget⟩ :=
        clReadBody_run_cursor hr hc currentStream get sz fields.2.2 currentInv moreNat bitInv
      have totalBound : used + usedStep ≤ bs.length := by simp only [List.length_drop] at stepBound; omega
      have remainder : (bs.drop used).drop usedStep = bs.drop (used + usedStep) := by simp only [List.drop_drop]
      have nextInput : BitInv after nextRegs (bs.drop (used + usedStep)) := by rw [← remainder]; exact nextInv
      refine ⟨.ok true, regs, setI h zs state, by simpa only [more, decide_true] using condRun,
        result, nextRegs, after, bodyRun, ?_⟩
      cases result with
      | error exit =>
        have heapSame : after = setI h zs state := post
        subst after
        obtain ⟨waitUsed, waitBound, waitInv, streamSame⟩ :=
          clReadBody_wait_stream hr hc currentStream get sz fields.2.2 currentInv moreNat bitInv bodyRun
        have sameUsed : waitUsed = usedStep := by
          have a := waitInv.have_eq
          have b := nextInv.have_eq
          simp only [List.length_drop] at a b waitBound stepBound
          omega
        subst waitUsed
        rw [remainder] at streamSame
        refine ⟨state, used + usedStep, get, totalBound, nextInput, fun _ => ⟨consumed, ?_, trace⟩⟩
        rw [streamSame]
        exact source
      | ok decision =>
        cases decision with
        | true =>
          obtain ⟨index, _literal, rejected⟩ := post
          have badGet : after.istates zs = some { state with mode := BAD } := by rw [rejected]; simp [tcBadHeap]
          exact ⟨{ state with mode := BAD }, used + usedStep, badGet, totalBound, nextInput,
            fun impossible => False.elim (impossible rfl)⟩
        | false =>
          obtain ⟨nextState, afterEq, writeFrame, nextSize, nextCount, progress, nextPrefix⟩ := post
          obtain ⟨traceUsed, traceState, bitsStep, traceBound, traceHeap, traceInv, traceSource, nextTrace⟩ :=
            clReadBody_prefix_trace hr hc currentStream get sz fields.2.2 currentInv currentContents currentRoot moreNat bitInv bodyRun
          have traceGet : after.istates zs = some traceState := by rw [traceHeap]; simp
          have nextGet : after.istates zs = some nextState := by rw [afterEq]; simp
          have sameState : traceState = nextState := Option.some.inj (traceGet.symm.trans nextGet)
          subst traceState
          have sameUsed : traceUsed = usedStep := by
            have a := traceInv.have_eq
            have b := nextInv.have_eq
            simp only [List.length_drop] at a b traceBound stepBound
            omega
          subst traceUsed
          rw [totalEq] at nextTrace
          rw [remainder] at traceSource
          have combined := trace.trans nextTrace
          have combinedSource : stream l bs = (consumed ++ bitsStep) ++ stream nextRegs (bs.drop (used + usedStep)) := by
            rw [List.append_assoc]
            rw [← traceSource]
            exact source
          subst after
          constructor
          · refine ⟨nextState, used + usedStep, consumed ++ bitsStep, by simp, ?_, nextSize, ?_, nextPrefix,
              totalBound, ?_, combinedSource, combined⟩
            · rw [writeFrame, frame]
            · rw [totalEq] at nextCount
              exact nextCount
            · simpa only [setI_setI] using nextInput
          · dsimp only [rank]
            simp only [setI_istates_same, Option.getD_some]
            rw [totalEq] at nextCount
            omega
    · refine ⟨.ok false, regs, setI h zs state, by simpa only [more, decide_false] using condRun,
        state, used, get, usedBound, bitInv, fun _ => ⟨consumed, source, trace⟩⟩
  · exact ⟨s, 0, [], (tcSetI_same hs).symm, rfl, size, haveBound, initialized, by omega,
      by simpa only [List.drop_zero] using B, by simp, ZlibF.Math.CodeLengthPrefix.Trace.refl alphabet total (actualLengthPrefix s)⟩
  · dsimp only [rank]
    rw [hs]
    simp only [Option.getD_some]
    unfold fuel total
    omega

/-- The causal trace, original safety/frame result and exact completed
CodeLens meaning hold on one actual reader call, including waiting outcomes. -/
theorem clRead_ordinary_trace_format {c : Ctx} {l : IL} {h : Heap}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8} {alphabet : List Nat}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (hz : r.get h = some z) (hs : h.istates zs = some s)
    (size : s.lens.size = 320) (mode : s.mode = CODELENS) (stateInv : CodeLengthInvariant zs s)
    (contents : Zlib.Inftrees.Proofs.CodeLengthContents s.codes 0 s.lenbits.toNat alphabet)
    (ordinaryRoot : ∀ index, index < 2 ^ s.lenbits.toNat → ∃ entry, s.codes[index]? = some entry ∧ entry.op = 0)
    (B : BitInv h l bs) :
    ∃ outcome regs after state used,
      runX (clRead c) l h = .ok ((outcome, regs), after) ∧ ClReadResultFull h r z zs s l bs outcome regs after ∧
      after.istates zs = some state ∧ used ≤ bs.length ∧ BitInv after regs (bs.drop used) ∧
      (state.mode ≠ BAD → ∃ consumed, stream l bs = consumed ++ stream regs (bs.drop used) ∧
        ZlibF.Math.CodeLengthPrefix.Trace alphabet (s.nlen.toNat + s.ndist.toNat)
          (actualLengthPrefix s) consumed (actualLengthPrefix state)) ∧
      (outcome = .ok () → state.mode ≠ BAD →
        CodeLens alphabet (s.nlen.toNat + s.ndist.toNat) (actualLengthPrefix s) (stream l bs)
          (stream regs (bs.drop used)) (actualLengthPrefix state)) := by
  obtain ⟨outcome, regs, after, run, full, _cursor⟩ := clRead_run_full_cursor hr hc hz hs size mode stateInv B
  obtain ⟨outcome2, regs2, after2, state2, used2, run2, get2, bound2, inv2, causal⟩ :=
    clRead_ordinary_prefix_trace hr hc hz hs size mode stateInv contents ordinaryRoot B
  rw [run] at run2
  cases run2
  obtain ⟨state, used, get, bound, inv, _shape, _bits, _frame, _size, _count, _prefix, _modes, complete⟩ := full.1
  have states : state2 = state := Option.some.inj (get2.symm.trans get)
  subst state2
  have uses : used2 = used := by
    have a := inv.have_eq
    have b := inv2.have_eq
    simp only [List.length_drop] at a b
    omega
  subst used2
  refine ⟨outcome, regs, after, state, used, run, full, get, bound, inv, causal, ?_⟩
  intro normal notBad
  have finished : state.«have».toNat = s.nlen.toNat + s.ndist.toNat := by
    rcases complete normal with bad | fullCount
    · exact False.elim (notBad bad)
    · exact fullCount
  obtain ⟨consumed, source, trace⟩ := causal notBad
  have parsed := trace.complete (future := stream regs (bs.drop used))
    (by simpa only [actualLengthPrefix, Zlib.Inftrees.Proofs.lensOf_length] using finished)
  rw [← source] at parsed
  exact parsed

/-- Cancel the unchanged unread byte suffix from the actual bit-stream
identity. The ledger mentions only bytes actually pulled into the decoder,
so callers may replace or discard their unread buffer on the next call. -/
theorem clRead_ordinary_consumed_input {c : Ctx} {l : IL} {h : Heap}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8} {alphabet : List Nat}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (hz : r.get h = some z) (hs : h.istates zs = some s)
    (size : s.lens.size = 320) (mode : s.mode = CODELENS) (stateInv : CodeLengthInvariant zs s)
    (contents : Zlib.Inftrees.Proofs.CodeLengthContents s.codes 0 s.lenbits.toNat alphabet)
    (ordinaryRoot : ∀ index, index < 2 ^ s.lenbits.toNat → ∃ entry, s.codes[index]? = some entry ∧ entry.op = 0)
    (B : BitInv h l bs) :
    ∃ outcome regs after state used,
      runX (clRead c) l h = .ok ((outcome, regs), after) ∧ ClReadResultFull h r z zs s l bs outcome regs after ∧
      after.istates zs = some state ∧ used ≤ bs.length ∧ BitInv after regs (bs.drop used) ∧
      (state.mode ≠ BAD → ∃ consumed,
        natBits l.bits.toNat l.hold.toNat ++ bytesBits (bs.take used) = consumed ++ natBits regs.bits.toNat regs.hold.toNat ∧
        ZlibF.Math.CodeLengthPrefix.Trace alphabet (s.nlen.toNat + s.ndist.toNat)
          (actualLengthPrefix s) consumed (actualLengthPrefix state)) := by
  obtain ⟨outcome, regs, after, state, used, run, full, get, bound, inv, causal, _format⟩ :=
    clRead_ordinary_trace_format hr hc hz hs size mode stateInv contents ordinaryRoot B
  refine ⟨outcome, regs, after, state, used, run, full, get, bound, inv, ?_⟩
  intro notBad
  obtain ⟨consumed, source, trace⟩ := causal notBad
  refine ⟨consumed, ?_, trace⟩
  have before : (natBits l.bits.toNat l.hold.toNat ++ bytesBits (bs.take used)) ++ bytesBits (bs.drop used) = stream l bs := by
    rw [List.append_assoc, ← bytesBits_append, List.take_append_drop]
    rfl
  have returned : (consumed ++ natBits regs.bits.toNat regs.hold.toNat) ++ bytesBits (bs.drop used) =
      consumed ++ stream regs (bs.drop used) := by rw [List.append_assoc]; rfl
  exact List.append_cancel_right (before.trans (source.trans returned.symm))

#print axioms clRead_ordinary_consumed_input
#print axioms clRead_ordinary_trace_format
#print axioms clRead_ordinary_prefix_trace
end Zlib.Inflate.Proofs
