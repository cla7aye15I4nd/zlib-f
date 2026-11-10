import ZlibF.Proof.«inflate.c.slow-match-resume-packet»
import ZlibF.Proof.«inflate.c.stored-views»

namespace Zlib.Inflate.Proofs.SlowMatchCompletion
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs ZlibF.Math.LZ77Copy
open SlowWindowSemanticPath ZlibF.Math.LZ77History SlowInputFragment SlowExtraSemanticPath
set_option autoImplicit false

/-- A valid actual segment exposes both its independent byte meaning and
all exact machine fields needed to execute another MATCH segment. -/
theorem valid_segment_complete_heap
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    {dict : List UInt8} (dictionary : InflateDictionary h s dict)
    {l : IL} {bs : List UInt8} {dest : BRef} {output : Array UInt8} {outOffset : Nat}
    (B : BitInv h l bs) (mode : s.mode = MATCH) (sane : s.sane ≠ 0)
    (put : l.put = .ref dest outOffset) (get : Space.get h dest = some output) (write : Space.ro h dest = false)
    (left : 0 < l.left.toNat) (length : 0 < s.length.toNat) (distance : 0 < s.offset.toNat)
    (room : outOffset + l.left.toNat ≤ output.size)
    (count : l.left.toNat ≤ l.out_.toNat) (produced : l.out_.toNat - l.left.toNat ≤ outOffset)
    (privateWindow : ∀ w, s.window = .ref (.blk w) 0 → dest ≠ .blk w)
    (separate : Separate l.next l.have_.toNat l.put l.left.toNat)
    (available : s.offset.toNat ≤ dict.length + (l.out_.toNat - l.left.toNat)) :
    ∃ amount regs after array,
      runX (inflate_MATCH c) l h = .ok ((.ok (), regs), after) ∧
      0 < amount.toNat ∧ amount.toNat ≤ l.left.toNat ∧ amount.toNat ≤ s.length.toNat ∧
      Good after r zs z (matchEmitState s amount) ∧ DataTablesSafe after (matchEmitState s amount) ∧
      BitInv after regs bs ∧ InflateDictionary after (matchEmitState s amount) dict ∧
      Space.get after dest = some array ∧ array.size = output.size ∧ Space.ro after dest = false ∧
      regs = {l with left := l.left - amount, copy := 0, put := .ref dest (outOffset + amount.toNat), from_ := regs.from_} ∧
      (matchEmitState s amount).length.toNat = s.length.toNat - amount.toNat ∧
      ((matchEmitState s amount).mode = LEN ∨ (matchEmitState s amount).mode = MATCH) ∧
      Separate regs.next regs.have_.toNat regs.put regs.left.toNat ∧
      writtenBytes array (outOffset + amount.toNat)
          (l.out_.toNat - l.left.toNat + amount.toNat) =
        copyBack dict s.offset.toNat amount.toNat
          (writtenBytes output outOffset (l.out_.toNat - l.left.toNat)) ∧
      after = setI (Space.put h dest array) zs (matchEmitState s amount) := by
  obtain ⟨amount, regs, after, array, actual, positive, copyLeft, copyLength, getAfter,
    size, stateGet, bytes⟩ := inflate_MATCH_valid_segment E good dict dictionary put get write
      left length distance room count produced privateWindow available
  have nonzero : l.left ≠ 0 := by
    intro zero
    rw [zero] at left
    contradiction
  obtain ⟨outcome, currentRegs, heap, stream, state, safetyRun, current, currentTables, inv, frame, kinds⟩ :=
    inflate_MATCH_boundary_ranges E good tables B put get write mode length distance sane
      room count produced privateWindow (B.output_positions put nonzero separate)
  have same := Except.ok.inj (actual.symm.trans safetyRun)
  cases same
  have stateEq : state = matchEmitState s amount := Option.some.inj (current.live.hs.symm.trans stateGet)
  subst state
  rcases kinds with ⟨impossible, _⟩ | ⟨ok, bad, _⟩ |
    ⟨ok, copy, source, sourceOffset, saved, pos, cLeft, cLength, regsEq, heapEq, stateEq, lengthEq, modes, decreases⟩
  · cases impossible
  · have modes : (matchEmitState s amount).mode = LEN ∨ (matchEmitState s amount).mode = s.mode := by
      dsimp only [matchEmitState]
      split <;> simp
    rcases modes with small | unchanged
    · rw [small] at bad
      contradiction
    · rw [unchanged, mode] at bad
      contradiction
  · have subtract : (matchEmitState s amount).length.toNat = s.length.toNat - amount.toNat := by
      dsimp only [matchEmitState]
      split <;> exact UInt32.toNat_sub_of_le _ _ copyLength
    have amountEq : amount = copy := by
      apply UInt32.toNat_inj.mp
      omega
    subst copy
    have streamGet : r.get after = some z := by
      rw [heapEq, ZStreamRef.get_setI, byte_view_put_stream]
      exact E.hz
    have streamEq : stream = z := Option.some.inj (current.live.hz.symm.trans streamGet)
    subst stream
    have finalTables : DataTablesSafe after (matchEmitState s amount) :=
      currentTables (by rcases modes with eq | eq <;> rw [eq] <;> simp [DataTableMode])
    have readonly : Space.ro after dest = false := by
      rw [heapEq, byte_view_ro_setI, byte_view_ro_write]
      exact write
    have dictionaryAfter : InflateDictionary after (matchEmitState s amount) dict := by
      rw [heapEq]
      exact match_dictionary_preserved good dictionary privateWindow _ _
    have nextSeparate : Separate regs.next regs.have_.toNat regs.put regs.left.toNat := by
      have advanced := separate_advance_output l.next l.put l.have_.toNat l.left.toNat amount.toNat copyLeft separate
      simpa only [regsEq, put, inputAdvance, UInt32.toNat_sub_of_le _ _ copyLeft] using advanced
    refine ⟨amount, regs, after, array, actual, positive, copyLeft, copyLength,
      current, finalTables, inv, dictionaryAfter, getAfter, size, readonly, ?_, subtract, modes,
      nextSeparate, bytes, ?_⟩
    · rw [regsEq]
    · have actualGet : Space.get after dest = some (ZlibF.Math.InflateMatchCopy.copy (decide (source = dest)) saved amount.toNat sourceOffset outOffset output) := by
        rw [heapEq, byte_view_get_setI]
        exact byte_view_get_put get write _
      have arrayEq := Option.some.inj (getAfter.symm.trans actualGet)
      simpa only [arrayEq] using heapEq

/-- With space for the full pending length, finitely many real dispatches
finish every valid slow match, including ring-wrap and output-overlap segments. -/
theorem complete_valid_match_heap
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    {dict : List UInt8} (dictionary : InflateDictionary h s dict)
    {l : IL} {bs : List UInt8} {dest : BRef} {output : Array UInt8} {outOffset : Nat}
    (B : BitInv h l bs) (mode : s.mode = MATCH) (sane : s.sane ≠ 0)
    (put : l.put = .ref dest outOffset) (get : Space.get h dest = some output) (write : Space.ro h dest = false)
    (length : 0 < s.length.toNat) (distance : 0 < s.offset.toNat)
    (room : outOffset + l.left.toNat ≤ output.size) (enough : s.length.toNat ≤ l.left.toNat)
    (count : l.left.toNat ≤ l.out_.toNat) (produced : l.out_.toNat - l.left.toNat ≤ outOffset)
    (privateWindow : ∀ w, s.window = .ref (.blk w) 0 → dest ≠ .blk w)
    (separate : Separate l.next l.have_.toNat l.put l.left.toNat)
    (available : s.offset.toNat ≤ dict.length + (l.out_.toNat - l.left.toNat)) :
    ∃ regs after state array steps,
      MatchSteps c l h regs after steps ∧ steps ≤ s.length.toNat ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧ BitInv after regs bs ∧
      InflateDictionary after state dict ∧ state.mode = LEN ∧ state.length = 0 ∧
      state.offset = s.offset ∧ state.was = s.was ∧ state.back = s.back ∧ DecodeStateFrame s state ∧ EmitRegFrame l regs ∧
      Space.get after dest = some array ∧ array.size = output.size ∧ Space.ro after dest = false ∧
      regs.left.toNat + s.length.toNat = l.left.toNat ∧
      regs.put = .ref dest (outOffset + s.length.toNat) ∧
      Separate regs.next regs.have_.toNat regs.put regs.left.toNat ∧
      writtenBytes array (outOffset + s.length.toNat)
          (l.out_.toNat - l.left.toNat + s.length.toNat) =
        copyBack dict s.offset.toNat s.length.toNat
          (writtenBytes output outOffset (l.out_.toNat - l.left.toNat)) ∧
      after = setI (Space.put h dest array) zs state := by
  generalize pending : s.length.toNat = n
  induction n using Nat.strongRecOn generalizing h s z l output outOffset with
  | ind n ih =>
    obtain ⟨amount, middle, heap, array, actual, positive, copyLeft, copyLength,
      current, currentTables, currentB, currentDictionary, arrayGet, arraySize,
      arrayRo, middleEq, remainEq, modes, nextSeparate, bytes, middleHeap⟩ :=
      valid_segment_complete_heap E good tables dictionary B mode sane put get write
        (by omega) length distance room count produced privateWindow separate available
    let nextState := matchEmitState s amount
    have nextFields : nextState.offset = s.offset ∧ nextState.window = s.window ∧ nextState.sane = s.sane ∧ nextState.was = s.was ∧ nextState.back = s.back := by
      dsimp only [nextState, matchEmitState]
      split <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    have nextFrame : DecodeStateFrame s nextState := by
      dsimp only [nextState, matchEmitState]
      split <;> rfl
    have middleFrame : EmitRegFrame l middle := by
      unfold EmitRegFrame
      rw [middleEq]
    have middleLeft : middle.left.toNat = l.left.toNat - amount.toNat := by
      rw [middleEq]
      exact UInt32.toNat_sub_of_le _ _ copyLeft
    have middleOut : middle.out_ = l.out_ := by rw [middleEq]
    have middlePut : middle.put = .ref dest (outOffset + amount.toNat) := by rw [middleEq]
    have dispatch := (inflate_dispatch_MATCH E l mode).trans actual
    by_cases done : amount.toNat = s.length.toNat
    · have nextMode : nextState.mode = LEN := by
        have zero : s.length - amount = 0 := by
          apply UInt32.toNat_inj.mp
          rw [UInt32.toNat_sub_of_le _ _ copyLength, done]
          simp
        simp only [nextState, matchEmitState, zero, beq_self_eq_true, ite_true]
      have nextLength : nextState.length = 0 := by
        apply UInt32.toNat_inj.mp
        rw [remainEq, done]
        simp
      refine ⟨middle, heap, nextState, array, 1, ?_, by omega, current,
        currentTables, currentB, currentDictionary, nextMode, nextLength,
        nextFields.1, nextFields.2.2.2.1, nextFields.2.2.2.2, nextFrame, middleFrame, arrayGet, arraySize, arrayRo, ?_, ?_,
        nextSeparate, ?_, middleHeap⟩
      · exact MatchSteps.step dispatch (MatchSteps.refl middle heap)
      · omega
      · simpa only [done, pending] using middlePut
      · simpa only [done, pending] using bytes
    · have nextPositive : 0 < nextState.length.toNat := by
        change 0 < (matchEmitState s amount).length.toNat
        rw [remainEq]
        omega
      have nextSmaller : nextState.length.toNat < n := by
        change (matchEmitState s amount).length.toNat < n
        rw [remainEq]
        omega
      have nextMode : nextState.mode = MATCH := by
        have nonzero : s.length - amount ≠ 0 := by
          intro zero
          have subNat : s.length.toNat - amount.toNat = 0 := by
            have same := congrArg UInt32.toNat zero
            simpa only [UInt32.toNat_sub_of_le _ _ copyLength, UInt32.toNat_zero] using same
          change 0 < (matchEmitState s amount).length.toNat at nextPositive
          rw [remainEq] at nextPositive
          omega
        simp only [nextState, matchEmitState, beq_eq_false_iff_ne.mpr nonzero, Bool.false_eq_true, ite_false, mode]
      have env : Env c heap r zs z nextState := ⟨E.strm, E.st, current.live.hz, current.live.hs⟩
      have nextRoom : outOffset + amount.toNat + middle.left.toNat ≤ array.size := by omega
      have nextEnough : nextState.length.toNat ≤ middle.left.toNat := by
        change (matchEmitState s amount).length.toNat ≤ middle.left.toNat
        rw [remainEq]
        omega
      have nextCount : middle.left.toNat ≤ middle.out_.toNat := by rw [middleOut]; omega
      have nextProduced : middle.out_.toNat - middle.left.toNat ≤ outOffset + amount.toNat := by
        rw [middleOut]
        omega
      have nextWindow : ∀ w, nextState.window = .ref (.blk w) 0 → dest ≠ .blk w := by
        intro w win
        rw [nextFields.2.1] at win
        exact privateWindow w win
      have nextAvailable : nextState.offset.toNat ≤ dict.length + (middle.out_.toNat - middle.left.toNat) := by
        rw [nextFields.1, middleOut]
        omega
      obtain ⟨final, after, state, result, steps, trace, stepBound, finalGood,
        finalTables, finalB, finalDictionary, finalMode, finalLength, finalOffset, finalWas, finalBack,
        finalFrame, finalRegs, finalGet, finalSize, finalRo, finalLeft, finalPut,
        finalSeparate, finalBytes, finalHeap⟩ := ih nextState.length.toNat nextSmaller env current
          currentTables currentDictionary currentB nextMode (by rw [nextFields.2.2.1]; exact sane)
          middlePut arrayGet arrayRo nextPositive (by rw [nextFields.1]; exact distance)
          nextRoom nextEnough nextCount nextProduced nextWindow nextSeparate nextAvailable rfl
      refine ⟨final, after, state, result, steps + 1, MatchSteps.step dispatch trace,
        ?_, finalGood, finalTables, finalB, finalDictionary, finalMode, finalLength,
        finalOffset.trans nextFields.1, finalWas.trans nextFields.2.2.2.1,
        finalBack.trans nextFields.2.2.2.2, nextFrame.trans finalFrame,
        emit_frame_trans middleFrame finalRegs, finalGet, finalSize.trans arraySize,
        finalRo, ?_, ?_, finalSeparate, ?_, ?_⟩
      · change steps ≤ (matchEmitState s amount).length.toNat at stepBound
        rw [remainEq] at stepBound
        omega
      · change final.left.toNat + (matchEmitState s amount).length.toNat = middle.left.toNat at finalLeft
        rw [remainEq] at finalLeft
        omega
      · have amounts : outOffset + amount.toNat + nextState.length.toNat = outOffset + s.length.toNat := by
          change outOffset + amount.toNat + (matchEmitState s amount).length.toNat = _
          rw [remainEq]
          omega
        simpa only [amounts, pending] using finalPut
      · have amounts : outOffset + amount.toNat + nextState.length.toNat = outOffset + s.length.toNat := by
          change outOffset + amount.toNat + (matchEmitState s amount).length.toNat = _
          rw [remainEq]
          omega
        have producedSum : middle.out_.toNat - middle.left.toNat + nextState.length.toNat =
            l.out_.toNat - l.left.toNat + s.length.toNat := by
          change middle.out_.toNat - middle.left.toNat + (matchEmitState s amount).length.toNat = _
          rw [remainEq, middleOut]
          omega
        have producedMiddle : middle.out_.toNat - middle.left.toNat =
            l.out_.toNat - l.left.toNat + amount.toNat := by
          rw [middleOut]
          omega
        rw [amounts, producedSum, nextFields.1, producedMiddle, bytes,
          ← copy_back_compose] at finalBytes
        have total : amount.toNat + nextState.length.toNat = s.length.toNat := by
          change amount.toNat + (matchEmitState s amount).length.toNat = _
          rw [remainEq]
          omega
        simpa only [total, pending] using finalBytes
      · rw [finalHeap, middleHeap, byte_view_put_setI, setI_setI, byte_view_put_put get write]

/-- Too little output space consumes exactly that space in finitely many
actual MATCH dispatches. The next real MATCH takes the zero-output leave;
all pending-token fields retain their source values. -/
theorem pending_valid_match_heap
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    {dict : List UInt8} (dictionary : InflateDictionary h s dict)
    {l : IL} {bs : List UInt8} {dest : BRef} {output : Array UInt8} {outOffset : Nat}
    (B : BitInv h l bs) (mode : s.mode = MATCH) (sane : s.sane ≠ 0)
    (put : l.put = .ref dest outOffset) (get : Space.get h dest = some output) (write : Space.ro h dest = false)
    (distance : 0 < s.offset.toNat)
    (room : outOffset + l.left.toNat ≤ output.size) (short : l.left.toNat < s.length.toNat)
    (count : l.left.toNat ≤ l.out_.toNat) (produced : l.out_.toNat - l.left.toNat ≤ outOffset)
    (privateWindow : ∀ w, s.window = .ref (.blk w) 0 → dest ≠ .blk w)
    (separate : Separate l.next l.have_.toNat l.put l.left.toNat)
    (available : s.offset.toNat ≤ dict.length + (l.out_.toNat - l.left.toNat)) :
    ∃ regs after state array steps,
      MatchSteps c l h regs after steps ∧ steps ≤ l.left.toNat ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧ BitInv after regs bs ∧
      InflateDictionary after state dict ∧ state.mode = MATCH ∧
      state.length.toNat = s.length.toNat - l.left.toNat ∧ 0 < state.length.toNat ∧
      state.offset = s.offset ∧ state.was = s.was ∧ state.back = s.back ∧
      DecodeStateFrame s state ∧ EmitRegFrame l regs ∧
      Space.get after dest = some array ∧ array.size = output.size ∧ Space.ro after dest = false ∧
      regs.left = 0 ∧ regs.put = .ref dest (outOffset + l.left.toNat) ∧
      Separate regs.next regs.have_.toNat regs.put regs.left.toNat ∧
      stream regs bs = stream l bs ∧
      runX (inflate_MATCH c) regs after = .ok ((.error Ex.leave, regs), after) ∧
      writtenBytes array (outOffset + l.left.toNat) l.out_.toNat =
        copyBack dict s.offset.toNat l.left.toNat
          (writtenBytes output outOffset (l.out_.toNat - l.left.toNat)) ∧
      after = setI (Space.put h dest array) zs state := by
  generalize capacity : l.left.toNat = n
  induction n using Nat.strongRecOn generalizing h s z l output outOffset with
  | ind n ih =>
    by_cases zero : l.left = 0
    · have zeroNat : l.left.toNat = 0 := by rw [zero]; rfl
      have noCapacity : n = 0 := by omega
      refine ⟨l, h, s, output, 0, MatchSteps.refl l h, by omega, good, tables, B,
        dictionary, mode, ?_, by omega, rfl, rfl, rfl, by rfl, by rfl, get, rfl,
        write, zero, ?_, separate, rfl, inflate_MATCH_wait c h l zero, ?_, ?_⟩
      · simp only [noCapacity, Nat.sub_zero]
      · simpa only [noCapacity, Nat.add_zero] using put
      · simp only [noCapacity, Nat.add_zero, Nat.sub_zero, copyBack]
      · simp only [byte_view_put_self get write]
        simp [setI, upd_self _ _ _ good.live.hs]
    · have left : 0 < l.left.toNat := by
        have positive : l.left.toNat ≠ 0 := by
          intro nil
          exact zero (UInt32.toNat_inj.mp nil)
        omega
      obtain ⟨amount, middle, heap, array, actual, positive, copyLeft, copyLength,
        current, currentTables, currentB, currentDictionary, arrayGet, arraySize,
        arrayRo, middleEq, remainEq, modes, nextSeparate, bytes, middleHeap⟩ :=
        valid_segment_complete_heap E good tables dictionary B mode sane put get write
          left (by omega) distance room count produced privateWindow separate available
      let nextState := matchEmitState s amount
      have nextFields : nextState.offset = s.offset ∧ nextState.window = s.window ∧
          nextState.sane = s.sane ∧ nextState.was = s.was ∧ nextState.back = s.back := by
        dsimp only [nextState, matchEmitState]
        split <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩
      have nextFrame : DecodeStateFrame s nextState := by
        dsimp only [nextState, matchEmitState]
        split <;> rfl
      have middleFrame : EmitRegFrame l middle := by
        unfold EmitRegFrame
        rw [middleEq]
      have middleLeft : middle.left.toNat = l.left.toNat - amount.toNat := by
        rw [middleEq]
        exact UInt32.toNat_sub_of_le _ _ copyLeft
      have middleOut : middle.out_ = l.out_ := by rw [middleEq]
      have middlePut : middle.put = .ref dest (outOffset + amount.toNat) := by rw [middleEq]
      have nextPositive : 0 < nextState.length.toNat := by
        change 0 < (matchEmitState s amount).length.toNat
        rw [remainEq]
        omega
      have nextMode : nextState.mode = MATCH := by
        have nonzero : s.length - amount ≠ 0 := by
          intro nil
          have subNat : s.length.toNat - amount.toNat = 0 := by
            have same := congrArg UInt32.toNat nil
            simpa only [UInt32.toNat_sub_of_le _ _ copyLength, UInt32.toNat_zero] using same
          omega
        simp only [nextState, matchEmitState, beq_eq_false_iff_ne.mpr nonzero,
          Bool.false_eq_true, ite_false, mode]
      have nextShort : middle.left.toNat < nextState.length.toNat := by
        change middle.left.toNat < (matchEmitState s amount).length.toNat
        rw [remainEq]
        omega
      have nextSmaller : middle.left.toNat < n := by omega
      have env : Env c heap r zs z nextState := ⟨E.strm, E.st, current.live.hz, current.live.hs⟩
      have nextRoom : outOffset + amount.toNat + middle.left.toNat ≤ array.size := by omega
      have nextCount : middle.left.toNat ≤ middle.out_.toNat := by rw [middleOut]; omega
      have nextProduced : middle.out_.toNat - middle.left.toNat ≤ outOffset + amount.toNat := by
        rw [middleOut]
        omega
      have nextWindow : ∀ w, nextState.window = .ref (.blk w) 0 → dest ≠ .blk w := by
        intro w win
        rw [nextFields.2.1] at win
        exact privateWindow w win
      have nextAvailable : nextState.offset.toNat ≤ dict.length + (middle.out_.toNat - middle.left.toNat) := by
        rw [nextFields.1, middleOut]
        omega
      obtain ⟨final, after, state, result, steps, trace, stepBound, finalGood,
        finalTables, finalB, finalDictionary, finalMode, finalLength, finalPositive,
        finalOffset, finalWas, finalBack, finalFrame, finalRegs, finalGet,
        finalSize, finalRo, finalLeft, finalPut, finalSeparate, finalSource,
        finalWait, finalBytes, finalHeap⟩ := ih middle.left.toNat nextSmaller env current currentTables
          currentDictionary currentB nextMode (by rw [nextFields.2.2.1]; exact sane)
          middlePut arrayGet arrayRo (by rw [nextFields.1]; exact distance)
          nextRoom nextShort nextCount nextProduced nextWindow nextSeparate nextAvailable rfl
      have frameSource : stream middle bs = stream l bs := by rw [middleEq]; rfl
      refine ⟨final, after, state, result, steps + 1,
        MatchSteps.step ((inflate_dispatch_MATCH E l mode).trans actual) trace,
        by omega, finalGood, finalTables, finalB, finalDictionary, finalMode,
        ?_, finalPositive, finalOffset.trans nextFields.1, finalWas.trans nextFields.2.2.2.1,
        finalBack.trans nextFields.2.2.2.2, nextFrame.trans finalFrame,
        emit_frame_trans middleFrame finalRegs, finalGet, finalSize.trans arraySize,
        finalRo, finalLeft, ?_, finalSeparate, finalSource.trans frameSource, finalWait, ?_, ?_⟩
      · change state.length.toNat = s.length.toNat - n
        change state.length.toNat = (matchEmitState s amount).length.toNat - middle.left.toNat at finalLength
        rw [remainEq] at finalLength
        omega
      · have amounts : outOffset + amount.toNat + middle.left.toNat = outOffset + n := by omega
        simpa only [amounts] using finalPut
      · have amounts : outOffset + amount.toNat + middle.left.toNat = outOffset + n := by omega
        rw [amounts, nextFields.1] at finalBytes
        have producedMiddle : middle.out_.toNat - middle.left.toNat =
            l.out_.toNat - l.left.toNat + amount.toNat := by
          rw [middleOut]
          omega
        rw [producedMiddle, bytes, ← copy_back_compose, middleOut] at finalBytes
        have total : amount.toNat + middle.left.toNat = n := by omega
        simpa only [total, capacity] using finalBytes
      · rw [finalHeap, middleHeap, byte_view_put_setI, setI_setI, byte_view_put_put get write]

/-- Resume an actual pending MATCH using any current output capacity.
The emitted amount is exactly min(remaining length, output room); actual
finite dispatches either finish in LEN or wait in MATCH with the same
independent token, including zero output capacity. -/
theorem resume_pending_match_fragment_heap
    {L D : List Nat} {p : CopySyntax L D}
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    {dict : List UInt8} (dictionary : InflateDictionary h s dict)
    {l : IL} {bs : List UInt8} {future : List Bool} {dest : BRef} {output : Array UInt8} {outOffset : Nat}
    (B : BitInv h l bs) (mode : s.mode = MATCH) (phase : PendingSyntax p s p.rest)
    (source : FutureSource l bs future p.rest) (sane : s.sane ≠ 0)
    (put : l.put = .ref dest outOffset) (get : Space.get h dest = some output) (write : Space.ro h dest = false)
    (positive : 0 < s.length.toNat)
    (room : outOffset + l.left.toNat ≤ output.size)
    (count : l.left.toNat ≤ l.out_.toNat) (produced : l.out_.toNat - l.left.toNat ≤ outOffset)
    (privateWindow : ∀ w, s.window = .ref (.blk w) 0 → dest ≠ .blk w)
    (separate : Separate l.next l.have_.toNat l.put l.left.toNat)
    (available : s.offset.toNat ≤ dict.length + (l.out_.toNat - l.left.toNat)) :
    ∃ made regs after state array steps,
      made = min s.length.toNat l.left.toNat ∧
      MatchSteps c l h regs after steps ∧ steps ≤ made ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧ BitInv after regs bs ∧
      InflateDictionary after state dict ∧ DecodeStateFrame s state ∧ EmitRegFrame l regs ∧
      state.length.toNat + made = s.length.toNat ∧
      state.offset = s.offset ∧ state.was = s.was ∧ state.back = s.back ∧
      regs.left.toNat + made = l.left.toNat ∧ regs.put = .ref dest (outOffset + made) ∧
      Space.get after dest = some array ∧ array.size = output.size ∧ Space.ro after dest = false ∧
      Separate regs.next regs.have_.toNat regs.put regs.left.toNat ∧
      stream regs bs = stream l bs ∧ FutureSource regs bs future p.rest ∧
      writtenBytes array (outOffset + made) (l.out_.toNat - l.left.toNat + made) =
        copyBack dict s.offset.toNat made (writtenBytes output outOffset (l.out_.toNat - l.left.toNat)) ∧
      after = setI (Space.put h dest array) zs state ∧
      ((state.mode = LEN ∧ state.length = 0) ∨
       (state.mode = MATCH ∧ 0 < state.length.toNat ∧ regs.left = 0 ∧
        PendingSyntax p state p.rest ∧
        runX (inflate_MATCH c) regs after = .ok ((.error Ex.leave, regs), after) ∧
        runX (inflate_dispatch c) regs after = .ok ((.error Ex.leave, regs), after))) := by
  obtain ⟨was, remaining, offset, back⟩ := pending_matching_fields mode phase
  obtain ⟨_lengthBase, _lengthBound, distanceBase, _distanceBound⟩ := copy_syntax_scalar_bounds p
  have distance : 0 < s.offset.toNat := by omega
  by_cases enough : s.length.toNat ≤ l.left.toNat
  · obtain ⟨regs, after, state, array, steps, trace, stepBound, current, currentTables,
      currentBits, currentDict, nextMode, nextLength, nextOffset, nextWas, nextBack,
      frame, regFrame, arrayGet, arraySize, arrayRo, finalLeft, finalPut, finalSep, bytes, heap⟩ :=
      complete_valid_match_heap E good tables dictionary B mode sane put get write
        positive distance room enough count produced privateWindow separate available
    have sourceEq : stream regs bs = stream l bs := by rw [regFrame]; rfl
    refine ⟨s.length.toNat, regs, after, state, array, steps, (Nat.min_eq_left enough).symm,
      trace, stepBound, current, currentTables, currentBits, currentDict, frame, regFrame,
      ?_, nextOffset, nextWas, nextBack, finalLeft, finalPut, arrayGet, arraySize, arrayRo,
      finalSep, sourceEq, ?_, bytes, heap, Or.inl ⟨nextMode, nextLength⟩⟩
    · simp only [nextLength, UInt32.toNat_zero, Nat.zero_add]
    · unfold FutureSource at *
      rw [sourceEq]
      exact source
  · have short : l.left.toNat < s.length.toNat := by omega
    obtain ⟨regs, after, state, array, steps, trace, stepBound, current, currentTables,
      currentBits, currentDict, nextMode, nextLength, nextPositive, nextOffset, nextWas,
      nextBack, frame, regFrame, arrayGet, arraySize, arrayRo, finalLeft, finalPut,
      finalSep, sourceEq, wait, bytes, heap⟩ := pending_valid_match_heap E good tables dictionary B
        mode sane put get write distance room short count produced privateWindow separate available
    have currentPhase : PendingSyntax p state p.rest := by
      apply PendingSyntax.matching nextMode
      · rw [nextWas]; exact was
      · rw [nextLength, nextWas]
        omega
      · rw [nextOffset]; exact offset
      · rw [nextBack]; exact back
    have env : Env c after r zs z state := ⟨E.strm, E.st, current.live.hz, current.live.hs⟩
    refine ⟨l.left.toNat, regs, after, state, array, steps, (Nat.min_eq_right (Nat.le_of_lt short)).symm,
      trace, stepBound, current, currentTables, currentBits, currentDict, frame, regFrame,
      ?_, nextOffset, nextWas, nextBack, ?_, finalPut, arrayGet, arraySize, arrayRo,
      finalSep, sourceEq, ?_, ?_, heap, Or.inr ⟨nextMode, nextPositive, finalLeft, currentPhase,
        wait, (inflate_dispatch_MATCH env regs nextMode).trans wait⟩⟩
    · omega
    · simp only [finalLeft, UInt32.toNat_zero, Nat.zero_add]
    · unfold FutureSource at *
      rw [sourceEq]
      exact source
    · have sum : l.out_.toNat - l.left.toNat + l.left.toNat = l.out_.toNat := by omega
      simpa only [sum] using bytes

/-- An exact generated MATCH heap and cursor frame produce every outgoing
public buffer clause; no final buffer property is an input. -/
theorem generated_match_heap_buffers
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s state : InflateState}
    {l regs : IL} {bs : List UInt8} {dest : BRef} {outOffset made : Nat}
    {output array : Array UInt8}
    (before : Good h r zs z s) (current : Good after r zs z state)
    (buffers : DispatchBuffers h r l bs) (frame : DecodeStateFrame s state)
    (regFrame : EmitRegFrame l regs) (get : Space.get h dest = some output)
    (write : Space.ro h dest = false) (size : array.size = output.size)
    (heap : after = setI (Space.put h dest array) zs state)
    (put : l.put = .ref dest outOffset) (cursor : regs.put = .ref dest (outOffset + made))
    (balance : regs.left.toNat + made = l.left.toNat)
    (bits : BitInv after regs bs)
    (separate : Separate regs.next regs.have_.toNat regs.put regs.left.toNat) :
    DispatchBuffers after r regs bs ∧ ByteViewSizes h after ∧
      (∀ ref : BRef, Space.ro after ref = Space.ro h ref) ∧
      after.static = h.static ∧ regs.bits = l.bits := by
  have sizes : ByteViewSizes h after := by
    rw [heap]
    exact (byte_view_sizes_put get write array size).trans (byte_view_sizes_setI _ _ _)
  have readonly : ∀ ref : BRef, Space.ro after ref = Space.ro h ref := by
    intro ref
    rw [heap, byte_view_ro_setI, byte_view_ro_write]
  have window : state.window = s.window := by rw [frame]
  have advance : regs.put = inputAdvance l.put made := by rw [put]; exact cursor
  have total : regs.out_ = l.out_ := by rw [regFrame]
  have finalOutput := buffers.output.emit before current window sizes readonly advance balance total
  exact ⟨buffers.emit before current window sizes readonly regFrame finalOutput bits separate,
    sizes, readonly, by rw [heap]; exact byte_view_put_static _ _ _, by rw [regFrame]⟩

/-- Unified generated MATCH semantics together with its produced outgoing
buffers, exact heap, unchanged read-only permissions and static image. -/
theorem resume_pending_match_fragment_buffers
    {L D : List Nat} {p : CopySyntax L D}
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    {dict : List UInt8} (dictionary : InflateDictionary h s dict)
    {l : IL} {bs : List UInt8} {future : List Bool} {dest : BRef} {output : Array UInt8} {outOffset : Nat}
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = MATCH) (phase : PendingSyntax p s p.rest)
    (source : FutureSource l bs future p.rest) (sane : s.sane ≠ 0)
    (put : l.put = .ref dest outOffset) (get : Space.get h dest = some output) (write : Space.ro h dest = false)
    (positive : 0 < s.length.toNat)
    (room : outOffset + l.left.toNat ≤ output.size)
    (count : l.left.toNat ≤ l.out_.toNat) (produced : l.out_.toNat - l.left.toNat ≤ outOffset)
    (privateWindow : ∀ w, s.window = .ref (.blk w) 0 → dest ≠ .blk w)
    (separate : Separate l.next l.have_.toNat l.put l.left.toNat)
    (available : s.offset.toNat ≤ dict.length + (l.out_.toNat - l.left.toNat)) :
    ∃ made regs after state array steps,
      made = min s.length.toNat l.left.toNat ∧
      MatchSteps c l h regs after steps ∧ steps ≤ made ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧ BitInv after regs bs ∧
      InflateDictionary after state dict ∧ DecodeStateFrame s state ∧ EmitRegFrame l regs ∧
      state.length.toNat + made = s.length.toNat ∧
      state.offset = s.offset ∧ state.was = s.was ∧ state.back = s.back ∧
      regs.left.toNat + made = l.left.toNat ∧ regs.put = .ref dest (outOffset + made) ∧
      Space.get after dest = some array ∧ array.size = output.size ∧ Space.ro after dest = false ∧
      Separate regs.next regs.have_.toNat regs.put regs.left.toNat ∧
      stream regs bs = stream l bs ∧ FutureSource regs bs future p.rest ∧
      writtenBytes array (outOffset + made) (l.out_.toNat - l.left.toNat + made) =
        copyBack dict s.offset.toNat made (writtenBytes output outOffset (l.out_.toNat - l.left.toNat)) ∧
      after = setI (Space.put h dest array) zs state ∧
      DispatchBuffers after r regs bs ∧ ByteViewSizes h after ∧
      (∀ ref : BRef, Space.ro after ref = Space.ro h ref) ∧
      after.static = h.static ∧ regs.bits = l.bits ∧
      ((state.mode = LEN ∧ state.length = 0) ∨
       (state.mode = MATCH ∧ 0 < state.length.toNat ∧ regs.left = 0 ∧
        PendingSyntax p state p.rest ∧
        runX (inflate_MATCH c) regs after = .ok ((.error Ex.leave, regs), after) ∧
        runX (inflate_dispatch c) regs after = .ok ((.error Ex.leave, regs), after))) := by
  obtain ⟨made, regs, after, state, array, steps, amount, trace, stepBound,
    current, currentTables, currentBits, currentDict, frame, regFrame, remaining,
    nextOffset, nextWas, nextBack, left, cursor, arrayGet, arraySize, arrayRo,
    finalSep, sameSource, futureSource, bytes, heap, outcome⟩ :=
    resume_pending_match_fragment_heap E good tables dictionary buffers.bits mode phase source sane
      put get write positive room count produced privateWindow separate available
  obtain ⟨finalBuffers, sizes, readonly, statics, bitsEq⟩ := generated_match_heap_buffers
    good current buffers frame regFrame get write arraySize heap put cursor left currentBits finalSep
  exact ⟨made, regs, after, state, array, steps, amount, trace, stepBound,
    current, currentTables, currentBits, currentDict, frame, regFrame, remaining,
    nextOffset, nextWas, nextBack, left, cursor, arrayGet, arraySize, arrayRo,
    finalSep, sameSource, futureSource, bytes, heap, finalBuffers, sizes, readonly,
    statics, bitsEq, outcome⟩

#print axioms valid_segment_complete_heap
#print axioms complete_valid_match_heap
#print axioms pending_valid_match_heap
#print axioms resume_pending_match_fragment_heap
#print axioms generated_match_heap_buffers
#print axioms resume_pending_match_fragment_buffers
end Zlib.Inflate.Proofs.SlowMatchCompletion
