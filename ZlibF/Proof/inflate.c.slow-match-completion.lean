import ZlibF.Proof.«inflate.c.slow-window-semantic»
import ZlibF.Proof.«inflate.c.match-output»
import ZlibF.Math.LZ77History
import ZlibF.Proof.«inflate.c.data-dispatch»

namespace Zlib.Inflate.Proofs.SlowMatchCompletion
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs ZlibF.Math.LZ77Copy
open SlowWindowSemanticPath ZlibF.Math.LZ77History
set_option autoImplicit false

/-- A finite prefix made only of actual successful MATCH dispatches. -/
inductive MatchSteps (c : Ctx) : IL → Heap → IL → Heap → Nat → Prop
  | refl (l h) : MatchSteps c l h l h 0
  | step {l h middle heap final after count} :
      runX (inflate_dispatch c) l h = .ok ((.ok (), middle), heap) →
      MatchSteps c middle heap final after count →
      MatchSteps c l h final after (count + 1)

/-- Output writes outside the private window preserve its exact logical contents. -/
theorem match_dictionary_preserved
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {dict : List UInt8} {dest : BRef} (good : Good h r zs z s)
    (dictionary : InflateDictionary h s dict)
    (privateWindow : ∀ w, s.window = .ref (.blk w) 0 → dest ≠ .blk w)
    (array : Array UInt8) (amount : UInt32) :
    InflateDictionary (setI (Space.put h dest array) zs (matchEmitState s amount))
      (matchEmitState s amount) dict := by
  have window : (matchEmitState s amount).window = s.window := by
    dsimp only [matchEmitState]
    split <;> rfl
  have size : (matchEmitState s amount).wsize = s.wsize := by
    dsimp only [matchEmitState]
    split <;> rfl
  have count : (matchEmitState s amount).whave = s.whave := by
    dsimp only [matchEmitState]
    split <;> rfl
  have next : (matchEmitState s amount).wnext = s.wnext := by
    dsimp only [matchEmitState]
    split <;> rfl
  rcases dictionary with empty | ⟨ref, off, saved, pointer, get, fit, bytes⟩
  · exact Or.inl ⟨by rw [count]; exact empty.1, empty.2⟩
  · have separate : ref ≠ dest := by
      rcases good.inv.win.block with null | ⟨w, wa, wp, wg, wr, ws⟩
      · rw [null] at pointer
        cases pointer
      · rw [wp] at pointer
        cases pointer
        exact (privateWindow w wp).symm
    refine Or.inr ⟨ref, off, saved, by rw [window]; exact pointer, ?_, ?_, ?_⟩
    · rw [byte_view_get_setI, byte_view_get_put_ne _ separate]
      exact get
    · simpa only [size] using fit
    · simpa only [count, next] using bytes

/-- A valid actual segment exposes both its independent byte meaning and
all exact machine fields needed to execute another MATCH segment. -/
theorem valid_segment_complete_fields
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
          (writtenBytes output outOffset (l.out_.toNat - l.left.toNat)) := by
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
      nextSeparate, bytes⟩
    rw [regsEq]

/-- Actual output-register frames compose across segment boundaries. -/
theorem emit_frame_trans {a b c : IL} (first : EmitRegFrame a b) (second : EmitRegFrame b c) :
    EmitRegFrame a c := by
  unfold EmitRegFrame at *
  rw [second, first]

/-- With space for the full pending length, finitely many real dispatches
finish every valid slow match, including ring-wrap and output-overlap segments. -/
theorem complete_valid_match
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
      state.offset = s.offset ∧ DecodeStateFrame s state ∧ EmitRegFrame l regs ∧
      Space.get after dest = some array ∧ array.size = output.size ∧ Space.ro after dest = false ∧
      regs.left.toNat + s.length.toNat = l.left.toNat ∧
      regs.put = .ref dest (outOffset + s.length.toNat) ∧
      Separate regs.next regs.have_.toNat regs.put regs.left.toNat ∧
      writtenBytes array (outOffset + s.length.toNat)
          (l.out_.toNat - l.left.toNat + s.length.toNat) =
        copyBack dict s.offset.toNat s.length.toNat
          (writtenBytes output outOffset (l.out_.toNat - l.left.toNat)) := by
  generalize pending : s.length.toNat = n
  induction n using Nat.strongRecOn generalizing h s z l output outOffset with
  | ind n ih =>
    obtain ⟨amount, middle, heap, array, actual, positive, copyLeft, copyLength,
      current, currentTables, currentB, currentDictionary, arrayGet, arraySize,
      arrayRo, middleEq, remainEq, modes, nextSeparate, bytes⟩ :=
      valid_segment_complete_fields E good tables dictionary B mode sane put get write
        (by omega) length distance room count produced privateWindow separate available
    let nextState := matchEmitState s amount
    have nextFields : nextState.offset = s.offset ∧ nextState.window = s.window ∧ nextState.sane = s.sane := by
      dsimp only [nextState, matchEmitState]
      split <;> exact ⟨rfl, rfl, rfl⟩
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
        nextFields.1, nextFrame, middleFrame, arrayGet, arraySize, arrayRo, ?_, ?_,
        nextSeparate, ?_⟩
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
        finalTables, finalB, finalDictionary, finalMode, finalLength, finalOffset,
        finalFrame, finalRegs, finalGet, finalSize, finalRo, finalLeft, finalPut,
        finalSeparate, finalBytes⟩ := ih nextState.length.toNat nextSmaller env current
          currentTables currentDictionary currentB nextMode (by rw [nextFields.2.2]; exact sane)
          middlePut arrayGet arrayRo nextPositive (by rw [nextFields.1]; exact distance)
          nextRoom nextEnough nextCount nextProduced nextWindow nextSeparate nextAvailable rfl
      refine ⟨final, after, state, result, steps + 1, MatchSteps.step dispatch trace,
        ?_, finalGood, finalTables, finalB, finalDictionary, finalMode, finalLength,
        finalOffset.trans nextFields.1, nextFrame.trans finalFrame,
        emit_frame_trans middleFrame finalRegs, finalGet, finalSize.trans arraySize,
        finalRo, ?_, ?_, finalSeparate, ?_⟩
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

#print axioms match_dictionary_preserved
#print axioms valid_segment_complete_fields
#print axioms emit_frame_trans
#print axioms complete_valid_match
end Zlib.Inflate.Proofs.SlowMatchCompletion
