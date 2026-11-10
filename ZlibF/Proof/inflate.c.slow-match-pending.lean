import ZlibF.Proof.«inflate.c.slow-match-completion»

namespace Zlib.Inflate.Proofs.SlowMatchCompletion
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs ZlibF.Math.LZ77Copy
open SlowWindowSemanticPath ZlibF.Math.LZ77History
set_option autoImplicit false

/-- Too little output space consumes exactly that space in finitely many
actual MATCH dispatches. The next real MATCH takes the zero-output leave;
all pending-token fields retain their source values. -/
theorem pending_valid_match
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
          (writtenBytes output outOffset (l.out_.toNat - l.left.toNat)) := by
  generalize capacity : l.left.toNat = n
  induction n using Nat.strongRecOn generalizing h s z l output outOffset with
  | ind n ih =>
    by_cases zero : l.left = 0
    · have zeroNat : l.left.toNat = 0 := by rw [zero]; rfl
      have noCapacity : n = 0 := by omega
      refine ⟨l, h, s, output, 0, MatchSteps.refl l h, by omega, good, tables, B,
        dictionary, mode, ?_, by omega, rfl, rfl, rfl, by rfl, by rfl, get, rfl,
        write, zero, ?_, separate, rfl, inflate_MATCH_wait c h l zero, ?_⟩
      · simp only [noCapacity, Nat.sub_zero]
      · simpa only [noCapacity, Nat.add_zero] using put
      · simp only [noCapacity, Nat.add_zero, Nat.sub_zero, copyBack]
    · have left : 0 < l.left.toNat := by
        have positive : l.left.toNat ≠ 0 := by
          intro nil
          exact zero (UInt32.toNat_inj.mp nil)
        omega
      obtain ⟨amount, middle, heap, array, actual, positive, copyLeft, copyLength,
        current, currentTables, currentB, currentDictionary, arrayGet, arraySize,
        arrayRo, middleEq, remainEq, modes, nextSeparate, bytes⟩ :=
        valid_segment_complete_fields E good tables dictionary B mode sane put get write
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
        finalWait, finalBytes⟩ := ih middle.left.toNat nextSmaller env current currentTables
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
        finalRo, finalLeft, ?_, finalSeparate, finalSource.trans frameSource, finalWait, ?_⟩
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

/-- Mathematical pending-match continuation agrees with completing the
original token after any emitted prefix. -/
theorem pending_copy_continuation (dict history : List UInt8) (distance total made : Nat)
    (consumedBound : made ≤ total) :
    copyBack dict distance (total - made) (copyBack dict distance made history) =
      copyBack dict distance total history := by
  rw [← copy_back_compose, Nat.add_sub_of_le consumedBound]

#print axioms pending_valid_match
#print axioms pending_copy_continuation
end Zlib.Inflate.Proofs.SlowMatchCompletion
