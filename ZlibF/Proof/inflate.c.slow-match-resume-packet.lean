import ZlibF.Proof.«inflate.c.slow-match-pending»
import ZlibF.Proof.«inflate.c.slow-extra-fragment-frames»
import ZlibF.Proof.«inflate.c.slow-fragment-public-handoff»

namespace Zlib.Inflate.Proofs.SlowMatchCompletion
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs ZlibF.Math.LZ77Copy
open SlowWindowSemanticPath ZlibF.Math.LZ77History SlowInputFragment SlowExtraSemanticPath
set_option autoImplicit false

/-- With space for the full pending length, finitely many real dispatches
finish every valid slow match, including ring-wrap and output-overlap segments. -/
theorem complete_valid_match_persistent
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
        finalTables, finalB, finalDictionary, finalMode, finalLength, finalOffset, finalWas, finalBack,
        finalFrame, finalRegs, finalGet, finalSize, finalRo, finalLeft, finalPut,
        finalSeparate, finalBytes⟩ := ih nextState.length.toNat nextSmaller env current
          currentTables currentDictionary currentB nextMode (by rw [nextFields.2.2.1]; exact sane)
          middlePut arrayGet arrayRo nextPositive (by rw [nextFields.1]; exact distance)
          nextRoom nextEnough nextCount nextProduced nextWindow nextSeparate nextAvailable rfl
      refine ⟨final, after, state, result, steps + 1, MatchSteps.step dispatch trace,
        ?_, finalGood, finalTables, finalB, finalDictionary, finalMode, finalLength,
        finalOffset.trans nextFields.1, finalWas.trans nextFields.2.2.2.1,
        finalBack.trans nextFields.2.2.2.2, nextFrame.trans finalFrame,
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


/-- A MATCH phase carries precisely the independently parsed copy fields. -/
theorem pending_matching_fields {L D : List Nat} {p : CopySyntax L D} {s : InflateState}
    {residual : List Bool} (mode : s.mode = MATCH) (phase : PendingSyntax p s residual) :
    s.was.toNat = lengthBases.getD (p.symbol - 257) 0 + p.lengthValue ∧
      s.length.toNat ≤ s.was.toNat ∧
      s.offset.toNat = distBases.getD p.distanceSymbol 0 + p.distanceValue ∧
      s.back = Int32.ofNat (L.getD p.symbol 0 + lengthExtras.getD (p.symbol - 257) 0 +
        D.getD p.distanceSymbol 0 + distExtras.getD p.distanceSymbol 0) := by
  cases phase with
  | len selected => rcases selected with selected | selected <;> rw [selected] at mode <;> contradiction
  | lenext selected _ _ _ => rw [selected] at mode; contradiction
  | dist selected _ _ _ => rw [selected] at mode; contradiction
  | distext selected _ _ _ _ _ => rw [selected] at mode; contradiction
  | matching _ was remaining offset back => exact ⟨was, remaining, offset, back⟩

/-- The independent format parse supplies bounded length and distance. -/
theorem copy_syntax_scalar_bounds {L D : List Nat} (p : CopySyntax L D) :
    3 ≤ lengthBases.getD (p.symbol - 257) 0 + p.lengthValue ∧
    lengthBases.getD (p.symbol - 257) 0 + p.lengthValue ≤ 258 ∧
    1 ≤ distBases.getD p.distanceSymbol 0 + p.distanceValue ∧
    distBases.getD p.distanceSymbol 0 + p.distanceValue ≤ 32768 := by
  have lengthRead := readBits_value_bound p.lengthRead
  obtain ⟨lengthBase, _, lengthBudget⟩ := SlowExtraFragmentProgress.length_base_extra_budget
    (p.symbol - 257) (by have := p.lengthLower; have := p.lengthUpper; omega)
  have distanceRead := readBits_value_bound p.distanceRead
  obtain ⟨distanceBase, _, distanceBudget⟩ := distance_base_extra_bounds p.distanceSymbol p.distanceUpper
  omega

/-- Resume an actual pending MATCH using any current output capacity.
The emitted amount is exactly min(remaining length, output room); actual
finite dispatches either finish in LEN or wait in MATCH with the same
independent token, including zero output capacity. -/
theorem resume_pending_match_fragment
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
      frame, regFrame, arrayGet, arraySize, arrayRo, finalLeft, finalPut, finalSep, bytes⟩ :=
      complete_valid_match_persistent E good tables dictionary B mode sane put get write
        positive distance room enough count produced privateWindow separate available
    have sourceEq : stream regs bs = stream l bs := by rw [regFrame]; rfl
    refine ⟨s.length.toNat, regs, after, state, array, steps, (Nat.min_eq_left enough).symm,
      trace, stepBound, current, currentTables, currentBits, currentDict, frame, regFrame,
      ?_, nextOffset, nextWas, nextBack, finalLeft, finalPut, arrayGet, arraySize, arrayRo,
      finalSep, sourceEq, ?_, bytes, Or.inl ⟨nextMode, nextLength⟩⟩
    · simp only [nextLength, UInt32.toNat_zero, Nat.zero_add]
    · unfold FutureSource at *
      rw [sourceEq]
      exact source
  · have short : l.left.toNat < s.length.toNat := by omega
    obtain ⟨regs, after, state, array, steps, trace, stepBound, current, currentTables,
      currentBits, currentDict, nextMode, nextLength, nextPositive, nextOffset, nextWas,
      nextBack, frame, regFrame, arrayGet, arraySize, arrayRo, finalLeft, finalPut,
      finalSep, sourceEq, wait, bytes⟩ := pending_valid_match E good tables dictionary B
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
      finalSep, sourceEq, ?_, ?_, Or.inr ⟨nextMode, nextPositive, finalLeft, currentPhase,
        wait, (inflate_dispatch_MATCH env regs nextMode).trans wait⟩⟩
    · omega
    · simp only [finalLeft, UInt32.toNat_zero, Nat.zero_add]
    · unfold FutureSource at *
      rw [sourceEq]
      exact source
    · have sum : l.out_.toNat - l.left.toNat + l.left.toNat = l.out_.toNat := by omega
      simpa only [sum] using bytes

/-- Pending syntax determines both the original token length and the
amount emitted before this call; no caller supplies a new scalar oracle. -/
theorem pending_match_remaining_ledger {L D : List Nat} {p : CopySyntax L D} {s state : InflateState}
    {made : Nat} (mode : s.mode = MATCH) (phase : PendingSyntax p s p.rest)
    (balance : state.length.toNat + made = s.length.toNat) :
    (lengthBases.getD (p.symbol - 257) 0 + p.lengthValue - state.length.toNat) =
      (lengthBases.getD (p.symbol - 257) 0 + p.lengthValue - s.length.toNat) + made := by
  obtain ⟨was, remaining, _⟩ := pending_matching_fields mode phase
  omega

/-- Completing the physical pending portion reconstructs the independent
original copy token after any previously emitted prefix. -/
theorem pending_match_original_copy {L D : List Nat} {p : CopySyntax L D} {s : InflateState}
    (mode : s.mode = MATCH) (phase : PendingSyntax p s p.rest) (dict history : List UInt8) :
    copyBack dict s.offset.toNat s.length.toNat
      (copyBack dict (distBases.getD p.distanceSymbol 0 + p.distanceValue)
        (lengthBases.getD (p.symbol - 257) 0 + p.lengthValue - s.length.toNat) history) =
      copyBack dict (distBases.getD p.distanceSymbol 0 + p.distanceValue)
        (lengthBases.getD (p.symbol - 257) 0 + p.lengthValue) history := by
  obtain ⟨was, remaining, offset, _back⟩ := pending_matching_fields mode phase
  rw [offset]
  have totalBound : s.length.toNat ≤ lengthBases.getD (p.symbol - 257) 0 + p.lengthValue := by omega
  have rest : lengthBases.getD (p.symbol - 257) 0 + p.lengthValue -
      (lengthBases.getD (p.symbol - 257) 0 + p.lengthValue - s.length.toNat) = s.length.toNat := by omega
  have composed := pending_copy_continuation dict history
    (distBases.getD p.distanceSymbol 0 + p.distanceValue)
    (lengthBases.getD (p.symbol - 257) 0 + p.lengthValue)
    (lengthBases.getD (p.symbol - 257) 0 + p.lengthValue - s.length.toNat) (by omega)
  simpa only [rest] using composed

/-- The original independent Symbols continuation remains valid after
finishing its pending portion. -/
theorem pending_match_original_symbols {L D : List Nat} {p : CopySyntax L D} {s : InflateState}
    {dict history output : List UInt8} {tail : List Bool}
    (mode : s.mode = MATCH) (phase : PendingSyntax p s p.rest)
    (continuation : Symbols L D dict
      (copyBack dict (distBases.getD p.distanceSymbol 0 + p.distanceValue)
        (lengthBases.getD (p.symbol - 257) 0 + p.lengthValue) history) p.rest tail output) :
    Symbols L D dict
      (copyBack dict s.offset.toNat s.length.toNat
        (copyBack dict (distBases.getD p.distanceSymbol 0 + p.distanceValue)
          (lengthBases.getD (p.symbol - 257) 0 + p.lengthValue - s.length.toNat) history))
      p.rest tail output := by
  rw [pending_match_original_copy mode phase]
  exact continuation

/-- Actual RESTORE, physical window update and final accounting retain
all scalar pending-MATCH meaning. No saved window contents are assumed. -/
theorem pending_match_leave_fields {L D : List Nat} {p : CopySyntax L D}
    {s middle state : InflateState} (l : IL) (mode : s.mode = MATCH)
    (phase : PendingSyntax p s p.rest)
    (window : WindowStateFrame (leaveState s l) middle)
    (metadata : LeaveMetadataFrame middle state) :
    PendingSyntax p state p.rest ∧ state.mode = MATCH ∧ state.length = s.length ∧
      state.was = s.was ∧ state.offset = s.offset ∧ state.back = s.back := by
  refine ⟨pending_metadata (pending_window (pending_restore phase l) window) metadata, ?_⟩
  rw [metadata, window]
  exact ⟨mode, rfl, rfl, rfl, rfl⟩

/-- A real caller Rebuffer retains the saved MATCH state and its independent
future source while producing the next actual LOAD bit invariant. -/
theorem pending_match_rebuffer {before after : Heap} {r : ZStreamRef} {zs : Nat}
    {z next : ZStream} {s : InflateState} {L D : List Nat} {p : CopySyntax L D}
    {chunk : List UInt8} {later : List Bool}
    (good : Good before r zs z s) (rebuffer : Rebuffer before after r)
    (tables : DataTableInvariant before s) (mode : s.mode = MATCH)
    (phase : PendingSyntax p s p.rest) (held : s.hold.toNat < 2 ^ s.bits.toNat)
    (observed : Bytes after next.next_in next.avail_in.toNat chunk)
    (saved : natBits s.bits.toNat s.hold.toNat ++ (bytesBits chunk ++ later) = p.rest) :
    after.istates zs = some s ∧ DataTableInvariant after s ∧ s.mode = MATCH ∧
      PendingSyntax p s p.rest ∧ BitInv after (dispatchRegs next s) chunk ∧
      FutureSource (dispatchRegs next s) chunk later p.rest := by
  obtain ⟨state, nextTables, nextPhase, bits, source⟩ :=
    rebuffer_pending_input good rebuffer tables phase held observed saved
  exact ⟨state, nextTables, mode, nextPhase, bits, source⟩

#print axioms complete_valid_match_persistent
#print axioms pending_matching_fields
#print axioms copy_syntax_scalar_bounds
#print axioms resume_pending_match_fragment
#print axioms pending_match_remaining_ledger
#print axioms pending_match_original_copy
#print axioms pending_match_original_symbols
#print axioms pending_match_leave_fields
#print axioms pending_match_rebuffer
end Zlib.Inflate.Proofs.SlowMatchCompletion
