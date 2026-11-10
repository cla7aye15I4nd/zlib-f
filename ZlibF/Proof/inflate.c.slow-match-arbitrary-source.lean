import ZlibF.Proof.«inflate.c.slow-match-output-buffers»

namespace Zlib.Inflate.Proofs.SlowArbitrarySource
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs SlowMatchCompletion SlowWindowSemanticPath
open ZlibF.Math.LZ77Copy
set_option autoImplicit false

/-- A real MATCH on arbitrary input either waits for output, rejects its
actual unavailable distance, or emits a genuine independent copyBack
prefix. No token parse, valid future or caller-supplied distance fit is used. -/
theorem MATCH_current_source
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {dict : List UInt8}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (dictionary : InflateDictionary h s dict) (buffers : DispatchBuffers h r l bs)
    (mode : s.mode = MATCH) (length : 0 < s.length.toNat) (offset : 0 < s.offset.toNat) (sane : s.sane ≠ 0) :
    (l.left = 0 ∧ runX (inflate_MATCH c) l h = .ok ((.error Ex.leave, l), h)) ∨
    (∃ after stream state,
      ¬ s.offset.toNat ≤ dict.length + (l.out_.toNat - l.left.toNat) ∧
      runX (inflate_MATCH c) l h = .ok ((.ok (), l), after) ∧
      Good after r zs stream state ∧ DataTableInvariant after state ∧ DispatchBuffers after r l bs ∧
      state.mode = BAD ∧ state = {s with mode := BAD} ∧
      DecodeStateFrame s state ∧ after.static = h.static) ∨
    (∃ (amount : UInt32) (dest : BRef) (off : Nat) (output : Array UInt8)
        (regs : IL) (after : Heap) (array : Array UInt8),
      s.offset.toNat ≤ dict.length + (l.out_.toNat - l.left.toNat) ∧
      l.put = .ref dest off ∧ Space.get h dest = some output ∧
      runX (inflate_MATCH c) l h = .ok ((.ok (), regs), after) ∧
      0 < amount.toNat ∧ amount.toNat ≤ l.left.toNat ∧ amount.toNat ≤ s.length.toNat ∧
      Good after r zs z (matchEmitState s amount) ∧ DataTablesSafe after (matchEmitState s amount) ∧
      DispatchBuffers after r regs bs ∧ InflateDictionary after (matchEmitState s amount) dict ∧
      Space.get after dest = some array ∧ array.size = output.size ∧ Space.ro after dest = false ∧
      DecodeStateFrame s (matchEmitState s amount) ∧ EmitRegFrame l regs ∧
      (matchEmitState s amount).length.toNat = s.length.toNat - amount.toNat ∧
      ((matchEmitState s amount).mode = LEN ∨ (matchEmitState s amount).mode = MATCH) ∧
      regs.left.toNat + amount.toNat = l.left.toNat ∧ regs.put = .ref dest (off + amount.toNat) ∧
      stream regs bs = stream l bs ∧ after.static = h.static ∧ regs.bits = l.bits ∧
      writtenBytes array (off + amount.toNat) (l.out_.toNat - l.left.toNat + amount.toNat) =
        copyBack dict s.offset.toNat amount.toNat (writtenBytes output off (l.out_.toNat - l.left.toNat)) ∧
      after = setI (Space.put h dest array) zs (matchEmitState s amount)) := by
  by_cases empty : l.left = 0
  · exact Or.inl ⟨empty, inflate_MATCH_wait c h l empty⟩
  have positive : 0 < l.left.toNat := by
    have nonzero : l.left.toNat ≠ 0 := by intro zero; exact empty (UInt32.toNat_inj.mp zero)
    omega
  obtain ⟨dest, output, off, put, get, write, room, count, produced, unowned⟩ :=
    callerRange_slow_output good l buffers.output.range buffers.output.nonnull buffers.output.count buffers.output.produced
  by_cases available : s.offset.toNat ≤ dict.length + (l.out_.toNat - l.left.toNat)
  · obtain ⟨amount, regs, after, array, actual, amountPositive, amountLeft, amountLength,
      current, currentTables, currentBits, currentDictionary, arrayGet, arraySize,
      arrayRo, regsEq, remain, modes, separate, bytes, heap⟩ :=
      valid_segment_complete_heap E good tables dictionary buffers.bits mode sane put get write
        positive length offset room count produced unowned buffers.separate available
    have frame : DecodeStateFrame s (matchEmitState s amount) := by
      dsimp only [matchEmitState]
      split <;> rfl
    have regFrame : EmitRegFrame l regs := by unfold EmitRegFrame; rw [regsEq]
    have left : regs.left.toNat + amount.toNat = l.left.toNat := by
      rw [regsEq]
      simp only [UInt32.toNat_sub_of_le _ _ amountLeft]
      omega
    have cursor : regs.put = .ref dest (off + amount.toNat) := by rw [regsEq]
    obtain ⟨finalBuffers, _sizes, _readonly, statics, bitsEq⟩ := generated_match_heap_buffers
      good current buffers frame regFrame get write arraySize heap put cursor left currentBits separate
    exact Or.inr (Or.inr ⟨amount, dest, off, output, regs, after, array, available, put, get,
      actual, amountPositive, amountLeft, amountLength, current, currentTables, finalBuffers,
      currentDictionary, arrayGet, arraySize, arrayRo, frame, regFrame, remain, modes, left,
      cursor, by rw [regFrame]; rfl, statics, bitsEq, bytes, heap⟩)
  · have dictLength := inflateDictionary_length good dictionary
    have outSub : (l.out_ - l.left).toNat = l.out_.toNat - l.left.toNat := UInt32.toNat_sub_of_le _ _ count
    have inWindow : s.offset > l.out_ - l.left := by
      exact UInt32.lt_iff_toNat_lt.mpr (by rw [outSub]; omega)
    have distanceSub : (s.offset - (l.out_ - l.left)).toNat = s.offset.toNat - (l.out_.toNat - l.left.toNat) := by
      rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by rw [outSub]; omega)), outSub]
    have beyond : s.offset - (l.out_ - l.left) > s.whave := by
      exact UInt32.lt_iff_toNat_lt.mpr (by rw [distanceSub]; omega)
    obtain ⟨i, _message, rejected⟩ := matchSelect_bad_run E l empty inWindow beyond sane
    have actual : runX (inflate_MATCH c) l h = .ok ((.ok (), l), badHeap h r zs z s i) := by
      rw [inflate_MATCH_select_cut]
      exact rejected
    obtain ⟨outcome, regs, after, stream, state, made, safetyRun, current, currentTables,
      finalBuffers, _sizes, frame, _regFrame, _residual, _count, _put, _kinds⟩ :=
      inflate_MATCH_dispatch E good tables buffers mode length offset sane
    have same := Except.ok.inj (actual.symm.trans safetyRun)
    cases same
    have stateEq : state = {s with mode := BAD} := by
      apply Option.some.inj
      rw [← current.live.hs]
      simp [badHeap, setI]
    exact Or.inr (Or.inl ⟨_, stream, state, available, actual, current, currentTables,
      finalBuffers, by rw [stateEq], stateEq, frame, by simp [badHeap, setI, ZStreamRef.put_static]⟩)

#print axioms MATCH_current_source
end Zlib.Inflate.Proofs.SlowArbitrarySource
