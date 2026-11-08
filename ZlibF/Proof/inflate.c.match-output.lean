import ZlibF.Proof.«inflate.c.output-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- A resumed match retains its original length, distance and back count.
Only the remaining pending length decreases. -/
def MatchResidual (before after : InflateState) : Prop :=
  after.mode = MATCH → 0 < after.length.toNat ∧ after.length.toNat ≤ before.length.toNat ∧
    after.offset = before.offset ∧ after.was = before.was ∧ after.back = before.back

/-- Complete MATCH emission preserves the dispatch buffers and their exact
cursor accounting. The stream's guarded mode facts supply the positive
pending length/distance and enabled sanity check. Zero output, unavailable
history and overlapping back-reference copies are all included. -/
theorem inflate_MATCH_output_step_frame {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (B : BitInv h l bs) (output : OutputCursorInvariant h r l)
    (separate : Separate l.next l.have_.toNat l.put l.left.toNat)
    (mode : s.mode = MATCH) (length : 0 < s.length.toNat) (offset : 0 < s.offset.toNat) (sane : s.sane ≠ 0) :
    ∃ outcome regs after stream state made,
      runX (inflate_MATCH c) l h = .ok ((outcome, regs), after) ∧
      Good after r zs stream state ∧ DataTableInvariant after state ∧ BitInv after regs bs ∧
      OutputCursorInvariant after r regs ∧ Separate regs.next regs.have_.toNat regs.put regs.left.toNat ∧
      ByteViewSizes h after ∧ DecodeStateFrame s state ∧ EmitRegFrame l regs ∧
      regs.left.toNat + made = l.left.toNat ∧ regs.put = inputAdvance l.put made ∧
      Zlib.Inflate.Proofs.stream regs bs = Zlib.Inflate.Proofs.stream l bs ∧
      ((outcome = .error Ex.leave ∧ made = 0) ∨
        (outcome = .ok () ∧ state.mode = BAD ∧ made = 0) ∨
        (outcome = .ok () ∧ 0 < made ∧ (state.mode = LEN ∨ state.mode = MATCH))) ∧
      (∀ ref : BRef, Space.ro after ref = Space.ro h ref) ∧ MatchResidual s state := by
  by_cases empty : l.left = 0
  · exact ⟨.error Ex.leave, l, h, z, s, 0, inflate_MATCH_wait c h l empty, good, fun _ => tables,
      B, output, separate, ByteViewSizes.refl h, by rfl, by rfl, by omega,
      (inputAdvance_zero l.put).symm, rfl, Or.inl ⟨rfl, rfl⟩, fun _ => rfl,
      fun _ => ⟨length, Nat.le_refl _, rfl, rfl, rfl⟩⟩
  · obtain ⟨dest, array, off, put, get, write, room, count, produced, privateWindow⟩ :=
      callerRange_slow_output good l output.range output.nonnull output.count output.produced
    obtain ⟨outcome, regs, after, stream, state, run, finalGood, data, inv, frame, kinds⟩ :=
      inflate_MATCH_boundary_ranges E good tables B put get write mode length offset sane
        room count produced privateWindow (B.output_positions put empty separate)
    rcases kinds with ⟨wait, regsEq, heapEq, stateEq⟩ | ⟨ok, bad, regsEq, i, msg, heapEq⟩ |
        ⟨ok, copy, source, sourceOffset, saved, positive, copyLeft, copyLength, regsEq, heapEq, stateEq, lengthEq, modes, decreases⟩
    · subst outcome regs after state
      exact ⟨.error Ex.leave, l, h, stream, s, 0, run, finalGood, data, inv, output, separate,
        ByteViewSizes.refl h, frame, by rfl, by omega, (inputAdvance_zero l.put).symm, rfl, Or.inl ⟨rfl, rfl⟩,
        fun _ => rfl, fun _ => ⟨length, Nat.le_refl _, rfl, rfl, rfl⟩⟩
    · subst outcome regs
      have sizes : ByteViewSizes h after := by
        rw [heapEq]
        exact (byte_view_sizes_stream_put h r { z with msg := .ref (.str i) 0 }).trans
          (byte_view_sizes_setI _ zs { s with mode := BAD })
      have readonly : ∀ ref : BRef, Space.ro after ref = Space.ro h ref := by
        intro ref
        rw [heapEq]
        unfold badHeap
        rw [byte_view_ro_setI, byte_view_ro_stream_put]
      have finalOutput := output.emit good finalGood (by rw [frame]) sizes readonly
        (inputAdvance_zero l.put).symm (made := 0) (by omega) rfl
      refine ⟨.ok (), l, after, stream, state, 0, run, finalGood, data, inv, finalOutput, separate,
        sizes, frame, by rfl, by omega, (inputAdvance_zero l.put).symm, rfl,
        Or.inr (Or.inl ⟨rfl, bad, rfl⟩), readonly, ?_⟩
      intro matching
      have ne : MATCH ≠ BAD := by decide
      exact False.elim (ne (matching.symm.trans bad))
    · subst outcome
      let bytes := ZlibF.Math.InflateMatchCopy.copy (decide (source = dest)) saved copy.toNat sourceOffset off array
      have size : bytes.size = array.size := ZlibF.Math.InflateMatchCopy.copy_size _ _ _ _ _ _
      have sizes : ByteViewSizes h after := by
        rw [heapEq]
        exact (byte_view_sizes_put get write bytes size).trans (byte_view_sizes_setI _ zs state)
      have readonly : ∀ ref : BRef, Space.ro after ref = Space.ro h ref := by
        intro ref
        rw [heapEq, byte_view_ro_setI, byte_view_ro_write]
      have countNat : (l.left - copy).toNat = l.left.toNat - copy.toNat := UInt32.toNat_sub_of_le _ _ copyLeft
      have left : regs.left.toNat + copy.toNat = l.left.toNat := by
        rw [regsEq]
        change (l.left - copy).toNat + copy.toNat = l.left.toNat
        rw [countNat]
        omega
      have nextPut : regs.put = inputAdvance l.put copy.toNat := by
        rw [regsEq]
        change Ptr.ref dest (off + copy.toNat) = inputAdvance l.put copy.toNat
        rw [put]
        rfl
      have finalOutput := output.emit good finalGood (by rw [frame]) sizes readonly nextPut left
        (by rw [regsEq])
      have nextSeparate : Separate regs.next regs.have_.toNat regs.put regs.left.toNat := by
        have advanced := separate_advance_output l.next l.put l.have_.toNat l.left.toNat copy.toNat copyLeft separate
        simpa only [regsEq, put, inputAdvance, countNat] using advanced
      refine ⟨.ok (), regs, after, stream, state, copy.toNat, run, finalGood, data, inv, finalOutput,
        nextSeparate, sizes, frame, ?_, left, nextPut, ?_, Or.inr (Or.inr ⟨rfl, positive, modes⟩), readonly, ?_⟩
      · rw [regsEq]
        rfl
      · rw [regsEq]
        rfl
      · intro matching
        rw [stateEq] at matching ⊢
        dsimp only [matchEmitState] at matching ⊢
        by_cases zero : (s.length - copy == 0) = true
        · simp only [zero, ↓reduceIte] at matching
          have ne : LEN ≠ MATCH := by decide
          exact False.elim (ne matching)
        · simp only [zero, Bool.false_eq_true, ↓reduceIte]
          have nonzero : (s.length - copy).toNat ≠ 0 := by
            intro zeroNat
            apply zero
            exact beq_iff_eq.mpr (UInt32.toNat_inj.mp zeroNat)
          have lengthNat := UInt32.toNat_sub_of_le s.length copy copyLength
          exact ⟨by omega, by omega, by trivial, by trivial, by trivial⟩

/-- Projection retaining the earlier exact output-accounting step. -/
theorem inflate_MATCH_output_step {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (B : BitInv h l bs) (output : OutputCursorInvariant h r l)
    (separate : Separate l.next l.have_.toNat l.put l.left.toNat)
    (mode : s.mode = MATCH) (length : 0 < s.length.toNat) (offset : 0 < s.offset.toNat) (sane : s.sane ≠ 0) :
    ∃ outcome regs after stream state made,
      runX (inflate_MATCH c) l h = .ok ((outcome, regs), after) ∧
      Good after r zs stream state ∧ DataTableInvariant after state ∧ BitInv after regs bs ∧
      OutputCursorInvariant after r regs ∧ Separate regs.next regs.have_.toNat regs.put regs.left.toNat ∧
      ByteViewSizes h after ∧ DecodeStateFrame s state ∧ EmitRegFrame l regs ∧
      regs.left.toNat + made = l.left.toNat ∧ regs.put = inputAdvance l.put made ∧
      Zlib.Inflate.Proofs.stream regs bs = Zlib.Inflate.Proofs.stream l bs ∧
      ((outcome = .error Ex.leave ∧ made = 0) ∨
        (outcome = .ok () ∧ state.mode = BAD ∧ made = 0) ∨
        (outcome = .ok () ∧ 0 < made ∧ (state.mode = LEN ∨ state.mode = MATCH))) := by
  obtain ⟨outcome, regs, after, stream, state, made, run, finalGood, data, inv,
    output, separate, sizes, stateFrame, regFrame, count, put, bits, kinds, _, _⟩ :=
      inflate_MATCH_output_step_frame E good tables B output separate mode length offset sane
  exact ⟨outcome, regs, after, stream, state, made, run, finalGood, data, inv,
    output, separate, sizes, stateFrame, regFrame, count, put, bits, kinds⟩

/-- MATCH preserves the same complete buffer relation used by the next
dispatch iteration. Its residual guard is suitable for a resumed match. -/
theorem inflate_MATCH_dispatch {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (buffers : DispatchBuffers h r l bs)
    (mode : s.mode = MATCH) (length : 0 < s.length.toNat) (offset : 0 < s.offset.toNat) (sane : s.sane ≠ 0) :
    ∃ outcome regs after stream state made,
      runX (inflate_MATCH c) l h = .ok ((outcome, regs), after) ∧
      Good after r zs stream state ∧ DataTableInvariant after state ∧ DispatchBuffers after r regs bs ∧
      ByteViewSizes h after ∧ DecodeStateFrame s state ∧ EmitRegFrame l regs ∧ MatchResidual s state ∧
      regs.left.toNat + made = l.left.toNat ∧ regs.put = inputAdvance l.put made ∧
      ((outcome = .error Ex.leave ∧ made = 0) ∨
        (outcome = .ok () ∧ state.mode = BAD ∧ made = 0) ∨
        (outcome = .ok () ∧ 0 < made ∧ (state.mode = LEN ∨ state.mode = MATCH))) := by
  obtain ⟨outcome, regs, after, stream, state, made, run, finalGood, data, inv,
    output, separate, sizes, stateFrame, regFrame, count, put, _, kinds, readonly, residual⟩ :=
      inflate_MATCH_output_step_frame E good tables buffers.bits buffers.output buffers.separate mode length offset sane
  have currentBuffers := buffers.emit good finalGood (by rw [stateFrame]) sizes readonly regFrame output inv separate
  exact ⟨outcome, regs, after, stream, state, made, run, finalGood, data, currentBuffers,
    sizes, stateFrame, regFrame, residual, count, put, kinds⟩

end Zlib.Inflate.Proofs
