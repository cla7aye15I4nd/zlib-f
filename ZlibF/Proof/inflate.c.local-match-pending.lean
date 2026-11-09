import ZlibF.Proof.«inflate.c.local-data-output»
import ZlibF.Proof.«inflate.c.pending-invariant»

/-! Actual decoder execution with local allocation uniqueness. -/
namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inffast.Spec ZlibF.Spec.Public
set_option autoImplicit false
set_option maxRecDepth 8192

theorem inflate_MATCH_step_input {c : Ctx} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (E : Env c h r zs z s) (good : LocalGood h cutoff r zs z s) (tables : DataTablesSafe h s)
    {l : IL} {bs : List UInt8} (B : BitInv h l bs)
    (mode : s.mode = MATCH) (length : 0 < s.length.toNat) (lengthWas : s.length.toNat ≤ s.was.toNat)
    (wasBound : s.was.toNat ≤ 258) (offset : 0 < s.offset.toNat) (sane : s.sane ≠ 0)
    (output : l.left ≠ 0 → ∃ (dest : BRef) (array : Array UInt8) (outOffset : Nat),
      l.put = .ref dest outOffset ∧ Space.get h dest = some array ∧ Space.ro h dest = false ∧
      outOffset + l.left.toNat ≤ array.size ∧ l.left.toNat ≤ l.out_.toNat ∧
      l.out_.toNat - l.left.toNat ≤ outOffset ∧
      (∀ w, s.window = .ref (.blk w) 0 → dest ≠ .blk w) ∧
      (bs = [] ∨ ∀ i, l.next = .ref dest i → i + bs.length ≤ outOffset ∨ outOffset + l.left.toNat ≤ i)) :
    ∃ outcome regs after stream state,
      runX (inflate_MATCH c) l h = .ok ((outcome, regs), after) ∧
      LocalGood after cutoff r zs stream state ∧ DataTableInvariant after state ∧ BitInv after regs bs ∧
      DecodeStateFrame s state ∧
      (outcome = .error Ex.leave ∨ outcome = .ok ()) ∧
      (state.mode = MATCH ∨ state.mode = LEN ∨ state.mode = BAD) ∧
      (state.mode = MATCH → 0 < state.length.toNat ∧ state.length.toNat ≤ state.was.toNat ∧
        state.was.toNat ≤ 258 ∧ state.offset = s.offset ∧ state.was = s.was ∧ state.sane = s.sane) ∧
      (outcome = .ok () → state.mode = BAD ∨ regs.left.toNat < l.left.toNat) ∧
      Zlib.Inflate.Proofs.stream regs bs = Zlib.Inflate.Proofs.stream l bs := by
  by_cases empty : l.left = 0
  · refine ⟨.error Ex.leave, l, h, z, s, inflate_MATCH_wait c h l empty, good,
      fun _ => tables, B, by rfl, Or.inl rfl, Or.inl mode,
      fun _ => ⟨length, lengthWas, wasBound, rfl, rfl, rfl⟩, ?_, rfl⟩
    intro impossible
    cases impossible
  · obtain ⟨dest, array, outOffset, put, get, write, room, count, produced, privateWindow, separate⟩ := output empty
    obtain ⟨outcome, regs, after, stream, state, run, finalGood, data, inv, frame, kinds⟩ :=
      inflate_MATCH_boundary_ranges E good tables B put get write mode length offset sane
        room count produced privateWindow separate
    refine ⟨outcome, regs, after, stream, state, run, finalGood, data, inv, frame, ?_, ?_, ?_, ?_, ?_⟩
    · rcases kinds with ⟨wait, _⟩ | ⟨ok, _⟩ | ⟨ok, _⟩
      · exact Or.inl wait
      · exact Or.inr ok
      · exact Or.inr ok
    · rcases kinds with ⟨_, _, _, stateEq⟩ | ⟨_, bad, _⟩ | ⟨_, copy, source, sourceOffset, saved, _, _, _, _, _, _, _, modes, _⟩
      · exact Or.inl ((congrArg InflateState.mode stateEq).trans mode)
      · exact Or.inr (Or.inr bad)
      · rcases modes with len | matchMode
        · exact Or.inr (Or.inl len)
        · exact Or.inl matchMode
    · intro matching
      rcases kinds with ⟨_, _, _, stateEq⟩ | ⟨_, bad, _⟩ | ⟨_, copy, source, sourceOffset, saved, positive, copyLeft, copyLength, _, _, stateEq, _, _, _⟩
      · subst state
        exact ⟨length, lengthWas, wasBound, rfl, rfl, rfl⟩
      · have impossible : MATCH ≠ BAD := by decide
        exact False.elim (impossible (matching.symm.trans bad))
      · rw [stateEq] at matching ⊢
        dsimp only [matchEmitState] at matching ⊢
        by_cases remaining : (s.length - copy == 0) = true
        · simp only [remaining, ↓reduceIte] at matching
          have impossible : LEN ≠ MATCH := by decide
          exact False.elim (impossible matching)
        · simp only [remaining, Bool.false_eq_true, ↓reduceIte]
          have nonzero : (s.length - copy).toNat ≠ 0 := by
            intro zero
            apply remaining
            exact beq_iff_eq.mpr (UInt32.toNat_inj.mp zero)
          have lengthNat := UInt32.toNat_sub_of_le s.length copy (by exact copyLength)
          exact ⟨by omega, by omega, wasBound, by trivial, by trivial, by trivial⟩
    · intro ok
      rcases kinds with ⟨wait, _⟩ | ⟨_, bad, _⟩ | ⟨_, copy, source, sourceOffset, saved, _, _, _, _, _, _, _, _, decrease⟩
      · rw [ok] at wait
        cases wait
      · exact Or.inl bad
      · exact Or.inr decrease

    · rcases kinds with ⟨_, regsEq, _, _⟩ | ⟨_, _, regsEq, _⟩ |
          ⟨_, copy, source, sourceOffset, saved, _, _, _, regsEq, _⟩
      · rw [regsEq]
      · rw [regsEq]
      · rw [regsEq]
        rfl

theorem inflate_MATCH_pending {c : Ctx} {l : IL} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8}
    (E : Env c h r zs z s) (good : LocalGood h cutoff r zs z s) (tables : DataTablesSafe h s)
    (buffers : DispatchBuffers h r l bs) (pending : DataPendingInvariant s) (mode : s.mode = MATCH) :
    ∃ outcome regs after stream state made,
      runX (inflate_MATCH c) l h = .ok ((outcome, regs), after) ∧
      LocalGood after cutoff r zs stream state ∧ DataTableInvariant after state ∧ DispatchBuffers after r regs bs ∧
      DataPendingInvariant state ∧ ByteViewSizes h after ∧ DecodeStateFrame s state ∧
      regs.left.toNat + made = l.left.toNat ∧ regs.put = inputAdvance l.put made ∧
      EmitRegFrame l regs ∧ Zlib.Inflate.Proofs.stream regs bs = Zlib.Inflate.Proofs.stream l bs ∧
      ((outcome = .error Ex.leave ∧ made = 0) ∨
        (outcome = .ok () ∧ state.mode = BAD ∧ made = 0) ∨
        (outcome = .ok () ∧ 0 < made ∧ (state.mode = LEN ∨ state.mode = MATCH))) := by
  have matchFacts := pending.matching mode
  have sane : s.sane ≠ 0 := by rw [pending.sane]; decide
  obtain ⟨outcome, regs, after, stream, state, made, run, finalGood, data, packet, sizes,
      frame, regFrame, residual, count, put, kinds⟩ :=
    inflate_MATCH_dispatch E good tables buffers mode matchFacts.1 matchFacts.2.2.2 sane
  have output : l.left ≠ 0 → ∃ (dest : BRef) (array : Array UInt8) (off : Nat),
      l.put = .ref dest off ∧ Space.get h dest = some array ∧ Space.ro h dest = false ∧
      off + l.left.toNat ≤ array.size ∧ l.left.toNat ≤ l.out_.toNat ∧
      l.out_.toNat - l.left.toNat ≤ off ∧
      (∀ w, s.window = .ref (.blk w) 0 → dest ≠ .blk w) ∧
      (bs = [] ∨ ∀ i, l.next = .ref dest i → i + bs.length ≤ off ∨ off + l.left.toNat ≤ i) := by
    intro nonempty
    obtain ⟨dest, array, off, ptr, get, write, room, total, produced, privateWindow⟩ :=
      callerRange_slow_output good l buffers.output.range buffers.output.nonnull
        buffers.output.count buffers.output.produced
    exact ⟨dest, array, off, ptr, get, write, room, total, produced, privateWindow,
      buffers.bits.output_positions ptr nonempty buffers.separate⟩
  obtain ⟨otherOutcome, otherRegs, otherHeap, otherStream, otherState, otherRun,
    otherGood, _, _, _, _, modes, retained, _, _⟩ :=
    inflate_MATCH_step_input E good tables buffers.bits mode matchFacts.1 matchFacts.2.1
      matchFacts.2.2.1 matchFacts.2.2.2 sane output
  have sameHeap : otherHeap = after :=
    congrArg Prod.snd (Except.ok.inj (otherRun.symm.trans run))
  have sameState : otherState = state := by
    apply Option.some.inj
    exact otherGood.live.hs.symm.trans (by rw [sameHeap]; exact finalGood.live.hs)
  subst otherState
  have invariant : DataPendingInvariant state := by
    apply dataPendingInvariant_match_modes (by rw [frame]; exact pending.sane) modes
    intro matching
    obtain ⟨positive, lengthWas, wasBound, offsetEq, _, _⟩ := retained matching
    exact ⟨positive, lengthWas, wasBound, by rw [offsetEq]; exact matchFacts.2.2.2⟩
  exact ⟨outcome, regs, after, stream, state, made, run, finalGood, data, packet,
    invariant, sizes, frame, count, put, regFrame, by rw [regFrame]; rfl, kinds⟩

#print axioms inflate_MATCH_step_input
#print axioms inflate_MATCH_pending
end Zlib.Inflate.Local
