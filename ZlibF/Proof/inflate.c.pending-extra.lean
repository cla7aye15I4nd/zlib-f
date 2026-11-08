import ZlibF.Proof.«inflate.c.pending-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

/-- Actual LENEXT retains its pending scalar clause on exhausted input,
or establishes the DIST clause for the actual continuation. -/
theorem inflate_LENEXT_pending_boundary {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (buffers : DispatchBuffers h r l bs) (pending : DataPendingInvariant s) (mode : s.mode = LENEXT) :
    (∃ regs used,
      runX (inflate_LENEXT c) l h = .ok ((.error Ex.leave, regs), h) ∧ used ≤ bs.length ∧
      DispatchBuffers h r regs (bs.drop used) ∧
      stream regs (bs.drop used) = stream l bs ∧ SymbolRegShape l regs ∧ regs.next = inputAdvance l.next used ∧ regs.bits.toNat ≤ max l.bits.toNat 22) ∨
    (∃ regs after state used,
      runX (inflate_LENEXT c) l h = runX (inflate_DIST c) regs after ∧ used ≤ bs.length ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧
      DispatchBuffers after r regs (bs.drop used) ∧ DataPendingInvariant state ∧
      state.mode = DIST ∧ DecodeStateFrame s state ∧ ByteViewSizes h after ∧
      stream regs (bs.drop used) = (stream l bs).drop s.extra.toNat ∧ SymbolRegShape l regs ∧
      regs.next = inputAdvance l.next used ∧ after = setI h zs state ∧ regs.bits.toNat ≤ max l.bits.toNat 22) := by
  obtain ⟨extra, lower, budget, before, backBound, back⟩ := pending.lenext mode
  rcases inflate_LENEXT_boundary_bounded before E.strm E.st good tables buffers.bits
      extra lower budget back backBound with wait | continued
  · obtain ⟨regs, used, run, usedBound, inv, _, bits, shape, cursor, bitBound⟩ := wait
    have packet := buffers.consume good good rfl (fun _ => rfl) (fun _ => rfl) shape cursor usedBound inv
    exact Or.inl ⟨regs, used, run, usedBound, packet, bits, shape, cursor, by omega⟩
  · obtain ⟨regs, after, state, used, run, usedBound, finalGood, finalTables, inv,
      nextMode, frame, shape, bits, was, finalLower, finalUpper, finalBack, heapEq, cursor, bitBound⟩ := continued
    have packet : DispatchBuffers after r regs (bs.drop used) := by
      apply buffers.consume good finalGood (by rw [frame]) _ _ shape cursor usedBound inv
      · intro ref
        rw [heapEq, byte_view_get_setI]
      · intro ref
        rw [heapEq, byte_view_ro_setI]
    have invariant := dataPendingInvariant_dist (by rw [frame]; exact pending.sane) nextMode
      ⟨⟨finalLower, finalUpper, was⟩, before + s.extra.toNat, by omega, finalBack⟩
    exact Or.inr ⟨regs, after, state, used, run, usedBound, finalGood, finalTables, packet,
      invariant, nextMode, frame, by rw [heapEq]; exact byte_view_sizes_setI h zs state, bits, shape, cursor, heapEq, by omega⟩

/-- Actual DISTEXT retains its pending scalar clause on exhausted input,
or establishes a positive pending match before the real MATCH call. -/
theorem inflate_DISTEXT_pending_boundary {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (buffers : DispatchBuffers h r l bs) (pending : DataPendingInvariant s) (mode : s.mode = DISTEXT) :
    (∃ regs used,
      runX (inflate_DISTEXT c) l h = .ok ((.error Ex.leave, regs), h) ∧ used ≤ bs.length ∧
      DispatchBuffers h r regs (bs.drop used) ∧
      stream regs (bs.drop used) = stream l bs ∧ SymbolRegShape l regs ∧ regs.next = inputAdvance l.next used ∧ regs.bits.toNat ≤ max l.bits.toNat 22) ∨
    (∃ regs after state used,
      runX (inflate_DISTEXT c) l h = runX (inflate_MATCH c) regs after ∧ used ≤ bs.length ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧
      DispatchBuffers after r regs (bs.drop used) ∧ DataPendingInvariant state ∧
      state.mode = MATCH ∧ DecodeStateFrame s state ∧ ByteViewSizes h after ∧
      stream regs (bs.drop used) = (stream l bs).drop s.extra.toNat ∧ SymbolRegShape l regs ∧
      regs.next = inputAdvance l.next used ∧ after = setI h zs state ∧ regs.bits.toNat ≤ max l.bits.toNat 22) := by
  obtain ⟨lengthFacts, extra, lower, budget, before, backBound, back⟩ := pending.distext mode
  rcases inflate_DISTEXT_boundary_bounded before E.strm E.st good tables buffers.bits
      extra lower budget back backBound with wait | continued
  · obtain ⟨regs, used, run, usedBound, inv, _, bits, shape, cursor, bitBound⟩ := wait
    have packet := buffers.consume good good rfl (fun _ => rfl) (fun _ => rfl) shape cursor usedBound inv
    exact Or.inl ⟨regs, used, run, usedBound, packet, bits, shape, cursor, by omega⟩
  · obtain ⟨regs, after, state, used, run, usedBound, finalGood, finalTables, inv,
      nextMode, frame, shape, bits, heapEq, stateEq, finalLower, _, _, cursor, bitBound⟩ := continued
    have packet : DispatchBuffers after r regs (bs.drop used) := by
      apply buffers.consume good finalGood (by rw [frame]) _ _ shape cursor usedBound inv
      · intro ref
        rw [heapEq, byte_view_get_setI]
      · intro ref
        rw [heapEq, byte_view_ro_setI]
    have facts : MatchSafe state := by
      rw [stateEq]
      change 0 < s.length.toNat ∧ s.length.toNat ≤ s.was.toNat ∧ s.was.toNat ≤ 258 ∧ 0 < state.offset.toNat
      obtain ⟨lengthLower, lengthUpper, was⟩ := lengthFacts
      rw [was]
      exact ⟨by omega, Nat.le_refl _, lengthUpper, by omega⟩
    have invariant := dataPendingInvariant_match (by rw [frame]; exact pending.sane) nextMode facts
    exact Or.inr ⟨regs, after, state, used, run, usedBound, finalGood, finalTables, packet,
      invariant, nextMode, frame, by rw [heapEq]; exact byte_view_sizes_setI h zs state, bits, shape, cursor, heapEq, by omega⟩

end Zlib.Inflate.Proofs
