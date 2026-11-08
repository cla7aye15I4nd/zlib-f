import ZlibF.Proof.«inflate.c.lookup-length»
import ZlibF.Proof.«inflate.c.decode-state»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inffast.Spec
set_option autoImplicit false

/-- The actual slow LEN prefix resolves its tables from the current heap.
It safely leaves on exhausted input, or enters the actual finishing suffix
with a proved leaf, bounded back count and enough held bits. The successor
suffix is executed by the source; no callee contract is assumed here. -/
theorem inflate_LEN_slow_lookup_boundary_mode {c : Ctx} {l : IL} {h : Heap}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8}
    (hc : c.st = some (.tab zs)) (good : Good h r zs z s)
    (tables : DataTablesSafe h s) (B : BitInv h l bs)
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    (∃ regs after state used,
      used ≤ 4 ∧ used ≤ bs.length ∧
      runX (inflate_LEN c) l h = .ok ((.error Ex.leave, regs), after) ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧
      BitInv after regs (bs.drop used) ∧ regs.have_ = 0 ∧
      stream regs (bs.drop used) = stream l bs ∧ SymbolRegShape l regs ∧
      DecodeStateFrame s state ∧ regs.bits.toNat ≤ max l.bits.toNat 22 ∧ regs.next = inputAdvance l.next used ∧ after = setI h zs state ∧ state.mode = s.mode) ∨
    (∃ regs after state used dropped,
      used ≤ 4 ∧ used ≤ bs.length ∧ dropped ≤ 15 ∧
      runX (inflate_LEN c) l h = runX (lenFinish c) regs after ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧
      BitInv after regs (bs.drop used) ∧ LenLeaf dropped regs.here ∧
      regs.here.bits.toNat ≤ regs.bits.toNat ∧ state.back = Int32.ofNat dropped ∧
      stream regs (bs.drop used) = (stream l bs).drop dropped ∧
      SymbolRegShape l regs ∧ DecodeStateFrame s state ∧
      regs.bits.toNat = l.bits.toNat + 8 * used - dropped ∧
      regs.bits.toNat ≤ max l.bits.toNat 22 ∧ after = setI h zs state ∧ regs.next = inputAdvance l.next used) := by
  let reset := { s with back := 0 }
  let heap := setI h zs reset
  have resetGood : Good heap r zs z reset := good.decode_update rfl good.live.mode
  have resetTables : DataTablesSafe heap reset := tables.decode_update good.live.hs rfl
  obtain ⟨ref, offset, array, pointer, tableGet, tableSafe⟩ := resetTables.lengthTable
  obtain ⟨result, regs, used, after, run, usedFour, usedBound, inv, shape, bitBound, kinds, done, leave, cursor⟩ :=
    lenLookup_run_cursor hc resetGood.live.hs pointer tableGet tableSafe rfl (B.decode_update zs reset)
  have source : runX (inflate_LEN c) l h = runX (do lenLookup c; lenFinish c) l heap := by
    rw [inflate_LEN_slow_cut slow, lenSlow_split]
    have write : wrS c.st (fun s => { s with back := 0 }) h = .ok ((), heap) := by rw [hc, wrI_eq, good.live.hs]
    rw [runX_bind, runX_lift_ok write]
  cases result with
  | error e =>
    have equal : e = Ex.leave := by
      rcases kinds with impossible | equal
      · cases impossible
      · exact Except.error.inj equal
    subst e
    obtain ⟨heapEq, empty, bits⟩ := leave rfl
    subst after
    left
    refine ⟨regs, heap, reset, used, usedFour, usedBound, ?_, resetGood, resetTables,
      inv, empty, bits, shape, rfl, bitBound, cursor, rfl, rfl⟩
    rw [source, runX_bind, run]
  | ok unit =>
    cases unit
    obtain ⟨dropped, dropBound, heapEq, leaf, enough, bits, count⟩ := done rfl
    subst after
    let state := { reset with back := Int32.ofNat dropped }
    have finalGood : Good (setI heap zs state) r zs z state :=
      resetGood.decode_update rfl resetGood.live.mode
    have finalTables : DataTablesSafe (setI heap zs state) state :=
      resetTables.decode_update resetGood.live.hs rfl
    right
    refine ⟨regs, setI heap zs state, state, used, dropped, usedFour, usedBound, dropBound,
      ?_, finalGood, finalTables, inv, leaf, enough, rfl, bits, shape, rfl, count, bitBound, by simp [heap], cursor⟩
    rw [source, runX_bind, run]

/-- Projection retaining the previous boundary. -/
theorem inflate_LEN_slow_lookup_boundary_frame {c : Ctx} {l : IL} {h : Heap}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8}
    (hc : c.st = some (.tab zs)) (good : Good h r zs z s)
    (tables : DataTablesSafe h s) (B : BitInv h l bs)
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    (∃ regs after state used,
      used ≤ 4 ∧ used ≤ bs.length ∧
      runX (inflate_LEN c) l h = .ok ((.error Ex.leave, regs), after) ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧
      BitInv after regs (bs.drop used) ∧ regs.have_ = 0 ∧
      stream regs (bs.drop used) = stream l bs ∧ SymbolRegShape l regs ∧
      DecodeStateFrame s state ∧ regs.bits.toNat ≤ max l.bits.toNat 22 ∧ regs.next = inputAdvance l.next used ∧ after = setI h zs state) ∨
    (∃ regs after state used dropped,
      used ≤ 4 ∧ used ≤ bs.length ∧ dropped ≤ 15 ∧
      runX (inflate_LEN c) l h = runX (lenFinish c) regs after ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧
      BitInv after regs (bs.drop used) ∧ LenLeaf dropped regs.here ∧
      regs.here.bits.toNat ≤ regs.bits.toNat ∧ state.back = Int32.ofNat dropped ∧
      stream regs (bs.drop used) = (stream l bs).drop dropped ∧
      SymbolRegShape l regs ∧ DecodeStateFrame s state ∧
      regs.bits.toNat = l.bits.toNat + 8 * used - dropped ∧
      regs.bits.toNat ≤ max l.bits.toNat 22 ∧ after = setI h zs state ∧ regs.next = inputAdvance l.next used) := by
  rcases inflate_LEN_slow_lookup_boundary_mode hc good tables B slow with stopped | continued
  · obtain ⟨regs, after, state, used, four, usedBound, run, finalGood, finalTables,
      inv, empty, bits, shape, frame, bitBound, cursor, heapEq, _⟩ := stopped
    exact Or.inl ⟨regs, after, state, used, four, usedBound, run, finalGood, finalTables,
      inv, empty, bits, shape, frame, bitBound, cursor, heapEq⟩
  · exact Or.inr continued

/-- Projection retaining the earlier input-cursor boundary. -/
theorem inflate_LEN_slow_lookup_boundary_cursor {c : Ctx} {l : IL} {h : Heap}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8}
    (hc : c.st = some (.tab zs)) (good : Good h r zs z s)
    (tables : DataTablesSafe h s) (B : BitInv h l bs)
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    (∃ regs after state used,
      used ≤ 4 ∧ used ≤ bs.length ∧
      runX (inflate_LEN c) l h = .ok ((.error Ex.leave, regs), after) ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧
      BitInv after regs (bs.drop used) ∧ regs.have_ = 0 ∧
      stream regs (bs.drop used) = stream l bs ∧ SymbolRegShape l regs ∧
      DecodeStateFrame s state ∧ regs.bits.toNat ≤ max l.bits.toNat 22 ∧ regs.next = inputAdvance l.next used) ∨
    (∃ regs after state used dropped,
      used ≤ 4 ∧ used ≤ bs.length ∧ dropped ≤ 15 ∧
      runX (inflate_LEN c) l h = runX (lenFinish c) regs after ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧
      BitInv after regs (bs.drop used) ∧ LenLeaf dropped regs.here ∧
      regs.here.bits.toNat ≤ regs.bits.toNat ∧ state.back = Int32.ofNat dropped ∧
      stream regs (bs.drop used) = (stream l bs).drop dropped ∧
      SymbolRegShape l regs ∧ DecodeStateFrame s state ∧
      regs.bits.toNat = l.bits.toNat + 8 * used - dropped ∧
      regs.bits.toNat ≤ max l.bits.toNat 22 ∧ after = setI h zs state ∧ regs.next = inputAdvance l.next used) := by
  rcases inflate_LEN_slow_lookup_boundary_frame hc good tables B slow with stopped | continued
  · obtain ⟨regs, after, state, used, four, usedBound, run, finalGood, finalTables,
      inv, empty, bits, shape, frame, bitBound, cursor, _⟩ := stopped
    exact Or.inl ⟨regs, after, state, used, four, usedBound, run, finalGood, finalTables,
      inv, empty, bits, shape, frame, bitBound, cursor⟩
  · exact Or.inr continued

/-- Projection retaining the original private-heap lookup boundary. -/
theorem inflate_LEN_slow_lookup_boundary_heap {c : Ctx} {l : IL} {h : Heap}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8}
    (hc : c.st = some (.tab zs)) (good : Good h r zs z s)
    (tables : DataTablesSafe h s) (B : BitInv h l bs)
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    (∃ regs after state used,
      used ≤ 4 ∧ used ≤ bs.length ∧
      runX (inflate_LEN c) l h = .ok ((.error Ex.leave, regs), after) ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧
      BitInv after regs (bs.drop used) ∧ regs.have_ = 0 ∧
      stream regs (bs.drop used) = stream l bs ∧ SymbolRegShape l regs ∧
      DecodeStateFrame s state ∧ regs.bits.toNat ≤ max l.bits.toNat 22) ∨
    (∃ regs after state used dropped,
      used ≤ 4 ∧ used ≤ bs.length ∧ dropped ≤ 15 ∧
      runX (inflate_LEN c) l h = runX (lenFinish c) regs after ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧
      BitInv after regs (bs.drop used) ∧ LenLeaf dropped regs.here ∧
      regs.here.bits.toNat ≤ regs.bits.toNat ∧ state.back = Int32.ofNat dropped ∧
      stream regs (bs.drop used) = (stream l bs).drop dropped ∧
      SymbolRegShape l regs ∧ DecodeStateFrame s state ∧
      regs.bits.toNat = l.bits.toNat + 8 * used - dropped ∧
      regs.bits.toNat ≤ max l.bits.toNat 22 ∧ after = setI h zs state) := by
  rcases inflate_LEN_slow_lookup_boundary_cursor hc good tables B slow with stopped | continued
  · obtain ⟨regs, after, state, used, four, usedBound, run, finalGood, finalTables,
      inv, empty, bits, shape, frame, bitBound, _⟩ := stopped
    exact Or.inl ⟨regs, after, state, used, four, usedBound, run, finalGood, finalTables,
      inv, empty, bits, shape, frame, bitBound⟩
  · obtain ⟨regs, after, state, used, dropped, four, usedBound, dropBound, run,
      finalGood, finalTables, inv, leaf, enough, back, bits, shape, frame, count, bound, heap, _⟩ := continued
    exact Or.inr ⟨regs, after, state, used, dropped, four, usedBound, dropBound, run,
      finalGood, finalTables, inv, leaf, enough, back, bits, shape, frame, count, bound, heap⟩

/-- Projection retaining the original lookup boundary. -/
theorem inflate_LEN_slow_lookup_boundary {c : Ctx} {l : IL} {h : Heap}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8}
    (hc : c.st = some (.tab zs)) (good : Good h r zs z s)
    (tables : DataTablesSafe h s) (B : BitInv h l bs)
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    (∃ regs after state used,
      used ≤ 4 ∧ used ≤ bs.length ∧
      runX (inflate_LEN c) l h = .ok ((.error Ex.leave, regs), after) ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧
      BitInv after regs (bs.drop used) ∧ regs.have_ = 0 ∧
      stream regs (bs.drop used) = stream l bs ∧ SymbolRegShape l regs ∧
      DecodeStateFrame s state ∧ regs.bits.toNat ≤ max l.bits.toNat 22) ∨
    (∃ regs after state used dropped,
      used ≤ 4 ∧ used ≤ bs.length ∧ dropped ≤ 15 ∧
      runX (inflate_LEN c) l h = runX (lenFinish c) regs after ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧
      BitInv after regs (bs.drop used) ∧ LenLeaf dropped regs.here ∧
      regs.here.bits.toNat ≤ regs.bits.toNat ∧ state.back = Int32.ofNat dropped ∧
      stream regs (bs.drop used) = (stream l bs).drop dropped ∧
      SymbolRegShape l regs ∧ DecodeStateFrame s state ∧
      regs.bits.toNat = l.bits.toNat + 8 * used - dropped ∧
      regs.bits.toNat ≤ max l.bits.toNat 22) := by
  rcases inflate_LEN_slow_lookup_boundary_heap hc good tables B slow with stopped | continued
  · exact Or.inl stopped
  · obtain ⟨regs, after, state, used, dropped, four, usedBound, dropBound, run,
      finalGood, finalTables, inv, leaf, enough, back, bits, shape, frame, count, bound, _⟩ := continued
    exact Or.inr ⟨regs, after, state, used, dropped, four, usedBound, dropBound, run,
      finalGood, finalTables, inv, leaf, enough, back, bits, shape, frame, count, bound⟩

end Zlib.Inflate.Proofs
