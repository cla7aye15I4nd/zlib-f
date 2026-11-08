import ZlibF.Proof.«inflate.c.distance-extra»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inffast.Spec
set_option autoImplicit false

/-- Complete actual DIST/DISTEXT execution up to the real MATCH call.
The extra-bit premises are established from the table leaf on the same run.
The precise final record frame preserves the pending length and was fields. -/
theorem inflate_DIST_to_MATCH_frame {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8} (before : Nat)
    (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (good : Good h r zs z s)
    (tables : DataTablesSafe h s) (B : BitInv h l bs)
    (back : s.back = Int32.ofNat before) (backBound : before ≤ 20) :
    (∃ outcome regs after finalZ state used consumed,
      used ≤ bs.length ∧ consumed ≤ 28 ∧
      runX (inflate_DIST c) l h = .ok ((outcome, regs), after) ∧
      Good after r zs finalZ state ∧ DataTableInvariant after state ∧ BitInv after regs (bs.drop used) ∧
      stream regs (bs.drop used) = (stream l bs).drop consumed ∧ SymbolRegShape l regs ∧
      (outcome = .error Ex.leave ∨ (outcome = .ok () ∧ state.mode = BAD)) ∧ regs.next = inputAdvance l.next used ∧
      DecodeStateFrame s state ∧ after = setI (r.put h finalZ) zs state) ∨
    (∃ regs after state used consumed,
      used ≤ bs.length ∧ consumed ≤ 28 ∧
      runX (inflate_DIST c) l h = runX (inflate_MATCH c) regs after ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧ BitInv after regs (bs.drop used) ∧
      stream regs (bs.drop used) = (stream l bs).drop consumed ∧ SymbolRegShape l regs ∧
      after = setI h zs state ∧
      state = { s with offset := state.offset, extra := state.extra, back := Int32.ofNat (before + consumed), mode := MATCH } ∧
      1 ≤ state.offset.toNat ∧ state.offset.toNat ≤ 73726 ∧ regs.next = inputAdvance l.next used) := by
  rcases inflate_DIST_lookup_boundary_cursor before hc good tables B back backBound with wait | continued
  · obtain ⟨regs, used, _, usedBound, run, inv, _, bits, shape, cursor⟩ := wait
    exact Or.inl ⟨.error Ex.leave, regs, h, z, s, used, 0, usedBound, by omega,
      run, good, fun _ => tables, inv, by simpa using bits, shape, Or.inl rfl, cursor, by rfl, by
        rw [ZStreamRef.put_self good.live.hz]; simp [setI, upd_self _ _ _ good.live.hs]⟩
  · obtain ⟨regs, rootHeap, rootState, used, dropped, _, usedBound, droppedBound,
      source, rootGood, rootTables, rootInv, leaf, enough, rootBack, rootBits, rootShape, _, _, rootHeapEq, rootFrame, cursor⟩ := continued
    obtain ⟨leafRegs, leafHeap, leafState, consumeRun, leafGood, leafTables, leafInv,
      _, leafShape, leafHeapEq, leafFrame, leafBits, _, _, leafCursor⟩ :=
      distFinish_consume_cursor before dropped hc rootGood rootTables leaf rootBack backBound enough rootInv
    let codeBits := dropped + regs.here.bits.toNat
    have codeBound : codeBits ≤ 15 := by have := leaf.1; omega
    have beforeBound : before + codeBits ≤ 35 := by omega
    have parsed : stream leafRegs (bs.drop used) = (stream l bs).drop codeBits := by
      rw [leafBits, rootBits, List.drop_drop]
    have source' : runX (inflate_DIST c) l h = runX (distLeafTail c regs.here) leafRegs leafHeap :=
      source.trans consumeRun
    rcases distLeafTail_boundary_frame hr hc leafGood leafTables leafInv leaf with invalid | valid
    · obtain ⟨after, finalZ, state, run, finalGood, data, inv, mode, badFrame, badHeapEq⟩ := invalid
      exact Or.inl ⟨.ok (), leafRegs, after, finalZ, state, used, codeBits, usedBound, by omega,
        source'.trans run, finalGood, data, inv, parsed, rootShape.trans leafShape, Or.inr ⟨rfl, mode⟩, leafCursor.trans cursor,
        by unfold DecodeStateFrame; rw [badFrame, leafFrame, rootFrame],
        by rw [badHeapEq, leafHeapEq, rootHeapEq, ZStreamRef.put_setI, ZStreamRef.put_setI, setI_setI, setI_setI]⟩
    · obtain ⟨baseHeap, baseState, classifyRun, baseGood, baseTables, baseInv, _, baseHeapEq,
        baseFrame, extra, lower, budget⟩ := valid
      have baseBack : baseState.back = Int32.ofNat (before + codeBits) := by
        rw [baseFrame, leafFrame]
        simp only [codeBits, Nat.add_assoc]
      rcases inflate_DISTEXT_boundary_cursor (before + codeBits) hr hc baseGood baseTables baseInv extra lower budget baseBack beforeBound with wait | continued
      · obtain ⟨finalRegs, used2, run, usedBound2, inv, _, bits, shape, cursor2⟩ := wait
        have totalBound : used + used2 ≤ bs.length := by simp only [List.length_drop] at usedBound2; omega
        have finalInv : BitInv baseHeap finalRegs (bs.drop (used + used2)) := by
          simpa only [List.drop_drop, Nat.add_comm] using inv
        have finalBits : stream finalRegs (bs.drop (used + used2)) = (stream l bs).drop codeBits := by
          simpa only [List.drop_drop, Nat.add_comm] using bits.trans parsed
        exact Or.inl ⟨.error Ex.leave, finalRegs, baseHeap, z, baseState, used + used2, codeBits,
          totalBound, by omega, source'.trans (classifyRun.trans run), baseGood, fun _ => baseTables,
          finalInv, finalBits, rootShape.trans (leafShape.trans shape), Or.inl rfl,
            by rw [cursor2, leafCursor, cursor, inputAdvance_add],
            by unfold DecodeStateFrame; rw [baseFrame, leafFrame, rootFrame],
            by rw [ZStreamRef.put_self good.live.hz, baseHeapEq, leafHeapEq, rootHeapEq, setI_setI, setI_setI]⟩
      · obtain ⟨finalRegs, after, state, used2, run, usedBound2, finalGood, finalTables, inv,
          _, _, shape, bits, heapEq, stateFrame, finalLower, finalUpper, _, cursor2⟩ := continued
        have totalBound : used + used2 ≤ bs.length := by simp only [List.length_drop] at usedBound2; omega
        have finalInv : BitInv after finalRegs (bs.drop (used + used2)) := by
          simpa only [List.drop_drop, Nat.add_comm] using inv
        have finalBits : stream finalRegs (bs.drop (used + used2)) =
            (stream l bs).drop (codeBits + baseState.extra.toNat) := by
          simp only [List.drop_drop] at bits
          rw [parsed, List.drop_drop] at bits
          exact bits
        have finalHeap : after = setI h zs state := by
          rw [heapEq, baseHeapEq, leafHeapEq, rootHeapEq, setI_setI, setI_setI, setI_setI]
        have finalFrame : state = { s with offset := state.offset, extra := state.extra, back := Int32.ofNat (before + (codeBits + baseState.extra.toNat)), mode := MATCH } := by
          rw [stateFrame, baseFrame, leafFrame, rootFrame]
          simp only [codeBits, Nat.add_assoc]
        exact Or.inr ⟨finalRegs, after, state, used + used2, codeBits + baseState.extra.toNat,
          totalBound, by omega, source'.trans (classifyRun.trans run), finalGood, finalTables,
          finalInv, finalBits, rootShape.trans (leafShape.trans shape), finalHeap, finalFrame, finalLower, finalUpper,
            by rw [cursor2, leafCursor, cursor, inputAdvance_add]⟩

/-- Projection retaining the previous boundary. -/
theorem inflate_DIST_to_MATCH_cursor {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8} (before : Nat)
    (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (good : Good h r zs z s)
    (tables : DataTablesSafe h s) (B : BitInv h l bs)
    (back : s.back = Int32.ofNat before) (backBound : before ≤ 20) :
    (∃ outcome regs after finalZ state used consumed,
      used ≤ bs.length ∧ consumed ≤ 28 ∧
      runX (inflate_DIST c) l h = .ok ((outcome, regs), after) ∧
      Good after r zs finalZ state ∧ DataTableInvariant after state ∧ BitInv after regs (bs.drop used) ∧
      stream regs (bs.drop used) = (stream l bs).drop consumed ∧ SymbolRegShape l regs ∧
      (outcome = .error Ex.leave ∨ (outcome = .ok () ∧ state.mode = BAD)) ∧ regs.next = inputAdvance l.next used) ∨
    (∃ regs after state used consumed,
      used ≤ bs.length ∧ consumed ≤ 28 ∧
      runX (inflate_DIST c) l h = runX (inflate_MATCH c) regs after ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧ BitInv after regs (bs.drop used) ∧
      stream regs (bs.drop used) = (stream l bs).drop consumed ∧ SymbolRegShape l regs ∧
      after = setI h zs state ∧
      state = { s with offset := state.offset, extra := state.extra, back := Int32.ofNat (before + consumed), mode := MATCH } ∧
      1 ≤ state.offset.toNat ∧ state.offset.toNat ≤ 73726 ∧ regs.next = inputAdvance l.next used) := by
  rcases inflate_DIST_to_MATCH_frame before hr hc good tables B back backBound with stopped | continued
  · obtain ⟨outcome, regs, after, finalZ, state, used, consumed, usedBound, consumedBound,
      run, finalGood, data, inv, bits, shape, kinds, cursor, _, _⟩ := stopped
    exact Or.inl ⟨outcome, regs, after, finalZ, state, used, consumed, usedBound, consumedBound,
      run, finalGood, data, inv, bits, shape, kinds, cursor⟩
  · exact Or.inr continued

/-- Projection retaining the original complete distance chain. -/
theorem inflate_DIST_to_MATCH {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8} (before : Nat)
    (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (good : Good h r zs z s)
    (tables : DataTablesSafe h s) (B : BitInv h l bs)
    (back : s.back = Int32.ofNat before) (backBound : before ≤ 20) :
    (∃ outcome regs after finalZ state used consumed,
      used ≤ bs.length ∧ consumed ≤ 28 ∧
      runX (inflate_DIST c) l h = .ok ((outcome, regs), after) ∧
      Good after r zs finalZ state ∧ DataTableInvariant after state ∧ BitInv after regs (bs.drop used) ∧
      stream regs (bs.drop used) = (stream l bs).drop consumed ∧ SymbolRegShape l regs ∧
      (outcome = .error Ex.leave ∨ (outcome = .ok () ∧ state.mode = BAD))) ∨
    (∃ regs after state used consumed,
      used ≤ bs.length ∧ consumed ≤ 28 ∧
      runX (inflate_DIST c) l h = runX (inflate_MATCH c) regs after ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧ BitInv after regs (bs.drop used) ∧
      stream regs (bs.drop used) = (stream l bs).drop consumed ∧ SymbolRegShape l regs ∧
      after = setI h zs state ∧
      state = { s with offset := state.offset, extra := state.extra, back := Int32.ofNat (before + consumed), mode := MATCH } ∧
      1 ≤ state.offset.toNat ∧ state.offset.toNat ≤ 73726) := by
  rcases inflate_DIST_to_MATCH_cursor before hr hc good tables B back backBound with stopped | continued
  · obtain ⟨outcome, regs, after, finalZ, state, used, consumed, usedBound, consumedBound,
      run, finalGood, data, inv, bits, shape, kinds, _⟩ := stopped
    exact Or.inl ⟨outcome, regs, after, finalZ, state, used, consumed, usedBound, consumedBound,
      run, finalGood, data, inv, bits, shape, kinds⟩
  · obtain ⟨regs, after, state, used, consumed, usedBound, consumedBound, run,
      finalGood, finalTables, inv, bits, shape, heap, stateEq, lower, upper, _⟩ := continued
    exact Or.inr ⟨regs, after, state, used, consumed, usedBound, consumedBound, run,
      finalGood, finalTables, inv, bits, shape, heap, stateEq, lower, upper⟩

/-- The actual complete slow symbol-decoding chain reaches a safe exit or
MATCH with a bounded pending length and positive distance. All intermediate
mode and counter premises are discharged by the same execution chain. -/
theorem inflate_LEN_slow_to_MATCH_frame {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (good : Good h r zs z s)
    (tables : DataTablesSafe h s) (B : BitInv h l bs)
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    (∃ outcome regs after finalZ state used consumed,
      used ≤ bs.length ∧ consumed ≤ 48 ∧
      runX (inflate_LEN c) l h = .ok ((outcome, regs), after) ∧
      Good after r zs finalZ state ∧ DataTableInvariant after state ∧ BitInv after regs (bs.drop used) ∧
      stream regs (bs.drop used) = (stream l bs).drop consumed ∧ SymbolRegShape l regs ∧
      (outcome = .error Ex.leave ∨ (outcome = .ok () ∧ (state.mode = LIT ∨ state.mode = TYPE ∨ state.mode = BAD))) ∧
      regs.next = inputAdvance l.next used ∧ DecodeStateFrame s state ∧
      after = setI (r.put h finalZ) zs state) ∨
    (∃ regs after state used consumed,
      used ≤ bs.length ∧ consumed ≤ 48 ∧
      runX (inflate_LEN c) l h = runX (inflate_MATCH c) regs after ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧ BitInv after regs (bs.drop used) ∧
      stream regs (bs.drop used) = (stream l bs).drop consumed ∧ SymbolRegShape l regs ∧
      state.mode = MATCH ∧ state.was = state.length ∧ 3 ≤ state.length.toNat ∧ state.length.toNat ≤ 258 ∧
      1 ≤ state.offset.toNat ∧ state.offset.toNat ≤ 73726 ∧ state.back = Int32.ofNat consumed ∧ DecodeStateFrame s state ∧ after = setI h zs state ∧ regs.next = inputAdvance l.next used) := by
  rcases inflate_LEN_slow_to_DIST_frame hr hc good tables B slow with stopped | continued
  · obtain ⟨outcome, regs, after, finalZ, state, used, consumed, usedBound, consumedBound,
      run, finalGood, data, inv, bits, shape, frame, kinds, cursor, heapEq⟩ := stopped
    exact Or.inl ⟨outcome, regs, after, finalZ, state, used, consumed, usedBound, by omega,
      run, finalGood, data, inv, bits, shape, kinds, cursor, frame, heapEq⟩
  · obtain ⟨regs, distanceHeap, distanceState, used, consumed, usedBound, consumedBound,
      source, distanceGood, distanceTables, distanceInv, bits, shape, lengthFrame, _, was, lower, upper, back, lengthHeapEq, cursor⟩ := continued
    rcases inflate_DIST_to_MATCH_frame consumed hr hc distanceGood distanceTables distanceInv back consumedBound with stopped | continued
    · obtain ⟨outcome, finalRegs, after, finalZ, state, used2, consumed2, usedBound2, consumedBound2,
        run, finalGood, data, inv, finalStream, finalShape, kinds, cursor2, finalFrame, finalHeapEq⟩ := stopped
      have totalBound : used + used2 ≤ bs.length := by simp only [List.length_drop] at usedBound2; omega
      have finalInv : BitInv after finalRegs (bs.drop (used + used2)) := by
        simpa only [List.drop_drop, Nat.add_comm] using inv
      have finalBits : stream finalRegs (bs.drop (used + used2)) =
          (stream l bs).drop (consumed + consumed2) := by
        simp only [List.drop_drop] at finalStream
        rw [bits, List.drop_drop] at finalStream
        exact finalStream
      have exits : outcome = .error Ex.leave ∨
          (outcome = .ok () ∧ (state.mode = LIT ∨ state.mode = TYPE ∨ state.mode = BAD)) := by
        rcases kinds with wait | ⟨ok, bad⟩
        · exact Or.inl wait
        · exact Or.inr ⟨ok, Or.inr (Or.inr bad)⟩
      exact Or.inl ⟨outcome, finalRegs, after, finalZ, state, used + used2, consumed + consumed2,
        totalBound, by omega, source.trans run, finalGood, data, finalInv, finalBits, shape.trans finalShape, exits, by rw [cursor2, cursor, inputAdvance_add],
          lengthFrame.trans finalFrame,
          by rw [finalHeapEq, lengthHeapEq, ZStreamRef.put_setI, setI_setI]⟩
    · obtain ⟨finalRegs, after, state, used2, consumed2, usedBound2, consumedBound2,
        run, finalGood, finalTables, inv, finalStream, finalShape, distanceHeapEq, frame, offsetLower, offsetUpper, cursor2⟩ := continued
      have totalBound : used + used2 ≤ bs.length := by simp only [List.length_drop] at usedBound2; omega
      have finalInv : BitInv after finalRegs (bs.drop (used + used2)) := by
        simpa only [List.drop_drop, Nat.add_comm] using inv
      have finalBits : stream finalRegs (bs.drop (used + used2)) =
          (stream l bs).drop (consumed + consumed2) := by
        simp only [List.drop_drop] at finalStream
        rw [bits, List.drop_drop] at finalStream
        exact finalStream
      refine Or.inr ⟨finalRegs, after, state, used + used2, consumed + consumed2,
        totalBound, by omega, source.trans run, finalGood, finalTables, finalInv, finalBits,
        shape.trans finalShape, ?_, ?_, ?_, ?_, offsetLower, offsetUpper, ?_, ?_, ?_, by rw [cursor2, cursor, inputAdvance_add]⟩
      · rw [frame]
      · rw [frame]
        exact was
      · rw [frame]
        exact lower
      · rw [frame]
        exact upper
      · rw [frame]

      · apply lengthFrame.trans
        unfold DecodeStateFrame
        rw [frame]

      · rw [distanceHeapEq, lengthHeapEq, setI_setI]
/-- Projection retaining the previous boundary. -/
theorem inflate_LEN_slow_to_MATCH_cursor {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (good : Good h r zs z s)
    (tables : DataTablesSafe h s) (B : BitInv h l bs)
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    (∃ outcome regs after finalZ state used consumed,
      used ≤ bs.length ∧ consumed ≤ 48 ∧
      runX (inflate_LEN c) l h = .ok ((outcome, regs), after) ∧
      Good after r zs finalZ state ∧ DataTableInvariant after state ∧ BitInv after regs (bs.drop used) ∧
      stream regs (bs.drop used) = (stream l bs).drop consumed ∧ SymbolRegShape l regs ∧
      (outcome = .error Ex.leave ∨ (outcome = .ok () ∧ (state.mode = LIT ∨ state.mode = TYPE ∨ state.mode = BAD))) ∧
      regs.next = inputAdvance l.next used) ∨
    (∃ regs after state used consumed,
      used ≤ bs.length ∧ consumed ≤ 48 ∧
      runX (inflate_LEN c) l h = runX (inflate_MATCH c) regs after ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧ BitInv after regs (bs.drop used) ∧
      stream regs (bs.drop used) = (stream l bs).drop consumed ∧ SymbolRegShape l regs ∧
      state.mode = MATCH ∧ state.was = state.length ∧ 3 ≤ state.length.toNat ∧ state.length.toNat ≤ 258 ∧
      1 ≤ state.offset.toNat ∧ state.offset.toNat ≤ 73726 ∧ state.back = Int32.ofNat consumed ∧ DecodeStateFrame s state ∧ after = setI h zs state ∧ regs.next = inputAdvance l.next used) := by
  rcases inflate_LEN_slow_to_MATCH_frame hr hc good tables B slow with stopped | continued
  · obtain ⟨outcome, regs, after, finalZ, state, used, consumed, usedBound, consumedBound,
      run, finalGood, data, inv, bits, shape, kinds, cursor, _, _⟩ := stopped
    exact Or.inl ⟨outcome, regs, after, finalZ, state, used, consumed, usedBound, consumedBound,
      run, finalGood, data, inv, bits, shape, kinds, cursor⟩
  · exact Or.inr continued

/-- Projection retaining the original slow-chain private heap frame. -/
theorem inflate_LEN_slow_to_MATCH_heap {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (good : Good h r zs z s)
    (tables : DataTablesSafe h s) (B : BitInv h l bs)
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    (∃ outcome regs after finalZ state used consumed,
      used ≤ bs.length ∧ consumed ≤ 48 ∧
      runX (inflate_LEN c) l h = .ok ((outcome, regs), after) ∧
      Good after r zs finalZ state ∧ DataTableInvariant after state ∧ BitInv after regs (bs.drop used) ∧
      stream regs (bs.drop used) = (stream l bs).drop consumed ∧ SymbolRegShape l regs ∧
      (outcome = .error Ex.leave ∨ (outcome = .ok () ∧ (state.mode = LIT ∨ state.mode = TYPE ∨ state.mode = BAD)))) ∨
    (∃ regs after state used consumed,
      used ≤ bs.length ∧ consumed ≤ 48 ∧
      runX (inflate_LEN c) l h = runX (inflate_MATCH c) regs after ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧ BitInv after regs (bs.drop used) ∧
      stream regs (bs.drop used) = (stream l bs).drop consumed ∧ SymbolRegShape l regs ∧
      state.mode = MATCH ∧ state.was = state.length ∧ 3 ≤ state.length.toNat ∧ state.length.toNat ≤ 258 ∧
      1 ≤ state.offset.toNat ∧ state.offset.toNat ≤ 73726 ∧ state.back = Int32.ofNat consumed ∧ DecodeStateFrame s state ∧ after = setI h zs state) := by
  rcases inflate_LEN_slow_to_MATCH_cursor hr hc good tables B slow with stopped | continued
  · obtain ⟨outcome, regs, after, finalZ, state, used, consumed, usedBound, consumedBound,
      run, finalGood, data, inv, bits, shape, kinds, _⟩ := stopped
    exact Or.inl ⟨outcome, regs, after, finalZ, state, used, consumed, usedBound, consumedBound,
      run, finalGood, data, inv, bits, shape, kinds⟩
  · obtain ⟨regs, after, state, used, consumed, usedBound, consumedBound, run,
      finalGood, finalTables, inv, bits, shape, mode, was, lower, upper, offsetLower, offsetUpper, back, frame, heap, _⟩ := continued
    exact Or.inr ⟨regs, after, state, used, consumed, usedBound, consumedBound, run,
      finalGood, finalTables, inv, bits, shape, mode, was, lower, upper, offsetLower, offsetUpper, back, frame, heap⟩

/-- Projection retaining the scalar frame of the full slow chain. -/
theorem inflate_LEN_slow_to_MATCH_full {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (good : Good h r zs z s)
    (tables : DataTablesSafe h s) (B : BitInv h l bs)
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    (∃ outcome regs after finalZ state used consumed,
      used ≤ bs.length ∧ consumed ≤ 48 ∧
      runX (inflate_LEN c) l h = .ok ((outcome, regs), after) ∧
      Good after r zs finalZ state ∧ DataTableInvariant after state ∧ BitInv after regs (bs.drop used) ∧
      stream regs (bs.drop used) = (stream l bs).drop consumed ∧ SymbolRegShape l regs ∧
      (outcome = .error Ex.leave ∨ (outcome = .ok () ∧ (state.mode = LIT ∨ state.mode = TYPE ∨ state.mode = BAD)))) ∨
    (∃ regs after state used consumed,
      used ≤ bs.length ∧ consumed ≤ 48 ∧
      runX (inflate_LEN c) l h = runX (inflate_MATCH c) regs after ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧ BitInv after regs (bs.drop used) ∧
      stream regs (bs.drop used) = (stream l bs).drop consumed ∧ SymbolRegShape l regs ∧
      state.mode = MATCH ∧ state.was = state.length ∧ 3 ≤ state.length.toNat ∧ state.length.toNat ≤ 258 ∧
      1 ≤ state.offset.toNat ∧ state.offset.toNat ≤ 73726 ∧ state.back = Int32.ofNat consumed ∧ DecodeStateFrame s state) := by
  rcases inflate_LEN_slow_to_MATCH_heap hr hc good tables B slow with stopped | continued
  · exact Or.inl stopped
  · obtain ⟨regs, after, state, used, consumed, usedBound, consumedBound, run,
      finalGood, finalTables, inv, bits, shape, mode, was, lower, upper, offsetLower, offsetUpper, back, frame, _⟩ := continued
    exact Or.inr ⟨regs, after, state, used, consumed, usedBound, consumedBound, run,
      finalGood, finalTables, inv, bits, shape, mode, was, lower, upper, offsetLower, offsetUpper, back, frame⟩

/-- Projection retaining the original complete slow lookup statement. -/
theorem inflate_LEN_slow_to_MATCH {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (good : Good h r zs z s)
    (tables : DataTablesSafe h s) (B : BitInv h l bs)
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    (∃ outcome regs after finalZ state used consumed,
      used ≤ bs.length ∧ consumed ≤ 48 ∧
      runX (inflate_LEN c) l h = .ok ((outcome, regs), after) ∧
      Good after r zs finalZ state ∧ DataTableInvariant after state ∧ BitInv after regs (bs.drop used) ∧
      stream regs (bs.drop used) = (stream l bs).drop consumed ∧ SymbolRegShape l regs ∧
      (outcome = .error Ex.leave ∨ (outcome = .ok () ∧ (state.mode = LIT ∨ state.mode = TYPE ∨ state.mode = BAD)))) ∨
    (∃ regs after state used consumed,
      used ≤ bs.length ∧ consumed ≤ 48 ∧
      runX (inflate_LEN c) l h = runX (inflate_MATCH c) regs after ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧ BitInv after regs (bs.drop used) ∧
      stream regs (bs.drop used) = (stream l bs).drop consumed ∧ SymbolRegShape l regs ∧
      state.mode = MATCH ∧ state.was = state.length ∧ 3 ≤ state.length.toNat ∧ state.length.toNat ≤ 258 ∧
      1 ≤ state.offset.toNat ∧ state.offset.toNat ≤ 73726 ∧ state.back = Int32.ofNat consumed) := by
  rcases inflate_LEN_slow_to_MATCH_full hr hc good tables B slow with stopped | continued
  · exact Or.inl stopped
  · obtain ⟨regs, after, state, used, consumed, usedBound, consumedBound,
      run, finalGood, finalTables, inv, bits, shape, mode, was, lower, upper,
      offsetLower, offsetUpper, back, _⟩ := continued
    exact Or.inr ⟨regs, after, state, used, consumed, usedBound, consumedBound,
      run, finalGood, finalTables, inv, bits, shape, mode, was, lower, upper,
      offsetLower, offsetUpper, back⟩

end Zlib.Inflate.Proofs
