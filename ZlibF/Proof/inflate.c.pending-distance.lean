import ZlibF.Proof.«inflate.c.pending-extra»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

/-- Complete actual DISTEXT execution includes its real MATCH call. The
resumed extra-bit and match clauses are derived and retained on every exit. -/
theorem inflate_DISTEXT_pending_step {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (buffers : DispatchBuffers h r l bs) (pending : DataPendingInvariant s) (mode : s.mode = DISTEXT) :
    ∃ outcome regs after stream state used consumed made,
      used ≤ bs.length ∧ consumed ≤ 13 ∧
      runX (inflate_DISTEXT c) l h = .ok ((outcome, regs), after) ∧
      Good after r zs stream state ∧ DataTableInvariant after state ∧
      DispatchBuffers after r regs (bs.drop used) ∧ DataPendingInvariant state ∧
      ByteViewSizes h after ∧ DecodeStateFrame s state ∧ regs.next = inputAdvance l.next used ∧
      regs.left.toNat + made = l.left.toNat ∧ regs.put = inputAdvance l.put made ∧
      Zlib.Inflate.Proofs.stream regs (bs.drop used) = (Zlib.Inflate.Proofs.stream l bs).drop consumed ∧
      (outcome = .error Ex.leave ∨
        (outcome = .ok () ∧ (0 < consumed + made ∨ state.mode = BAD))) ∧
      regs.bits.toNat ≤ max l.bits.toNat 22 := by
  rcases inflate_DISTEXT_pending_boundary E good tables buffers pending mode with wait | continued
  · obtain ⟨regs, used, run, usedBound, packet, bits, shape, cursor, bitBound⟩ := wait
    exact ⟨.error Ex.leave, regs, h, z, s, used, 0, 0, usedBound, by omega, run,
      good, fun _ => tables, packet, pending, ByteViewSizes.refl h, by rfl, cursor,
      by rw [shape]; rfl, by rw [shape, inputAdvance_zero], by simpa using bits, Or.inl rfl, bitBound⟩
  · obtain ⟨current, heap, currentState, used, sourceRun, usedBound, currentGood, currentTables,
      currentBuffers, currentPending, nextMode, frame, currentSizes, bits, shape, cursor, _, currentBitBound⟩ := continued
    have currentEnv : Env c heap r zs z currentState :=
      ⟨E.strm, E.st, currentGood.live.hz, currentGood.live.hs⟩
    obtain ⟨outcome, regs, after, stream, state, made, run, finalGood, data, packet, invariant,
      sizes, stateFrame, count, put, regFrame, sameInput, kinds⟩ :=
      inflate_MATCH_pending currentEnv currentGood currentTables currentBuffers currentPending nextMode
    have left : current.left = l.left := by rw [shape]
    have putEq : current.put = l.put := by rw [shape]
    have inputEq : regs.next = current.next := by rw [regFrame]
    refine ⟨outcome, regs, after, stream, state, used, s.extra.toNat, made, usedBound,
      (pending.distext mode).2.1, sourceRun.trans run, finalGood, data, packet, invariant,
      currentSizes.trans sizes, frame.trans stateFrame, inputEq.trans cursor,
      by rwa [left] at count, by rwa [putEq] at put, sameInput.trans bits, ?_, ?_⟩
    · rcases kinds with wait | bad | emitted
      · exact Or.inl wait.1
      · exact Or.inr ⟨bad.1, Or.inr bad.2.1⟩
      · exact Or.inr ⟨emitted.1, Or.inl (by omega)⟩
    · rw [regFrame]
      exact currentBitBound

/-- Complete actual DIST lookup, classification, extra bits and MATCH.
The distance leaf establishes the resumed DISTEXT clause; the match theorem
then retains the same scalar and buffer relation on every return. -/
theorem inflate_DIST_pending_step {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (buffers : DispatchBuffers h r l bs) (pending : DataPendingInvariant s) (mode : s.mode = DIST) :
    ∃ outcome regs after stream state used consumed made,
      used ≤ bs.length ∧ consumed ≤ 28 ∧
      runX (inflate_DIST c) l h = .ok ((outcome, regs), after) ∧
      Good after r zs stream state ∧ DataTableInvariant after state ∧
      DispatchBuffers after r regs (bs.drop used) ∧ DataPendingInvariant state ∧
      ByteViewSizes h after ∧ DecodeStateFrame s state ∧ regs.next = inputAdvance l.next used ∧
      regs.left.toNat + made = l.left.toNat ∧ regs.put = inputAdvance l.put made ∧
      Zlib.Inflate.Proofs.stream regs (bs.drop used) = (Zlib.Inflate.Proofs.stream l bs).drop consumed ∧
      (outcome = .error Ex.leave ∨
        (outcome = .ok () ∧ (0 < consumed + made ∨ state.mode = BAD))) ∧
      regs.bits.toNat ≤ max l.bits.toNat 22 := by
  obtain ⟨lengthFacts, before, backBound, back⟩ := pending.dist mode
  rcases inflate_DIST_lookup_boundary_bounded before E.st good tables buffers.bits back backBound with wait | continued
  · obtain ⟨regs, used, _, usedBound, run, inv, _, bits, shape, cursor, bitBound⟩ := wait
    have packet := buffers.consume good good rfl (fun _ => rfl) (fun _ => rfl) shape cursor usedBound inv
    exact ⟨.error Ex.leave, regs, h, z, s, used, 0, 0, usedBound, by omega, run, good,
      fun _ => tables, packet, pending, ByteViewSizes.refl h, by rfl, cursor,
      by rw [shape]; rfl, by rw [shape, inputAdvance_zero], by simpa using bits, Or.inl rfl, bitBound⟩
  · obtain ⟨regs, rootHeap, rootState, used, dropped, _, usedBound, droppedBound,
      sourceRun, rootGood, rootTables, rootInv, leaf, enough, rootBack, rootBits, rootShape,
      _, _, rootHeapEq, rootStateEq, rootCursor, rootBitBound⟩ := continued
    obtain ⟨leafRegs, leafHeap, leafState, consumeRun, leafGood, leafTables, leafInv,
      _, leafShape, leafHeapEq, leafStateEq, leafBits, leafCount, _, leafCursor⟩ :=
      distFinish_consume_cursor before dropped E.st rootGood rootTables leaf rootBack backBound enough rootInv
    let codeBits := dropped + regs.here.bits.toNat
    have codeBound : codeBits ≤ 15 := by have := leaf.1; omega
    have parsed : Zlib.Inflate.Proofs.stream leafRegs (bs.drop used) =
        (Zlib.Inflate.Proofs.stream l bs).drop codeBits := by rw [leafBits, rootBits, List.drop_drop]
    have leafBitBound : leafRegs.bits.toNat ≤ max l.bits.toNat 22 := by rw [leafCount]; omega
    have leafHeapOriginal : leafHeap = setI h zs leafState := by rw [leafHeapEq, rootHeapEq, setI_setI]
    have leafFrame : DecodeStateFrame s leafState := by
      unfold DecodeStateFrame
      rw [leafStateEq, rootStateEq]
    have leafPacket : DispatchBuffers leafHeap r leafRegs (bs.drop used) := by
      apply buffers.consume good leafGood (by rw [leafFrame]) _ _ (rootShape.trans leafShape)
        (leafCursor.trans rootCursor) usedBound leafInv
      · intro ref
        rw [leafHeapOriginal, byte_view_get_setI]
      · intro ref
        rw [leafHeapOriginal, byte_view_ro_setI]
    have source : runX (inflate_DIST c) l h = runX (distLeafTail c regs.here) leafRegs leafHeap :=
      sourceRun.trans consumeRun
    rcases distLeafTail_boundary_frame E.strm E.st leafGood leafTables leafInv leaf with invalid | valid
    · obtain ⟨after, stream, state, run, finalGood, data, inv, bad, stateEq, heapEq⟩ := invalid
      have frame : DecodeStateFrame s state := by unfold DecodeStateFrame; rw [stateEq, leafStateEq, rootStateEq]
      have packet : DispatchBuffers after r leafRegs (bs.drop used) := by
        apply buffers.consume good finalGood (by rw [frame]) _ _ (rootShape.trans leafShape)
          (leafCursor.trans rootCursor) usedBound inv
        · intro ref
          rw [heapEq, byte_view_get_setI, byte_view_get_stream_put, leafHeapOriginal, byte_view_get_setI]
        · intro ref
          rw [heapEq, byte_view_ro_setI, byte_view_ro_stream_put, leafHeapOriginal, byte_view_ro_setI]
      have invariant : DataPendingInvariant state := by
        apply dataPendingInvariant_idle (by rw [frame]; exact pending.sane)
        rw [bad]
        decide
      have sizes : ByteViewSizes h after := by
        rw [heapEq]
        have leafSizes : ByteViewSizes h leafHeap := by rw [leafHeapOriginal]; exact byte_view_sizes_setI h zs leafState
        exact leafSizes.trans
          ((byte_view_sizes_stream_put leafHeap r stream).trans (byte_view_sizes_setI _ zs state))
      exact ⟨.ok (), leafRegs, after, stream, state, used, codeBits, 0, usedBound, by omega,
        source.trans run, finalGood, data, packet, invariant, sizes, frame, leafCursor.trans rootCursor,
        by rw [leafShape, rootShape]; rfl, by rw [leafShape, rootShape, inputAdvance_zero], parsed,
        Or.inr ⟨rfl, Or.inr bad⟩, leafBitBound⟩
    · obtain ⟨baseHeap, baseState, classifyRun, baseGood, baseTables, baseInv, nextMode,
        baseHeapEq, baseStateEq, extra, lower, budget⟩ := valid
      have baseFrame : DecodeStateFrame s baseState := by
        unfold DecodeStateFrame
        rw [baseStateEq, leafStateEq, rootStateEq]
      have baseHeapOriginal : baseHeap = setI h zs baseState := by rw [baseHeapEq, leafHeapOriginal, setI_setI]
      have baseLength : PendingLengthSafe baseState := by
        rw [baseStateEq, leafStateEq, rootStateEq]
        exact lengthFacts
      have baseBack : baseState.back = Int32.ofNat (before + codeBits) := by
        rw [baseStateEq, leafStateEq]
        simp only [codeBits, Nat.add_assoc]
      have basePending := dataPendingInvariant_distext (by rw [baseFrame]; exact pending.sane) nextMode
        ⟨baseLength, extra, lower, budget, before + codeBits, by omega, baseBack⟩
      have basePacket : DispatchBuffers baseHeap r leafRegs (bs.drop used) := by
        apply buffers.consume good baseGood (by rw [baseFrame]) _ _ (rootShape.trans leafShape)
          (leafCursor.trans rootCursor) usedBound baseInv
        · intro ref
          rw [baseHeapOriginal, byte_view_get_setI]
        · intro ref
          rw [baseHeapOriginal, byte_view_ro_setI]
      have baseEnv : Env c baseHeap r zs z baseState := ⟨E.strm, E.st, baseGood.live.hz, baseGood.live.hs⟩
      obtain ⟨outcome, finalRegs, after, stream, state, used2, consumed2, made,
        usedBound2, consumedBound2, run, finalGood, data, packet, invariant, sizes, frame,
        cursor, count, put, bits, kinds, finalBitBound⟩ :=
        inflate_DISTEXT_pending_step baseEnv baseGood baseTables basePacket basePending nextMode
      have totalBound : used + used2 ≤ bs.length := by simp only [List.length_drop] at usedBound2; omega
      have finalPacket : DispatchBuffers after r finalRegs (bs.drop (used + used2)) := by
        simpa only [List.drop_drop, Nat.add_comm] using packet
      have finalBits : Zlib.Inflate.Proofs.stream finalRegs (bs.drop (used + used2)) =
          (Zlib.Inflate.Proofs.stream l bs).drop (codeBits + consumed2) := by
        simp only [List.drop_drop] at bits
        rw [parsed, List.drop_drop] at bits
        exact bits
      have left : leafRegs.left = l.left := by rw [leafShape, rootShape]
      have output : leafRegs.put = l.put := by rw [leafShape, rootShape]
      refine ⟨outcome, finalRegs, after, stream, state, used + used2, codeBits + consumed2, made,
        totalBound, by omega, source.trans (classifyRun.trans run), finalGood, data, finalPacket,
        invariant, ?_, baseFrame.trans frame, ?_, by rwa [left] at count, by rwa [output] at put,
        finalBits, ?_, ?_⟩
      · have baseSizes : ByteViewSizes h baseHeap := by rw [baseHeapOriginal]; exact byte_view_sizes_setI h zs baseState
        exact baseSizes.trans sizes
      · rw [cursor, leafCursor, rootCursor, inputAdvance_add]
      · rcases kinds with wait | ⟨ok, progress | bad⟩
        · exact Or.inl wait
        · exact Or.inr ⟨ok, Or.inl (by omega)⟩
        · exact Or.inr ⟨ok, Or.inr bad⟩
      · omega

end Zlib.Inflate.Proofs
