import ZlibF.Proof.«inflate.c.local-data-invariant»
import ZlibF.Proof.«inflate.c.slow-progress»

/-! Actual decoder execution with local allocation uniqueness. -/
namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inffast.Spec ZlibF.Spec.Public
set_option autoImplicit false
set_option maxRecDepth 8192

theorem inflate_DISTEXT_pending_step_output_progress {c : Ctx} {l : IL} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8}
    (E : Env c h r zs z s) (good : LocalGood h cutoff r zs z s) (tables : DataTablesSafe h s)
    (buffers : DispatchBuffers h r l bs) (pending : DataPendingInvariant s) (mode : s.mode = DISTEXT) :
    ∃ outcome regs after stream state used consumed made,
      used ≤ bs.length ∧ consumed ≤ 13 ∧
      runX (inflate_DISTEXT c) l h = .ok ((outcome, regs), after) ∧
      LocalGood after cutoff r zs stream state ∧ DataTableInvariant after state ∧
      DispatchBuffers after r regs (bs.drop used) ∧ DataPendingInvariant state ∧
      ByteViewSizes h after ∧ DecodeStateFrame s state ∧ regs.next = inputAdvance l.next used ∧
      regs.left.toNat + made = l.left.toNat ∧ regs.put = inputAdvance l.put made ∧
      Zlib.Inflate.Proofs.stream regs (bs.drop used) = (Zlib.Inflate.Proofs.stream l bs).drop consumed ∧
      (outcome = .error Ex.leave ∨
        (outcome = .ok () ∧ (0 < made ∨ state.mode = BAD))) ∧
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

theorem inflate_DIST_pending_step_output_progress {c : Ctx} {l : IL} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8}
    (E : Env c h r zs z s) (good : LocalGood h cutoff r zs z s) (tables : DataTablesSafe h s)
    (buffers : DispatchBuffers h r l bs) (pending : DataPendingInvariant s) (mode : s.mode = DIST) :
    ∃ outcome regs after stream state used consumed made,
      used ≤ bs.length ∧ consumed ≤ 28 ∧
      runX (inflate_DIST c) l h = .ok ((outcome, regs), after) ∧
      LocalGood after cutoff r zs stream state ∧ DataTableInvariant after state ∧
      DispatchBuffers after r regs (bs.drop used) ∧ DataPendingInvariant state ∧
      ByteViewSizes h after ∧ DecodeStateFrame s state ∧ regs.next = inputAdvance l.next used ∧
      regs.left.toNat + made = l.left.toNat ∧ regs.put = inputAdvance l.put made ∧
      Zlib.Inflate.Proofs.stream regs (bs.drop used) = (Zlib.Inflate.Proofs.stream l bs).drop consumed ∧
      (outcome = .error Ex.leave ∨
        (outcome = .ok () ∧ (0 < made ∨ state.mode = BAD))) ∧
      regs.bits.toNat ≤ max l.bits.toNat 22 := by
  obtain ⟨lengthFacts, before, backBound, back⟩ := pending.dist mode
  rcases inflate_DIST_lookup_boundary_bounded before E.st good tables buffers.bits back backBound with wait | continued
  · obtain ⟨regs, used, _, usedBound, run, inv, _, bits, shape, cursor, bitBound⟩ := wait
    have packet := dispatch_consume_local buffers good good rfl (fun _ => rfl) (fun _ => rfl) shape cursor usedBound inv
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
      apply dispatch_consume_local buffers good leafGood (by rw [leafFrame]) _ _ (rootShape.trans leafShape)
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
        apply dispatch_consume_local buffers good finalGood (by rw [frame]) _ _ (rootShape.trans leafShape)
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
        apply dispatch_consume_local buffers good baseGood (by rw [baseFrame]) _ _ (rootShape.trans leafShape)
          (leafCursor.trans rootCursor) usedBound baseInv
        · intro ref
          rw [baseHeapOriginal, byte_view_get_setI]
        · intro ref
          rw [baseHeapOriginal, byte_view_ro_setI]
      have baseEnv : Env c baseHeap r zs z baseState := ⟨E.strm, E.st, baseGood.live.hz, baseGood.live.hs⟩
      obtain ⟨outcome, finalRegs, after, stream, state, used2, consumed2, made,
        usedBound2, consumedBound2, run, finalGood, data, packet, invariant, sizes, frame,
        cursor, count, put, bits, kinds, finalBitBound⟩ :=
        inflate_DISTEXT_pending_step_output_progress baseEnv baseGood baseTables basePacket basePending nextMode
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

theorem inflate_LENEXT_pending_step_output_progress {c : Ctx} {l : IL} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8}
    (E : Env c h r zs z s) (good : LocalGood h cutoff r zs z s) (tables : DataTablesSafe h s)
    (buffers : DispatchBuffers h r l bs) (pending : DataPendingInvariant s) (mode : s.mode = LENEXT) :
    ∃ outcome regs after stream state used consumed made,
      used ≤ bs.length ∧ consumed ≤ 33 ∧
      runX (inflate_LENEXT c) l h = .ok ((outcome, regs), after) ∧
      LocalGood after cutoff r zs stream state ∧ DataTableInvariant after state ∧
      DispatchBuffers after r regs (bs.drop used) ∧ DataPendingInvariant state ∧
      ByteViewSizes h after ∧ DecodeStateFrame s state ∧ regs.next = inputAdvance l.next used ∧
      regs.left.toNat + made = l.left.toNat ∧ regs.put = inputAdvance l.put made ∧
      Zlib.Inflate.Proofs.stream regs (bs.drop used) = (Zlib.Inflate.Proofs.stream l bs).drop consumed ∧
      (outcome = .error Ex.leave ∨
        (outcome = .ok () ∧ (0 < made ∨ state.mode = BAD))) ∧
      regs.bits.toNat ≤ max l.bits.toNat 22 := by
  rcases inflate_LENEXT_pending_boundary E good tables buffers pending mode with wait | continued
  · obtain ⟨regs, used, run, usedBound, packet, bits, shape, cursor, bitBound⟩ := wait
    exact ⟨.error Ex.leave, regs, h, z, s, used, 0, 0, usedBound, by omega, run,
      good, fun _ => tables, packet, pending, ByteViewSizes.refl h, by rfl, cursor,
      by rw [shape]; rfl, by rw [shape, inputAdvance_zero], by simpa using bits, Or.inl rfl, bitBound⟩
  · obtain ⟨current, heap, currentState, used, sourceRun, usedBound, currentGood, currentTables,
      currentBuffers, currentPending, nextMode, frame, currentSizes, bits, shape, cursor, _, currentBitBound⟩ := continued
    have currentEnv : Env c heap r zs z currentState :=
      ⟨E.strm, E.st, currentGood.live.hz, currentGood.live.hs⟩
    obtain ⟨outcome, regs, after, stream, state, used2, consumed2, made, usedBound2, consumedBound2,
      run, finalGood, data, packet, invariant, sizes, stateFrame, cursor2, count, put, finalStream, kinds, finalBitBound⟩ :=
      inflate_DIST_pending_step_output_progress currentEnv currentGood currentTables currentBuffers currentPending nextMode
    have totalBound : used + used2 ≤ bs.length := by simp only [List.length_drop] at usedBound2; omega
    have finalPacket : DispatchBuffers after r regs (bs.drop (used + used2)) := by
      simpa only [List.drop_drop, Nat.add_comm] using packet
    have finalBits : Zlib.Inflate.Proofs.stream regs (bs.drop (used + used2)) =
        (Zlib.Inflate.Proofs.stream l bs).drop (s.extra.toNat + consumed2) := by
      simp only [List.drop_drop] at finalStream
      rw [bits, List.drop_drop] at finalStream
      exact finalStream
    have left : current.left = l.left := by rw [shape]
    have output : current.put = l.put := by rw [shape]
    refine ⟨outcome, regs, after, stream, state, used + used2, s.extra.toNat + consumed2, made,
      totalBound, by have := (pending.lenext mode).1; omega, sourceRun.trans run, finalGood, data,
      finalPacket, invariant, currentSizes.trans sizes, frame.trans stateFrame,
      by rw [cursor2, cursor, inputAdvance_add], by rwa [left] at count, by rwa [output] at put,
      finalBits, ?_, ?_⟩
    · rcases kinds with wait | ⟨ok, progress | bad⟩
      · exact Or.inl wait
      · exact Or.inr ⟨ok, Or.inl (by omega)⟩
      · exact Or.inr ⟨ok, Or.inr bad⟩
    · omega

theorem inflate_LEN_pending_step_output_progress {c : Ctx} {l : IL} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8}
    (E : Env c h r zs z s) (good : LocalGood h cutoff r zs z s) (tables : DataTablesSafe h s)
    (buffers : DispatchBuffers h r l bs) (pending : DataPendingInvariant s) (mode : s.mode = LEN)
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    ∃ outcome regs after stream state used consumed made,
      used ≤ bs.length ∧ consumed ≤ 48 ∧
      runX (inflate_LEN c) l h = .ok ((outcome, regs), after) ∧
      LocalGood after cutoff r zs stream state ∧ DataTableInvariant after state ∧
      DispatchBuffers after r regs (bs.drop used) ∧ DataPendingInvariant state ∧
      ByteViewSizes h after ∧ DecodeStateFrame s state ∧ regs.next = inputAdvance l.next used ∧
      regs.left.toNat + made = l.left.toNat ∧ regs.put = inputAdvance l.put made ∧
      Zlib.Inflate.Proofs.stream regs (bs.drop used) = (Zlib.Inflate.Proofs.stream l bs).drop consumed ∧
      (outcome = .error Ex.leave ∨ (outcome = .ok () ∧
        (0 < made ∨ state.mode = LIT ∨ state.mode = TYPE ∨ state.mode = BAD))) ∧
      regs.bits.toNat ≤ max l.bits.toNat 22 := by
  rcases inflate_LEN_slow_lookup_boundary_mode E.st good tables buffers.bits slow with wait | continued
  · obtain ⟨regs, after, state, used, _, usedBound, run, finalGood, finalTables,
      inv, _, bits, shape, frame, bitBound, cursor, heapEq, modeEq⟩ := wait
    have packet : DispatchBuffers after r regs (bs.drop used) := by
      apply dispatch_consume_local buffers good finalGood (by rw [frame]) _ _ shape cursor usedBound inv
      · intro ref
        rw [heapEq, byte_view_get_setI]
      · intro ref
        rw [heapEq, byte_view_ro_setI]
    have invariant : DataPendingInvariant state := by
      apply dataPendingInvariant_idle (by rw [frame]; exact pending.sane)
      rw [modeEq, mode]
      decide
    exact ⟨.error Ex.leave, regs, after, z, state, used, 0, 0, usedBound, by omega, run,
      finalGood, fun _ => finalTables, packet, invariant,
      by rw [heapEq]; exact byte_view_sizes_setI h zs state, frame, cursor,
      by rw [shape]; rfl, by rw [shape, inputAdvance_zero], by simpa using bits, Or.inl rfl, bitBound⟩
  · obtain ⟨regs, rootHeap, rootState, used, dropped, _, usedBound, droppedBound, sourceRun,
      rootGood, rootTables, rootInv, leaf, enough, rootBack, rootBits, rootShape, rootFrame,
      _, rootBitBound, rootHeapEq, rootCursor⟩ := continued
    have backNat : rootState.back.toInt = dropped := by rw [rootBack]; exact back_ofNat_small dropped droppedBound
    obtain ⟨leafRegs, leafHeap, leafState, consumeRun, leafGood, leafTables, leafInv,
      leafFrame, leafShape, lengthEq, leafBack, leafBits, leafCount, _, leafHeapEq, leafCursor⟩ :=
      lenFinish_consume_cursor dropped E.st rootGood rootTables leaf backNat enough rootInv
    let codeBits := dropped + regs.here.bits.toNat
    have codeBound : codeBits ≤ 15 := by have := leaf.1; omega
    have parsed : Zlib.Inflate.Proofs.stream leafRegs (bs.drop used) =
        (Zlib.Inflate.Proofs.stream l bs).drop codeBits := by rw [leafBits, rootBits, List.drop_drop]
    have leafBitBound : leafRegs.bits.toNat ≤ max l.bits.toNat 22 := by rw [leafCount]; omega
    have leafHeapOriginal : leafHeap = setI h zs leafState := by rw [leafHeapEq, rootHeapEq, setI_setI]
    have source : runX (inflate_LEN c) l h = runX (lenLeafTail c regs.here) leafRegs leafHeap :=
      sourceRun.trans consumeRun
    rcases lenLeafTail_boundary_frame E.strm E.st leafGood leafTables leafInv leaf lengthEq with terminal | valid
    · obtain ⟨after, stream, state, run, finalGood, data, inv, modes, finalFrame, heapEq⟩ := terminal
      have frame := rootFrame.trans (leafFrame.trans finalFrame)
      have packet : DispatchBuffers after r leafRegs (bs.drop used) := by
        apply dispatch_consume_local buffers good finalGood (by rw [frame]) _ _ (rootShape.trans leafShape)
          (leafCursor.trans rootCursor) usedBound inv
        · intro ref
          rw [heapEq, byte_view_get_setI, byte_view_get_stream_put, leafHeapOriginal, byte_view_get_setI]
        · intro ref
          rw [heapEq, byte_view_ro_setI, byte_view_ro_stream_put, leafHeapOriginal, byte_view_ro_setI]
      have invariant : DataPendingInvariant state := by
        apply dataPendingInvariant_idle (by rw [frame]; exact pending.sane)
        rcases modes with literalMode | typeMode | badMode
        · rw [literalMode]; decide
        · rw [typeMode]; decide
        · rw [badMode]; decide
      have sizes : ByteViewSizes h after := by
        rw [heapEq]
        have leafSizes : ByteViewSizes h leafHeap := by rw [leafHeapOriginal]; exact byte_view_sizes_setI h zs leafState
        exact leafSizes.trans ((byte_view_sizes_stream_put leafHeap r stream).trans (byte_view_sizes_setI _ zs state))
      exact ⟨.ok (), leafRegs, after, stream, state, used, codeBits, 0, usedBound, by omega,
        source.trans run, finalGood, data, packet, invariant, sizes, frame, leafCursor.trans rootCursor,
        by rw [leafShape, rootShape]; rfl, by rw [leafShape, rootShape, inputAdvance_zero], parsed,
        Or.inr ⟨rfl, Or.inr modes⟩, leafBitBound⟩
    · obtain ⟨baseHeap, baseState, classifyRun, baseGood, baseTables, baseInv, nextMode,
        baseFrame, extra, lower, budget, retainedBack, baseHeapEq⟩ := valid
      have prefixFrame := rootFrame.trans (leafFrame.trans baseFrame)
      have baseHeapOriginal : baseHeap = setI h zs baseState := by rw [baseHeapEq, leafHeapOriginal, setI_setI]
      have basePending := dataPendingInvariant_lenext (by rw [prefixFrame]; exact pending.sane) nextMode
        ⟨extra, lower, budget, codeBits, codeBound, retainedBack.trans leafBack⟩
      have basePacket : DispatchBuffers baseHeap r leafRegs (bs.drop used) := by
        apply dispatch_consume_local buffers good baseGood (by rw [prefixFrame]) _ _ (rootShape.trans leafShape)
          (leafCursor.trans rootCursor) usedBound baseInv
        · intro ref
          rw [baseHeapOriginal, byte_view_get_setI]
        · intro ref
          rw [baseHeapOriginal, byte_view_ro_setI]
      have baseEnv : Env c baseHeap r zs z baseState := ⟨E.strm, E.st, baseGood.live.hz, baseGood.live.hs⟩
      obtain ⟨outcome, finalRegs, after, stream, state, used2, consumed2, made,
        usedBound2, consumedBound2, run, finalGood, data, packet, invariant, sizes, frame,
        cursor, count, put, bits, kinds, finalBitBound⟩ :=
        inflate_LENEXT_pending_step_output_progress baseEnv baseGood baseTables basePacket basePending nextMode
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
        invariant, ?_, prefixFrame.trans frame, ?_, by rwa [left] at count, by rwa [output] at put,
        finalBits, ?_, ?_⟩
      · have baseSizes : ByteViewSizes h baseHeap := by rw [baseHeapOriginal]; exact byte_view_sizes_setI h zs baseState
        exact baseSizes.trans sizes
      · rw [cursor, leafCursor, rootCursor, inputAdvance_add]
      · rcases kinds with wait | ⟨ok, progress | bad⟩
        · exact Or.inl wait
        · exact Or.inr ⟨ok, Or.inl (by omega)⟩
        · exact Or.inr ⟨ok, Or.inr (Or.inr (Or.inr bad))⟩
      · omega

theorem inflate_LEN_start_pending_step_output_progress {c : Ctx} {l : IL} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8}
    (E : Env c h r zs z s) (good : LocalGood h cutoff r zs z s) (tables : DataTablesSafe h s)
    (buffers : DispatchBuffers h r l bs) (pending : DataPendingInvariant s)
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    ∃ outcome regs after stream state used consumed made,
      used ≤ bs.length ∧ consumed ≤ 48 ∧
      runX (inflate_LEN_ c) l h = .ok ((outcome, regs), after) ∧
      LocalGood after cutoff r zs stream state ∧ DataTableInvariant after state ∧
      DispatchBuffers after r regs (bs.drop used) ∧ DataPendingInvariant state ∧
      ByteViewSizes h after ∧ DecodeStateFrame s state ∧ regs.next = inputAdvance l.next used ∧
      regs.left.toNat + made = l.left.toNat ∧ regs.put = inputAdvance l.put made ∧
      Zlib.Inflate.Proofs.stream regs (bs.drop used) = (Zlib.Inflate.Proofs.stream l bs).drop consumed ∧
      (outcome = .error Ex.leave ∨ (outcome = .ok () ∧
        (0 < made ∨ state.mode = LIT ∨ state.mode = TYPE ∨ state.mode = BAD))) ∧
      regs.bits.toNat ≤ max l.bits.toNat 22 := by
  let current := { s with mode := LEN }
  let heap := setI h zs current
  have frame : DecodeStateFrame s current := by rfl
  have currentGood := good.decode_after frame (by change HEAD ≤ LEN ∧ LEN ≤ SYNC; decide)
  have currentTables := tables.decode_update good.live.hs frame
  have currentPending : DataPendingInvariant current := by
    apply dataPendingInvariant_idle (s := current) (by exact pending.sane)
    change LEN ≠ LENEXT ∧ LEN ≠ DIST ∧ LEN ≠ DISTEXT ∧ LEN ≠ MATCH
    decide
  have currentBuffers : DispatchBuffers heap r l bs := by
    have inv := buffers.bits.decode_update zs current
    apply dispatch_consume_local buffers good currentGood (by rw [frame]) _ _ (by rfl)
      (used := 0) (inputAdvance_zero l.next).symm (by omega) (by simpa using inv)
    · intro ref
      exact byte_view_get_setI h zs current ref
    · intro ref
      exact byte_view_ro_setI h zs current ref
  have currentEnv : Env c heap r zs z current := ⟨E.strm, E.st, currentGood.live.hz, currentGood.live.hs⟩
  obtain ⟨outcome, regs, after, stream, state, used, consumed, made, usedBound, consumedBound,
    run, finalGood, data, packet, invariant, sizes, finalFrame, cursor, count, put, bits, kinds, finalBitBound⟩ :=
    inflate_LEN_pending_step_output_progress currentEnv currentGood currentTables currentBuffers currentPending rfl slow
  have source : runX (inflate_LEN_ c) l h = runX (inflate_LEN c) l heap := by
    unfold inflate_LEN_
    rw [runX_bind, runX_setMode E]
  exact ⟨outcome, regs, after, stream, state, used, consumed, made, usedBound, consumedBound,
    source.trans run, finalGood, data, packet, invariant, (byte_view_sizes_setI h zs current).trans sizes,
    frame.trans finalFrame, cursor, count, put, bits, kinds, finalBitBound⟩

theorem inflate_dispatch_pending_output_progress {c : Ctx} {l : IL} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8}
    (E : Env c h r zs z s) (good : LocalGood h cutoff r zs z s) (tables : DataTableInvariant h s)
    (buffers : DispatchBuffers h r l bs) (pending : DataPendingInvariant s)
    (mode : DataTableMode s.mode)
    (slow : s.mode = LEN_ ∨ s.mode = LEN → ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    ∃ outcome regs after stream state used consumed made,
      used ≤ bs.length ∧ consumed ≤ 48 ∧
      runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) ∧
      LocalGood after cutoff r zs stream state ∧ DataTableInvariant after state ∧
      DispatchBuffers after r regs (bs.drop used) ∧ DataPendingInvariant state ∧
      ByteViewSizes h after ∧ DecodeStateFrame s state ∧ regs.next = inputAdvance l.next used ∧
      regs.left.toNat + made = l.left.toNat ∧ regs.put = inputAdvance l.put made ∧
      Zlib.Inflate.Proofs.stream regs (bs.drop used) = (Zlib.Inflate.Proofs.stream l bs).drop consumed ∧
      (outcome = .error Ex.leave ∨ (outcome = .ok () ∧
        (0 < made ∨ state.mode = LIT ∨ state.mode = TYPE ∨ state.mode = BAD))) ∧
      regs.bits.toNat ≤ max l.bits.toNat 22 := by
  have safe := tables mode
  rcases mode with start | lengthMode | lengthExtra | distanceMode | distanceExtra | matchMode | literalMode
  · obtain ⟨outcome, regs, after, stream, state, used, consumed, made, usedBound, consumedBound,
      run, finalGood, data, packet, invariant, sizes, frame, cursor, count, put, bits, kinds, bitBound⟩ :=
      inflate_LEN_start_pending_step_output_progress E good safe buffers pending (slow (Or.inl start))
    exact ⟨outcome, regs, after, stream, state, used, consumed, made, usedBound, consumedBound,
      (inflate_dispatch_LEN_start E l start).trans run, finalGood, data, packet, invariant, sizes, frame,
      cursor, count, put, bits, kinds, bitBound⟩
  · obtain ⟨outcome, regs, after, stream, state, used, consumed, made, usedBound, consumedBound,
      run, finalGood, data, packet, invariant, sizes, frame, cursor, count, put, bits, kinds, bitBound⟩ :=
      inflate_LEN_pending_step_output_progress E good safe buffers pending lengthMode (slow (Or.inr lengthMode))
    exact ⟨outcome, regs, after, stream, state, used, consumed, made, usedBound, consumedBound,
      (inflate_dispatch_LEN E l lengthMode).trans run, finalGood, data, packet, invariant, sizes, frame,
      cursor, count, put, bits, kinds, bitBound⟩
  · obtain ⟨outcome, regs, after, stream, state, used, consumed, made, usedBound, consumedBound,
      run, finalGood, data, packet, invariant, sizes, frame, cursor, count, put, bits, kinds, bitBound⟩ :=
      inflate_LENEXT_pending_step_output_progress E good safe buffers pending lengthExtra
    refine ⟨outcome, regs, after, stream, state, used, consumed, made, usedBound, by omega,
      (inflate_dispatch_LENEXT E l lengthExtra).trans run, finalGood, data, packet, invariant, sizes, frame,
      cursor, count, put, bits, ?_, bitBound⟩
    rcases kinds with wait | ⟨ok, progress | bad⟩
    · exact Or.inl wait
    · exact Or.inr ⟨ok, Or.inl progress⟩
    · exact Or.inr ⟨ok, Or.inr (Or.inr (Or.inr bad))⟩
  · obtain ⟨outcome, regs, after, stream, state, used, consumed, made, usedBound, consumedBound,
      run, finalGood, data, packet, invariant, sizes, frame, cursor, count, put, bits, kinds, bitBound⟩ :=
      inflate_DIST_pending_step_output_progress E good safe buffers pending distanceMode
    refine ⟨outcome, regs, after, stream, state, used, consumed, made, usedBound, by omega,
      (inflate_dispatch_DIST E l distanceMode).trans run, finalGood, data, packet, invariant, sizes, frame,
      cursor, count, put, bits, ?_, bitBound⟩
    rcases kinds with wait | ⟨ok, progress | bad⟩
    · exact Or.inl wait
    · exact Or.inr ⟨ok, Or.inl progress⟩
    · exact Or.inr ⟨ok, Or.inr (Or.inr (Or.inr bad))⟩
  · obtain ⟨outcome, regs, after, stream, state, used, consumed, made, usedBound, consumedBound,
      run, finalGood, data, packet, invariant, sizes, frame, cursor, count, put, bits, kinds, bitBound⟩ :=
      inflate_DISTEXT_pending_step_output_progress E good safe buffers pending distanceExtra
    refine ⟨outcome, regs, after, stream, state, used, consumed, made, usedBound, by omega,
      (inflate_dispatch_DISTEXT E l distanceExtra).trans run, finalGood, data, packet, invariant, sizes, frame,
      cursor, count, put, bits, ?_, bitBound⟩
    rcases kinds with wait | ⟨ok, progress | bad⟩
    · exact Or.inl wait
    · exact Or.inr ⟨ok, Or.inl progress⟩
    · exact Or.inr ⟨ok, Or.inr (Or.inr (Or.inr bad))⟩
  · obtain ⟨outcome, regs, after, stream, state, made, run, finalGood, data, packet,
      invariant, sizes, frame, count, put, regFrame, bits, kinds⟩ :=
      inflate_MATCH_pending E good safe buffers pending matchMode
    refine ⟨outcome, regs, after, stream, state, 0, 0, made, by omega, by omega,
      (inflate_dispatch_MATCH E l matchMode).trans run, finalGood, data, by simpa using packet,
      invariant, sizes, frame, by rw [regFrame, inputAdvance_zero], count, put, by simpa using bits, ?_, by rw [regFrame]; exact Nat.le_max_left _ _⟩
    rcases kinds with wait | bad | emitted
    · exact Or.inl wait.1
    · exact Or.inr ⟨bad.1, Or.inr (Or.inr (Or.inr bad.2.1))⟩
    · exact Or.inr ⟨emitted.1, Or.inl (by omega)⟩
  · obtain ⟨outcome, regs, after, state, run, finalGood, finalTables, packet, sizes, frame, regFrame, kinds⟩ :=
      inflate_LIT_dispatch E good safe buffers
    have bits : Zlib.Inflate.Proofs.stream regs bs = Zlib.Inflate.Proofs.stream l bs := by rw [regFrame]; rfl
    rcases kinds with ⟨wait, regsEq, _, stateEq⟩ | ⟨ok, stateEq, put, count⟩
    · exact ⟨outcome, regs, after, z, state, 0, 0, 0, by omega, by omega,
        (inflate_dispatch_LIT E l literalMode).trans run, finalGood, fun _ => finalTables,
        by simpa using packet, by rwa [stateEq], sizes, frame,
        by rw [regFrame, inputAdvance_zero], by rw [regsEq]; rfl,
        by rw [regsEq, inputAdvance_zero], by simpa using bits, Or.inl wait, by rw [regFrame]; exact Nat.le_max_left _ _⟩
    · have invariant : DataPendingInvariant state := by
        apply dataPendingInvariant_idle (by rw [frame]; exact pending.sane)
        rw [stateEq]
        change LEN ≠ LENEXT ∧ LEN ≠ DIST ∧ LEN ≠ DISTEXT ∧ LEN ≠ MATCH
        decide
      exact ⟨outcome, regs, after, z, state, 0, 0, 1, by omega, by omega,
        (inflate_dispatch_LIT E l literalMode).trans run, finalGood, fun _ => finalTables,
        by simpa using packet, invariant, sizes, frame, by rw [regFrame, inputAdvance_zero], count,
        put, by simpa using bits, Or.inr ⟨ok, Or.inl (by decide)⟩, by rw [regFrame]; exact Nat.le_max_left _ _⟩

#print axioms inflate_DISTEXT_pending_step_output_progress
#print axioms inflate_DIST_pending_step_output_progress
#print axioms inflate_LENEXT_pending_step_output_progress
#print axioms inflate_LEN_pending_step_output_progress
#print axioms inflate_LEN_start_pending_step_output_progress
#print axioms inflate_dispatch_pending_output_progress
end Zlib.Inflate.Local
