import ZlibF.Proof.«inflate.c.match-output»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Both exits of the real slow lookup retain the dispatch buffer
relation. Exhausted input has the same exact private-state frame as the
continuation, including an empty unread slice in a shared allocation. -/
theorem inflate_LEN_slow_lookup_buffers {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (buffers : DispatchBuffers h r l bs)
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    (∃ regs after state used,
      used ≤ 4 ∧ used ≤ bs.length ∧
      runX (inflate_LEN c) l h = .ok ((.error Ex.leave, regs), after) ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧
      DispatchBuffers after r regs (bs.drop used) ∧
      Zlib.Inflate.Proofs.stream regs (bs.drop used) = Zlib.Inflate.Proofs.stream l bs ∧
      DecodeStateFrame s state ∧ ByteViewSizes h after) ∨
    (∃ regs after state used dropped,
      used ≤ 4 ∧ used ≤ bs.length ∧ dropped ≤ 15 ∧
      runX (inflate_LEN c) l h = runX (lenFinish c) regs after ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧
      DispatchBuffers after r regs (bs.drop used) ∧ Zlib.Inffast.Spec.LenLeaf dropped regs.here ∧
      regs.here.bits.toNat ≤ regs.bits.toNat ∧ state.back = Int32.ofNat dropped ∧
      Zlib.Inflate.Proofs.stream regs (bs.drop used) = (Zlib.Inflate.Proofs.stream l bs).drop dropped ∧
      DecodeStateFrame s state ∧ ByteViewSizes h after) := by
  rcases inflate_LEN_slow_lookup_boundary_frame E.st good tables buffers.bits slow with stopped | continued
  · obtain ⟨regs, after, state, used, four, usedBound, run, finalGood, finalTables,
      inv, empty, bits, shape, frame, bitBound, cursor, heapEq⟩ := stopped
    have packet : DispatchBuffers after r regs (bs.drop used) := by
      apply buffers.consume good finalGood (by rw [frame]) _ _ shape cursor usedBound inv
      · intro ref
        rw [heapEq, byte_view_get_setI]
      · intro ref
        rw [heapEq, byte_view_ro_setI]
    exact Or.inl ⟨regs, after, state, used, four, usedBound, run, finalGood, finalTables,
      packet, bits, frame, by rw [heapEq]; exact byte_view_sizes_setI h zs state⟩
  · obtain ⟨regs, after, state, used, dropped, four, usedBound, dropBound, run,
      finalGood, finalTables, inv, leaf, enough, back, bits, shape, frame, count, bitBound, heapEq, cursor⟩ := continued
    have packet : DispatchBuffers after r regs (bs.drop used) := by
      apply buffers.consume good finalGood (by rw [frame]) _ _ shape cursor usedBound inv
      · intro ref
        rw [heapEq, byte_view_get_setI]
      · intro ref
        rw [heapEq, byte_view_ro_setI]
    exact Or.inr ⟨regs, after, state, used, dropped, four, usedBound, dropBound, run,
      finalGood, finalTables, packet, leaf, enough, back, bits, frame,
      by rw [heapEq]; exact byte_view_sizes_setI h zs state⟩

/-- The actual slow symbol chain either stops while reading/classifying a
symbol, or executes MATCH with the same complete buffer relation as entry.
The latter branch derives every MATCH premise from decoding; it includes
short output, unavailable history and overlapping copies. The uniform
buffer-preserving boundary below strengthens both branches. -/
theorem inflate_LEN_slow_MATCH_buffers {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (buffers : DispatchBuffers h r l bs) (sane : s.sane ≠ 0)
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    (∃ outcome regs after stream state used consumed,
      used ≤ bs.length ∧ consumed ≤ 48 ∧
      runX (inflate_LEN c) l h = .ok ((outcome, regs), after) ∧
      Good after r zs stream state ∧ DataTableInvariant after state ∧ BitInv after regs (bs.drop used) ∧
      Zlib.Inflate.Proofs.stream regs (bs.drop used) = (Zlib.Inflate.Proofs.stream l bs).drop consumed ∧
      (outcome = .error Ex.leave ∨
        (outcome = .ok () ∧ (state.mode = LIT ∨ state.mode = TYPE ∨ state.mode = BAD)))) ∨
    (∃ outcome regs after stream state used consumed made,
      used ≤ bs.length ∧ consumed ≤ 48 ∧
      runX (inflate_LEN c) l h = .ok ((outcome, regs), after) ∧
      Good after r zs stream state ∧ DataTableInvariant after state ∧
      DispatchBuffers after r regs (bs.drop used) ∧ ByteViewSizes h after ∧ DecodeStateFrame s state ∧
      regs.left.toNat + made = l.left.toNat ∧ regs.put = inputAdvance l.put made ∧
      Zlib.Inflate.Proofs.stream regs (bs.drop used) = (Zlib.Inflate.Proofs.stream l bs).drop consumed ∧
      ((outcome = .error Ex.leave ∧ made = 0) ∨
        (outcome = .ok () ∧ state.mode = BAD ∧ made = 0) ∨
        (outcome = .ok () ∧ 0 < made ∧ (state.mode = LEN ∨ state.mode = MATCH)))) := by
  rcases inflate_LEN_slow_to_MATCH_cursor E.strm E.st good tables buffers.bits slow with stopped | continued
  · obtain ⟨outcome, regs, after, stream, state, used, consumed, usedBound, consumedBound,
      run, finalGood, data, inv, bits, _, kinds, _⟩ := stopped
    exact Or.inl ⟨outcome, regs, after, stream, state, used, consumed, usedBound, consumedBound,
      run, finalGood, data, inv, bits, kinds⟩
  · obtain ⟨current, heap, pending, used, consumed, usedBound, consumedBound, sourceRun,
      pendingGood, pendingTables, pendingInv, bits, shape, mode, was, lower, upper,
      distancePositive, distanceUpper, back, frame, heapEq, cursor⟩ := continued
    have currentEnv : Env c heap r zs z pending :=
      ⟨E.strm, E.st, pendingGood.live.hz, pendingGood.live.hs⟩
    have currentBuffers : DispatchBuffers heap r current (bs.drop used) := by
      apply buffers.consume good pendingGood (by rw [frame]) _ _ shape cursor usedBound pendingInv
      · intro ref
        rw [heapEq, byte_view_get_setI]
      · intro ref
        rw [heapEq, byte_view_ro_setI]
    obtain ⟨outcome, regs, after, stream, state, made, run, finalGood, data, finalBuffers,
      sizes, stateFrame, regFrame, residual, count, put, kinds⟩ :=
      inflate_MATCH_dispatch currentEnv pendingGood pendingTables currentBuffers mode (by omega)
        (by omega) (by rw [frame]; exact sane)
    have currentSizes : ByteViewSizes h heap := by rw [heapEq]; exact byte_view_sizes_setI h zs pending
    have currentLeft : current.left = l.left := by rw [shape]
    have currentPut : current.put = l.put := by rw [shape]
    have currentStream : Zlib.Inflate.Proofs.stream regs (bs.drop used) =
        Zlib.Inflate.Proofs.stream current (bs.drop used) := by rw [regFrame]; rfl
    exact Or.inr ⟨outcome, regs, after, stream, state, used, consumed, made, usedBound, consumedBound,
      sourceRun.trans run, finalGood, data, finalBuffers, currentSizes.trans sizes, frame.trans stateFrame,
      by rwa [currentLeft] at count, by rwa [currentPut] at put, currentStream.trans bits, kinds⟩

/-- Every exit of the actual complete slow LEN step preserves one buffer
relation. Decoding, malformed codes, exhausted input and MATCH emission
compose on the same heap. Positive emission accounts for output progress. -/
theorem inflate_LEN_slow_dispatch {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (buffers : DispatchBuffers h r l bs) (sane : s.sane ≠ 0)
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    ∃ outcome regs after stream state used consumed made,
      used ≤ bs.length ∧ consumed ≤ 48 ∧
      runX (inflate_LEN c) l h = .ok ((outcome, regs), after) ∧
      Good after r zs stream state ∧ DataTableInvariant after state ∧
      DispatchBuffers after r regs (bs.drop used) ∧ ByteViewSizes h after ∧ DecodeStateFrame s state ∧
      regs.left.toNat + made = l.left.toNat ∧ regs.put = inputAdvance l.put made ∧
      Zlib.Inflate.Proofs.stream regs (bs.drop used) = (Zlib.Inflate.Proofs.stream l bs).drop consumed ∧
      (outcome = .error Ex.leave ∨
        (outcome = .ok () ∧ (state.mode = LIT ∨ state.mode = TYPE ∨ state.mode = BAD)) ∨
        (outcome = .ok () ∧ (state.mode = LEN ∨ state.mode = MATCH) ∧ 0 < made)) := by
  rcases inflate_LEN_slow_to_MATCH_frame E.strm E.st good tables buffers.bits slow with stopped | continued
  · obtain ⟨outcome, regs, after, stream, state, used, consumed, usedBound, consumedBound,
      run, finalGood, data, inv, bits, shape, kinds, cursor, frame, heapEq⟩ := stopped
    have packet : DispatchBuffers after r regs (bs.drop used) := by
      apply buffers.consume good finalGood (by rw [frame]) _ _ shape cursor usedBound inv
      · intro ref
        rw [heapEq, byte_view_get_setI, byte_view_get_stream_put]
      · intro ref
        rw [heapEq, byte_view_ro_setI, byte_view_ro_stream_put]
    have sizes : ByteViewSizes h after := by
      rw [heapEq]
      exact (byte_view_sizes_stream_put h r stream).trans (byte_view_sizes_setI _ zs state)
    refine ⟨outcome, regs, after, stream, state, used, consumed, 0, usedBound, consumedBound,
      run, finalGood, data, packet, sizes, frame, ?_, ?_, bits, ?_⟩
    · rw [shape]
      rfl
    · rw [shape, inputAdvance_zero]
    · rcases kinds with wait | normal
      · exact Or.inl wait
      · exact Or.inr (Or.inl normal)
  · obtain ⟨current, heap, pending, used, consumed, usedBound, consumedBound, sourceRun,
      pendingGood, pendingTables, pendingInv, bits, shape, mode, was, lower, upper,
      distancePositive, distanceUpper, back, frame, heapEq, cursor⟩ := continued
    have currentEnv : Env c heap r zs z pending :=
      ⟨E.strm, E.st, pendingGood.live.hz, pendingGood.live.hs⟩
    have currentBuffers : DispatchBuffers heap r current (bs.drop used) := by
      apply buffers.consume good pendingGood (by rw [frame]) _ _ shape cursor usedBound pendingInv
      · intro ref
        rw [heapEq, byte_view_get_setI]
      · intro ref
        rw [heapEq, byte_view_ro_setI]
    obtain ⟨outcome, regs, after, stream, state, made, run, finalGood, data, finalBuffers,
      sizes, stateFrame, regFrame, residual, count, put, kinds⟩ :=
      inflate_MATCH_dispatch currentEnv pendingGood pendingTables currentBuffers mode (by omega)
        (by omega) (by rw [frame]; exact sane)
    have currentSizes : ByteViewSizes h heap := by rw [heapEq]; exact byte_view_sizes_setI h zs pending
    have currentLeft : current.left = l.left := by rw [shape]
    have currentPut : current.put = l.put := by rw [shape]
    have currentStream : Zlib.Inflate.Proofs.stream regs (bs.drop used) =
        Zlib.Inflate.Proofs.stream current (bs.drop used) := by rw [regFrame]; rfl
    refine ⟨outcome, regs, after, stream, state, used, consumed, made, usedBound, consumedBound,
      sourceRun.trans run, finalGood, data, finalBuffers, currentSizes.trans sizes, frame.trans stateFrame,
      by rwa [currentLeft] at count, by rwa [currentPut] at put, currentStream.trans bits, ?_⟩
    rcases kinds with wait | bad | matching
    · exact Or.inl wait.1
    · exact Or.inr (Or.inl ⟨bad.1, Or.inr (Or.inr bad.2.1)⟩)
    · exact Or.inr (Or.inr ⟨matching.1, matching.2.2, matching.2.1⟩)

end Zlib.Inflate.Proofs
