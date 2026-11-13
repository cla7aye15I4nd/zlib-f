import ZlibF.Proof.«inflate.c.slow-length»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inffast.Spec
set_option autoImplicit false

/-- The actual LEN classification after consuming the selected leaf. -/
def lenLeafTail (c : Ctx) (here : Code) : X Unit := do
  if here.op.toNat == 0 then
    setMode c.st LIT
    return
  if (here.op &&& 32) != 0 then
    wrS c.st fun s => { s with back := -1, mode := TYPE }
    return
  if (here.op &&& 64) != 0 then
    badMode c "invalid literal/length code"
    return
  wrS c.st fun s => { s with extra := here.op.toUInt32 &&& 15, mode := LENEXT }
  inflate_LENEXT c

/-- Consume the actual selected leaf and perform the checked signed back
update. The total code width bounds the addition, including second-level
codes. Only back and length are written before the classification suffix. -/
theorem lenFinish_consume_cursor {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8} (dropped : Nat)
    (hc : c.st = some (.tab zs)) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (leaf : LenLeaf dropped l.here) (back : s.back.toInt = dropped)
    (enough : l.here.bits.toNat ≤ l.bits.toNat) (B : BitInv h l bs) :
    ∃ regs after state,
      runX (lenFinish c) l h = runX (lenLeafTail c l.here) regs after ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧ BitInv after regs bs ∧
      DecodeStateFrame s state ∧ SymbolRegShape l regs ∧
      state.length = l.here.val.toUInt32 ∧
      state.back = Int32.ofNat (dropped + l.here.bits.toNat) ∧
      stream regs bs = (stream l bs).drop l.here.bits.toNat ∧
      regs.bits.toNat = l.bits.toNat - l.here.bits.toNat ∧
      regs.here = l.here ∧ after = setI h zs state ∧ regs.next = l.next := by
  have small : l.here.bits.toUInt32.toNat < 64 := by rw [UInt8.toNat_toUInt32]; have := leaf.1; omega
  obtain ⟨nextInv, bits, count⟩ := DROPBITS_inv B l.here.bits.toUInt32 (by simpa using enough) small
  let regs := { l with hold := l.hold >>> l.here.bits.toUInt32.toUInt64, bits := l.bits - l.here.bits.toUInt32 }
  let state := { s with back := Int32.ofNat (dropped + l.here.bits.toNat), length := l.here.val.toUInt32 }
  let after := setI h zs state
  have checked : chkI32 (s.back.toInt + l.here.bits.toNat) h =
      .ok (Int32.ofNat (dropped + l.here.bits.toNat), h) := by
    rw [back]
    unfold chkI32
    have bound := leaf.1
    split
    · rfl
    · omega
  have load : ldInflateState c.st h = .ok (s, h) := by rw [hc, ldI_eq, good.live.hs]
  have write : wrS c.st (fun s => { s with back := Int32.ofNat (dropped + l.here.bits.toNat), length := l.here.val.toUInt32 }) h = .ok ((), after) := by rw [hc, wrI_eq, good.live.hs]
  refine ⟨regs, after, state, ?_, good.decode_update rfl good.live.mode,
    tables.decode_update good.live.hs rfl, nextInv.decode_update zs state, rfl, by rfl,
    rfl, rfl, ?_, ?_, rfl, rfl, rfl⟩
  · unfold lenFinish lenLeafTail
    simp only [runX_bind, runX_get, DROPBITS_run l h _ small,
      runX_lift_ok load, runX_lift_ok checked, runX_lift_ok write]
    rfl
  · simpa only [UInt8.toNat_toUInt32] using bits
  · simpa only [UInt8.toNat_toUInt32] using count

/-- Projection retaining the exact private heap update. -/
theorem lenFinish_consume_heap {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8} (dropped : Nat)
    (hc : c.st = some (.tab zs)) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (leaf : LenLeaf dropped l.here) (back : s.back.toInt = dropped)
    (enough : l.here.bits.toNat ≤ l.bits.toNat) (B : BitInv h l bs) :
    ∃ regs after state,
      runX (lenFinish c) l h = runX (lenLeafTail c l.here) regs after ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧ BitInv after regs bs ∧
      DecodeStateFrame s state ∧ SymbolRegShape l regs ∧
      state.length = l.here.val.toUInt32 ∧
      state.back = Int32.ofNat (dropped + l.here.bits.toNat) ∧
      stream regs bs = (stream l bs).drop l.here.bits.toNat ∧
      regs.bits.toNat = l.bits.toNat - l.here.bits.toNat ∧
      regs.here = l.here ∧ after = setI h zs state := by
  obtain ⟨regs, after, state, run, finalGood, finalTables, inv, frame, shape,
    length, back, bits, count, here, heap, _⟩ := lenFinish_consume_cursor dropped hc good tables leaf back enough B
  exact ⟨regs, after, state, run, finalGood, finalTables, inv, frame, shape, length, back, bits, count, here, heap⟩

/-- Projection retaining the original leaf-consumption statement. -/
theorem lenFinish_consume {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8} (dropped : Nat)
    (hc : c.st = some (.tab zs)) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (leaf : LenLeaf dropped l.here) (back : s.back.toInt = dropped)
    (enough : l.here.bits.toNat ≤ l.bits.toNat) (B : BitInv h l bs) :
    ∃ regs after state,
      runX (lenFinish c) l h = runX (lenLeafTail c l.here) regs after ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧ BitInv after regs bs ∧
      DecodeStateFrame s state ∧ SymbolRegShape l regs ∧
      state.length = l.here.val.toUInt32 ∧
      state.back = Int32.ofNat (dropped + l.here.bits.toNat) ∧
      stream regs bs = (stream l bs).drop l.here.bits.toNat ∧
      regs.bits.toNat = l.bits.toNat - l.here.bits.toNat ∧
      regs.here = l.here := by
  obtain ⟨regs, after, state, run, finalGood, finalTables, inv, frame, shape,
    length, back, bits, count, here, _⟩ := lenFinish_consume_heap dropped hc good tables leaf back enough B
  exact ⟨regs, after, state, run, finalGood, finalTables, inv, frame, shape, length, back, bits, count, here⟩

/-- Every normal slow-lookup result has a small signed back value. -/
theorem back_ofNat_small (dropped : Nat) (bound : dropped ≤ 15) :
    (Int32.ofNat dropped).toInt = dropped :=
  int32_ofInt_toInt dropped (by omega) (by omega)

/-- Actual leaf classification returns a literal, block end or malformed-code
exit, or reaches LENEXT with the constructor's precise base/extra-bit bound. -/
theorem lenLeafTail_boundary_frame {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {here : Code} {bs : List UInt8} {dropped : Nat}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs))
    (good : Good h r zs z s) (tables : DataTablesSafe h s) (B : BitInv h l bs)
    (leaf : LenLeaf dropped here) (length : s.length = here.val.toUInt32) :
    (∃ after stream state,
      runX (lenLeafTail c here) l h = .ok ((.ok (), l), after) ∧
      Good after r zs stream state ∧ DataTableInvariant after state ∧ BitInv after l bs ∧
      (state.mode = LIT ∨ state.mode = TYPE ∨ state.mode = BAD) ∧ DecodeStateFrame s state ∧ after = setI (r.put h stream) zs state) ∨
    (∃ after state,
      runX (lenLeafTail c here) l h = runX (inflate_LENEXT c) l after ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧ BitInv after l bs ∧
      state.mode = LENEXT ∧ DecodeStateFrame s state ∧
      state.extra.toNat ≤ 5 ∧ 3 ≤ state.length.toNat ∧ state.length.toNat + 2 ^ state.extra.toNat ≤ 259 ∧ state.back = s.back ∧ after = setI h zs state) := by
  have env : Env c h r zs z s := ⟨hr, hc, good.live.hz, good.live.hs⟩
  by_cases literal : here.op.toNat = 0
  · left
    let state := { s with mode := LIT }
    have finalGood := good.decode_update (after := state) rfl
      (by change HEAD ≤ LIT ∧ LIT ≤ SYNC; decide)
    have finalTables := tables.decode_update good.live.hs (after := state) rfl
    refine ⟨setI h zs state, z, state, ?_, finalGood, fun _ => finalTables,
      B.decode_update zs state, Or.inl rfl, rfl, by rw [ZStreamRef.put_self good.live.hz]⟩
    unfold lenLeafTail
    simp only [literal, beq_self_eq_true, ite_true, runX_bind, runX_setMode env, runX_pure]
    rfl
  by_cases endCode : here.op &&& 32 ≠ 0
  · left
    let state := { s with back := -1, mode := TYPE }
    have finalGood := good.decode_update (after := state) rfl
      (by change HEAD ≤ TYPE ∧ TYPE ≤ SYNC; decide)
    have finalTables := tables.decode_update good.live.hs (after := state) rfl
    refine ⟨setI h zs state, z, state, ?_, finalGood, fun _ => finalTables,
      B.decode_update zs state, Or.inr (Or.inl rfl), rfl, by rw [ZStreamRef.put_self good.live.hz]⟩
    unfold lenLeafTail
    simp [literal, endCode, runX_bind, runX_wrS env, runX_pure, state]
  by_cases invalid : here.op &&& 64 ≠ 0
  · left
    have member : "invalid literal/length code" ∈ strTable := by decide +kernel
    obtain ⟨i, _, badRun⟩ := badMode_run env member
    let stream := { z with msg := .ref (.str i) 0 }
    let state := { s with mode := BAD }
    have inv : StInv h zs state := good.inv.of_fields rfl rfl rfl rfl rfl rfl rfl rfl rfl good.inv.bits rfl rfl rfl
    have finalGood : Good (badHeap h r zs z s i) r zs stream state :=
      good.setZI rfl good.live.zalloc good.live.zfree rfl
        (by change HEAD ≤ BAD ∧ BAD ≤ SYNC; decide) inv
    have bits : BitInv (badHeap h r zs z s i) l bs := by
      refine ⟨B.have_eq, ?_, B.hold_lt⟩
      rcases B.next with empty | ⟨ref, array, off, pointer, arrayGet, bound, contents⟩
      · exact Or.inl empty
      · refine Or.inr ⟨ref, array, off, pointer, ?_, bound, contents⟩
        cases ref with
        | str sourceIndex =>
          have stable : C.LibcBorrow.BorrowStable h (badHeap h r zs z s i) (.str sourceIndex) := by
            apply Or.inr
            cases r <;> simp only [badHeap, setI, ZStreamRef.put] <;>
              first | rfl | split <;> rfl
          exact (C.LibcBorrow.str_view_stable stable).trans arrayGet
        | _ =>
          cases r <;> simp only [badHeap, setI, Space.get, ZStreamRef.put] <;>
            first | exact arrayGet | split <;> exact arrayGet
    have data : DataTableInvariant (badHeap h r zs z s i) state := by
      intro active
      change DataTableMode BAD at active
      rcases active with eq | eq | eq | eq | eq | eq | eq <;> cases eq
    refine ⟨badHeap h r zs z s i, stream, state, ?_, finalGood, data, bits,
      Or.inr (Or.inr rfl), rfl, rfl⟩
    unfold lenLeafTail
    simp [literal, endCode, invalid, runX_bind, runX_lift_ok badRun, runX_pure]
  · right
    have base : here.op &&& 16 ≠ 0 ∧ (here.op &&& 15).toNat ≤ 5 ∧
        3 ≤ here.val.toNat ∧ here.val.toNat + 2 ^ (here.op &&& 15).toNat ≤ 259 := by
      rcases leaf.2 with lit | base | bad
      · exact False.elim (literal (by rw [lit]; rfl))
      · exact base
      · exact False.elim (invalid bad.2)
    let state := { s with extra := here.op.toUInt32 &&& 15, mode := LENEXT }
    have finalGood := good.decode_update (after := state) rfl
      (by change HEAD ≤ LENEXT ∧ LENEXT ≤ SYNC; decide)
    have finalTables := tables.decode_update good.live.hs (after := state) rfl
    have extra : state.extra.toNat = (here.op &&& 15).toNat := by
      change (here.op.toUInt32 &&& 15).toNat = _
      rw [UInt32.toNat_and, UInt8.toNat_toUInt32, UInt8.toNat_and]
      rfl
    refine ⟨setI h zs state, state, ?_, finalGood, finalTables, B.decode_update zs state,
      rfl, rfl, by rw [extra]; exact base.2.1, ?_, ?_, rfl, rfl⟩
    · unfold lenLeafTail
      simp [literal, endCode, invalid, runX_bind, runX_wrS env, state]
    · change 3 ≤ s.length.toNat
      rw [length, UInt16.toNat_toUInt32]
      exact base.2.2.1
    · change s.length.toNat + 2 ^ state.extra.toNat ≤ 259
      rw [length, UInt16.toNat_toUInt32, extra]
      exact base.2.2.2

/-- Projection retaining the previous boundary. -/
theorem lenLeafTail_boundary_heap {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {here : Code} {bs : List UInt8} {dropped : Nat}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs))
    (good : Good h r zs z s) (tables : DataTablesSafe h s) (B : BitInv h l bs)
    (leaf : LenLeaf dropped here) (length : s.length = here.val.toUInt32) :
    (∃ after stream state,
      runX (lenLeafTail c here) l h = .ok ((.ok (), l), after) ∧
      Good after r zs stream state ∧ DataTableInvariant after state ∧ BitInv after l bs ∧
      (state.mode = LIT ∨ state.mode = TYPE ∨ state.mode = BAD) ∧ DecodeStateFrame s state) ∨
    (∃ after state,
      runX (lenLeafTail c here) l h = runX (inflate_LENEXT c) l after ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧ BitInv after l bs ∧
      state.mode = LENEXT ∧ DecodeStateFrame s state ∧
      state.extra.toNat ≤ 5 ∧ 3 ≤ state.length.toNat ∧ state.length.toNat + 2 ^ state.extra.toNat ≤ 259 ∧ state.back = s.back ∧ after = setI h zs state) := by
  rcases lenLeafTail_boundary_frame hr hc good tables B leaf length with stopped | continued
  · obtain ⟨after, stream, state, run, finalGood, data, inv, modes, frame, _⟩ := stopped
    exact Or.inl ⟨after, stream, state, run, finalGood, data, inv, modes, frame⟩
  · exact Or.inr continued

/-- Projection retaining the original full leaf classification. -/
theorem lenLeafTail_boundary_full {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {here : Code} {bs : List UInt8} {dropped : Nat}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs))
    (good : Good h r zs z s) (tables : DataTablesSafe h s) (B : BitInv h l bs)
    (leaf : LenLeaf dropped here) (length : s.length = here.val.toUInt32) :
    (∃ after stream state,
      runX (lenLeafTail c here) l h = .ok ((.ok (), l), after) ∧
      Good after r zs stream state ∧ DataTableInvariant after state ∧ BitInv after l bs ∧
      (state.mode = LIT ∨ state.mode = TYPE ∨ state.mode = BAD) ∧ DecodeStateFrame s state) ∨
    (∃ after state,
      runX (lenLeafTail c here) l h = runX (inflate_LENEXT c) l after ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧ BitInv after l bs ∧
      state.mode = LENEXT ∧ DecodeStateFrame s state ∧
      state.extra.toNat ≤ 5 ∧ 3 ≤ state.length.toNat ∧ state.length.toNat + 2 ^ state.extra.toNat ≤ 259 ∧ state.back = s.back) := by
  rcases lenLeafTail_boundary_heap hr hc good tables B leaf length with stopped | continued
  · exact Or.inl stopped
  · obtain ⟨after, state, run, finalGood, finalTables, inv, mode, frame, extra, lower, upper, back, _⟩ := continued
    exact Or.inr ⟨after, state, run, finalGood, finalTables, inv, mode, frame, extra, lower, upper, back⟩

/-- Actual leaf classification returns a literal, block end or malformed-code
exit, or reaches LENEXT with the constructor's precise base/extra-bit bound. -/
theorem lenLeafTail_boundary {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {here : Code} {bs : List UInt8} {dropped : Nat}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs))
    (good : Good h r zs z s) (tables : DataTablesSafe h s) (B : BitInv h l bs)
    (leaf : LenLeaf dropped here) (length : s.length = here.val.toUInt32) :
    (∃ after stream state,
      runX (lenLeafTail c here) l h = .ok ((.ok (), l), after) ∧
      Good after r zs stream state ∧ DataTableInvariant after state ∧ BitInv after l bs ∧
      (state.mode = LIT ∨ state.mode = TYPE ∨ state.mode = BAD) ∧ DecodeStateFrame s state) ∨
    (∃ after state,
      runX (lenLeafTail c here) l h = runX (inflate_LENEXT c) l after ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧ BitInv after l bs ∧
      state.mode = LENEXT ∧ DecodeStateFrame s state ∧
      state.extra.toNat ≤ 5 ∧ 3 ≤ state.length.toNat ∧ state.length.toNat + 2 ^ state.extra.toNat ≤ 259) := by
  rcases lenLeafTail_boundary_full hr hc good tables B leaf length with stopped | continued
  · exact Or.inl stopped
  · obtain ⟨after, state, run, finalGood, finalTables, inv, mode, frame, extra, lower, upper, _⟩ := continued
    exact Or.inr ⟨after, state, run, finalGood, finalTables, inv, mode, frame, extra, lower, upper⟩

/-- Complete actual slow LEN execution through leaf classification. All
input-short, literal, block-end and invalid-code exits are checked. Valid
length codes reach the actual LENEXT call with bounded base and extra bits.
The remaining LENEXT/DIST/MATCH continuation is not assumed correct. A
normal exit (a literal, the end of the block or an invalid code) consumes at
least one bit, since every leaf of the installed length table reads one. -/
theorem inflate_LEN_slow_boundary_positive {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (good : Good h r zs z s)
    (tables : DataTablesSafe h s) (B : BitInv h l bs)
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    (∃ outcome regs after finalZ state used consumed,
      used ≤ 4 ∧ used ≤ bs.length ∧ consumed ≤ 15 ∧
      runX (inflate_LEN c) l h = .ok ((outcome, regs), after) ∧
      Good after r zs finalZ state ∧ DataTableInvariant after state ∧ BitInv after regs (bs.drop used) ∧
      stream regs (bs.drop used) = (stream l bs).drop consumed ∧
      SymbolRegShape l regs ∧ DecodeStateFrame s state ∧ regs.bits.toNat ≤ max l.bits.toNat 22 ∧
      (outcome = .error Ex.leave ∨ (outcome = .ok () ∧ (state.mode = LIT ∨ state.mode = TYPE ∨ state.mode = BAD))) ∧
      regs.next = inputAdvance l.next used ∧ after = setI (r.put h finalZ) zs state ∧
      (outcome = .ok () → 1 ≤ consumed)) ∨
    (∃ regs after state used consumed,
      used ≤ 4 ∧ used ≤ bs.length ∧ consumed ≤ 15 ∧
      runX (inflate_LEN c) l h = runX (inflate_LENEXT c) regs after ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧ BitInv after regs (bs.drop used) ∧
      stream regs (bs.drop used) = (stream l bs).drop consumed ∧
      SymbolRegShape l regs ∧ DecodeStateFrame s state ∧ regs.bits.toNat ≤ max l.bits.toNat 22 ∧
      state.mode = LENEXT ∧ state.extra.toNat ≤ 5 ∧ 3 ≤ state.length.toNat ∧
      state.length.toNat + 2 ^ state.extra.toNat ≤ 259 ∧ state.back = Int32.ofNat consumed ∧ after = setI h zs state ∧ regs.next = inputAdvance l.next used) := by
  rcases inflate_LEN_slow_lookup_boundary_leaf hc good tables B slow with stopped | continued
  · obtain ⟨regs, after, state, used, usedFour, usedBound, run, finalGood, finalTables,
      inv, _, bits, shape, frame, bitBound, cursor, heapEq, _⟩ := stopped
    left
    exact ⟨.error Ex.leave, regs, after, z, state, used, 0, usedFour, usedBound, by omega,
      run, finalGood, fun _ => finalTables, inv, by simpa using bits, shape, frame, bitBound, Or.inl rfl, cursor, by rw [ZStreamRef.put_self good.live.hz]; exact heapEq,
      fun impossible => by cases impossible⟩
  · obtain ⟨regs, after, state, used, dropped, usedFour, usedBound, dropBound, source,
      nextGood, nextTables, nextInv, leaf, enough, back, bits, shape, frame, _, bitBound, prefixHeap, cursor,
      positive⟩ := continued
    have backNat : state.back.toInt = dropped := by rw [back]; exact back_ofNat_small dropped dropBound
    obtain ⟨finalRegs, leafHeap, leafState, consumeRun, leafGood, leafTables, leafInv,
      leafFrame, leafShape, length, leafBack, leafStream, leafCount, _, leafHeapEq, leafCursor⟩ :=
      lenFinish_consume_cursor dropped hc nextGood nextTables leaf backNat enough nextInv
    have consumed : dropped + regs.here.bits.toNat ≤ 15 := by have := leaf.1; omega
    have finalStream : stream finalRegs (bs.drop used) =
        (stream l bs).drop (dropped + regs.here.bits.toNat) := by
      rw [leafStream, bits, List.drop_drop]
    have finalBound : finalRegs.bits.toNat ≤ max l.bits.toNat 22 := by rw [leafCount]; omega
    have source' : runX (inflate_LEN c) l h = runX (lenLeafTail c regs.here) finalRegs leafHeap :=
      source.trans consumeRun
    rcases lenLeafTail_boundary_frame hr hc leafGood leafTables leafInv leaf length with stopped | continued
    · obtain ⟨finalHeap, stream, finalState, run, finalGood, finalData, finalInv, modes, finalFrame, finalHeapEq⟩ := stopped
      left
      exact ⟨.ok (), finalRegs, finalHeap, stream, finalState, used, dropped + regs.here.bits.toNat,
        usedFour, usedBound, consumed, source'.trans run, finalGood, finalData, finalInv, finalStream,
        shape.trans leafShape, frame.trans (leafFrame.trans finalFrame), finalBound, Or.inr ⟨rfl, modes⟩, leafCursor.trans cursor, by
          rw [finalHeapEq, leafHeapEq, prefixHeap, ZStreamRef.put_setI, ZStreamRef.put_setI, setI_setI, setI_setI],
        fun _ => by omega⟩
    · obtain ⟨finalHeap, finalState, run, finalGood, finalTables, finalInv, mode, finalFrame,
        extra, lower, upper, retainedBack, finalHeapEq⟩ := continued
      right
      exact ⟨finalRegs, finalHeap, finalState, used, dropped + regs.here.bits.toNat,
        usedFour, usedBound, consumed, source'.trans run, finalGood, finalTables, finalInv, finalStream,
        shape.trans leafShape, frame.trans (leafFrame.trans finalFrame), finalBound, mode, extra, lower, upper, retainedBack.trans leafBack,
          by rw [finalHeapEq, leafHeapEq, prefixHeap, setI_setI, setI_setI], leafCursor.trans cursor⟩

/-- Projection without the consumed-bit lower bound. -/
theorem inflate_LEN_slow_boundary_frame {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (good : Good h r zs z s)
    (tables : DataTablesSafe h s) (B : BitInv h l bs)
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    (∃ outcome regs after finalZ state used consumed,
      used ≤ 4 ∧ used ≤ bs.length ∧ consumed ≤ 15 ∧
      runX (inflate_LEN c) l h = .ok ((outcome, regs), after) ∧
      Good after r zs finalZ state ∧ DataTableInvariant after state ∧ BitInv after regs (bs.drop used) ∧
      stream regs (bs.drop used) = (stream l bs).drop consumed ∧
      SymbolRegShape l regs ∧ DecodeStateFrame s state ∧ regs.bits.toNat ≤ max l.bits.toNat 22 ∧
      (outcome = .error Ex.leave ∨ (outcome = .ok () ∧ (state.mode = LIT ∨ state.mode = TYPE ∨ state.mode = BAD))) ∧
      regs.next = inputAdvance l.next used ∧ after = setI (r.put h finalZ) zs state) ∨
    (∃ regs after state used consumed,
      used ≤ 4 ∧ used ≤ bs.length ∧ consumed ≤ 15 ∧
      runX (inflate_LEN c) l h = runX (inflate_LENEXT c) regs after ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧ BitInv after regs (bs.drop used) ∧
      stream regs (bs.drop used) = (stream l bs).drop consumed ∧
      SymbolRegShape l regs ∧ DecodeStateFrame s state ∧ regs.bits.toNat ≤ max l.bits.toNat 22 ∧
      state.mode = LENEXT ∧ state.extra.toNat ≤ 5 ∧ 3 ≤ state.length.toNat ∧
      state.length.toNat + 2 ^ state.extra.toNat ≤ 259 ∧ state.back = Int32.ofNat consumed ∧ after = setI h zs state ∧ regs.next = inputAdvance l.next used) := by
  rcases inflate_LEN_slow_boundary_positive hr hc good tables B slow with stopped | continued
  · obtain ⟨outcome, regs, after, finalZ, state, used, consumed, four, usedBound, consumedBound,
      run, finalGood, data, inv, bits, shape, frame, bitBound, kinds, cursor, heapEq, _⟩ := stopped
    exact Or.inl ⟨outcome, regs, after, finalZ, state, used, consumed, four, usedBound, consumedBound,
      run, finalGood, data, inv, bits, shape, frame, bitBound, kinds, cursor, heapEq⟩
  · exact Or.inr continued

/-- Projection retaining the previous boundary. -/
theorem inflate_LEN_slow_boundary_cursor {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (good : Good h r zs z s)
    (tables : DataTablesSafe h s) (B : BitInv h l bs)
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    (∃ outcome regs after finalZ state used consumed,
      used ≤ 4 ∧ used ≤ bs.length ∧ consumed ≤ 15 ∧
      runX (inflate_LEN c) l h = .ok ((outcome, regs), after) ∧
      Good after r zs finalZ state ∧ DataTableInvariant after state ∧ BitInv after regs (bs.drop used) ∧
      stream regs (bs.drop used) = (stream l bs).drop consumed ∧
      SymbolRegShape l regs ∧ DecodeStateFrame s state ∧ regs.bits.toNat ≤ max l.bits.toNat 22 ∧
      (outcome = .error Ex.leave ∨ (outcome = .ok () ∧ (state.mode = LIT ∨ state.mode = TYPE ∨ state.mode = BAD))) ∧
      regs.next = inputAdvance l.next used) ∨
    (∃ regs after state used consumed,
      used ≤ 4 ∧ used ≤ bs.length ∧ consumed ≤ 15 ∧
      runX (inflate_LEN c) l h = runX (inflate_LENEXT c) regs after ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧ BitInv after regs (bs.drop used) ∧
      stream regs (bs.drop used) = (stream l bs).drop consumed ∧
      SymbolRegShape l regs ∧ DecodeStateFrame s state ∧ regs.bits.toNat ≤ max l.bits.toNat 22 ∧
      state.mode = LENEXT ∧ state.extra.toNat ≤ 5 ∧ 3 ≤ state.length.toNat ∧
      state.length.toNat + 2 ^ state.extra.toNat ≤ 259 ∧ state.back = Int32.ofNat consumed ∧ after = setI h zs state ∧ regs.next = inputAdvance l.next used) := by
  rcases inflate_LEN_slow_boundary_frame hr hc good tables B slow with stopped | continued
  · obtain ⟨outcome, regs, after, finalZ, state, used, consumed, four, usedBound, consumedBound,
      run, finalGood, data, inv, bits, shape, frame, bitBound, kinds, cursor, _⟩ := stopped
    exact Or.inl ⟨outcome, regs, after, finalZ, state, used, consumed, four, usedBound, consumedBound,
      run, finalGood, data, inv, bits, shape, frame, bitBound, kinds, cursor⟩
  · exact Or.inr continued

/-- Projection retaining the original slow LEN heap boundary. -/
theorem inflate_LEN_slow_boundary_heap {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (good : Good h r zs z s)
    (tables : DataTablesSafe h s) (B : BitInv h l bs)
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    (∃ outcome regs after finalZ state used consumed,
      used ≤ 4 ∧ used ≤ bs.length ∧ consumed ≤ 15 ∧
      runX (inflate_LEN c) l h = .ok ((outcome, regs), after) ∧
      Good after r zs finalZ state ∧ DataTableInvariant after state ∧ BitInv after regs (bs.drop used) ∧
      stream regs (bs.drop used) = (stream l bs).drop consumed ∧
      SymbolRegShape l regs ∧ DecodeStateFrame s state ∧ regs.bits.toNat ≤ max l.bits.toNat 22 ∧
      (outcome = .error Ex.leave ∨ (outcome = .ok () ∧ (state.mode = LIT ∨ state.mode = TYPE ∨ state.mode = BAD)))) ∨
    (∃ regs after state used consumed,
      used ≤ 4 ∧ used ≤ bs.length ∧ consumed ≤ 15 ∧
      runX (inflate_LEN c) l h = runX (inflate_LENEXT c) regs after ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧ BitInv after regs (bs.drop used) ∧
      stream regs (bs.drop used) = (stream l bs).drop consumed ∧
      SymbolRegShape l regs ∧ DecodeStateFrame s state ∧ regs.bits.toNat ≤ max l.bits.toNat 22 ∧
      state.mode = LENEXT ∧ state.extra.toNat ≤ 5 ∧ 3 ≤ state.length.toNat ∧
      state.length.toNat + 2 ^ state.extra.toNat ≤ 259 ∧ state.back = Int32.ofNat consumed ∧ after = setI h zs state) := by
  rcases inflate_LEN_slow_boundary_cursor hr hc good tables B slow with stopped | continued
  · obtain ⟨outcome, regs, after, finalZ, state, used, consumed, four, usedBound, consumedBound,
      run, finalGood, data, inv, bits, shape, frame, bound, kinds, _⟩ := stopped
    exact Or.inl ⟨outcome, regs, after, finalZ, state, used, consumed, four, usedBound, consumedBound,
      run, finalGood, data, inv, bits, shape, frame, bound, kinds⟩
  · obtain ⟨regs, after, state, used, consumed, four, usedBound, consumedBound, run,
      finalGood, finalTables, inv, bits, shape, frame, bound, mode, extra, lower, upper, back, heap, _⟩ := continued
    exact Or.inr ⟨regs, after, state, used, consumed, four, usedBound, consumedBound, run,
      finalGood, finalTables, inv, bits, shape, frame, bound, mode, extra, lower, upper, back, heap⟩

/-- Projection retaining the original full slow LEN boundary. -/
theorem inflate_LEN_slow_boundary_full {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (good : Good h r zs z s)
    (tables : DataTablesSafe h s) (B : BitInv h l bs)
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    (∃ outcome regs after finalZ state used consumed,
      used ≤ 4 ∧ used ≤ bs.length ∧ consumed ≤ 15 ∧
      runX (inflate_LEN c) l h = .ok ((outcome, regs), after) ∧
      Good after r zs finalZ state ∧ DataTableInvariant after state ∧ BitInv after regs (bs.drop used) ∧
      stream regs (bs.drop used) = (stream l bs).drop consumed ∧
      SymbolRegShape l regs ∧ DecodeStateFrame s state ∧ regs.bits.toNat ≤ max l.bits.toNat 22 ∧
      (outcome = .error Ex.leave ∨ (outcome = .ok () ∧ (state.mode = LIT ∨ state.mode = TYPE ∨ state.mode = BAD)))) ∨
    (∃ regs after state used consumed,
      used ≤ 4 ∧ used ≤ bs.length ∧ consumed ≤ 15 ∧
      runX (inflate_LEN c) l h = runX (inflate_LENEXT c) regs after ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧ BitInv after regs (bs.drop used) ∧
      stream regs (bs.drop used) = (stream l bs).drop consumed ∧
      SymbolRegShape l regs ∧ DecodeStateFrame s state ∧ regs.bits.toNat ≤ max l.bits.toNat 22 ∧
      state.mode = LENEXT ∧ state.extra.toNat ≤ 5 ∧ 3 ≤ state.length.toNat ∧
      state.length.toNat + 2 ^ state.extra.toNat ≤ 259 ∧ state.back = Int32.ofNat consumed) := by
  rcases inflate_LEN_slow_boundary_heap hr hc good tables B slow with stopped | continued
  · exact Or.inl stopped
  · obtain ⟨regs, after, state, used, consumed, four, usedBound, consumedBound, run,
      finalGood, finalTables, inv, bits, shape, frame, bound, mode, extra, lower, upper, back, _⟩ := continued
    exact Or.inr ⟨regs, after, state, used, consumed, four, usedBound, consumedBound, run,
      finalGood, finalTables, inv, bits, shape, frame, bound, mode, extra, lower, upper, back⟩
/-- Complete actual slow LEN execution through leaf classification. All
input-short, literal, block-end and invalid-code exits are checked. Valid
length codes reach the actual LENEXT call with bounded base and extra bits.
The remaining LENEXT/DIST/MATCH continuation is not assumed correct. -/
theorem inflate_LEN_slow_boundary {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (good : Good h r zs z s)
    (tables : DataTablesSafe h s) (B : BitInv h l bs)
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    (∃ outcome regs after finalZ state used consumed,
      used ≤ 4 ∧ used ≤ bs.length ∧ consumed ≤ 15 ∧
      runX (inflate_LEN c) l h = .ok ((outcome, regs), after) ∧
      Good after r zs finalZ state ∧ DataTableInvariant after state ∧ BitInv after regs (bs.drop used) ∧
      stream regs (bs.drop used) = (stream l bs).drop consumed ∧
      SymbolRegShape l regs ∧ DecodeStateFrame s state ∧ regs.bits.toNat ≤ max l.bits.toNat 22 ∧
      (outcome = .error Ex.leave ∨ (outcome = .ok () ∧ (state.mode = LIT ∨ state.mode = TYPE ∨ state.mode = BAD)))) ∨
    (∃ regs after state used consumed,
      used ≤ 4 ∧ used ≤ bs.length ∧ consumed ≤ 15 ∧
      runX (inflate_LEN c) l h = runX (inflate_LENEXT c) regs after ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧ BitInv after regs (bs.drop used) ∧
      stream regs (bs.drop used) = (stream l bs).drop consumed ∧
      SymbolRegShape l regs ∧ DecodeStateFrame s state ∧ regs.bits.toNat ≤ max l.bits.toNat 22 ∧
      state.mode = LENEXT ∧ state.extra.toNat ≤ 5 ∧ 3 ≤ state.length.toNat ∧
      state.length.toNat + 2 ^ state.extra.toNat ≤ 259) := by
  rcases inflate_LEN_slow_boundary_full hr hc good tables B slow with stopped | continued
  · exact Or.inl stopped
  · obtain ⟨regs, after, state, used, consumed, usedFour, usedBound, consumedBound,
      run, finalGood, finalTables, inv, bits, shape, frame, bitBound, mode, extra, lower, upper, _⟩ := continued
    exact Or.inr ⟨regs, after, state, used, consumed, usedFour, usedBound, consumedBound,
      run, finalGood, finalTables, inv, bits, shape, frame, bitBound, mode, extra, lower, upper⟩

end Zlib.Inflate.Proofs
