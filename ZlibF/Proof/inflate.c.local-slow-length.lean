import ZlibF.Proof.«inflate.c.local-operations»
import ZlibF.Proof.«inflate.c.length-extra»

/-! Actual slow length-symbol decoding on local decoder storage.
The original table reads and bit parsing run on the same heap. -/
namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inffast.Spec
set_option autoImplicit false
set_option maxRecDepth 8192

theorem LocalGood.decode_after {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {before after : InflateState} (good : LocalGood h cutoff r zs z before)
    (frame : DecodeStateFrame before after) (mode : HEAD ≤ after.mode ∧ after.mode ≤ SYNC) :
    LocalGood (setI h zs after) cutoff r zs z after := good.decode_update frame mode

theorem inflate_LEN_slow_lookup_boundary_mode {c : Ctx} {l : IL} {h : Heap} {cutoff : Nat}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8}
    (hc : c.st = some (.tab zs)) (good : LocalGood h cutoff r zs z s)
    (tables : DataTablesSafe h s) (B : BitInv h l bs)
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    (∃ regs after state used,
      used ≤ 4 ∧ used ≤ bs.length ∧
      runX (inflate_LEN c) l h = .ok ((.error Ex.leave, regs), after) ∧
      LocalGood after cutoff r zs z state ∧ DataTablesSafe after state ∧
      BitInv after regs (bs.drop used) ∧ regs.have_ = 0 ∧
      stream regs (bs.drop used) = stream l bs ∧ SymbolRegShape l regs ∧
      DecodeStateFrame s state ∧ regs.bits.toNat ≤ max l.bits.toNat 22 ∧ regs.next = inputAdvance l.next used ∧ after = setI h zs state ∧ state.mode = s.mode) ∨
    (∃ regs after state used dropped,
      used ≤ 4 ∧ used ≤ bs.length ∧ dropped ≤ 15 ∧
      runX (inflate_LEN c) l h = runX (lenFinish c) regs after ∧
      LocalGood after cutoff r zs z state ∧ DataTablesSafe after state ∧
      BitInv after regs (bs.drop used) ∧ LenLeaf dropped regs.here ∧
      regs.here.bits.toNat ≤ regs.bits.toNat ∧ state.back = Int32.ofNat dropped ∧
      stream regs (bs.drop used) = (stream l bs).drop dropped ∧
      SymbolRegShape l regs ∧ DecodeStateFrame s state ∧
      regs.bits.toNat = l.bits.toNat + 8 * used - dropped ∧
      regs.bits.toNat ≤ max l.bits.toNat 22 ∧ after = setI h zs state ∧ regs.next = inputAdvance l.next used) := by
  let reset := { s with back := 0 }
  let heap := setI h zs reset
  have resetGood : LocalGood heap cutoff r zs z reset := good.decode_after rfl good.live.mode
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
    have finalGood : LocalGood (setI heap zs state) cutoff r zs z state :=
      resetGood.decode_after rfl resetGood.live.mode
    have finalTables : DataTablesSafe (setI heap zs state) state :=
      resetTables.decode_update resetGood.live.hs rfl
    right
    refine ⟨regs, setI heap zs state, state, used, dropped, usedFour, usedBound, dropBound,
      ?_, finalGood, finalTables, inv, leaf, enough, rfl, bits, shape, rfl, count, bitBound, by simp [heap], cursor⟩
    rw [source, runX_bind, run]

theorem inflate_LEN_slow_lookup_boundary_frame {c : Ctx} {l : IL} {h : Heap} {cutoff : Nat}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8}
    (hc : c.st = some (.tab zs)) (good : LocalGood h cutoff r zs z s)
    (tables : DataTablesSafe h s) (B : BitInv h l bs)
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    (∃ regs after state used,
      used ≤ 4 ∧ used ≤ bs.length ∧
      runX (inflate_LEN c) l h = .ok ((.error Ex.leave, regs), after) ∧
      LocalGood after cutoff r zs z state ∧ DataTablesSafe after state ∧
      BitInv after regs (bs.drop used) ∧ regs.have_ = 0 ∧
      stream regs (bs.drop used) = stream l bs ∧ SymbolRegShape l regs ∧
      DecodeStateFrame s state ∧ regs.bits.toNat ≤ max l.bits.toNat 22 ∧ regs.next = inputAdvance l.next used ∧ after = setI h zs state) ∨
    (∃ regs after state used dropped,
      used ≤ 4 ∧ used ≤ bs.length ∧ dropped ≤ 15 ∧
      runX (inflate_LEN c) l h = runX (lenFinish c) regs after ∧
      LocalGood after cutoff r zs z state ∧ DataTablesSafe after state ∧
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

theorem lenFinish_consume_cursor {c : Ctx} {l : IL} {h : Heap} {cutoff : Nat} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8} (dropped : Nat)
    (hc : c.st = some (.tab zs)) (good : LocalGood h cutoff r zs z s) (tables : DataTablesSafe h s)
    (leaf : LenLeaf dropped l.here) (back : s.back.toInt = dropped)
    (enough : l.here.bits.toNat ≤ l.bits.toNat) (B : BitInv h l bs) :
    ∃ regs after state,
      runX (lenFinish c) l h = runX (lenLeafTail c l.here) regs after ∧
      LocalGood after cutoff r zs z state ∧ DataTablesSafe after state ∧ BitInv after regs bs ∧
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
  refine ⟨regs, after, state, ?_, good.decode_after rfl good.live.mode,
    tables.decode_update good.live.hs rfl, nextInv.decode_update zs state, rfl, by rfl,
    rfl, rfl, ?_, ?_, rfl, rfl, rfl⟩
  · unfold lenFinish lenLeafTail
    simp only [runX_bind, runX_get, DROPBITS_run l h _ small,
      runX_lift_ok load, runX_lift_ok checked, runX_lift_ok write]
    rfl
  · simpa only [UInt8.toNat_toUInt32] using bits
  · simpa only [UInt8.toNat_toUInt32] using count

theorem lenLeafTail_boundary_frame {c : Ctx} {l : IL} {h : Heap} {cutoff : Nat} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {here : Code} {bs : List UInt8} {dropped : Nat}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs))
    (good : LocalGood h cutoff r zs z s) (tables : DataTablesSafe h s) (B : BitInv h l bs)
    (leaf : LenLeaf dropped here) (length : s.length = here.val.toUInt32) :
    (∃ after stream state,
      runX (lenLeafTail c here) l h = .ok ((.ok (), l), after) ∧
      LocalGood after cutoff r zs stream state ∧ DataTableInvariant after state ∧ BitInv after l bs ∧
      (state.mode = LIT ∨ state.mode = TYPE ∨ state.mode = BAD) ∧ DecodeStateFrame s state ∧ after = setI (r.put h stream) zs state) ∨
    (∃ after state,
      runX (lenLeafTail c here) l h = runX (inflate_LENEXT c) l after ∧
      LocalGood after cutoff r zs z state ∧ DataTablesSafe after state ∧ BitInv after l bs ∧
      state.mode = LENEXT ∧ DecodeStateFrame s state ∧
      state.extra.toNat ≤ 5 ∧ 3 ≤ state.length.toNat ∧ state.length.toNat + 2 ^ state.extra.toNat ≤ 259 ∧ state.back = s.back ∧ after = setI h zs state) := by
  have env : Env c h r zs z s := ⟨hr, hc, good.live.hz, good.live.hs⟩
  by_cases literal : here.op.toNat = 0
  · left
    let state := { s with mode := LIT }
    have finalGood := good.decode_after (after := state) rfl
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
    have finalGood := good.decode_after (after := state) rfl
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
    have finalGood : LocalGood (badHeap h r zs z s i) cutoff r zs stream state :=
      good.setZI rfl good.live.zalloc good.live.zfree rfl
        (by change HEAD ≤ BAD ∧ BAD ≤ SYNC; decide) inv
    have bits : BitInv (badHeap h r zs z s i) l bs := by
      refine ⟨B.have_eq, ?_, B.hold_lt⟩
      rcases B.next with empty | ⟨ref, array, off, pointer, arrayGet, bound, contents⟩
      · exact Or.inl empty
      · refine Or.inr ⟨ref, array, off, pointer, ?_, bound, contents⟩
        cases ref <;> cases r <;>
          simp only [badHeap, setI, Space.get, ZStreamRef.put] <;>
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
    have finalGood := good.decode_after (after := state) rfl
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

theorem inflate_LEN_slow_boundary_frame {c : Ctx} {l : IL} {h : Heap} {cutoff : Nat} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (good : LocalGood h cutoff r zs z s)
    (tables : DataTablesSafe h s) (B : BitInv h l bs)
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    (∃ outcome regs after finalZ state used consumed,
      used ≤ 4 ∧ used ≤ bs.length ∧ consumed ≤ 15 ∧
      runX (inflate_LEN c) l h = .ok ((outcome, regs), after) ∧
      LocalGood after cutoff r zs finalZ state ∧ DataTableInvariant after state ∧ BitInv after regs (bs.drop used) ∧
      stream regs (bs.drop used) = (stream l bs).drop consumed ∧
      SymbolRegShape l regs ∧ DecodeStateFrame s state ∧ regs.bits.toNat ≤ max l.bits.toNat 22 ∧
      (outcome = .error Ex.leave ∨ (outcome = .ok () ∧ (state.mode = LIT ∨ state.mode = TYPE ∨ state.mode = BAD))) ∧
      regs.next = inputAdvance l.next used ∧ after = setI (r.put h finalZ) zs state) ∨
    (∃ regs after state used consumed,
      used ≤ 4 ∧ used ≤ bs.length ∧ consumed ≤ 15 ∧
      runX (inflate_LEN c) l h = runX (inflate_LENEXT c) regs after ∧
      LocalGood after cutoff r zs z state ∧ DataTablesSafe after state ∧ BitInv after regs (bs.drop used) ∧
      stream regs (bs.drop used) = (stream l bs).drop consumed ∧
      SymbolRegShape l regs ∧ DecodeStateFrame s state ∧ regs.bits.toNat ≤ max l.bits.toNat 22 ∧
      state.mode = LENEXT ∧ state.extra.toNat ≤ 5 ∧ 3 ≤ state.length.toNat ∧
      state.length.toNat + 2 ^ state.extra.toNat ≤ 259 ∧ state.back = Int32.ofNat consumed ∧ after = setI h zs state ∧ regs.next = inputAdvance l.next used) := by
  rcases inflate_LEN_slow_lookup_boundary_frame hc good tables B slow with stopped | continued
  · obtain ⟨regs, after, state, used, usedFour, usedBound, run, finalGood, finalTables,
      inv, _, bits, shape, frame, bitBound, cursor, heapEq⟩ := stopped
    left
    exact ⟨.error Ex.leave, regs, after, z, state, used, 0, usedFour, usedBound, by omega,
      run, finalGood, fun _ => finalTables, inv, by simpa using bits, shape, frame, bitBound, Or.inl rfl, cursor, by rw [ZStreamRef.put_self good.live.hz]; exact heapEq⟩
  · obtain ⟨regs, after, state, used, dropped, usedFour, usedBound, dropBound, source,
      nextGood, nextTables, nextInv, leaf, enough, back, bits, shape, frame, _, bitBound, prefixHeap, cursor⟩ := continued
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
          rw [finalHeapEq, leafHeapEq, prefixHeap, ZStreamRef.put_setI, ZStreamRef.put_setI, setI_setI, setI_setI]⟩
    · obtain ⟨finalHeap, finalState, run, finalGood, finalTables, finalInv, mode, finalFrame,
        extra, lower, upper, retainedBack, finalHeapEq⟩ := continued
      right
      exact ⟨finalRegs, finalHeap, finalState, used, dropped + regs.here.bits.toNat,
        usedFour, usedBound, consumed, source'.trans run, finalGood, finalTables, finalInv, finalStream,
        shape.trans leafShape, frame.trans (leafFrame.trans finalFrame), finalBound, mode, extra, lower, upper, retainedBack.trans leafBack,
          by rw [finalHeapEq, leafHeapEq, prefixHeap, setI_setI, setI_setI], leafCursor.trans cursor⟩

theorem inflate_LENEXT_boundary_bounded {c : Ctx} {l : IL} {h : Heap} {cutoff : Nat} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8} (before : Nat)
    (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (good : LocalGood h cutoff r zs z s) (tables : DataTablesSafe h s)
    (B : BitInv h l bs) (extra : s.extra.toNat ≤ 5)
    (lower : 3 ≤ s.length.toNat) (budget : s.length.toNat + 2 ^ s.extra.toNat ≤ 259)
    (back : s.back = Int32.ofNat before) (backBound : before ≤ 15) :
    (∃ regs used,
      runX (inflate_LENEXT c) l h = .ok ((.error Ex.leave, regs), h) ∧
      used ≤ bs.length ∧ BitInv h regs (bs.drop used) ∧ regs.have_ = 0 ∧
      stream regs (bs.drop used) = stream l bs ∧ SymbolRegShape l regs ∧ regs.next = inputAdvance l.next used ∧ regs.bits.toNat ≤ max l.bits.toNat 12) ∨
    (∃ regs after state used,
      runX (inflate_LENEXT c) l h = runX (inflate_DIST c) regs after ∧
      used ≤ bs.length ∧ LocalGood after cutoff r zs z state ∧ DataTablesSafe after state ∧
      BitInv after regs (bs.drop used) ∧ state.mode = DIST ∧ DecodeStateFrame s state ∧
      SymbolRegShape l regs ∧ stream regs (bs.drop used) = (stream l bs).drop s.extra.toNat ∧
      state.was = state.length ∧ 3 ≤ state.length.toNat ∧ state.length.toNat ≤ 258 ∧
      state.back = Int32.ofNat (before + s.extra.toNat) ∧ after = setI h zs state ∧ regs.next = inputAdvance l.next used ∧ regs.bits.toNat ≤ max l.bits.toNat 12) := by
  have env : Env c h r zs z s := ⟨hr, hc, good.live.hz, good.live.hs⟩
  have load : ldInflateState c.st h = .ok (s, h) := by rw [hc, ldI_eq, good.live.hs]
  by_cases zero : s.extra = 0
  · right
    let state := { s with was := s.length, mode := DIST }
    have finalGood := good.decode_after (after := state) rfl (by change HEAD ≤ DIST ∧ DIST ≤ SYNC; decide)
    have finalTables := tables.decode_update good.live.hs (after := state) rfl
    refine ⟨l, setI h zs state, state, 0, ?_, by omega, finalGood, finalTables,
      B.decode_update zs state, rfl, rfl, by rfl, ?_, rfl, lower, ?_, ?_, rfl, (inputAdvance_zero l.next).symm, Nat.le_max_left _ _⟩
    · unfold inflate_LENEXT
      simp only [runX_bind, runX_lift_ok load, zero, bne_self_eq_false, Bool.false_eq_true, ite_false,
        runX_wrS env]
      simp only [state, zero]
    · simp only [zero, UInt32.toNat_zero, List.drop_zero]
    · rw [zero] at budget
      change s.length.toNat ≤ 258
      have : (0 : UInt32).toNat = 0 := rfl
      simp only [this, Nat.pow_zero] at budget
      omega
    · simp only [zero, UInt32.toNat_zero, Nat.add_zero]
      exact back
  · obtain ⟨result, current, used, run, usedBound, currentInv, sameStream, count, shape,
        bitBound, _, enough, empty, kinds, cursor⟩ := NEEDBITS_run_cursor B s.extra (by omega)
    have prefixRun := inflate_LENEXT_need_cut (l := l) hc good.live.hs zero
    cases result with
    | error e =>
      have equal : e = Ex.leave := by
        rcases kinds with impossible | equal
        · cases impossible
        · exact Except.error.inj equal
      subst e
      left
      refine ⟨current, used, ?_, usedBound, currentInv, (empty rfl).2.1, sameStream, ?_, cursor, by omega⟩
      · rw [prefixRun]
        unfold lenExtraNeed
        rw [runX_bind, run]
      · unfold SymbolRegShape
        rw [shape]
    | ok unit =>
      cases unit
      have available := enough rfl
      let bits := current.hold.toUInt32 &&& ((1 : UInt32) <<< s.extra - 1)
      have bitsNat : bits.toNat = current.hold.toNat % 2 ^ s.extra.toNat := BITS_toNat current s.extra (by omega)
      have bitsBound : bits.toNat < 2 ^ s.extra.toNat := by rw [bitsNat]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
      have lengthNat : (s.length + bits).toNat = s.length.toNat + bits.toNat := by
        rw [UInt32.toNat_add, Nat.mod_eq_of_lt (by omega)]
      have unsignedBack : (i2u s.back).toNat = before := by
        rw [back]
        simp [i2u, Nat.mod_eq_of_lt (by omega : before < 2 ^ 32)]
      have backNat : (i2u s.back + s.extra).toNat = before + s.extra.toNat := by
        rw [UInt32.toNat_add, unsignedBack, Nat.mod_eq_of_lt (by omega)]
      have backEq : u2i (i2u s.back + s.extra) = Int32.ofNat (before + s.extra.toNat) := by
        unfold u2i
        rw [backNat]
        rfl
      have small : s.extra.toNat < 64 := by omega
      obtain ⟨finalInv, finalStream, finalCount⟩ := DROPBITS_inv currentInv s.extra available small
      let regs := { current with hold := current.hold >>> s.extra.toUInt64, bits := current.bits - s.extra }
      let state := { s with length := s.length + bits, back := Int32.ofNat (before + s.extra.toNat), was := s.length + bits, mode := DIST }
      let after := setI h zs state
      have finalGood := good.decode_after (after := state) rfl (by change HEAD ≤ DIST ∧ DIST ≤ SYNC; decide)
      have finalTables := tables.decode_update good.live.hs (after := state) rfl
      right
      refine ⟨regs, after, state, used, ?_, usedBound, finalGood, finalTables,
        finalInv.decode_update zs state, rfl, rfl, ?_, ?_, rfl, ?_, ?_, rfl, rfl, cursor, by
          change (current.bits - s.extra).toNat ≤ max l.bits.toNat 12
          rw [UInt32.toNat_sub_of_le _ _ available]
          omega⟩
      · rw [prefixRun]
        unfold lenExtraNeed
        rw [runX_bind, run]
        simp only [runX_bind, BITS_run current h s.extra (by omega), runX_lift, hc,
          wrI_eq, good.live.hs, setI_istates_same, DROPBITS_run, small, setI_setI]
        simp only [backEq]
        rfl
      · unfold SymbolRegShape
        dsimp only [regs]
        rw [shape]
      · exact finalStream.trans (congrArg (List.drop s.extra.toNat) sameStream)
      · change 3 ≤ (s.length + bits).toNat
        rw [lengthNat]
        omega
      · change (s.length + bits).toNat ≤ 258
        rw [lengthNat]
        omega

theorem inflate_LENEXT_boundary_cursor {c : Ctx} {l : IL} {h : Heap} {cutoff : Nat} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8} (before : Nat)
    (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (good : LocalGood h cutoff r zs z s) (tables : DataTablesSafe h s)
    (B : BitInv h l bs) (extra : s.extra.toNat ≤ 5)
    (lower : 3 ≤ s.length.toNat) (budget : s.length.toNat + 2 ^ s.extra.toNat ≤ 259)
    (back : s.back = Int32.ofNat before) (backBound : before ≤ 15) :
    (∃ regs used,
      runX (inflate_LENEXT c) l h = .ok ((.error Ex.leave, regs), h) ∧
      used ≤ bs.length ∧ BitInv h regs (bs.drop used) ∧ regs.have_ = 0 ∧
      stream regs (bs.drop used) = stream l bs ∧ SymbolRegShape l regs ∧ regs.next = inputAdvance l.next used) ∨
    (∃ regs after state used,
      runX (inflate_LENEXT c) l h = runX (inflate_DIST c) regs after ∧
      used ≤ bs.length ∧ LocalGood after cutoff r zs z state ∧ DataTablesSafe after state ∧
      BitInv after regs (bs.drop used) ∧ state.mode = DIST ∧ DecodeStateFrame s state ∧
      SymbolRegShape l regs ∧ stream regs (bs.drop used) = (stream l bs).drop s.extra.toNat ∧
      state.was = state.length ∧ 3 ≤ state.length.toNat ∧ state.length.toNat ≤ 258 ∧
      state.back = Int32.ofNat (before + s.extra.toNat) ∧ after = setI h zs state ∧ regs.next = inputAdvance l.next used) := by
  rcases inflate_LENEXT_boundary_bounded before hr hc good tables B extra lower budget back backBound with wait | continued
  · obtain ⟨regs, used, run, usedBound, inv, empty, bits, shape, cursor, _⟩ := wait
    exact Or.inl ⟨regs, used, run, usedBound, inv, empty, bits, shape, cursor⟩
  · obtain ⟨regs, after, state, used, run, usedBound, finalGood, finalTables, inv,
      mode, frame, shape, bits, was, lower, upper, back, heap, cursor, _⟩ := continued
    exact Or.inr ⟨regs, after, state, used, run, usedBound, finalGood, finalTables, inv,
      mode, frame, shape, bits, was, lower, upper, back, heap, cursor⟩

theorem inflate_LEN_slow_to_DIST_frame {c : Ctx} {l : IL} {h : Heap} {cutoff : Nat} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (good : LocalGood h cutoff r zs z s)
    (tables : DataTablesSafe h s) (B : BitInv h l bs)
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    (∃ outcome regs after finalZ state used consumed,
      used ≤ bs.length ∧ consumed ≤ 20 ∧
      runX (inflate_LEN c) l h = .ok ((outcome, regs), after) ∧
      LocalGood after cutoff r zs finalZ state ∧ DataTableInvariant after state ∧ BitInv after regs (bs.drop used) ∧
      stream regs (bs.drop used) = (stream l bs).drop consumed ∧
      SymbolRegShape l regs ∧ DecodeStateFrame s state ∧
      (outcome = .error Ex.leave ∨ (outcome = .ok () ∧ (state.mode = LIT ∨ state.mode = TYPE ∨ state.mode = BAD))) ∧
      regs.next = inputAdvance l.next used ∧ after = setI (r.put h finalZ) zs state) ∨
    (∃ regs after state used consumed,
      used ≤ bs.length ∧ consumed ≤ 20 ∧
      runX (inflate_LEN c) l h = runX (inflate_DIST c) regs after ∧
      LocalGood after cutoff r zs z state ∧ DataTablesSafe after state ∧ BitInv after regs (bs.drop used) ∧
      stream regs (bs.drop used) = (stream l bs).drop consumed ∧
      SymbolRegShape l regs ∧ DecodeStateFrame s state ∧ state.mode = DIST ∧
      state.was = state.length ∧ 3 ≤ state.length.toNat ∧ state.length.toNat ≤ 258 ∧
      state.back = Int32.ofNat consumed ∧ after = setI h zs state ∧ regs.next = inputAdvance l.next used) := by
  rcases inflate_LEN_slow_boundary_frame hr hc good tables B slow with stopped | continued
  · obtain ⟨outcome, regs, after, finalZ, state, used, consumed, _, usedBound, consumedBound,
      run, finalGood, data, inv, bits, shape, frame, _, kinds, cursor, heapEq⟩ := stopped
    exact Or.inl ⟨outcome, regs, after, finalZ, state, used, consumed, usedBound, by omega,
      run, finalGood, data, inv, bits, shape, frame, kinds, cursor, heapEq⟩
  · obtain ⟨regs, after, state, used, consumed, _, usedBound, consumedBound,
      source, nextGood, nextTables, nextInv, bits, shape, frame, _, _, extra, lower, upper, back, heapEq, cursor⟩ := continued
    rcases inflate_LENEXT_boundary_cursor consumed hr hc nextGood nextTables nextInv extra lower upper back consumedBound with wait | continued
    · obtain ⟨finalRegs, used2, run, usedBound2, finalInv, _, finalStream, finalShape, cursor2⟩ := wait
      have totalBound : used + used2 ≤ bs.length := by simp only [List.length_drop] at usedBound2; omega
      have inv : BitInv after finalRegs (bs.drop (used + used2)) := by
        simpa only [List.drop_drop, Nat.add_comm] using finalInv
      have finalBits : stream finalRegs (bs.drop (used + used2)) = (stream l bs).drop consumed := by
        simpa only [List.drop_drop, Nat.add_comm] using finalStream.trans bits
      exact Or.inl ⟨.error Ex.leave, finalRegs, after, z, state, used + used2, consumed,
        totalBound, by omega, source.trans run, nextGood, fun _ => nextTables, inv, finalBits,
        shape.trans finalShape, frame, Or.inl rfl, by rw [cursor2, cursor, inputAdvance_add],
        by rw [ZStreamRef.put_self good.live.hz]; exact heapEq⟩
    · obtain ⟨finalRegs, finalHeap, finalState, used2, run, usedBound2, finalGood, finalTables,
        finalInv, mode, finalFrame, finalShape, finalStream, was, finalLower, finalUpper, finalBack, finalHeapEq, cursor2⟩ := continued
      have totalBound : used + used2 ≤ bs.length := by simp only [List.length_drop] at usedBound2; omega
      have inv : BitInv finalHeap finalRegs (bs.drop (used + used2)) := by
        simpa only [List.drop_drop, Nat.add_comm] using finalInv
      have finalBits : stream finalRegs (bs.drop (used + used2)) =
          (stream l bs).drop (consumed + state.extra.toNat) := by
        simp only [List.drop_drop] at finalStream
        rw [bits, List.drop_drop] at finalStream
        exact finalStream
      exact Or.inr ⟨finalRegs, finalHeap, finalState, used + used2, consumed + state.extra.toNat,
        totalBound, by omega, source.trans run, finalGood, finalTables, inv, finalBits,
        shape.trans finalShape, frame.trans finalFrame, mode, was, finalLower, finalUpper, finalBack,
          by rw [finalHeapEq, heapEq, setI_setI], by rw [cursor2, cursor, inputAdvance_add]⟩

#print axioms inflate_LEN_slow_to_DIST_frame
#print axioms inflate_LENEXT_boundary_bounded
end Zlib.Inflate.Local
