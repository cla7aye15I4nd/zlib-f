import ZlibF.Proof.«inflate.c.lookup-distance»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inffast.Spec
set_option autoImplicit false

/-- Actual DIST classification after consuming the selected leaf. -/
def distLeafTail (c : Ctx) (here : Code) : X Unit := do
  if (here.op &&& 64) != 0 then
    badMode c "invalid distance code"
    return
  wrS c.st fun s => { s with offset := here.val.toUInt32, extra := here.op.toUInt32 &&& 15 }
  setMode c.st DISTEXT
  inflate_DISTEXT c

/-- Consume the actual distance leaf. Its total root/leaf width bounds the
checked signed addition. No pending match length or other scalar is changed. -/
theorem distFinish_consume_cursor {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8} (before dropped : Nat)
    (hc : c.st = some (.tab zs)) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (leaf : DistLeaf dropped l.here) (back : s.back = Int32.ofNat (before + dropped))
    (backBound : before ≤ 20) (enough : l.here.bits.toNat ≤ l.bits.toNat) (B : BitInv h l bs) :
    ∃ regs after state,
      runX (distFinish c) l h = runX (distLeafTail c l.here) regs after ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧ BitInv after regs bs ∧
      DecodeStateFrame s state ∧ SymbolRegShape l regs ∧
      after = setI h zs state ∧ state = { s with back := Int32.ofNat (before + dropped + l.here.bits.toNat) } ∧
      stream regs bs = (stream l bs).drop l.here.bits.toNat ∧
      regs.bits.toNat = l.bits.toNat - l.here.bits.toNat ∧ regs.here = l.here ∧ regs.next = l.next := by
  have small : l.here.bits.toUInt32.toNat < 64 := by rw [UInt8.toNat_toUInt32]; have := leaf.1; omega
  obtain ⟨nextInv, bits, count⟩ := DROPBITS_inv B l.here.bits.toUInt32 (by simpa using enough) small
  let regs := { l with hold := l.hold >>> l.here.bits.toUInt32.toUInt64, bits := l.bits - l.here.bits.toUInt32 }
  let state := { s with back := Int32.ofNat (before + dropped + l.here.bits.toNat) }
  let after := setI h zs state
  have oldBack : s.back.toInt = (before + dropped : Nat) := by
    rw [back]
    exact int32_ofInt_toInt (before + dropped) (by omega) (by have := leaf.1; omega)
  have checked : chkI32 (s.back.toInt + l.here.bits.toNat) h =
      .ok (Int32.ofNat (before + dropped + l.here.bits.toNat), h) := by
    rw [oldBack]
    unfold chkI32
    have bound := leaf.1
    split
    · rfl
    · omega
  have load : ldInflateState c.st h = .ok (s, h) := by rw [hc, ldI_eq, good.live.hs]
  have write : wrS c.st (fun s => { s with back := Int32.ofNat (before + dropped + l.here.bits.toNat) }) h =
      .ok ((), after) := by rw [hc, wrI_eq, good.live.hs]
  refine ⟨regs, after, state, ?_, good.decode_update rfl good.live.mode,
    tables.decode_update good.live.hs rfl, nextInv.decode_update zs state, rfl, by rfl,
    rfl, rfl, ?_, ?_, rfl, rfl⟩
  · unfold distFinish distLeafTail
    simp only [runX_bind, runX_get, DROPBITS_run l h _ small,
      runX_lift_ok load, runX_lift_ok checked, runX_lift_ok write]
    rfl
  · simpa only [UInt8.toNat_toUInt32] using bits
  · simpa only [UInt8.toNat_toUInt32] using count

/-- Projection retaining the original distance leaf execution. -/
theorem distFinish_consume {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8} (before dropped : Nat)
    (hc : c.st = some (.tab zs)) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (leaf : DistLeaf dropped l.here) (back : s.back = Int32.ofNat (before + dropped))
    (backBound : before ≤ 20) (enough : l.here.bits.toNat ≤ l.bits.toNat) (B : BitInv h l bs) :
    ∃ regs after state,
      runX (distFinish c) l h = runX (distLeafTail c l.here) regs after ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧ BitInv after regs bs ∧
      DecodeStateFrame s state ∧ SymbolRegShape l regs ∧
      after = setI h zs state ∧ state = { s with back := Int32.ofNat (before + dropped + l.here.bits.toNat) } ∧
      stream regs bs = (stream l bs).drop l.here.bits.toNat ∧
      regs.bits.toNat = l.bits.toNat - l.here.bits.toNat ∧ regs.here = l.here := by
  obtain ⟨regs, after, state, run, finalGood, finalTables, inv, frame, shape,
    heap, stateEq, bits, count, here, _⟩ := distFinish_consume_cursor before dropped hc good tables leaf back backBound enough B
  exact ⟨regs, after, state, run, finalGood, finalTables, inv, frame, shape, heap, stateEq, bits, count, here⟩

/-- DIST rejects an invalid leaf or installs the actual distance base and
extra-bit count before its real DISTEXT continuation. The pending match
length and was fields are preserved by the exact record update. -/
theorem distLeafTail_boundary_frame {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {here : Code} {bs : List UInt8} {dropped : Nat}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs))
    (good : Good h r zs z s) (tables : DataTablesSafe h s) (B : BitInv h l bs)
    (leaf : DistLeaf dropped here) :
    (∃ after finalZ state,
      runX (distLeafTail c here) l h = .ok ((.ok (), l), after) ∧
      Good after r zs finalZ state ∧ DataTableInvariant after state ∧ BitInv after l bs ∧
      state.mode = BAD ∧ state = { s with mode := BAD } ∧ after = setI (r.put h finalZ) zs state) ∨
    (∃ after state,
      runX (distLeafTail c here) l h = runX (inflate_DISTEXT c) l after ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧ BitInv after l bs ∧
      state.mode = DISTEXT ∧
      after = setI h zs state ∧
      state = { s with offset := here.val.toUInt32, extra := here.op.toUInt32 &&& 15, mode := DISTEXT } ∧
      state.extra.toNat ≤ 13 ∧ 1 ≤ state.offset.toNat ∧ state.offset.toNat + 2 ^ state.extra.toNat ≤ 73727) := by
  have env : Env c h r zs z s := ⟨hr, hc, good.live.hz, good.live.hs⟩
  by_cases invalid : here.op &&& 64 ≠ 0
  · left
    have member : "invalid distance code" ∈ strTable := by decide +kernel
    obtain ⟨i, _, badRun⟩ := badMode_run env member
    let finalZ := { z with msg := .ref (.str i) 0 }
    let state := { s with mode := BAD }
    have inv : StInv h zs state := good.inv.of_fields rfl rfl rfl rfl rfl rfl rfl rfl rfl good.inv.bits rfl rfl rfl
    have finalGood : Good (badHeap h r zs z s i) r zs finalZ state :=
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
    refine ⟨badHeap h r zs z s i, finalZ, state, ?_, finalGood, data, bits, rfl, rfl, rfl⟩
    unfold distLeafTail
    simp [invalid, runX_bind, runX_lift_ok badRun, runX_pure]
  · right
    have base : here.op &&& 16 ≠ 0 ∧ (here.op &&& 15).toNat ≤ 13 ∧ 1 ≤ here.val.toNat := by
      rcases leaf.2 with base | bad
      · exact base
      · exact False.elim (invalid bad.2)
    let state := { s with offset := here.val.toUInt32, extra := here.op.toUInt32 &&& 15, mode := DISTEXT }
    have finalGood := good.decode_update (after := state) rfl
      (by change HEAD ≤ DISTEXT ∧ DISTEXT ≤ SYNC; decide)
    have finalTables := tables.decode_update good.live.hs (after := state) rfl
    have extra : state.extra.toNat = (here.op &&& 15).toNat := by
      change (here.op.toUInt32 &&& 15).toNat = _
      rw [UInt32.toNat_and, UInt8.toNat_toUInt32, UInt8.toNat_and]
      rfl
    refine ⟨setI h zs state, state, ?_, finalGood, finalTables, B.decode_update zs state,
      rfl, rfl, rfl, by rw [extra]; exact base.2.1, ?_, ?_⟩
    · unfold distLeafTail
      simp only [bne_iff_ne, invalid, ite_false, runX_bind, runX_wrS env]
      have stateGet : (setI h zs { s with offset := here.val.toUInt32, extra := here.op.toUInt32 &&& 15 }).istates zs =
          some { s with offset := here.val.toUInt32, extra := here.op.toUInt32 &&& 15 } := by simp
      rw [runX_lift_ok (by rw [hc]; exact setMode_tab stateGet DISTEXT)]
      simp only [setI_setI]
      rfl
    · change 1 ≤ here.val.toUInt32.toNat
      rw [UInt16.toNat_toUInt32]
      exact base.2.2
    · change here.val.toUInt32.toNat + 2 ^ state.extra.toNat ≤ 73727
      rw [UInt16.toNat_toUInt32, extra]
      have valBound := UInt16.toNat_lt here.val
      have powBound := Nat.pow_le_pow_right (by decide : 1 ≤ 2) base.2.1
      omega

/-- Projection retaining the previous boundary. -/
theorem distLeafTail_boundary {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {here : Code} {bs : List UInt8} {dropped : Nat}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs))
    (good : Good h r zs z s) (tables : DataTablesSafe h s) (B : BitInv h l bs)
    (leaf : DistLeaf dropped here) :
    (∃ after finalZ state,
      runX (distLeafTail c here) l h = .ok ((.ok (), l), after) ∧
      Good after r zs finalZ state ∧ DataTableInvariant after state ∧ BitInv after l bs ∧
      state.mode = BAD ∧ state = { s with mode := BAD }) ∨
    (∃ after state,
      runX (distLeafTail c here) l h = runX (inflate_DISTEXT c) l after ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧ BitInv after l bs ∧
      state.mode = DISTEXT ∧
      after = setI h zs state ∧
      state = { s with offset := here.val.toUInt32, extra := here.op.toUInt32 &&& 15, mode := DISTEXT } ∧
      state.extra.toNat ≤ 13 ∧ 1 ≤ state.offset.toNat ∧ state.offset.toNat + 2 ^ state.extra.toNat ≤ 73727) := by
  rcases distLeafTail_boundary_frame hr hc good tables B leaf with stopped | continued
  · obtain ⟨after, finalZ, state, run, finalGood, data, inv, mode, frame, _⟩ := stopped
    exact Or.inl ⟨after, finalZ, state, run, finalGood, data, inv, mode, frame⟩
  · exact Or.inr continued

end Zlib.Inflate.Proofs
