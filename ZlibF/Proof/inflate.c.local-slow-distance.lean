import ZlibF.Proof.«inflate.c.local-slow-length»
import ZlibF.Proof.«inflate.c.slow-distance»

/-! Actual slow distance-symbol decoding on local decoder storage. -/
namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inffast.Spec
set_option autoImplicit false
set_option maxRecDepth 8192

theorem inflate_DIST_lookup_boundary_bounded {c : Ctx} {l : IL} {h : Heap} {cutoff : Nat}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8} (before : Nat)
    (hc : c.st = some (.tab zs)) (good : LocalGood h cutoff r zs z s)
    (tables : DataTablesSafe h s) (B : BitInv h l bs)
    (back : s.back = Int32.ofNat before) (backBound : before ≤ 20) :
    (∃ regs used,
      used ≤ 4 ∧ used ≤ bs.length ∧
      runX (inflate_DIST c) l h = .ok ((.error Ex.leave, regs), h) ∧
      BitInv h regs (bs.drop used) ∧ regs.have_ = 0 ∧
      stream regs (bs.drop used) = stream l bs ∧ SymbolRegShape l regs ∧ regs.next = inputAdvance l.next used ∧ regs.bits.toNat ≤ max l.bits.toNat 22) ∨
    (∃ regs after state used dropped,
      used ≤ 4 ∧ used ≤ bs.length ∧ dropped ≤ 15 ∧
      runX (inflate_DIST c) l h = runX (distFinish c) regs after ∧
      LocalGood after cutoff r zs z state ∧ DataTablesSafe after state ∧
      BitInv after regs (bs.drop used) ∧ DistLeaf dropped regs.here ∧
      regs.here.bits.toNat ≤ regs.bits.toNat ∧ state.back = Int32.ofNat (before + dropped) ∧
      stream regs (bs.drop used) = (stream l bs).drop dropped ∧
      SymbolRegShape l regs ∧ DecodeStateFrame s state ∧
      regs.bits.toNat = l.bits.toNat + 8 * used - dropped ∧
      after = setI h zs state ∧ state = { s with back := Int32.ofNat (before + dropped) } ∧ regs.next = inputAdvance l.next used ∧ regs.bits.toNat ≤ max l.bits.toNat 22) := by
  obtain ⟨ref, offset, array, pointer, tableGet, tableSafe⟩ := tables.distanceTable
  obtain ⟨result, regs, used, after, run, usedFour, usedBound, inv, shape, bitBound, kinds, done, leave, cursor⟩ :=
    distLookup_run_cursor hc good.live.hs pointer tableGet tableSafe before back backBound B
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
    refine ⟨regs, used, usedFour, usedBound, ?_, inv, empty, bits, shape, cursor, bitBound⟩
    rw [inflate_DIST_lookup_cut, runX_bind, run]
  | ok unit =>
    cases unit
    obtain ⟨dropped, dropBound, heapEq, leaf, enough, bits, count⟩ := done rfl
    subst after
    let state := { s with back := Int32.ofNat (before + dropped) }
    have finalGood : LocalGood (setI h zs state) cutoff r zs z state := good.decode_after rfl good.live.mode
    have finalTables : DataTablesSafe (setI h zs state) state := tables.decode_update good.live.hs rfl
    right
    refine ⟨regs, setI h zs state, state, used, dropped, usedFour, usedBound, dropBound,
      ?_, finalGood, finalTables, inv, leaf, enough, rfl, bits, shape, rfl, count, rfl, rfl, cursor, bitBound⟩
    rw [inflate_DIST_lookup_cut, runX_bind, run]

theorem inflate_DIST_lookup_boundary_cursor {c : Ctx} {l : IL} {h : Heap} {cutoff : Nat}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8} (before : Nat)
    (hc : c.st = some (.tab zs)) (good : LocalGood h cutoff r zs z s)
    (tables : DataTablesSafe h s) (B : BitInv h l bs)
    (back : s.back = Int32.ofNat before) (backBound : before ≤ 20) :
    (∃ regs used,
      used ≤ 4 ∧ used ≤ bs.length ∧
      runX (inflate_DIST c) l h = .ok ((.error Ex.leave, regs), h) ∧
      BitInv h regs (bs.drop used) ∧ regs.have_ = 0 ∧
      stream regs (bs.drop used) = stream l bs ∧ SymbolRegShape l regs ∧ regs.next = inputAdvance l.next used) ∨
    (∃ regs after state used dropped,
      used ≤ 4 ∧ used ≤ bs.length ∧ dropped ≤ 15 ∧
      runX (inflate_DIST c) l h = runX (distFinish c) regs after ∧
      LocalGood after cutoff r zs z state ∧ DataTablesSafe after state ∧
      BitInv after regs (bs.drop used) ∧ DistLeaf dropped regs.here ∧
      regs.here.bits.toNat ≤ regs.bits.toNat ∧ state.back = Int32.ofNat (before + dropped) ∧
      stream regs (bs.drop used) = (stream l bs).drop dropped ∧
      SymbolRegShape l regs ∧ DecodeStateFrame s state ∧
      regs.bits.toNat = l.bits.toNat + 8 * used - dropped ∧
      after = setI h zs state ∧ state = { s with back := Int32.ofNat (before + dropped) } ∧ regs.next = inputAdvance l.next used) := by
  rcases inflate_DIST_lookup_boundary_bounded before hc good tables B back backBound with wait | continued
  · obtain ⟨regs, used, four, usedBound, run, inv, empty, bits, shape, cursor, _⟩ := wait
    exact Or.inl ⟨regs, used, four, usedBound, run, inv, empty, bits, shape, cursor⟩
  · obtain ⟨regs, after, state, used, dropped, four, usedBound, dropBound, run,
      finalGood, finalTables, inv, leaf, enough, back, bits, shape, frame, count, heap, stateEq, cursor, _⟩ := continued
    exact Or.inr ⟨regs, after, state, used, dropped, four, usedBound, dropBound, run,
      finalGood, finalTables, inv, leaf, enough, back, bits, shape, frame, count, heap, stateEq, cursor⟩

theorem distFinish_consume_cursor {c : Ctx} {l : IL} {h : Heap} {cutoff : Nat} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8} (before dropped : Nat)
    (hc : c.st = some (.tab zs)) (good : LocalGood h cutoff r zs z s) (tables : DataTablesSafe h s)
    (leaf : DistLeaf dropped l.here) (back : s.back = Int32.ofNat (before + dropped))
    (backBound : before ≤ 20) (enough : l.here.bits.toNat ≤ l.bits.toNat) (B : BitInv h l bs) :
    ∃ regs after state,
      runX (distFinish c) l h = runX (distLeafTail c l.here) regs after ∧
      LocalGood after cutoff r zs z state ∧ DataTablesSafe after state ∧ BitInv after regs bs ∧
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
  refine ⟨regs, after, state, ?_, good.decode_after rfl good.live.mode,
    tables.decode_update good.live.hs rfl, nextInv.decode_update zs state, rfl, by rfl,
    rfl, rfl, ?_, ?_, rfl, rfl⟩
  · unfold distFinish distLeafTail
    simp only [runX_bind, runX_get, DROPBITS_run l h _ small,
      runX_lift_ok load, runX_lift_ok checked, runX_lift_ok write]
    rfl
  · simpa only [UInt8.toNat_toUInt32] using bits
  · simpa only [UInt8.toNat_toUInt32] using count

theorem distLeafTail_boundary_frame {c : Ctx} {l : IL} {h : Heap} {cutoff : Nat} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {here : Code} {bs : List UInt8} {dropped : Nat}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs))
    (good : LocalGood h cutoff r zs z s) (tables : DataTablesSafe h s) (B : BitInv h l bs)
    (leaf : DistLeaf dropped here) :
    (∃ after finalZ state,
      runX (distLeafTail c here) l h = .ok ((.ok (), l), after) ∧
      LocalGood after cutoff r zs finalZ state ∧ DataTableInvariant after state ∧ BitInv after l bs ∧
      state.mode = BAD ∧ state = { s with mode := BAD } ∧ after = setI (r.put h finalZ) zs state) ∨
    (∃ after state,
      runX (distLeafTail c here) l h = runX (inflate_DISTEXT c) l after ∧
      LocalGood after cutoff r zs z state ∧ DataTablesSafe after state ∧ BitInv after l bs ∧
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
    have finalGood : LocalGood (badHeap h r zs z s i) cutoff r zs finalZ state :=
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
    have finalGood := good.decode_after (after := state) rfl
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

theorem inflate_DISTEXT_boundary_bounded {c : Ctx} {l : IL} {h : Heap} {cutoff : Nat} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8} (before : Nat)
    (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (good : LocalGood h cutoff r zs z s) (tables : DataTablesSafe h s)
    (B : BitInv h l bs) (extra : s.extra.toNat ≤ 13)
    (lower : 1 ≤ s.offset.toNat) (budget : s.offset.toNat + 2 ^ s.extra.toNat ≤ 73727)
    (back : s.back = Int32.ofNat before) (backBound : before ≤ 35) :
    (∃ regs used,
      runX (inflate_DISTEXT c) l h = .ok ((.error Ex.leave, regs), h) ∧
      used ≤ bs.length ∧ BitInv h regs (bs.drop used) ∧ regs.have_ = 0 ∧
      stream regs (bs.drop used) = stream l bs ∧ SymbolRegShape l regs ∧ regs.next = inputAdvance l.next used ∧ regs.bits.toNat ≤ max l.bits.toNat 20) ∨
    (∃ regs after state used,
      runX (inflate_DISTEXT c) l h = runX (inflate_MATCH c) regs after ∧
      used ≤ bs.length ∧ LocalGood after cutoff r zs z state ∧ DataTablesSafe after state ∧
      BitInv after regs (bs.drop used) ∧ state.mode = MATCH ∧ DecodeStateFrame s state ∧
      SymbolRegShape l regs ∧ stream regs (bs.drop used) = (stream l bs).drop s.extra.toNat ∧
      after = setI h zs state ∧ state = { s with offset := state.offset, back := Int32.ofNat (before + s.extra.toNat), mode := MATCH } ∧
      1 ≤ state.offset.toNat ∧ state.offset.toNat ≤ 73726 ∧
      state.back = Int32.ofNat (before + s.extra.toNat) ∧ regs.next = inputAdvance l.next used ∧ regs.bits.toNat ≤ max l.bits.toNat 20) := by
  have env : Env c h r zs z s := ⟨hr, hc, good.live.hz, good.live.hs⟩
  have load : ldInflateState c.st h = .ok (s, h) := by rw [hc, ldI_eq, good.live.hs]
  by_cases zero : s.extra = 0
  · right
    let state := { s with mode := MATCH }
    have finalGood := good.decode_after (after := state) rfl (by change HEAD ≤ MATCH ∧ MATCH ≤ SYNC; decide)
    have finalTables := tables.decode_update good.live.hs (after := state) rfl
    refine ⟨l, setI h zs state, state, 0, ?_, by omega, finalGood, finalTables,
      B.decode_update zs state, rfl, rfl, by rfl, ?_, rfl, ?_, lower, ?_, ?_, (inputAdvance_zero l.next).symm, Nat.le_max_left _ _⟩
    · unfold inflate_DISTEXT
      simp only [runX_bind, runX_lift_ok load, zero, bne_self_eq_false, Bool.false_eq_true, ite_false,
        runX_setMode env]
      simp only [state, zero]
    · simp only [zero, UInt32.toNat_zero, List.drop_zero]
    · simp only [zero, UInt32.toNat_zero, Nat.add_zero]
      simp only [state, back, zero]
    · rw [zero] at budget
      change s.offset.toNat ≤ 73726
      have : (0 : UInt32).toNat = 0 := rfl
      simp only [this, Nat.pow_zero] at budget
      omega
    · simp only [zero, UInt32.toNat_zero, Nat.add_zero]
      exact back
  · obtain ⟨result, current, used, run, usedBound, currentInv, sameStream, count, shape,
        bitBound, _, enough, empty, kinds, cursor⟩ := NEEDBITS_run_cursor B s.extra (by omega)
    have prefixRun := inflate_DISTEXT_need_cut (l := l) hc good.live.hs zero
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
        unfold distExtraNeed
        rw [runX_bind, run]
      · unfold SymbolRegShape
        rw [shape]
    | ok unit =>
      cases unit
      have available := enough rfl
      let bits := current.hold.toUInt32 &&& ((1 : UInt32) <<< s.extra - 1)
      have bitsNat : bits.toNat = current.hold.toNat % 2 ^ s.extra.toNat := BITS_toNat current s.extra (by omega)
      have bitsBound : bits.toNat < 2 ^ s.extra.toNat := by rw [bitsNat]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
      have lengthNat : (s.offset + bits).toNat = s.offset.toNat + bits.toNat := by
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
      let state := { s with offset := s.offset + bits, back := Int32.ofNat (before + s.extra.toNat), mode := MATCH }
      let after := setI h zs state
      have finalGood := good.decode_after (after := state) rfl (by change HEAD ≤ MATCH ∧ MATCH ≤ SYNC; decide)
      have finalTables := tables.decode_update good.live.hs (after := state) rfl
      right
      refine ⟨regs, after, state, used, ?_, usedBound, finalGood, finalTables,
        finalInv.decode_update zs state, rfl, rfl, ?_, ?_, rfl, rfl, ?_, ?_, rfl, cursor, by
          change (current.bits - s.extra).toNat ≤ max l.bits.toNat 20
          rw [UInt32.toNat_sub_of_le _ _ available]
          omega⟩
      · rw [prefixRun]
        unfold distExtraNeed
        rw [runX_bind, run]
        simp only [runX_bind, BITS_run current h s.extra (by omega), runX_lift, hc,
          wrI_eq, good.live.hs, setI_istates_same, DROPBITS_run, small, setI_setI, setMode]
        simp only [backEq]
        rfl
      · unfold SymbolRegShape
        dsimp only [regs]
        rw [shape]
      · exact finalStream.trans (congrArg (List.drop s.extra.toNat) sameStream)
      · change 1 ≤ (s.offset + bits).toNat
        rw [lengthNat]
        omega
      · change (s.offset + bits).toNat ≤ 73726
        rw [lengthNat]
        omega

theorem inflate_DISTEXT_boundary_cursor {c : Ctx} {l : IL} {h : Heap} {cutoff : Nat} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8} (before : Nat)
    (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (good : LocalGood h cutoff r zs z s) (tables : DataTablesSafe h s)
    (B : BitInv h l bs) (extra : s.extra.toNat ≤ 13)
    (lower : 1 ≤ s.offset.toNat) (budget : s.offset.toNat + 2 ^ s.extra.toNat ≤ 73727)
    (back : s.back = Int32.ofNat before) (backBound : before ≤ 35) :
    (∃ regs used,
      runX (inflate_DISTEXT c) l h = .ok ((.error Ex.leave, regs), h) ∧
      used ≤ bs.length ∧ BitInv h regs (bs.drop used) ∧ regs.have_ = 0 ∧
      stream regs (bs.drop used) = stream l bs ∧ SymbolRegShape l regs ∧ regs.next = inputAdvance l.next used) ∨
    (∃ regs after state used,
      runX (inflate_DISTEXT c) l h = runX (inflate_MATCH c) regs after ∧
      used ≤ bs.length ∧ LocalGood after cutoff r zs z state ∧ DataTablesSafe after state ∧
      BitInv after regs (bs.drop used) ∧ state.mode = MATCH ∧ DecodeStateFrame s state ∧
      SymbolRegShape l regs ∧ stream regs (bs.drop used) = (stream l bs).drop s.extra.toNat ∧
      after = setI h zs state ∧ state = { s with offset := state.offset, back := Int32.ofNat (before + s.extra.toNat), mode := MATCH } ∧
      1 ≤ state.offset.toNat ∧ state.offset.toNat ≤ 73726 ∧
      state.back = Int32.ofNat (before + s.extra.toNat) ∧ regs.next = inputAdvance l.next used) := by
  rcases inflate_DISTEXT_boundary_bounded before hr hc good tables B extra lower budget back backBound with wait | continued
  · obtain ⟨regs, used, run, usedBound, inv, empty, bits, shape, cursor, _⟩ := wait
    exact Or.inl ⟨regs, used, run, usedBound, inv, empty, bits, shape, cursor⟩
  · obtain ⟨regs, after, state, used, run, usedBound, finalGood, finalTables, inv,
      mode, frame, shape, bits, heap, stateEq, lower, upper, back, cursor, _⟩ := continued
    exact Or.inr ⟨regs, after, state, used, run, usedBound, finalGood, finalTables, inv,
      mode, frame, shape, bits, heap, stateEq, lower, upper, back, cursor⟩

theorem inflate_DIST_to_MATCH_frame {c : Ctx} {l : IL} {h : Heap} {cutoff : Nat} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8} (before : Nat)
    (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (good : LocalGood h cutoff r zs z s)
    (tables : DataTablesSafe h s) (B : BitInv h l bs)
    (back : s.back = Int32.ofNat before) (backBound : before ≤ 20) :
    (∃ outcome regs after finalZ state used consumed,
      used ≤ bs.length ∧ consumed ≤ 28 ∧
      runX (inflate_DIST c) l h = .ok ((outcome, regs), after) ∧
      LocalGood after cutoff r zs finalZ state ∧ DataTableInvariant after state ∧ BitInv after regs (bs.drop used) ∧
      stream regs (bs.drop used) = (stream l bs).drop consumed ∧ SymbolRegShape l regs ∧
      (outcome = .error Ex.leave ∨ (outcome = .ok () ∧ state.mode = BAD)) ∧ regs.next = inputAdvance l.next used ∧
      DecodeStateFrame s state ∧ after = setI (r.put h finalZ) zs state) ∨
    (∃ regs after state used consumed,
      used ≤ bs.length ∧ consumed ≤ 28 ∧
      runX (inflate_DIST c) l h = runX (inflate_MATCH c) regs after ∧
      LocalGood after cutoff r zs z state ∧ DataTablesSafe after state ∧ BitInv after regs (bs.drop used) ∧
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

theorem inflate_LEN_slow_to_MATCH_frame {c : Ctx} {l : IL} {h : Heap} {cutoff : Nat} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (good : LocalGood h cutoff r zs z s)
    (tables : DataTablesSafe h s) (B : BitInv h l bs)
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    (∃ outcome regs after finalZ state used consumed,
      used ≤ bs.length ∧ consumed ≤ 48 ∧
      runX (inflate_LEN c) l h = .ok ((outcome, regs), after) ∧
      LocalGood after cutoff r zs finalZ state ∧ DataTableInvariant after state ∧ BitInv after regs (bs.drop used) ∧
      stream regs (bs.drop used) = (stream l bs).drop consumed ∧ SymbolRegShape l regs ∧
      (outcome = .error Ex.leave ∨ (outcome = .ok () ∧ (state.mode = LIT ∨ state.mode = TYPE ∨ state.mode = BAD))) ∧
      regs.next = inputAdvance l.next used ∧ DecodeStateFrame s state ∧
      after = setI (r.put h finalZ) zs state) ∨
    (∃ regs after state used consumed,
      used ≤ bs.length ∧ consumed ≤ 48 ∧
      runX (inflate_LEN c) l h = runX (inflate_MATCH c) regs after ∧
      LocalGood after cutoff r zs z state ∧ DataTablesSafe after state ∧ BitInv after regs (bs.drop used) ∧
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

#print axioms inflate_DIST_to_MATCH_frame
#print axioms inflate_LEN_slow_to_MATCH_frame
#print axioms inflate_DISTEXT_boundary_bounded
end Zlib.Inflate.Local
