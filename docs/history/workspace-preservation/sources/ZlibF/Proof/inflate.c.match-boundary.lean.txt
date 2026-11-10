import ZlibF.Proof.«inflate.c.match-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

/-- The actual MATCH boundary either waits for output, refuses an unavailable
distance, or emits a positive bounded segment. All outcomes retain the
representation invariant, active tables, unread input and exact write frame.
The scalar mode obligations are internal clauses to be supplied by histories. -/
theorem inflate_MATCH_boundary_ranges {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    {l : IL} {bs : List UInt8} (B : BitInv h l bs) {dest : BRef} {output : Array UInt8} {outOffset : Nat}
    (put : l.put = .ref dest outOffset) (get : Space.get h dest = some output) (write : Space.ro h dest = false)
    (mode : s.mode = MATCH) (length : 0 < s.length.toNat) (offset : 0 < s.offset.toNat) (sane : s.sane ≠ 0)
    (room : outOffset + l.left.toNat ≤ output.size)
    (count : l.left.toNat ≤ l.out_.toNat) (produced : l.out_.toNat - l.left.toNat ≤ outOffset)
    (privateWindow : ∀ w, s.window = .ref (.blk w) 0 → dest ≠ .blk w)
    (inputSeparate : bs = [] ∨ ∀ i, l.next = .ref dest i → i + bs.length ≤ outOffset ∨ outOffset + l.left.toNat ≤ i) :
    ∃ outcome regs after stream state,
      runX (inflate_MATCH c) l h = .ok ((outcome, regs), after) ∧
      Good after r zs stream state ∧ DataTableInvariant after state ∧ BitInv after regs bs ∧
      DecodeStateFrame s state ∧
      ((outcome = .error Ex.leave ∧ regs = l ∧ after = h ∧ state = s) ∨
       (outcome = .ok () ∧ state.mode = BAD ∧ regs = l ∧
         ∃ i, strTable[i]? = some "invalid distance too far back" ∧ after = badHeap h r zs z s i) ∨
       (outcome = .ok () ∧ ∃ copy source sourceOffset saved,
         0 < copy.toNat ∧ copy.toNat ≤ l.left.toNat ∧ copy.toNat ≤ s.length.toNat ∧
         regs = { l with left := l.left - copy, copy := 0, put := .ref dest (outOffset + copy.toNat), from_ := .ref source (sourceOffset + copy.toNat) } ∧
         after = setI (Space.put h dest (ZlibF.Math.InflateMatchCopy.copy (decide (source = dest)) saved
           copy.toNat sourceOffset outOffset output)) zs state ∧
         state = matchEmitState s copy ∧ state.length.toNat = s.length.toNat - copy.toNat ∧
         (state.mode = LEN ∨ state.mode = MATCH) ∧ regs.left.toNat < l.left.toNat)) := by
  rw [inflate_MATCH_select_cut]
  by_cases noRoom : l.left = 0
  · refine ⟨.error Ex.leave, l, h, z, s, matchSelect_wait c h l noRoom,
      good, fun _ => tables, B, ?_, Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩
    unfold DecodeStateFrame
    rfl
  by_cases badHistory : s.offset > l.out_ - l.left ∧ s.offset - (l.out_ - l.left) > s.whave
  · obtain ⟨i, msg, run⟩ := matchSelect_bad_run E l noRoom badHistory.1 badHistory.2 sane
    let stream := { z with msg := .ref (.str i) 0 }
    let state := { s with mode := BAD }
    have finalGood : Good (badHeap h r zs z s i) r zs stream state :=
      good.setZI rfl good.live.zalloc good.live.zfree rfl (by change HEAD ≤ BAD ∧ BAD ≤ SYNC; decide)
        (good.inv.of_fields rfl rfl rfl rfl rfl rfl rfl rfl rfl good.inv.bits rfl rfl rfl)
    have bits : BitInv (badHeap h r zs z s i) l bs := by
      refine ⟨B.have_eq, ?_, B.hold_lt⟩
      rcases B.next with empty | ⟨ref, array, off, ptr, arrayGet, bound, contents⟩
      · exact Or.inl empty
      · refine Or.inr ⟨ref, array, off, ptr, ?_, bound, contents⟩
        cases ref <;> cases r <;> simp only [badHeap, setI, Space.get, ZStreamRef.put] <;>
          first | exact arrayGet | split <;> exact arrayGet
    have data : DataTableInvariant (badHeap h r zs z s i) state := by
      intro active
      change DataTableMode BAD at active
      rcases active with eq | eq | eq | eq | eq | eq | eq <;> cases eq
    exact ⟨.ok (), l, badHeap h r zs z s i, stream, state, run, finalGood, data, bits,
      by rfl, Or.inr (Or.inl ⟨rfl, rfl, rfl, i, msg, rfl⟩)⟩
  · have leftPositive : 0 < l.left.toNat := by
      have nonzero : l.left.toNat ≠ 0 := by intro zero; apply noRoom; exact UInt32.toNat_inj.mp zero
      omega
    obtain ⟨copy, source, sourceOffset, saved, positive, copyLeft, copyLength, outFit, sourceGet, sourceFit, select⟩ :=
      matchSelect_segment E good.inv.win put get leftPositive length offset room count produced privateWindow
        (by intro inWindow beyond; exact badHistory ⟨inWindow, beyond⟩)
    let array := ZlibF.Math.InflateMatchCopy.copy (decide (source = dest)) saved copy.toNat sourceOffset outOffset output
    let state := matchEmitState s copy
    let regs := { l with left := l.left - copy, copy := 0, put := .ref dest (outOffset + copy.toNat), from_ := .ref source (sourceOffset + copy.toNat) }
    let after := setI (Space.put h dest array) zs state
    have frame : DecodeStateFrame s state := by dsimp only [state, matchEmitState]; split <;> rfl
    have modeRange : HEAD ≤ state.mode ∧ state.mode ≤ SYNC := by
      dsimp only [state, matchEmitState]
      split
      · change HEAD ≤ LEN ∧ LEN ≤ SYNC
        decide
      · exact good.live.mode
    have finalGood := (good.byte_view_put get write privateWindow array).decode_update frame modeRange
    have finalTables := (tables.byte_view_put dest array).decode_update
      (by rw [byte_view_put_istates]; exact good.live.hs) frame
    have bits := (B.match_copy_ranges get write (decide (source = dest)) saved copy.toNat sourceOffset outOffset
      (by
        rcases inputSeparate with empty | separate
        · exact Or.inl empty
        · right
          intro i ptr
          rcases separate i ptr with before | later
          · exact Or.inl before
          · exact Or.inr (by omega))).decode_update zs state
    have finalBits : BitInv after regs bs := ⟨bits.have_eq, bits.next, bits.hold_lt⟩
    have run : runX (matchSelect c) l h = .ok ((.ok (), regs), after) :=
      select.trans (matchEmit_run E put get write sourceGet outFit sourceFit positive)
    refine ⟨.ok (), regs, after, z, state, run, finalGood, fun _ => finalTables, finalBits, frame,
      Or.inr (Or.inr ⟨rfl, copy, source, sourceOffset, saved, positive, copyLeft, copyLength, rfl, rfl, rfl, ?_, ?_, ?_⟩)⟩
    · dsimp only [state, matchEmitState]
      split <;> exact UInt32.toNat_sub_of_le _ _ (by exact copyLength)
    · dsimp only [state, matchEmitState]
      split
      · exact Or.inl rfl
      · exact Or.inr mode
    · change (l.left - copy).toNat < l.left.toNat
      rw [UInt32.toNat_sub_of_le _ _ (by exact copyLeft)]
      omega

/-- Projection retaining the earlier positional separation premise. -/
theorem inflate_MATCH_boundary {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    {l : IL} {bs : List UInt8} (B : BitInv h l bs) {dest : BRef} {output : Array UInt8} {outOffset : Nat}
    (put : l.put = .ref dest outOffset) (get : Space.get h dest = some output) (write : Space.ro h dest = false)
    (mode : s.mode = MATCH) (length : 0 < s.length.toNat) (offset : 0 < s.offset.toNat) (sane : s.sane ≠ 0)
    (room : outOffset + l.left.toNat ≤ output.size)
    (count : l.left.toNat ≤ l.out_.toNat) (produced : l.out_.toNat - l.left.toNat ≤ outOffset)
    (privateWindow : ∀ w, s.window = .ref (.blk w) 0 → dest ≠ .blk w)
    (inputSeparate : ∀ i, l.next = .ref dest i → i + bs.length ≤ outOffset ∨ outOffset + l.left.toNat ≤ i) :
    ∃ outcome regs after stream state,
      runX (inflate_MATCH c) l h = .ok ((outcome, regs), after) ∧
      Good after r zs stream state ∧ DataTableInvariant after state ∧ BitInv after regs bs ∧
      DecodeStateFrame s state ∧
      ((outcome = .error Ex.leave ∧ regs = l ∧ after = h ∧ state = s) ∨
       (outcome = .ok () ∧ state.mode = BAD ∧ regs = l ∧
         ∃ i, strTable[i]? = some "invalid distance too far back" ∧ after = badHeap h r zs z s i) ∨
       (outcome = .ok () ∧ ∃ copy source sourceOffset saved,
         0 < copy.toNat ∧ copy.toNat ≤ l.left.toNat ∧ copy.toNat ≤ s.length.toNat ∧
         regs = { l with left := l.left - copy, copy := 0, put := .ref dest (outOffset + copy.toNat), from_ := .ref source (sourceOffset + copy.toNat) } ∧
         after = setI (Space.put h dest (ZlibF.Math.InflateMatchCopy.copy (decide (source = dest)) saved
           copy.toNat sourceOffset outOffset output)) zs state ∧
         state = matchEmitState s copy ∧ state.length.toNat = s.length.toNat - copy.toNat ∧
         (state.mode = LEN ∨ state.mode = MATCH) ∧ regs.left.toNat < l.left.toNat)) := by
  exact inflate_MATCH_boundary_ranges E good tables B put get write mode length offset sane
    room count produced privateWindow (Or.inr inputSeparate)

end Zlib.Inflate.Proofs
