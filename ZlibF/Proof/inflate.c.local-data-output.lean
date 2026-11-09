import ZlibF.Proof.«inflate.c.local-stored»
import ZlibF.Proof.«inflate.c.local-slow-distance»
import ZlibF.Proof.«inflate.c.match-output»
import ZlibF.Proof.«inflate.c.literal-step»

/-! Actual decoder execution with local allocation uniqueness. -/
namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inffast.Spec ZlibF.Spec.Public
set_option autoImplicit false
set_option maxRecDepth 8192

theorem inflate_MATCH_boundary_ranges {c : Ctx} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (E : Env c h r zs z s) (good : LocalGood h cutoff r zs z s) (tables : DataTablesSafe h s)
    {l : IL} {bs : List UInt8} (B : BitInv h l bs) {dest : BRef} {output : Array UInt8} {outOffset : Nat}
    (put : l.put = .ref dest outOffset) (get : Space.get h dest = some output) (write : Space.ro h dest = false)
    (mode : s.mode = MATCH) (length : 0 < s.length.toNat) (offset : 0 < s.offset.toNat) (sane : s.sane ≠ 0)
    (room : outOffset + l.left.toNat ≤ output.size)
    (count : l.left.toNat ≤ l.out_.toNat) (produced : l.out_.toNat - l.left.toNat ≤ outOffset)
    (privateWindow : ∀ w, s.window = .ref (.blk w) 0 → dest ≠ .blk w)
    (inputSeparate : bs = [] ∨ ∀ i, l.next = .ref dest i → i + bs.length ≤ outOffset ∨ outOffset + l.left.toNat ≤ i) :
    ∃ outcome regs after stream state,
      runX (inflate_MATCH c) l h = .ok ((outcome, regs), after) ∧
      LocalGood after cutoff r zs stream state ∧ DataTableInvariant after state ∧ BitInv after regs bs ∧
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
    have finalGood : LocalGood (badHeap h r zs z s i) cutoff r zs stream state :=
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

theorem inflate_MATCH_output_step_frame {c : Ctx} {l : IL} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8}
    (E : Env c h r zs z s) (good : LocalGood h cutoff r zs z s) (tables : DataTablesSafe h s)
    (B : BitInv h l bs) (output : OutputCursorInvariant h r l)
    (separate : Separate l.next l.have_.toNat l.put l.left.toNat)
    (mode : s.mode = MATCH) (length : 0 < s.length.toNat) (offset : 0 < s.offset.toNat) (sane : s.sane ≠ 0) :
    ∃ outcome regs after stream state made,
      runX (inflate_MATCH c) l h = .ok ((outcome, regs), after) ∧
      LocalGood after cutoff r zs stream state ∧ DataTableInvariant after state ∧ BitInv after regs bs ∧
      OutputCursorInvariant after r regs ∧ Separate regs.next regs.have_.toNat regs.put regs.left.toNat ∧
      ByteViewSizes h after ∧ DecodeStateFrame s state ∧ EmitRegFrame l regs ∧
      regs.left.toNat + made = l.left.toNat ∧ regs.put = inputAdvance l.put made ∧
      Zlib.Inflate.Proofs.stream regs bs = Zlib.Inflate.Proofs.stream l bs ∧
      ((outcome = .error Ex.leave ∧ made = 0) ∨
        (outcome = .ok () ∧ state.mode = BAD ∧ made = 0) ∨
        (outcome = .ok () ∧ 0 < made ∧ (state.mode = LEN ∨ state.mode = MATCH))) ∧
      (∀ ref : BRef, Space.ro after ref = Space.ro h ref) ∧ MatchResidual s state := by
  by_cases empty : l.left = 0
  · exact ⟨.error Ex.leave, l, h, z, s, 0, inflate_MATCH_wait c h l empty, good, fun _ => tables,
      B, output, separate, ByteViewSizes.refl h, by rfl, by rfl, by omega,
      (inputAdvance_zero l.put).symm, rfl, Or.inl ⟨rfl, rfl⟩, fun _ => rfl,
      fun _ => ⟨length, Nat.le_refl _, rfl, rfl, rfl⟩⟩
  · obtain ⟨dest, array, off, put, get, write, room, count, produced, privateWindow⟩ :=
      callerRange_slow_output good l output.range output.nonnull output.count output.produced
    obtain ⟨outcome, regs, after, stream, state, run, finalGood, data, inv, frame, kinds⟩ :=
      inflate_MATCH_boundary_ranges E good tables B put get write mode length offset sane
        room count produced privateWindow (B.output_positions put empty separate)
    rcases kinds with ⟨wait, regsEq, heapEq, stateEq⟩ | ⟨ok, bad, regsEq, i, msg, heapEq⟩ |
        ⟨ok, copy, source, sourceOffset, saved, positive, copyLeft, copyLength, regsEq, heapEq, stateEq, lengthEq, modes, decreases⟩
    · subst outcome regs after state
      exact ⟨.error Ex.leave, l, h, stream, s, 0, run, finalGood, data, inv, output, separate,
        ByteViewSizes.refl h, frame, by rfl, by omega, (inputAdvance_zero l.put).symm, rfl, Or.inl ⟨rfl, rfl⟩,
        fun _ => rfl, fun _ => ⟨length, Nat.le_refl _, rfl, rfl, rfl⟩⟩
    · subst outcome regs
      have sizes : ByteViewSizes h after := by
        rw [heapEq]
        exact (byte_view_sizes_stream_put h r { z with msg := .ref (.str i) 0 }).trans
          (byte_view_sizes_setI _ zs { s with mode := BAD })
      have readonly : ∀ ref : BRef, Space.ro after ref = Space.ro h ref := by
        intro ref
        rw [heapEq]
        unfold badHeap
        rw [byte_view_ro_setI, byte_view_ro_stream_put]
      have finalOutput := output_emit_local output good finalGood (by rw [frame]) sizes readonly
        (inputAdvance_zero l.put).symm (made := 0) (by omega) rfl
      refine ⟨.ok (), l, after, stream, state, 0, run, finalGood, data, inv, finalOutput, separate,
        sizes, frame, by rfl, by omega, (inputAdvance_zero l.put).symm, rfl,
        Or.inr (Or.inl ⟨rfl, bad, rfl⟩), readonly, ?_⟩
      intro matching
      have ne : MATCH ≠ BAD := by decide
      exact False.elim (ne (matching.symm.trans bad))
    · subst outcome
      let bytes := ZlibF.Math.InflateMatchCopy.copy (decide (source = dest)) saved copy.toNat sourceOffset off array
      have size : bytes.size = array.size := ZlibF.Math.InflateMatchCopy.copy_size _ _ _ _ _ _
      have sizes : ByteViewSizes h after := by
        rw [heapEq]
        exact (byte_view_sizes_put get write bytes size).trans (byte_view_sizes_setI _ zs state)
      have readonly : ∀ ref : BRef, Space.ro after ref = Space.ro h ref := by
        intro ref
        rw [heapEq, byte_view_ro_setI, byte_view_ro_write]
      have countNat : (l.left - copy).toNat = l.left.toNat - copy.toNat := UInt32.toNat_sub_of_le _ _ copyLeft
      have left : regs.left.toNat + copy.toNat = l.left.toNat := by
        rw [regsEq]
        change (l.left - copy).toNat + copy.toNat = l.left.toNat
        rw [countNat]
        omega
      have nextPut : regs.put = inputAdvance l.put copy.toNat := by
        rw [regsEq]
        change Ptr.ref dest (off + copy.toNat) = inputAdvance l.put copy.toNat
        rw [put]
        rfl
      have finalOutput := output_emit_local output good finalGood (by rw [frame]) sizes readonly nextPut left
        (by rw [regsEq])
      have nextSeparate : Separate regs.next regs.have_.toNat regs.put regs.left.toNat := by
        have advanced := separate_advance_output l.next l.put l.have_.toNat l.left.toNat copy.toNat copyLeft separate
        simpa only [regsEq, put, inputAdvance, countNat] using advanced
      refine ⟨.ok (), regs, after, stream, state, copy.toNat, run, finalGood, data, inv, finalOutput,
        nextSeparate, sizes, frame, ?_, left, nextPut, ?_, Or.inr (Or.inr ⟨rfl, positive, modes⟩), readonly, ?_⟩
      · rw [regsEq]
        rfl
      · rw [regsEq]
        rfl
      · intro matching
        rw [stateEq] at matching ⊢
        dsimp only [matchEmitState] at matching ⊢
        by_cases zero : (s.length - copy == 0) = true
        · simp only [zero, ↓reduceIte] at matching
          have ne : LEN ≠ MATCH := by decide
          exact False.elim (ne matching)
        · simp only [zero, Bool.false_eq_true, ↓reduceIte]
          have nonzero : (s.length - copy).toNat ≠ 0 := by
            intro zeroNat
            apply zero
            exact beq_iff_eq.mpr (UInt32.toNat_inj.mp zeroNat)
          have lengthNat := UInt32.toNat_sub_of_le s.length copy copyLength
          exact ⟨by omega, by omega, by trivial, by trivial, by trivial⟩

theorem inflate_MATCH_output_step {c : Ctx} {l : IL} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8}
    (E : Env c h r zs z s) (good : LocalGood h cutoff r zs z s) (tables : DataTablesSafe h s)
    (B : BitInv h l bs) (output : OutputCursorInvariant h r l)
    (separate : Separate l.next l.have_.toNat l.put l.left.toNat)
    (mode : s.mode = MATCH) (length : 0 < s.length.toNat) (offset : 0 < s.offset.toNat) (sane : s.sane ≠ 0) :
    ∃ outcome regs after stream state made,
      runX (inflate_MATCH c) l h = .ok ((outcome, regs), after) ∧
      LocalGood after cutoff r zs stream state ∧ DataTableInvariant after state ∧ BitInv after regs bs ∧
      OutputCursorInvariant after r regs ∧ Separate regs.next regs.have_.toNat regs.put regs.left.toNat ∧
      ByteViewSizes h after ∧ DecodeStateFrame s state ∧ EmitRegFrame l regs ∧
      regs.left.toNat + made = l.left.toNat ∧ regs.put = inputAdvance l.put made ∧
      Zlib.Inflate.Proofs.stream regs bs = Zlib.Inflate.Proofs.stream l bs ∧
      ((outcome = .error Ex.leave ∧ made = 0) ∨
        (outcome = .ok () ∧ state.mode = BAD ∧ made = 0) ∨
        (outcome = .ok () ∧ 0 < made ∧ (state.mode = LEN ∨ state.mode = MATCH))) := by
  obtain ⟨outcome, regs, after, stream, state, made, run, finalGood, data, inv,
    output, separate, sizes, stateFrame, regFrame, count, put, bits, kinds, _, _⟩ :=
      inflate_MATCH_output_step_frame E good tables B output separate mode length offset sane
  exact ⟨outcome, regs, after, stream, state, made, run, finalGood, data, inv,
    output, separate, sizes, stateFrame, regFrame, count, put, bits, kinds⟩

theorem inflate_MATCH_dispatch {c : Ctx} {l : IL} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8}
    (E : Env c h r zs z s) (good : LocalGood h cutoff r zs z s) (tables : DataTablesSafe h s)
    (buffers : DispatchBuffers h r l bs)
    (mode : s.mode = MATCH) (length : 0 < s.length.toNat) (offset : 0 < s.offset.toNat) (sane : s.sane ≠ 0) :
    ∃ outcome regs after stream state made,
      runX (inflate_MATCH c) l h = .ok ((outcome, regs), after) ∧
      LocalGood after cutoff r zs stream state ∧ DataTableInvariant after state ∧ DispatchBuffers after r regs bs ∧
      ByteViewSizes h after ∧ DecodeStateFrame s state ∧ EmitRegFrame l regs ∧ MatchResidual s state ∧
      regs.left.toNat + made = l.left.toNat ∧ regs.put = inputAdvance l.put made ∧
      ((outcome = .error Ex.leave ∧ made = 0) ∨
        (outcome = .ok () ∧ state.mode = BAD ∧ made = 0) ∨
        (outcome = .ok () ∧ 0 < made ∧ (state.mode = LEN ∨ state.mode = MATCH))) := by
  obtain ⟨outcome, regs, after, stream, state, made, run, finalGood, data, inv,
    output, separate, sizes, stateFrame, regFrame, count, put, _, kinds, readonly, residual⟩ :=
      inflate_MATCH_output_step_frame E good tables buffers.bits buffers.output buffers.separate mode length offset sane
  have currentBuffers := dispatch_emit_local buffers good finalGood (by rw [stateFrame]) sizes readonly regFrame output inv separate
  exact ⟨outcome, regs, after, stream, state, made, run, finalGood, data, currentBuffers,
    sizes, stateFrame, regFrame, residual, count, put, kinds⟩

theorem inflate_LIT_step {c : Ctx} {l : IL} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8}
    (E : Env c h r zs z s) (good : LocalGood h cutoff r zs z s) (tables : DataTablesSafe h s)
    (B : BitInv h l bs) (output : OutputCursorInvariant h r l)
    (separate : Separate l.next l.have_.toNat l.put l.left.toNat) :
    ∃ outcome regs after state,
      runX (inflate_LIT c) l h = .ok ((outcome, regs), after) ∧
      LocalGood after cutoff r zs z state ∧ DataTablesSafe after state ∧ BitInv after regs bs ∧
      OutputCursorInvariant after r regs ∧ Separate regs.next regs.have_.toNat regs.put regs.left.toNat ∧
      ByteViewSizes h after ∧ DecodeStateFrame s state ∧ EmitRegFrame l regs ∧
      Zlib.Inflate.Proofs.stream regs bs = Zlib.Inflate.Proofs.stream l bs ∧
      ((outcome = .error Ex.leave ∧ regs = l ∧ after = h ∧ state = s) ∨
       (outcome = .ok () ∧ state = { s with mode := LEN } ∧ regs.put = inputAdvance l.put 1 ∧
         regs.left.toNat + 1 = l.left.toNat ∧
         ∃ dest off array, l.put = .ref dest off ∧ Space.get h dest = some array ∧
           after = setI (Space.put h dest (array.set! off s.length.toUInt8)) zs state)) := by
  by_cases empty : l.left = 0
  · exact ⟨.error Ex.leave, l, h, s, inflate_LIT_full c l h empty, good, tables, B, output,
      separate, ByteViewSizes.refl h, by rfl, by rfl, rfl, Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩
  · obtain ⟨dest, array, off, put, get, write, room, _, _, privateWindow⟩ :=
      callerRange_slow_output good l output.range output.nonnull output.count output.produced
    have positive : 0 < l.left.toNat := by
      have nonzero : l.left.toNat ≠ 0 := by intro zero; exact empty (UInt32.toNat_inj.mp zero)
      omega
    let bytes := array.set! off s.length.toUInt8
    let state := { s with mode := LEN }
    let after := setI (Space.put h dest bytes) zs state
    let regs := { l with put := .ref dest (off + 1), left := l.left - 1 }
    have countNat : (l.left - 1).toNat = l.left.toNat - 1 := UInt32.toNat_sub_of_le _ _ (by exact positive)
    have frame : DecodeStateFrame s state := by rfl
    have finalGood : LocalGood after cutoff r zs z state :=
      (good.byte_view_put get write privateWindow bytes).decode_update frame
        (by change HEAD ≤ LEN ∧ LEN ≤ SYNC; decide)
    have finalTables : DataTablesSafe after state :=
      (tables.byte_view_put dest bytes).decode_update
        (by rw [byte_view_put_istates]; exact good.live.hs) frame
    have sizes : ByteViewSizes h after :=
      (byte_view_sizes_put get write bytes (by simp [bytes])).trans (byte_view_sizes_setI _ zs state)
    have ro : ∀ ref : BRef, Space.ro after ref = Space.ro h ref := by
      intro ref
      dsimp only [after]
      rw [byte_view_ro_setI]
      cases ref <;> simp only [Space.ro, byte_view_put_ro]
    have nextPut : regs.put = inputAdvance l.put 1 := by
      change Ptr.ref dest (off + 1) = inputAdvance l.put 1
      rw [put]
      rfl
    have leftCount : regs.left.toNat + 1 = l.left.toNat := by
      change (l.left - 1).toNat + 1 = l.left.toNat
      rw [countNat]
      omega
    have finalOutput : OutputCursorInvariant after r regs :=
      output_emit_local output good finalGood rfl sizes ro nextPut leftCount rfl
    have positions : bs = [] ∨ ∀ i, l.next = .ref dest i → i + bs.length ≤ off ∨ off + 1 ≤ i := by
      rcases B.output_positions put empty separate with noInput | positions
      · exact Or.inl noInput
      · right
        intro i ptr
        rcases positions i ptr with before | later
        · exact Or.inl before
        · exact Or.inr (by omega)
    have inv := (B.store_byte get write s.length.toUInt8 positions).decode_update zs state
    have finalInv : BitInv after regs bs := ⟨inv.have_eq, inv.next, inv.hold_lt⟩
    have nextSeparate : Separate regs.next regs.have_.toNat regs.put regs.left.toNat := by
      have advanced := separate_advance_output l.next l.put l.have_.toNat l.left.toNat 1 positive separate
      simpa only [regs, put, inputAdvance, countNat] using advanced
    refine ⟨.ok (), regs, after, state, inflate_LIT_view_run E empty put get write (by omega),
      finalGood, finalTables, finalInv, finalOutput, nextSeparate, sizes, frame, by rfl, rfl,
      Or.inr ⟨rfl, rfl, nextPut, leftCount, dest, off, array, put, get, rfl⟩⟩

theorem inflate_LIT_dispatch {c : Ctx} {l : IL} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8}
    (E : Env c h r zs z s) (good : LocalGood h cutoff r zs z s) (tables : DataTablesSafe h s)
    (buffers : DispatchBuffers h r l bs) :
    ∃ outcome regs after state,
      runX (inflate_LIT c) l h = .ok ((outcome, regs), after) ∧
      LocalGood after cutoff r zs z state ∧ DataTablesSafe after state ∧ DispatchBuffers after r regs bs ∧
      ByteViewSizes h after ∧ DecodeStateFrame s state ∧ EmitRegFrame l regs ∧
      ((outcome = .error Ex.leave ∧ regs = l ∧ after = h ∧ state = s) ∨
       (outcome = .ok () ∧ state = { s with mode := LEN } ∧ regs.put = inputAdvance l.put 1 ∧
         regs.left.toNat + 1 = l.left.toNat)) := by
  obtain ⟨outcome, regs, after, state, run, finalGood, finalTables, inv, output, separate,
    sizes, stateFrame, regFrame, _, kinds⟩ :=
      inflate_LIT_step E good tables buffers.bits buffers.output buffers.separate
  have readonly : ∀ ref : BRef, Space.ro after ref = Space.ro h ref := by
    rcases kinds with ⟨_, _, heapEq, _⟩ | ⟨_, _, _, _, dest, off, array, _, _, heapEq⟩
    · intro ref
      rw [heapEq]
    · intro ref
      rw [heapEq, byte_view_ro_setI, byte_view_ro_write]
  have currentBuffers := dispatch_emit_local buffers good finalGood (by rw [stateFrame]) sizes readonly regFrame output inv separate
  refine ⟨outcome, regs, after, state, run, finalGood, finalTables, currentBuffers, sizes, stateFrame, regFrame, ?_⟩
  rcases kinds with wait | ⟨ok, stateEq, put, left, _⟩
  · exact Or.inl wait
  · exact Or.inr ⟨ok, stateEq, put, left⟩

#print axioms inflate_MATCH_boundary_ranges
#print axioms inflate_MATCH_output_step_frame
#print axioms inflate_MATCH_output_step
#print axioms inflate_MATCH_dispatch
#print axioms inflate_LIT_step
#print axioms inflate_LIT_dispatch
end Zlib.Inflate.Local
