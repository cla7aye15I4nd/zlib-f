import ZlibF.Proof.«inflate.c.output-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Actual LIT execution for every supported writable caller byte view. -/
theorem inflate_LIT_view_run {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) {dest : BRef} {off : Nat} {array : Array UInt8}
    (left : l.left ≠ 0) (put : l.put = .ref dest off) (get : Space.get h dest = some array)
    (write : Space.ro h dest = false) (fit : off < array.size) :
    runX (inflate_LIT c) l h = .ok ((.ok (), { l with put := .ref dest (off + 1), left := l.left - 1 }),
      setI (Space.put h dest (array.set! off s.length.toUInt8)) zs { s with mode := LEN }) := by
  let bytes := array.set! off s.length.toUInt8
  let after := Space.put h dest bytes
  have store : store8 l.put s.length.toUInt8 h = .ok ((), after) := by
    rw [put]
    exact Ptr.store_ok get write fit
  have add : l.put.add 1 after = .ok (.ref dest (off + 1), after) := by
    rw [put]
    exact Ptr.add_nat_ok (n := 1) (byte_view_get_put get write bytes) (by simp [bytes]; omega)
  have afterEnv : Env c after r zs z s :=
    ⟨E.strm, E.st, by rw [byte_view_put_stream]; exact E.hz,
      by rw [byte_view_put_istates]; exact E.hs⟩
  unfold inflate_LIT
  rw [runX_bind, runX_get]
  simp only [left, beq_iff_eq, ↓reduceIte]
  rw [runX_bind, runX_ldS E]
  simp only []
  rw [runX_bind, runX_lift_ok store]
  simp only []
  rw [runX_bind, runX_lift_ok add]
  simp only []
  rw [runX_bind, runX_set]
  simp only []
  exact runX_setMode afterEnv LEN _

/-- The actual LIT step preserves the dispatch output clause, all unread
input and byte-view extents. Normal execution emits exactly one byte and
strictly decreases output room; an exhausted output leaves unchanged. -/
theorem inflate_LIT_step {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (B : BitInv h l bs) (output : OutputCursorInvariant h r l)
    (separate : Separate l.next l.have_.toNat l.put l.left.toNat) :
    ∃ outcome regs after state,
      runX (inflate_LIT c) l h = .ok ((outcome, regs), after) ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧ BitInv after regs bs ∧
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
    have finalGood : Good after r zs z state :=
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
      output.emit good finalGood rfl sizes ro nextPut leftCount rfl
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

/-- Complete LIT execution preserves all buffer clauses for the next real
dispatch iteration, including caller ownership and platform byte extents. -/
theorem inflate_LIT_dispatch {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (buffers : DispatchBuffers h r l bs) :
    ∃ outcome regs after state,
      runX (inflate_LIT c) l h = .ok ((outcome, regs), after) ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧ DispatchBuffers after r regs bs ∧
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
  have currentBuffers := buffers.emit good finalGood (by rw [stateFrame]) sizes readonly regFrame output inv separate
  refine ⟨outcome, regs, after, state, run, finalGood, finalTables, currentBuffers, sizes, stateFrame, regFrame, ?_⟩
  rcases kinds with wait | ⟨ok, stateEq, put, left, _⟩
  · exact Or.inl wait
  · exact Or.inr ⟨ok, stateEq, put, left⟩

end Zlib.Inflate.Proofs
