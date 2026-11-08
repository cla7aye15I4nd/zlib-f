import ZlibF.Proof.«inflate.c.block-type»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Byte-view replacement never changes the static library image. -/
theorem byte_view_put_static (h : Heap) (ref : BRef) (array : Array UInt8) :
    (Space.put h ref array).static = h.static := by
  cases ref <;> simp only [Space.put]
  split <;> rfl

/-- The real stored-copy suffix admits every writable public byte view.
The source and destination may be disjoint slices of the same object. -/
theorem copyTail_views_run {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) (l : IL)
    {n : UInt32} (positive : n ≠ 0) {source dest : BRef} {io oo : Nat}
    {input output : Array UInt8}
    (next : l.next = .ref source io) (put : l.put = .ref dest oo)
    (inputGet : Space.get h source = some input) (outputGet : Space.get h dest = some output)
    (write : Space.ro h dest = false) (inputFit : io + n.toNat ≤ input.size)
    (outputFit : oo + n.toNat ≤ output.size)
    (separate : dest ≠ source ∨ oo + n.toNat ≤ io ∨ io + n.toNat ≤ oo) :
    runX (copyTail c n) l h = .ok ((.ok (),
      copyRegs l n (.ref source (io + n.toNat)) (.ref dest (oo + n.toNat))),
      setI (Space.put h dest (copyRange output input oo io n.toNat)) zs { s with length := s.length - n }) := by
  let array := copyRange output input oo io n.toNat
  let base := Space.put h dest array
  have size : array.size = output.size := size_copyRange ..
  have copy : memcpyB l.put l.next n.toNat h = .ok ((), base) := by
    rw [put, next]
    exact Ptr.memcpy_ok outputGet inputGet write outputFit inputFit separate
  have sizes := byte_view_sizes_put outputGet write array size
  obtain ⟨saved, savedGet, savedSize⟩ := sizes.view inputGet
  have destGet : Space.get base dest = some array := byte_view_get_put outputGet write array
  have nextAdd : l.next.add (n.toNat : Int) base = .ok (.ref source (io + n.toNat), base) := by
    rw [next]
    exact Ptr.add_nat_ok savedGet (by omega)
  have putAdd : l.put.add (n.toNat : Int) base = .ok (.ref dest (oo + n.toNat), base) := by
    rw [put]
    exact Ptr.add_nat_ok destGet (by omega)
  have E1 : Env c base r zs z s :=
    ⟨E.strm, E.st, by rw [byte_view_put_stream]; exact E.hz,
      by rw [byte_view_put_istates]; exact E.hs⟩
  unfold copyTail
  rw [runX_bind, runX_get]
  simp only [beq_iff_eq, positive, ↓reduceIte]
  rw [runX_bind, runX_lift_ok copy]
  simp only []
  rw [runX_bind, runX_lift_ok nextAdd]
  simp only []
  rw [runX_bind, runX_lift_ok putAdd]
  simp only []
  rw [runX_bind, runX_set]
  simp only []
  rw [runX_bind, runX_wrS E1]
  rfl

/-- The actual COPY branch uses the generic byte-view suffix. -/
theorem inflate_COPY_views_run {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) (l : IL)
    (nonempty : s.length ≠ 0) (positive : copyAmt s.length l.have_ l.left ≠ 0)
    {source dest : BRef} {io oo : Nat} {input output : Array UInt8}
    (next : l.next = .ref source io) (put : l.put = .ref dest oo)
    (inputGet : Space.get h source = some input) (outputGet : Space.get h dest = some output)
    (write : Space.ro h dest = false)
    (inputFit : io + (copyAmt s.length l.have_ l.left).toNat ≤ input.size)
    (outputFit : oo + (copyAmt s.length l.have_ l.left).toNat ≤ output.size)
    (separate : dest ≠ source ∨ oo + (copyAmt s.length l.have_ l.left).toNat ≤ io ∨
      io + (copyAmt s.length l.have_ l.left).toNat ≤ oo) :
    let n := copyAmt s.length l.have_ l.left
    runX (inflate_COPY c) l h = .ok ((.ok (),
      copyRegs l n (.ref source (io + n.toNat)) (.ref dest (oo + n.toNat))),
      setI (Space.put h dest (copyRange output input oo io n.toNat)) zs { s with length := s.length - n }) := by
  rw [inflate_COPY_split E l nonempty]
  exact copyTail_views_run E l positive next put inputGet outputGet write inputFit outputFit separate

/-- A disjoint input slice survives a stored-block memcpy, even when its
allocation is also the destination allocation. -/
theorem BitInv.stored_copy {h : Heap} {l : IL} {bs : List UInt8} (B : BitInv h l bs)
    {dest : BRef} {input output : Array UInt8} {io oo n : Nat}
    (get : Space.get h dest = some output) (write : Space.ro h dest = false)
    (inputFit : io + n ≤ input.size) (outputFit : oo + n ≤ output.size)
    (separate : bs = [] ∨ ∀ i, l.next = .ref dest i → i + bs.length ≤ oo ∨ oo + n ≤ i) :
    BitInv (Space.put h dest (copyRange output input oo io n)) l bs := by
  let array := copyRange output input oo io n
  refine ⟨B.have_eq, ?_, B.hold_lt⟩
  rcases separate with empty | positions
  · exact Or.inl empty
  · rcases B.next with empty | ⟨source, saved, off, next, sourceGet, room, content⟩
    · exact Or.inl empty
    · by_cases same : source = dest
      · subst source
        have equal : saved = output := Option.some.inj (sourceGet.symm.trans get)
        subst saved
        refine Or.inr ⟨dest, array, off, next, byte_view_get_put get write array,
          by simpa only [array, size_copyRange] using room, ?_⟩
        have unchanged := copyRange_read_disjoint output input oo io n off bs.length outputFit inputFit room
          (by rcases positions off next with before | later; exact Or.inr before; exact Or.inl later)
        apply content.trans
        symm
        apply List.ext_getElem
        · simp only [List.length_take, List.length_drop, Array.length_toList, array, size_copyRange]
        · intro i hi hj
          have bound : i < bs.length := by simp only [List.length_take] at hi; omega
          have eq := unchanged i bound
          have copied : off + i < array.size := by rw [size_copyRange]; omega
          have original : off + i < output.size := by omega
          rw [getElem!_pos array (off + i) copied, getElem!_pos output (off + i) original] at eq
          simpa only [List.getElem_take, List.getElem_drop, Array.getElem_toList] using eq
      · exact Or.inr ⟨source, saved, off, next,
          by rw [byte_view_get_put_ne h same array]; exact sourceGet, room, content⟩

/-- Exact input advancement transports the readable suffix on the same heap. -/
theorem BitInv.advance_bytes {h : Heap} {l regs : IL} {bs : List UInt8} {used : Nat}
    (B : BitInv h l bs) (bound : used ≤ bs.length)
    (cursor : regs.next = inputAdvance l.next used)
    (count : regs.have_.toNat + used = l.have_.toNat)
    (hold : regs.hold = l.hold) (bits : regs.bits = l.bits) :
    BitInv h regs (bs.drop used) := by
  refine ⟨by rw [List.length_drop, ← B.have_eq]; omega, ?_, ?_⟩
  · rcases B.next with empty | ⟨ref, array, off, ptr, get, room, content⟩
    · exact Or.inl (by simp only [empty, List.drop_nil])
    · refine Or.inr ⟨ref, array, off + used, ?_, get, ?_, ?_⟩
      · rw [cursor, ptr]
        rfl
      · rw [List.length_drop]
        omega
      · rw [List.length_drop]
        conv => lhs; rw [content, List.drop_take, List.drop_drop]
  · rw [hold, bits]
    exact B.hold_lt

/-- The complete actual COPY mode keeps the caller packet on public byte
views, including empty buffers and disjoint slices of a single allocation.
A continuing copy strictly consumes input and output and decreases length. -/
theorem inflate_COPY_boundary_frame {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (good : Good h r zs z s) (pending : DataPendingInvariant s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = COPY) :
    ∃ (outcome : Except Ex Unit) (regs : IL) (after : Heap) (state : InflateState) (made : Nat),
      made ≤ bs.length ∧ runX (inflate_COPY c) l h = .ok ((outcome, regs), after) ∧
      Good after r zs z state ∧ DataTableInvariant after state ∧ DataPendingInvariant state ∧
      DispatchBuffers after r regs (bs.drop made) ∧ ByteViewSizes h after ∧ DecodeStateFrame s state ∧
      regs.next = inputAdvance l.next made ∧ regs.have_.toNat + made = l.have_.toNat ∧
      regs.put = inputAdvance l.put made ∧ regs.left.toNat + made = l.left.toNat ∧
      regs.bits = l.bits ∧ regs.hold = l.hold ∧
      ((outcome = .error Ex.leave ∧ made = 0 ∧ state = s) ∨
        (outcome = .ok () ∧ made = 0 ∧ state.mode = TYPE) ∨
        (outcome = .ok () ∧ 0 < made ∧ state.mode = COPY ∧ state.length.toNat + made = s.length.toNat)) ∧ after.static = h.static ∧ Shape h after := by
  by_cases done : s.length = 0
  · let state := { s with mode := TYPE }
    let after := setI h zs state
    let regs := { l with copy := 0 }
    have current : Good after r zs z state := good.decode_update (by rfl)
      (by change HEAD ≤ TYPE ∧ TYPE ≤ SYNC; decide)
    have inv : BitInv after regs bs :=
      ⟨buffers.bits.have_eq, (buffers.bits.decode_update zs state).next, buffers.bits.hold_lt⟩
    have packet : DispatchBuffers after r regs bs := by
      simpa only [List.drop_zero] using buffers.advance_both good current rfl
        (byte_view_sizes_setI h zs state) (fun ref => byte_view_ro_setI h zs state ref)
        (regs := regs) (used := 0) (made := 0) (by simp only [inputAdvance_zero, regs])
        (by rfl) (by simp only [inputAdvance_zero, regs]) (by rfl) rfl
        (by simpa only [List.drop_zero] using inv)
    refine ⟨.ok (), regs, after, state, 0, by omega, inflate_COPY_done E l done, current,
      dataTableInvariant_inactive (by change ¬ DataTableMode TYPE; unfold DataTableMode; decide),
      dataPendingInvariant_idle pending.sane (by change TYPE ≠ LENEXT ∧ TYPE ≠ DIST ∧ TYPE ≠ DISTEXT ∧ TYPE ≠ MATCH; decide),
      by simpa only [List.drop_zero] using packet, byte_view_sizes_setI h zs state, by rfl,
      (inputAdvance_zero l.next).symm, by rfl, (inputAdvance_zero l.put).symm, by rfl,
      rfl, rfl, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩), rfl, shape_setI good.live.hs state⟩
  · let n := copyAmt s.length l.have_ l.left
    obtain ⟨lengthBound, inputBound, outputBound⟩ := copyAmt_le s.length l.have_ l.left
    change n.toNat ≤ s.length.toNat at lengthBound
    change n.toNat ≤ l.have_.toNat at inputBound
    change n.toNat ≤ l.left.toNat at outputBound
    by_cases stall : n = 0
    · let regs := { l with copy := 0 }
      have inv : BitInv h regs bs := ⟨buffers.bits.have_eq, buffers.bits.next, buffers.bits.hold_lt⟩
      have packet : DispatchBuffers h r regs bs := by
        simpa only [List.drop_zero] using buffers.advance_both good good rfl (ByteViewSizes.refl h)
          (fun _ => rfl) (regs := regs) (used := 0) (made := 0) (by simp only [inputAdvance_zero, regs])
          (by rfl) (by simp only [inputAdvance_zero, regs]) (by rfl) rfl
          (by simpa only [List.drop_zero] using inv)
      exact ⟨.error Ex.leave, regs, h, s, 0, by omega, inflate_COPY_leave E l done stall,
        good, dataTableInvariant_inactive (by rw [mode]; unfold DataTableMode; decide), pending,
        by simpa only [List.drop_zero] using packet, ByteViewSizes.refl h, by rfl,
        (inputAdvance_zero l.next).symm, by rfl, (inputAdvance_zero l.put).symm, by rfl,
        rfl, rfl, Or.inl ⟨rfl, rfl, rfl⟩, rfl, Shape.refl h⟩
    · have positive : 0 < n.toNat := by
        have nonzero : n.toNat ≠ 0 := by intro zero; exact stall (UInt32.toNat_inj.mp zero)
        omega
      have nonempty : bs ≠ [] := by intro empty; rw [empty] at buffers; have := buffers.bits.have_eq; simp at this; omega
      obtain ⟨source, input, io, next, inputGet, inputRoom, _⟩ := buffers.bits.next.resolve_left nonempty
      obtain ⟨dest, output, oo, put, outputGet, write, outputRoom, _, _, privateWindow⟩ :=
        callerRange_slow_output good l buffers.output.range buffers.output.nonnull buffers.output.count buffers.output.produced
      have inputFit : io + n.toNat ≤ input.size := by have eq := buffers.bits.have_eq; omega
      have outputFit : oo + n.toNat ≤ output.size := by omega
      have separate : dest ≠ source ∨ oo + n.toNat ≤ io ∨ io + n.toNat ≤ oo := by
        have sep := buffers.separate
        rw [next, put] at sep
        rcases sep with empty | empty | different | before | later
        · omega
        · omega
        · exact Or.inl (Ne.symm different)
        · exact Or.inr (Or.inr (by omega))
        · exact Or.inr (Or.inl (by omega))
      let array := copyRange output input oo io n.toNat
      let state := { s with length := s.length - n }
      let base := Space.put h dest array
      let after := setI base zs state
      let regs := copyRegs l n (.ref source (io + n.toNat)) (.ref dest (oo + n.toNat))
      have frame : DecodeStateFrame s state := by rfl
      have current : Good after r zs z state := (good.byte_view_put outputGet write privateWindow array).decode_update
        frame (by change HEAD ≤ s.mode ∧ s.mode ≤ SYNC; exact good.live.mode)
      have sizes : ByteViewSizes h after :=
        (byte_view_sizes_put outputGet write array (size_copyRange ..)).trans (byte_view_sizes_setI _ zs state)
      have readonly : ∀ ref : BRef, Space.ro after ref = Space.ro h ref := by
        intro ref
        rw [byte_view_ro_setI, byte_view_ro_write]
      have nextCursor : regs.next = inputAdvance l.next n.toNat := by rw [next]; rfl
      have putCursor : regs.put = inputAdvance l.put n.toNat := by rw [put]; rfl
      have haveCount : regs.have_.toNat + n.toNat = l.have_.toNat := by
        change (l.have_ - n).toNat + n.toNat = _
        rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr inputBound)]
        omega
      have leftCount : regs.left.toNat + n.toNat = l.left.toNat := by
        change (l.left - n).toNat + n.toNat = _
        rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr outputBound)]
        omega
      have usedBound : n.toNat ≤ bs.length := by rw [← buffers.bits.have_eq]; exact inputBound
      have positions : bs = [] ∨ ∀ i, l.next = .ref dest i → i + bs.length ≤ oo ∨ oo + n.toNat ≤ i := by
        right
        intro i ptr
        have sep := buffers.bits.output_positions put (by intro zero; have eq := congrArg UInt32.toNat zero; change l.left.toNat = 0 at eq; omega) buffers.separate
        rcases sep with empty | separated
        · exact False.elim (nonempty empty)
        · rcases separated i ptr with before | later
          · exact Or.inl before
          · exact Or.inr (by omega)
      have copiedInv := buffers.bits.stored_copy (input := input) (io := io) (oo := oo) (n := n.toNat) outputGet write
        inputFit outputFit positions
      have advanced := copiedInv.advance_bytes usedBound nextCursor haveCount (by rfl) (by rfl)
      have inv : BitInv after regs (bs.drop n.toNat) := advanced.decode_update zs state
      have packet := buffers.advance_both good current rfl sizes readonly nextCursor haveCount putCursor leftCount rfl inv
      have idle : DataPendingInvariant state := by
        apply dataPendingInvariant_idle (s := state) (by exact pending.sane)
        change s.mode ≠ LENEXT ∧ s.mode ≠ DIST ∧ s.mode ≠ DISTEXT ∧ s.mode ≠ MATCH
        rw [mode]
        decide
      have remaining : state.length.toNat + n.toNat = s.length.toNat := by
        change (s.length - n).toNat + n.toNat = _
        rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr lengthBound)]
        omega
      exact ⟨.ok (), regs, after, state, n.toNat, usedBound,
        inflate_COPY_views_run E l done stall next put inputGet outputGet write
          inputFit outputFit separate,
        current, dataTableInvariant_inactive (by change ¬ DataTableMode s.mode; rw [mode]; unfold DataTableMode; decide),
        idle, packet, sizes, frame, nextCursor, haveCount, putCursor, leftCount, rfl, rfl,
        Or.inr (Or.inr ⟨rfl, positive, mode, remaining⟩),
        byte_view_put_static h dest array,
        (byte_view_put_shape outputGet write array).trans
          (shape_setI (by rw [byte_view_put_istates]; exact good.live.hs) state)⟩

/-- Projection retaining the original complete COPY boundary. -/
theorem inflate_COPY_boundary {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (good : Good h r zs z s) (pending : DataPendingInvariant s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = COPY) :
    ∃ (outcome : Except Ex Unit) (regs : IL) (after : Heap) (state : InflateState) (made : Nat),
      made ≤ bs.length ∧ runX (inflate_COPY c) l h = .ok ((outcome, regs), after) ∧
      Good after r zs z state ∧ DataTableInvariant after state ∧ DataPendingInvariant state ∧
      DispatchBuffers after r regs (bs.drop made) ∧ ByteViewSizes h after ∧ DecodeStateFrame s state ∧
      regs.next = inputAdvance l.next made ∧ regs.have_.toNat + made = l.have_.toNat ∧
      regs.put = inputAdvance l.put made ∧ regs.left.toNat + made = l.left.toNat ∧
      regs.bits = l.bits ∧ regs.hold = l.hold ∧
      ((outcome = .error Ex.leave ∧ made = 0 ∧ state = s) ∨
        (outcome = .ok () ∧ made = 0 ∧ state.mode = TYPE) ∨
        (outcome = .ok () ∧ 0 < made ∧ state.mode = COPY ∧ state.length.toNat + made = s.length.toNat)) := by
  obtain ⟨outcome, regs, after, state, made, bound, run, current, tables, nextPending,
    packet, sizes, frame, next, haveCount, put, left, bits, hold, kinds, _, _⟩ :=
    inflate_COPY_boundary_frame E good pending buffers mode
  exact ⟨outcome, regs, after, state, made, bound, run, current, tables, nextPending,
    packet, sizes, frame, next, haveCount, put, left, bits, hold, kinds⟩

/-- The real COPY_ entry normalizes its mode and executes the complete
public-view COPY boundary on that same heap. -/
theorem inflate_COPY_start_boundary_frame {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (good : Good h r zs z s) (pending : DataPendingInvariant s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = COPY_) :
    ∃ (outcome : Except Ex Unit) (regs : IL) (after : Heap) (state : InflateState) (made : Nat),
      made ≤ bs.length ∧ runX (inflate_COPY_ c) l h = .ok ((outcome, regs), after) ∧
      Good after r zs z state ∧ DataTableInvariant after state ∧ DataPendingInvariant state ∧
      DispatchBuffers after r regs (bs.drop made) ∧ ByteViewSizes h after ∧ DecodeStateFrame s state ∧
      regs.next = inputAdvance l.next made ∧ regs.have_.toNat + made = l.have_.toNat ∧
      regs.put = inputAdvance l.put made ∧ regs.left.toNat + made = l.left.toNat ∧
      regs.bits = l.bits ∧ regs.hold = l.hold ∧
      ((outcome = .error Ex.leave ∧ made = 0 ∧ state = { s with mode := COPY }) ∨
        (outcome = .ok () ∧ made = 0 ∧ state.mode = TYPE) ∨
        (outcome = .ok () ∧ 0 < made ∧ state.mode = COPY ∧ state.length.toNat + made = s.length.toNat)) ∧ after.static = h.static ∧ Shape h after := by
  let ready := { s with mode := COPY }
  let heap0 := setI h zs ready
  have good0 : Good heap0 r zs z ready := good.decode_update (by rfl)
    (by change HEAD ≤ COPY ∧ COPY ≤ SYNC; decide)
  have E0 : Env c heap0 r zs z ready := ⟨E.strm, E.st, good0.live.hz, good0.live.hs⟩
  have pending0 : DataPendingInvariant ready := by
    apply dataPendingInvariant_idle (s := ready) (by exact pending.sane)
    change COPY ≠ LENEXT ∧ COPY ≠ DIST ∧ COPY ≠ DISTEXT ∧ COPY ≠ MATCH
    decide
  have packet0 := buffers.byte_views good good0 rfl (fun ref => byte_view_get_setI h zs ready ref)
    (fun ref => byte_view_ro_setI h zs ready ref)
  obtain ⟨outcome, regs, after, state, made, bound, run, current, tables, nextPending,
    packet, sizes, frame, next, haveCount, put, left, bits, hold, kinds, static, shape⟩ :=
    inflate_COPY_boundary_frame E0 good0 pending0 packet0 rfl
  exact ⟨outcome, regs, after, state, made, bound, (inflate_COPY__eq E l).trans run,
    current, tables, nextPending, packet, (byte_view_sizes_setI h zs ready).trans sizes,
    DecodeStateFrame.trans (by rfl) frame, next, haveCount, put, left, bits, hold, kinds, static, (shape_setI good.live.hs ready).trans shape⟩

/-- Projection retaining the original complete COPY_ boundary. -/
theorem inflate_COPY_start_boundary {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (good : Good h r zs z s) (pending : DataPendingInvariant s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = COPY_) :
    ∃ (outcome : Except Ex Unit) (regs : IL) (after : Heap) (state : InflateState) (made : Nat),
      made ≤ bs.length ∧ runX (inflate_COPY_ c) l h = .ok ((outcome, regs), after) ∧
      Good after r zs z state ∧ DataTableInvariant after state ∧ DataPendingInvariant state ∧
      DispatchBuffers after r regs (bs.drop made) ∧ ByteViewSizes h after ∧ DecodeStateFrame s state ∧
      regs.next = inputAdvance l.next made ∧ regs.have_.toNat + made = l.have_.toNat ∧
      regs.put = inputAdvance l.put made ∧ regs.left.toNat + made = l.left.toNat ∧
      regs.bits = l.bits ∧ regs.hold = l.hold ∧
      ((outcome = .error Ex.leave ∧ made = 0 ∧ state = { s with mode := COPY }) ∨
        (outcome = .ok () ∧ made = 0 ∧ state.mode = TYPE) ∨
        (outcome = .ok () ∧ 0 < made ∧ state.mode = COPY ∧ state.length.toNat + made = s.length.toNat)) := by
  obtain ⟨outcome, regs, after, state, made, bound, run, current, tables, nextPending,
    packet, sizes, frame, next, haveCount, put, left, bits, hold, kinds, _, _⟩ :=
    inflate_COPY_start_boundary_frame E good pending buffers mode
  exact ⟨outcome, regs, after, state, made, bound, run, current, tables, nextPending,
    packet, sizes, frame, next, haveCount, put, left, bits, hold, kinds⟩

end Zlib.Inflate.Proofs
