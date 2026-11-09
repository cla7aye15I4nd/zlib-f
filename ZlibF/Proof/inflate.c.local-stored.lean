import ZlibF.Proof.«inflate.c.local-head»
import ZlibF.Proof.«inflate.c.stored-dispatch»

/-! Actual stored-block dispatch on local decoder storage.
Caller ranges can remain separate intervals of the same allocation. -/
namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

theorem callerRange_private_window {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (good : LocalGood h cutoff r zs z s) {pointer : BPtr} {size : Nat} {writing : Bool}
    (range : CallerRange h r pointer size writing) {dest : BRef} {offset : Nat}
    (ptr : pointer = .ref dest offset) :
    ∀ w, s.window = .ref (.blk w) 0 → dest ≠ .blk w := by
  rcases range with null | ⟨_, _, unowned⟩
  · rw [ptr] at null
    cases null
  · intro w window same
    have root : ByteRoot pointer w := by rw [ptr, same]; exact rfl
    apply unowned w root
    exact ⟨z, good.live.hz, Or.inl ⟨zs, s, good.live.zst, good.live.hs, Or.inr window⟩⟩

/-- Extract the slow decoder's output view and private-window separation
from the public range. Cursor accounting remains an internal loop fact. -/
theorem callerRange_slow_output {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (good : LocalGood h cutoff r zs z s) (l : IL) (range : CallerRange h r l.put l.left.toNat true)
    (nonnull : l.put ≠ .null) (count : l.left.toNat ≤ l.out_.toNat)
    (produced : ∀ dest offset, l.put = .ref dest offset → l.out_.toNat - l.left.toNat ≤ offset) :
    ∃ (dest : BRef) (array : Array UInt8) (outOffset : Nat),
      l.put = .ref dest outOffset ∧ Space.get h dest = some array ∧ Space.ro h dest = false ∧
      outOffset + l.left.toNat ≤ array.size ∧ l.left.toNat ≤ l.out_.toNat ∧
      l.out_.toNat - l.left.toNat ≤ outOffset ∧
      (∀ w, s.window = .ref (.blk w) 0 → dest ≠ .blk w) := by
  have writable : Writable h l.put l.left.toNat := by
    rcases range with null | ⟨_, write, _⟩
    · exact False.elim (nonnull null)
    · exact write rfl
  rcases writable with ⟨null, _⟩ | ⟨dest, outOffset, array, ptr, get, write, room⟩
  · exact False.elim (nonnull null)
  · exact ⟨dest, array, outOffset, ptr, get, write, room, count, produced dest outOffset ptr,
      callerRange_private_window good range ptr⟩


theorem inflate_COPY_boundary_frame {c : Ctx} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (good : LocalGood h cutoff r zs z s) (pending : DataPendingInvariant s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = COPY) :
    ∃ (outcome : Except Ex Unit) (regs : IL) (after : Heap) (state : InflateState) (made : Nat),
      made ≤ bs.length ∧ runX (inflate_COPY c) l h = .ok ((outcome, regs), after) ∧
      LocalGood after cutoff r zs z state ∧ DataTableInvariant after state ∧ DataPendingInvariant state ∧
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
    have current : LocalGood after cutoff r zs z state := good.decode_update (by rfl)
      (by change HEAD ≤ TYPE ∧ TYPE ≤ SYNC; decide)
    have inv : BitInv after regs bs :=
      ⟨buffers.bits.have_eq, (buffers.bits.decode_update zs state).next, buffers.bits.hold_lt⟩
    have packet : DispatchBuffers after r regs bs := by
      simpa only [List.drop_zero] using dispatch_advance_both_local buffers good current rfl
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
        simpa only [List.drop_zero] using dispatch_advance_both_local buffers good good rfl (ByteViewSizes.refl h)
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
      have current : LocalGood after cutoff r zs z state := (good.byte_view_put outputGet write privateWindow array).decode_update
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
      have packet := dispatch_advance_both_local buffers good current rfl sizes readonly nextCursor haveCount putCursor leftCount rfl inv
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
theorem inflate_COPY_boundary {c : Ctx} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (good : LocalGood h cutoff r zs z s) (pending : DataPendingInvariant s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = COPY) :
    ∃ (outcome : Except Ex Unit) (regs : IL) (after : Heap) (state : InflateState) (made : Nat),
      made ≤ bs.length ∧ runX (inflate_COPY c) l h = .ok ((outcome, regs), after) ∧
      LocalGood after cutoff r zs z state ∧ DataTableInvariant after state ∧ DataPendingInvariant state ∧
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
theorem inflate_COPY_start_boundary_frame {c : Ctx} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (good : LocalGood h cutoff r zs z s) (pending : DataPendingInvariant s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = COPY_) :
    ∃ (outcome : Except Ex Unit) (regs : IL) (after : Heap) (state : InflateState) (made : Nat),
      made ≤ bs.length ∧ runX (inflate_COPY_ c) l h = .ok ((outcome, regs), after) ∧
      LocalGood after cutoff r zs z state ∧ DataTableInvariant after state ∧ DataPendingInvariant state ∧
      DispatchBuffers after r regs (bs.drop made) ∧ ByteViewSizes h after ∧ DecodeStateFrame s state ∧
      regs.next = inputAdvance l.next made ∧ regs.have_.toNat + made = l.have_.toNat ∧
      regs.put = inputAdvance l.put made ∧ regs.left.toNat + made = l.left.toNat ∧
      regs.bits = l.bits ∧ regs.hold = l.hold ∧
      ((outcome = .error Ex.leave ∧ made = 0 ∧ state = { s with mode := COPY }) ∨
        (outcome = .ok () ∧ made = 0 ∧ state.mode = TYPE) ∨
        (outcome = .ok () ∧ 0 < made ∧ state.mode = COPY ∧ state.length.toNat + made = s.length.toNat)) ∧ after.static = h.static ∧ Shape h after := by
  let ready := { s with mode := COPY }
  let heap0 := setI h zs ready
  have good0 : LocalGood heap0 cutoff r zs z ready := good.decode_update (by rfl)
    (by change HEAD ≤ COPY ∧ COPY ≤ SYNC; decide)
  have E0 : Env c heap0 r zs z ready := ⟨E.strm, E.st, good0.live.hz, good0.live.hs⟩
  have pending0 : DataPendingInvariant ready := by
    apply dataPendingInvariant_idle (s := ready) (by exact pending.sane)
    change COPY ≠ LENEXT ∧ COPY ≠ DIST ∧ COPY ≠ DISTEXT ∧ COPY ≠ MATCH
    decide
  have packet0 : DispatchBuffers heap0 r l bs := by
    simpa only [List.drop_zero] using dispatch_consume_local buffers good good0 rfl
      (fun ref => byte_view_get_setI h zs ready ref) (fun ref => byte_view_ro_setI h zs ready ref)
      (regs := l) (used := 0) (by rfl) (by simp only [inputAdvance_zero]) (by omega)
      (by simpa only [List.drop_zero] using buffers.bits.decode_update zs ready)
  obtain ⟨outcome, regs, after, state, made, bound, run, current, tables, nextPending,
    packet, sizes, frame, next, haveCount, put, left, bits, hold, kinds, static, shape⟩ :=
    inflate_COPY_boundary_frame E0 good0 pending0 packet0 rfl
  exact ⟨outcome, regs, after, state, made, bound, (inflate_COPY__eq E l).trans run,
    current, tables, nextPending, packet, (byte_view_sizes_setI h zs ready).trans sizes,
    DecodeStateFrame.trans (by rfl) frame, next, haveCount, put, left, bits, hold, kinds, static, (shape_setI good.live.hs ready).trans shape⟩

/-- Projection retaining the original complete COPY_ boundary. -/
theorem inflate_COPY_start_boundary {c : Ctx} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (good : LocalGood h cutoff r zs z s) (pending : DataPendingInvariant s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = COPY_) :
    ∃ (outcome : Except Ex Unit) (regs : IL) (after : Heap) (state : InflateState) (made : Nat),
      made ≤ bs.length ∧ runX (inflate_COPY_ c) l h = .ok ((outcome, regs), after) ∧
      LocalGood after cutoff r zs z state ∧ DataTableInvariant after state ∧ DataPendingInvariant state ∧
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


theorem inflate_STORED_boundary_budget_modes {c : Ctx} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (good : LocalGood h cutoff r zs z s) (pending : DataPendingInvariant s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = STORED) (incoming : l.bits.toNat ≤ 39) :
    ∃ (outcome : Except Ex Unit) (regs : IL) (after : Heap) (stream : ZStream)
      (state : InflateState) (used made : Nat), used ≤ bs.length ∧
      runX (inflate_STORED c) l h = .ok ((outcome, regs), after) ∧
      LocalGood after cutoff r zs stream state ∧ DataTableInvariant after state ∧ DataPendingInvariant state ∧
      DispatchBuffers after r regs (bs.drop used) ∧ ByteViewSizes h after ∧ DecodeStateFrame s state ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = inputAdvance l.put made ∧ regs.left.toNat + made = l.left.toNat ∧
      regs.bits.toNat ≤ 39 ∧ (outcome = .ok () ∨ outcome = .error Ex.leave) ∧ after.static = h.static ∧ Shape h after ∧
      regs.bits.toNat ≤ l.bits.toNat + 8 * used ∧
      (outcome = .ok () → state.mode = COPY ∨ state.mode = TYPE ∨ state.mode = BAD) := by
  obtain ⟨aligned, _, _⟩ := BYTEBITS_inv buffers.bits
  have alignCount := UInt32.toNat_sub_of_le l.bits (l.bits &&& 7)
    (UInt32.le_iff_toNat_le.mpr (and7_le l))
  have alignedLe : (bytebits l).bits.toNat ≤ l.bits.toNat := by
    change (l.bits - (l.bits &&& 7)).toNat ≤ _
    rw [alignCount]
    omega
  have alignedBound : (bytebits l).bits.toNat ≤ 39 := by
    change (l.bits - (l.bits &&& 7)).toNat ≤ _
    rw [alignCount]
    omega
  obtain ⟨outcome, current, used, pull, usedBound, bitInv, _, bitCount, shape,
    bitBound, _, _, _, kinds, cursor⟩ := NEEDBITS_run_cursor aligned 32 (by decide)
  have symbolShape : SymbolRegShape l current := by rw [shape]; rfl
  have next : current.next = inputAdvance l.next used := cursor
  have haveCount : current.have_.toNat + used = l.have_.toNat := by
    rw [bitInv.have_eq, buffers.bits.have_eq, List.length_drop]
    omega
  have put : current.put = l.put := by rw [shape]; rfl
  have left : current.left = l.left := by rw [shape]; rfl
  have bounded : current.bits.toNat ≤ 39 := by
    change current.bits.toNat ≤ max (bytebits l).bits.toNat 39 at bitBound
    omega
  have packet := dispatch_consume_local buffers good good rfl (fun _ => rfl) (fun _ => rfl)
    symbolShape next usedBound bitInv
  rcases kinds with normal | wait
  · rw [normal] at pull
    by_cases bad : ((current.hold &&& (0xffff : UInt64)) != ((current.hold >>> 16) ^^^ (0xffff : UInt64))) = true
    · obtain ⟨i, _, run⟩ := inflate_STORED_bad E l current pull bad
      obtain ⟨currentGood, tables, nextPending, nextPacket, sizes, static⟩ :=
        Zlib.Inflate.Local.head_bad_packet good pending packet bitInv (by rfl) i
      exact ⟨.ok (), current, badHeap h r zs z s i, { z with msg := .ref (.str i) 0 },
        { s with mode := BAD }, used, 0, usedBound, run, currentGood, tables, nextPending,
        nextPacket, sizes, by rfl, next, haveCount, by rw [put, inputAdvance_zero],
        by rw [left]; rfl, bounded, Or.inl rfl, static,
        (shape_put good.live.hz { z with msg := .ref (.str i) 0 }).trans
          (shape_setI (by rw [ZStreamRef.put_istates]; exact good.live.hs) { s with mode := BAD }),
        by omega,
        fun _ => Or.inr (Or.inr rfl)⟩
    · let ready := { s with length := current.hold.toUInt32 &&& 0xffff, mode := COPY_ }
      let heap0 := setI h zs ready
      let first := { current with hold := 0, bits := 0 }
      have frame : DecodeStateFrame s ready := by rfl
      have good0 : LocalGood heap0 cutoff r zs z ready := good.decode_update frame
        (by change HEAD ≤ COPY_ ∧ COPY_ ≤ SYNC; decide)
      have E0 : Env c heap0 r zs z ready := ⟨E.strm, E.st, good0.live.hz, good0.live.hs⟩
      have pending0 : DataPendingInvariant ready := by
        apply dataPendingInvariant_idle (s := ready) (by exact pending.sane)
        change COPY_ ≠ LENEXT ∧ COPY_ ≠ DIST ∧ COPY_ ≠ DISTEXT ∧ COPY_ ≠ MATCH
        decide
      have inv0 : BitInv heap0 first (bs.drop used) :=
        (INITBITS_inv bitInv).1.decode_update zs ready
      have packet0 : DispatchBuffers heap0 r first (bs.drop used) :=
        dispatch_consume_local buffers good good0 rfl (fun ref => byte_view_get_setI h zs ready ref)
          (fun ref => byte_view_ro_setI h zs ready ref) (by dsimp only [first]; rw [shape]; rfl) next usedBound inv0
      have sourceCut := inflate_STORED_ok E l current pull bad
      by_cases trees : c.flush = Z_TREES
      · have run : runX (inflate_STORED c) l h = .ok ((.error Ex.leave, first), heap0) := by
          rw [sourceCut]
          simp only [trees, beq_self_eq_true, ↓reduceIte]
          rfl
        exact ⟨.error Ex.leave, first, heap0, z, ready, used, 0, usedBound, run, good0,
          dataTableInvariant_inactive (by change ¬ DataTableMode COPY_; unfold DataTableMode; decide),
          pending0, packet0, byte_view_sizes_setI h zs ready, frame, next, haveCount,
          by rw [inputAdvance_zero]; exact put, by change current.left.toNat + 0 = l.left.toNat; rw [left]; rfl, by change 0 ≤ 39; decide, Or.inr rfl, rfl, shape_setI good.live.hs ready,
          by change 0 ≤ _; omega, fun impossible => by cases impossible⟩
      · have sourceRun : runX (inflate_STORED c) l h = runX (inflate_COPY_ c) first heap0 := by
          rw [sourceCut]
          simp only [beq_iff_eq, trees, ↓reduceIte]
          rfl
        obtain ⟨exit, regs, after, state, made, madeBound, run, currentGood, tables, nextPending,
          nextPacket, sizes, stateFrame, nextCursor, inputCount, putCursor, outputCount,
          bits, _, exits, static, heapShape⟩ := inflate_COPY_start_boundary_frame E0 good0 pending0 packet0 rfl
        have exitKinds : exit = .ok () ∨ exit = .error Ex.leave := by
          rcases exits with wait | done | copied
          · exact Or.inr wait.1
          · exact Or.inl done.1
          · exact Or.inl copied.1
        have normalModes : exit = .ok () → state.mode = COPY ∨ state.mode = TYPE ∨ state.mode = BAD := by
          intro normal
          rcases exits with wait | done | copied
          · have impossible := wait.1.symm.trans normal
            cases impossible
          · exact Or.inr (Or.inl done.2.2)
          · exact Or.inl copied.2.2.1
        have totalBound : used + made ≤ bs.length := by rw [List.length_drop] at madeBound; omega
        refine ⟨exit, regs, after, z, state, used + made, made, totalBound, sourceRun.trans run,
          currentGood, tables, nextPending, ?_, (byte_view_sizes_setI h zs ready).trans sizes,
          frame.trans stateFrame, ?_, ?_, ?_, ?_, ?_, exitKinds, static, (shape_setI good.live.hs ready).trans heapShape,
          by rw [bits]; change 0 ≤ _; omega, normalModes⟩
        · simpa only [List.drop_drop] using nextPacket
        · rw [nextCursor]
          change inputAdvance current.next made = _
          rw [next, inputAdvance_add]
        · change regs.have_.toNat + made = current.have_.toNat at inputCount
          omega
        · rw [putCursor]
          change inputAdvance current.put made = _
          rw [put]
        · change regs.left.toNat + made = current.left.toNat at outputCount
          rwa [left] at outputCount
        · rw [bits]
          change 0 ≤ 39
          decide
  · have run := inflate_STORED_wait (c := c) l current h Ex.leave (by rwa [wait] at pull)
    exact ⟨.error Ex.leave, current, h, z, s, used, 0, usedBound, run, good,
      dataTableInvariant_inactive (by rw [mode]; unfold DataTableMode; decide), pending, packet,
      ByteViewSizes.refl h, by rfl, next, haveCount, by rw [put, inputAdvance_zero],
      by rw [left]; rfl, bounded, Or.inr rfl, rfl, Shape.refl h,
      by omega,
      fun impossible => by cases impossible⟩

/-- Projection retaining the original complete STORED heap frame. -/
theorem inflate_STORED_boundary_frame {c : Ctx} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (good : LocalGood h cutoff r zs z s) (pending : DataPendingInvariant s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = STORED) (incoming : l.bits.toNat ≤ 39) :
    ∃ (outcome : Except Ex Unit) (regs : IL) (after : Heap) (stream : ZStream)
      (state : InflateState) (used made : Nat), used ≤ bs.length ∧
      runX (inflate_STORED c) l h = .ok ((outcome, regs), after) ∧
      LocalGood after cutoff r zs stream state ∧ DataTableInvariant after state ∧ DataPendingInvariant state ∧
      DispatchBuffers after r regs (bs.drop used) ∧ ByteViewSizes h after ∧ DecodeStateFrame s state ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = inputAdvance l.put made ∧ regs.left.toNat + made = l.left.toNat ∧
      regs.bits.toNat ≤ 39 ∧ (outcome = .ok () ∨ outcome = .error Ex.leave) ∧ after.static = h.static ∧ Shape h after := by
  obtain ⟨outcome, regs, after, stream, state, used, made, bound, run, current, tables,
    nextPending, packet, sizes, frame, next, count, put, left, bits, kinds, static, shape, _, _⟩ :=
    inflate_STORED_boundary_budget_modes E good pending buffers mode incoming
  exact ⟨outcome, regs, after, stream, state, used, made, bound, run, current, tables,
    nextPending, packet, sizes, frame, next, count, put, left, bits, kinds, static, shape⟩

/-- Projection retaining the original complete STORED boundary. -/
theorem inflate_STORED_boundary {c : Ctx} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (good : LocalGood h cutoff r zs z s) (pending : DataPendingInvariant s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = STORED) (incoming : l.bits.toNat ≤ 39) :
    ∃ (outcome : Except Ex Unit) (regs : IL) (after : Heap) (stream : ZStream)
      (state : InflateState) (used made : Nat), used ≤ bs.length ∧
      runX (inflate_STORED c) l h = .ok ((outcome, regs), after) ∧
      LocalGood after cutoff r zs stream state ∧ DataTableInvariant after state ∧ DataPendingInvariant state ∧
      DispatchBuffers after r regs (bs.drop used) ∧ ByteViewSizes h after ∧ DecodeStateFrame s state ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = inputAdvance l.put made ∧ regs.left.toNat + made = l.left.toNat ∧
      regs.bits.toNat ≤ 39 ∧ (outcome = .ok () ∨ outcome = .error Ex.leave) := by
  obtain ⟨outcome, regs, after, stream, state, used, made, bound, run, current, tables,
    nextPending, packet, sizes, frame, next, count, put, left, bits, kinds, _, _⟩ :=
    inflate_STORED_boundary_frame E good pending buffers mode incoming
  exact ⟨outcome, regs, after, stream, state, used, made, bound, run, current, tables,
    nextPending, packet, sizes, frame, next, count, put, left, bits, kinds⟩


theorem inflate_dispatch_stored_boundary {c : Ctx} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (good : LocalGood h cutoff r zs z s) (pending : DataPendingInvariant s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = STORED ∨ s.mode = COPY_ ∨ s.mode = COPY) (incoming : l.bits.toNat ≤ 39) :
    ∃ (outcome : Except Ex Unit) (regs : IL) (after : Heap) (stream : ZStream)
      (state : InflateState) (used made : Nat), used ≤ bs.length ∧
      runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) ∧
      LocalGood after cutoff r zs stream state ∧ DataTableInvariant after state ∧ DataPendingInvariant state ∧
      DispatchBuffers after r regs (bs.drop used) ∧ ByteViewSizes h after ∧ DecodeStateFrame s state ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = inputAdvance l.put made ∧ regs.left.toNat + made = l.left.toNat ∧
      regs.bits.toNat ≤ 39 ∧ (outcome = .ok () ∨ outcome = .error Ex.leave) ∧ after.static = h.static ∧ Shape h after := by
  rcases mode with stored | start | copy
  · rw [inflate_dispatch_STORED E l stored]
    exact inflate_STORED_boundary_frame E good pending buffers stored incoming
  · obtain ⟨outcome, regs, after, state, made, bound, run, current, tables, nextPending,
      packet, sizes, frame, next, count, put, left, bits, _, exits, static, shape⟩ :=
      inflate_COPY_start_boundary_frame E good pending buffers start
    have kinds : outcome = .ok () ∨ outcome = .error Ex.leave := by
      rcases exits with wait | done | copied
      · exact Or.inr wait.1
      · exact Or.inl done.1
      · exact Or.inl copied.1
    exact ⟨outcome, regs, after, z, state, made, made, bound,
      (inflate_dispatch_COPY_start E l start).trans run, current, tables, nextPending,
      packet, sizes, frame, next, count, put, left, by rw [bits]; exact incoming, kinds, static, shape⟩
  · obtain ⟨outcome, regs, after, state, made, bound, run, current, tables, nextPending,
      packet, sizes, frame, next, count, put, left, bits, _, exits, static, shape⟩ :=
      inflate_COPY_boundary_frame E good pending buffers copy
    have kinds : outcome = .ok () ∨ outcome = .error Ex.leave := by
      rcases exits with wait | done | copied
      · exact Or.inr wait.1
      · exact Or.inl done.1
      · exact Or.inl copied.1
    exact ⟨outcome, regs, after, z, state, made, made, bound,
      (inflate_dispatch_COPY E l copy).trans run, current, tables, nextPending,
      packet, sizes, frame, next, count, put, left, by rw [bits]; exact incoming, kinds, static, shape⟩


#print axioms inflate_COPY_boundary_frame
#print axioms inflate_COPY_start_boundary_frame
#print axioms inflate_STORED_boundary_budget_modes
#print axioms inflate_dispatch_stored_boundary
end Zlib.Inflate.Local
