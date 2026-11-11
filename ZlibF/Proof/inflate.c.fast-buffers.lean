import ZlibF.Proof.«inflate.c.fast-entry»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Simultaneous input and output advancement retains the public packet.
This uses the original interval-separation domain and exact cursor/count
accounting, independently of how the translated step produced its bytes. -/
theorem DispatchBuffers.advance_both {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState} {l regs : IL} {bs : List UInt8} {used made : Nat}
    (buffers : DispatchBuffers h r l bs) (before : Good h r zs z s)
    (current : Good after r zs stream state) (window : state.window = s.window)
    (sizes : ByteViewSizes h after) (readonly : ∀ ref : BRef, Space.ro after ref = Space.ro h ref)
    (next : regs.next = inputAdvance l.next used) (haveCount : regs.have_.toNat + used = l.have_.toNat)
    (put : regs.put = inputAdvance l.put made) (left : regs.left.toNat + made = l.left.toNat)
    (total : regs.out_ = l.out_) (bits : BitInv after regs (bs.drop used)) :
    DispatchBuffers after r regs (bs.drop used) := by
  have input := callerRange_capacity before current window sizes readonly buffers.input
  have inputBound : used ≤ l.have_.toNat := by omega
  have outputBound : made ≤ l.left.toNat := by omega
  have inputAdvance := callerRange_advance input inputBound
  have nextCount : regs.have_.toNat = l.have_.toNat - used := by omega
  have nextLeft : regs.left.toNat = l.left.toNat - made := by omega
  have output := buffers.output.emit before current window sizes readonly put left total
  have separate := inputAdvance_separate l.next l.put l.have_.toNat l.left.toNat used inputBound buffers.separate
  have separate := separate_advance_output _ _ _ _ made outputBound separate
  refine ⟨?_, output, ?_, bits⟩
  · simpa only [← next, ← nextCount] using inputAdvance
  · simpa only [← next, ← put, ← nextCount, ← nextLeft] using separate

/-- A proved concrete fast result retains the complete dispatch buffer
packet. This heap transport consumes the actual FastPost; the enclosing
mode must obtain it from the translated fast-callee theorem. It reads the
input block back from the heap at entry, so it keeps input and output in
distinct blocks. -/
theorem fastPost_buffers (e : Zlib.Inffast.Proofs.Env) {after : Heap} {l : IL} {bs : List UInt8}
    (good : Good e.h0 e.r e.stid e.sm0 e.s0) (buffers : DispatchBuffers e.h0 e.r l bs)
    (pending : DataPendingInvariant e.s0)
    (leaves : ∀ ref offset ca, e.s0.lencode = .ref ref offset → Space.get e.h0 ref = some ca →
      Zlib.Inffast.Spec.LenLeavesPositive ca offset e.s0.lenbits.toNat)
    (input : l.next = e.sm0.next_in) (inputCount : l.have_ = e.sm0.avail_in)
    (output : l.put = e.sm0.next_out) (outputCount : l.left = e.sm0.avail_out)
    (post : Zlib.Inffast.Spec.FastPost e after) (different : e.ib ≠ e.ob) :
    ∃ used made regs stream state, used ≤ bs.length ∧
      Good after e.r e.stid stream state ∧ DispatchBuffers after e.r regs (bs.drop used) ∧
      ByteViewSizes e.h0 after ∧ regs.next = inputAdvance l.next used ∧
      regs.have_.toNat + used = l.have_.toNat ∧ regs.put = inputAdvance l.put made ∧
      regs.left.toNat + made = l.left.toNat ∧
      regs = { l with put := stream.next_out, left := stream.avail_out, next := stream.next_in, have_ := stream.avail_in, hold := state.hold, bits := state.bits } := by
  have actualPost := post
  obtain ⟨used, made, buffered, bytes, msg, mode, bits, hold, usedBound, _, madeBound, size,
    bitCount, held, heapEq, _, _, _⟩ := post
  have privateWindow := callerRange_private_window good buffers.output.range (output.trans e.hnout)
  have unowned : ∀ w, e.s0.window = .ref (.blk w) 0 → e.ob ≠ w := by
    intro w win equal
    exact privateWindow w win (by rw [equal])
  obtain ⟨stream, state, current, _, _, _, _, window⟩ := fastPost_retained e good pending leaves unowned actualPost
  let streamValue := { e.sm0 with next_in := .ref (.blk e.ib) (e.i0 + used), next_out := .ref (.blk e.ob) (e.o0 + made), avail_in := UInt32.ofNat (e.sm0.avail_in.toNat - used), avail_out := UInt32.ofNat (e.sm0.avail_out.toNat - made), msg }
  let stateValue := { e.s0 with mode, bits, hold }
  have stateGet : after.istates e.stid = some stateValue := by rw [heapEq, ZStreamRef.put_istates, upd_same]
  have stateEq : state = stateValue := Option.some.inj (current.live.hs.symm.trans stateGet)
  have baseGet : e.r.get { e.h0 with bytes := upd e.h0.bytes e.ob (some bytes), istates := upd e.h0.istates e.stid (some stateValue) } = some e.sm0 := by
    cases refEq : e.r with
    | tab i => simpa only [refEq, ZStreamRef.get] using e.hsm
    | in_gzstate_strm i => simpa only [refEq, ZStreamRef.get] using e.hsm
  have streamGet : e.r.get after = some streamValue := by rw [heapEq, ZStreamRef.get_put, baseGet]; rfl
  have streamEq : stream = streamValue := Option.some.inj (current.live.hz.symm.trans streamGet)
  subst state
  subst stream
  let regs := { l with put := streamValue.next_out, left := streamValue.avail_out, next := streamValue.next_in, have_ := streamValue.avail_in, hold := stateValue.hold, bits := stateValue.bits }
  have usedLe : used ≤ e.sm0.avail_in.toNat := by omega
  have usedBytes : used ≤ bs.length := by rw [← buffers.bits.have_eq, inputCount]; exact usedLe
  have next : regs.next = inputAdvance l.next used := by rw [input, e.hnin]; rfl
  have put : regs.put = inputAdvance l.put made := by rw [output, e.hnout]; rfl
  have haveCount : regs.have_.toNat + used = l.have_.toNat := by
    change (UInt32.ofNat (e.sm0.avail_in.toNat - used)).toNat + used = _
    rw [UInt32.toNat_ofNat_of_lt' (by simp only [UInt32.size]; have := e.sm0.avail_in.toNat_lt; omega), inputCount]
    omega
  have leftCount : regs.left.toNat + made = l.left.toNat := by
    change (UInt32.ofNat (e.sm0.avail_out.toNat - made)).toNat + made = _
    rw [UInt32.toNat_ofNat_of_lt' (by simp only [UInt32.size]; have := e.sm0.avail_out.toNat_lt; omega), outputCount]
    omega
  have sizes : ByteViewSizes e.h0 after := by
    rw [heapEq]
    have write := byte_view_sizes_put (dest := .blk e.ob) e.hA0 e.hro bytes size
    have step := (write.trans (byte_view_sizes_setI _ e.stid stateValue)).trans
      (byte_view_sizes_stream_put _ e.r streamValue)
    exact step
  have readonly : ∀ ref : BRef, Space.ro after ref = Space.ro e.h0 ref := by
    intro ref
    rw [heapEq]
    cases ref <;> simp only [Space.ro, ZStreamRef.put_ro]
  have inputGet : Space.get after (BRef.blk e.ib) = some e.IN := by
    rw [heapEq]
    simp only [Space.get, ZStreamRef.put_bytes, upd_ne _ _ _ _ different]
    exact e.hIN
  have inputContents : bs = (e.IN.toList.drop e.i0).take bs.length := by
    rcases buffers.bits.next with empty | ⟨ref, array, off, ptr, get, _, contents⟩
    · have : bs.length = 0 := by rw [empty]; rfl
      simp [empty]
    · rw [input, e.hnin] at ptr
      cases ptr
      have same : array = e.IN := Option.some.inj (get.symm.trans e.hIN)
      simpa only [same] using contents
  have finalBits : BitInv after regs (bs.drop used) := by
    refine ⟨by rw [List.length_drop, ← buffers.bits.have_eq]; omega, Or.inr ?_, held⟩
    refine ⟨.blk e.ib, e.IN, e.i0 + used, rfl, inputGet, ?_, ?_⟩
    · rw [List.length_drop, ← buffers.bits.have_eq, inputCount]
      have := e.hINsz
      omega
    · rw [List.length_drop]
      conv => lhs; rw [inputContents, List.drop_take, List.drop_drop]
  refine ⟨used, made, regs, streamValue, stateValue, usedBytes, current,
    buffers.advance_both good current window sizes readonly next haveCount put leftCount rfl finalBits,
    sizes, next, haveCount, put, leftCount, rfl⟩

/-- Unchanged byte views retain the bit-source view and held-bit bound. -/
theorem BitInv.byte_views {h after : Heap} {l : IL} {bs : List UInt8} (inv : BitInv h l bs)
    (views : ∀ ref : BRef, (Space.get after ref : Option (Array UInt8)) = Space.get h ref) :
    BitInv after l bs := by
  refine ⟨inv.have_eq, ?_, inv.hold_lt⟩
  rcases inv.next with empty | ⟨ref, array, off, ptr, get, fit, content⟩
  · exact Or.inl empty
  · exact Or.inr ⟨ref, array, off, ptr, by rw [views]; exact get, fit, content⟩

/-- Pure private writes retain a whole packet on the same local registers. -/
theorem DispatchBuffers.byte_views {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState} {l : IL} {bs : List UInt8}
    (buffers : DispatchBuffers h r l bs) (before : Good h r zs z s)
    (current : Good after r zs stream state) (window : state.window = s.window)
    (views : ∀ ref : BRef, (Space.get after ref : Option (Array UInt8)) = Space.get h ref)
    (readonly : ∀ ref : BRef, Space.ro after ref = Space.ro h ref) : DispatchBuffers after r l bs := by
  simpa only [List.drop_zero] using buffers.consume before current window views readonly
    (regs := l) (used := 0) (by rfl) (by simp only [inputAdvance_zero]) (by omega)
    (by simpa only [List.drop_zero] using buffers.bits.byte_views views)

/-- The real fast LEN call retains the complete scalar/table/buffer packet
for distinct raw input/output blocks. Input and output advances, remaining
counts and normalized bits all come from the actual callee. General caller
views, semantic bit consumption and whole-loop progress remain open. -/
theorem inflate_LEN_fast_raw_buffers {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8} {ib io ob oo : Nat}
    (E : Env c h r zs z s) (good : Good h r zs z s)
    (fit : ZlibF.PlatformMemory.ByteObjectsFit h) (tables : DataTablesSafe h s)
    (buffers : DispatchBuffers h r l bs) (pending : DataPendingInvariant s)
    (input : l.next = .ref (.blk ib) io) (output : l.put = .ref (.blk ob) oo)
    (different : ib ≠ ob) (fast : (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    ∃ used made regs after stream state, used ≤ bs.length ∧
      runX (inflate_LEN c) l h = .ok ((.ok (), regs), after) ∧ Good after r zs stream state ∧
      DataTableInvariant after state ∧ DataPendingInvariant state ∧ DispatchBuffers after r regs (bs.drop used) ∧
      ByteViewSizes h after ∧ regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = inputAdvance l.put made ∧ regs.left.toNat + made = l.left.toNat ∧ regs.bits.toNat < 8 := by
  obtain ⟨entry, heap1, cut, post, _, strmEq, refEq, idEq, stateEq, streamEq, heapEq, outputEq⟩ :=
    inflate_LEN_fast_raw_cut E good fit tables buffers pending input output different fast
  have bitCount : l.bits.toNat < 8 := by
    have margins : (6 ≤ l.have_ ∧ 258 ≤ l.left) ∧ l.bits < 8 := by
      simpa only [Bool.and_eq_true, decide_eq_true_eq] using fast
    simpa [UInt32.lt_iff_toNat_lt] using margins.2
  obtain ⟨good0, pending0, _, sizes0⟩ := leave_restore_invariant E good pending buffers.bits (by omega)
  have views0 : ∀ ref : BRef,
      (Space.get (setI (r.put h (leaveStream z l)) zs (leaveState s l)) ref : Option (Array UInt8)) = Space.get h ref := by
    intro ref
    rw [byte_view_get_setI, byte_view_get_stream_put]
  have packet0 := buffers.byte_views good good0 rfl views0 (by
    intro ref
    rw [byte_view_ro_setI, byte_view_ro_stream_put])
  have entryGood : Good entry.toEnv.h0 entry.toEnv.r entry.toEnv.stid entry.toEnv.sm0 entry.toEnv.s0 := by
    change Good entry.h0 entry.r entry.stid entry.sm0 entry.s0
    rw [heapEq, refEq, idEq, streamEq, stateEq]
    exact good0
  have entryPending : DataPendingInvariant entry.toEnv.s0 := by change DataPendingInvariant entry.s0; rw [stateEq]; exact pending0
  have entryLeaves : ∀ ref offset ca, entry.toEnv.s0.lencode = .ref ref offset → Space.get entry.toEnv.h0 ref = some ca →
      Zlib.Inffast.Spec.LenLeavesPositive ca offset entry.toEnv.s0.lenbits.toNat := by
    change ∀ ref offset ca, entry.s0.lencode = .ref ref offset → Space.get entry.h0 ref = some ca →
      Zlib.Inffast.Spec.LenLeavesPositive ca offset entry.s0.lenbits.toNat
    rw [stateEq, heapEq]
    exact leaveEntry_leaves good.live.hs tables
  have entryPacket : DispatchBuffers entry.toEnv.h0 entry.toEnv.r l bs := by
    change DispatchBuffers entry.h0 entry.r l bs
    rw [heapEq, refEq]
    exact packet0
  have inCursor : l.next = entry.toEnv.sm0.next_in := by change l.next = entry.sm0.next_in; rw [streamEq]; rfl
  have inCount : l.have_ = entry.toEnv.sm0.avail_in := by change l.have_ = entry.sm0.avail_in; rw [streamEq]; rfl
  have outCursor : l.put = entry.toEnv.sm0.next_out := by change l.put = entry.sm0.next_out; rw [streamEq]; rfl
  have outCount : l.left = entry.toEnv.sm0.avail_out := by change l.left = entry.sm0.avail_out; rw [streamEq]; rfl
  obtain ⟨used, made, regs, stream1, state1, usedBound, good1, packet1, sizes1, next, haveCount, put, left, regEq⟩ :=
    fastPost_buffers entry.toEnv entryGood entryPacket entryPending entryLeaves inCursor inCount outCursor outCount post entry.hsep
  have privateWindow := callerRange_private_window good buffers.output.range output
  have unowned : ∀ w, entry.toEnv.s0.window = .ref (.blk w) 0 → entry.toEnv.ob ≠ w := by
    change ∀ w, entry.s0.window = .ref (.blk w) 0 → entry.ob ≠ w
    rw [stateEq, outputEq]
    intro w win equal
    exact privateWindow w win (by rw [equal])
  obtain ⟨stream2, state2, good2, tables2, pending2, held2, bits2, _⟩ :=
    fastPost_retained entry.toEnv entryGood entryPending entryLeaves unowned post
  have sameStream : stream2 = stream1 := Option.some.inj (good2.live.hz.symm.trans good1.live.hz)
  have sameState : state2 = state1 := Option.some.inj (good2.live.hs.symm.trans good1.live.hs)
  subst stream2
  subst state2
  have good1' : Good heap1 r zs stream1 state1 := by
    change Good heap1 entry.r entry.stid stream1 state1 at good1
    simpa only [refEq, idEq] using good1
  have packet1' : DispatchBuffers heap1 r regs (bs.drop used) := by
    change DispatchBuffers heap1 entry.r regs (bs.drop used) at packet1
    simpa only [refEq] using packet1
  have sizeTotal : ByteViewSizes h heap1 := by
    change ByteViewSizes entry.h0 heap1 at sizes1
    rw [heapEq] at sizes1
    exact sizes0.trans sizes1
  have env1 : Env c heap1 r zs stream1 state1 := ⟨E.strm, E.st, good1'.live.hz, good1'.live.hs⟩
  have regBits : regs.bits.toNat < 8 := by rw [regEq]; exact bits2
  by_cases type : state1.mode = TYPE
  · let state3 := { state1 with back := -1 }
    have good3 := good1'.decode_update (after := state3) (by rfl) (by exact good1'.live.mode)
    have pending3 : DataPendingInvariant state3 := by
      apply dataPendingInvariant_idle (s := state3) pending2.sane
      change state1.mode ≠ LENEXT ∧ state1.mode ≠ DIST ∧ state1.mode ≠ DISTEXT ∧ state1.mode ≠ MATCH
      rw [type]; decide
    have tables3 : DataTableInvariant (setI heap1 zs state3) state3 := by
      intro active
      change DataTableMode state1.mode at active
      rw [type] at active
      exact False.elim ((by unfold DataTableMode; decide : ¬ DataTableMode TYPE) active)
    have packet3 := packet1'.byte_views good1' good3 rfl (fun ref => byte_view_get_setI heap1 zs state3 ref)
      (fun ref => byte_view_ro_setI heap1 zs state3 ref)
    refine ⟨used, made, regs, _, stream1, state3, usedBound, ?_, good3, tables3, pending3, packet3,
      sizeTotal.trans (byte_view_sizes_setI _ zs state3), next, haveCount, put, left, regBits⟩
    rw [cut, inflateAfterFast_run env1, regEq]
    simp only [state3, type, ↓reduceIte]
  · refine ⟨used, made, regs, heap1, stream1, state1, usedBound, ?_, good1', tables2, pending2,
      packet1', sizeTotal, next, haveCount, put, left, regBits⟩
    rw [cut, inflateAfterFast_run env1, regEq]
    simp only [type, ↓reduceIte]

/-- The LEN_ fall-through establishes LEN before the same actual fast call. -/
theorem inflate_LEN_start_fast_raw_buffers {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8} {ib io ob oo : Nat}
    (E : Env c h r zs z s) (good : Good h r zs z s)
    (fit : ZlibF.PlatformMemory.ByteObjectsFit h) (tables : DataTablesSafe h s)
    (buffers : DispatchBuffers h r l bs) (pending : DataPendingInvariant s)
    (input : l.next = .ref (.blk ib) io) (output : l.put = .ref (.blk ob) oo)
    (different : ib ≠ ob) (fast : (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    ∃ used made regs after stream state, used ≤ bs.length ∧
      runX (inflate_LEN_ c) l h = .ok ((.ok (), regs), after) ∧ Good after r zs stream state ∧
      DataTableInvariant after state ∧ DataPendingInvariant state ∧ DispatchBuffers after r regs (bs.drop used) ∧
      ByteViewSizes h after ∧ regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = inputAdvance l.put made ∧ regs.left.toNat + made = l.left.toNat ∧ regs.bits.toNat < 8 := by
  let state0 := { s with mode := LEN }
  let heap0 := setI h zs state0
  have good0 : Good heap0 r zs z state0 := good.decode_update (by rfl)
    (by change HEAD ≤ LEN ∧ LEN ≤ SYNC; decide)
  have env0 : Env c heap0 r zs z state0 := ⟨E.strm, E.st, good0.live.hz, good0.live.hs⟩
  have tables0 : DataTablesSafe heap0 state0 := tables.decode_update good.live.hs (by rfl)
  have pending0 : DataPendingInvariant state0 := by
    apply dataPendingInvariant_idle (s := state0) pending.sane
    change LEN ≠ LENEXT ∧ LEN ≠ DIST ∧ LEN ≠ DISTEXT ∧ LEN ≠ MATCH
    decide
  have packet0 := buffers.byte_views good good0 rfl (fun ref => byte_view_get_setI h zs state0 ref)
    (fun ref => byte_view_ro_setI h zs state0 ref)
  have sizes0 := byte_view_sizes_setI h zs state0
  have fit0 := sizes0.platform fit
  obtain ⟨used, made, regs, after, stream, state, usedBound, run, nextGood, nextTables,
    nextPending, nextPacket, sizes, next, haveCount, put, left, bitCount⟩ :=
    inflate_LEN_fast_raw_buffers env0 good0 fit0 tables0 packet0 pending0 input output different fast
  refine ⟨used, made, regs, after, stream, state, usedBound, ?_, nextGood, nextTables,
    nextPending, nextPacket, sizes0.trans sizes, next, haveCount, put, left, bitCount⟩
  unfold inflate_LEN_
  rw [runX_bind, runX_setMode E]
  exact run

end Zlib.Inflate.Proofs
