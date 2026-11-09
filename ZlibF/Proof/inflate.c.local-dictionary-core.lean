import ZlibF.Proof.«inflate.c.local-stored-state»
import ZlibF.Proof.«inflate.c.dictionary-default-state»

/-! Actual decoder execution with local allocation uniqueness. -/
namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inffast.Spec ZlibF.Spec.Public
set_option autoImplicit false
set_option maxRecDepth 8192

theorem inflate_DICT_wait_boundary {c : Ctx} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (good : LocalGood h cutoff r zs z s) (pending : DataPendingInvariant s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = DICT)
    (missing : s.havedict = 0) (bitsBound : l.bits.toNat ≤ 39) :
    let stream := dictWaitStream z l
    let state := leaveState s l
    let after := setI (r.put h stream) zs state
    runX (inflate_DICT c) l h = .ok ((.error (Ex.ret Z_NEED_DICT), l), after) ∧
      LocalGood after cutoff r zs stream state ∧ DataTableInvariant after state ∧ DataPendingInvariant state ∧
      DispatchBuffers after r l bs ∧ ByteViewSizes h after ∧ after.static = h.static ∧
      state.hold.toNat < 2 ^ state.bits.toNat ∧
      stream.total_out = z.total_out ∧ state.total = s.total := by
  dsimp only
  let stream := dictWaitStream z l
  let state := leaveState s l
  let after := setI (r.put h stream) zs state
  have nextGood : LocalGood after cutoff r zs stream state :=
    good.setZI rfl good.live.zalloc good.live.zfree rfl good.live.mode
      (good.inv.of_fields rfl rfl rfl rfl rfl rfl rfl rfl rfl bitsBound rfl rfl rfl)
  have views : ∀ ref : BRef, (Space.get after ref : Option (Array UInt8)) = Space.get h ref := by
    intro ref
    rw [byte_view_get_setI, byte_view_get_stream_put]
  have readonly : ∀ ref : BRef, Space.ro after ref = Space.ro h ref := by
    intro ref
    rw [byte_view_ro_setI, byte_view_ro_stream_put]
  have nextPending : DataPendingInvariant state :=
    ⟨pending.sane, pending.lenext, pending.dist, pending.distext, pending.matching⟩
  exact ⟨inflate_DICT_wait_run E l missing, nextGood,
    dataTableInvariant_inactive (by change ¬ DataTableMode s.mode; rw [mode]; unfold DataTableMode; decide),
    nextPending, dispatch_byte_views_local buffers good nextGood rfl views readonly,
    by intro ref; rw [views], by simp only [after, setI, ZStreamRef.put_static], buffers.bits.hold_lt, rfl, rfl⟩

theorem inflate_DICT_ready_boundary {c : Ctx} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (good : LocalGood h cutoff r zs z s) (pending : DataPendingInvariant s)
    (buffers : DispatchBuffers h r l bs) (globals : LibraryGlobals h)
    (present : s.havedict ≠ 0) :
    ∃ (outcome : Except Ex Unit) (regs : IL) (after : Heap) (stream : ZStream)
      (state : InflateState) (used consumed : Nat), used ≤ bs.length ∧
      runX (inflate_DICT c) l h = .ok ((outcome, regs), after) ∧
      LocalGood after cutoff r zs stream state ∧ DataTableInvariant after state ∧ DataPendingInvariant state ∧
      DispatchBuffers after r regs (bs.drop used) ∧ ByteViewSizes h after ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = l.put ∧ regs.left = l.left ∧
      regs.bits.toNat + consumed = l.bits.toNat + 8 * used ∧
      regs.bits.toNat ≤ max l.bits.toNat 10 ∧ after.static = h.static ∧
      BlockHeaderFrame { s with check := 1, mode := TYPE } state ∧ HeaderStreamFrame { z with adler := 1 } stream ∧
      (outcome = .ok () ∨ outcome = .error Ex.leave) ∧
      (s.last = 0 → outcome = .ok () → consumed = 3) := by
  let ready := { s with check := 1, mode := TYPE }
  let stream0 := { z with adler := 1 }
  let heap0 := setI (r.put h stream0) zs ready
  have good0 : LocalGood heap0 cutoff r zs stream0 ready :=
    good.setZI rfl good.live.zalloc good.live.zfree rfl (by change HEAD ≤ TYPE ∧ TYPE ≤ SYNC; decide)
      (good.inv.of_fields rfl rfl rfl rfl rfl rfl rfl rfl rfl good.inv.bits rfl rfl rfl)
  have views : ∀ ref : BRef, (Space.get heap0 ref : Option (Array UInt8)) = Space.get h ref := by
    intro ref
    rw [byte_view_get_setI, byte_view_get_stream_put]
  have readonly : ∀ ref : BRef, Space.ro heap0 ref = Space.ro h ref := by
    intro ref
    rw [byte_view_ro_setI, byte_view_ro_stream_put]
  have sizes0 : ByteViewSizes h heap0 := by intro ref; rw [views]
  have static0 : heap0.static = h.static := by simp only [heap0, setI, ZStreamRef.put_static]
  have globals0 : LibraryGlobals heap0 := by change heap0.static = _; rw [static0]; exact globals
  have E0 : Env c heap0 r zs stream0 ready := ⟨E.strm, E.st, good0.live.hz, good0.live.hs⟩
  have pending0 : DataPendingInvariant ready := by
    apply dataPendingInvariant_idle (s := ready) (by exact pending.sane)
    change TYPE ≠ LENEXT ∧ TYPE ≠ DIST ∧ TYPE ≠ DISTEXT ∧ TYPE ≠ MATCH
    decide
  have packet0 := dispatch_byte_views_local buffers good good0 rfl views readonly
  obtain ⟨outcome, regs, after, stream, state, used, consumed, bound, run, current, tables,
    nextPending, packet, sizes, cursor, count, put, left, bitCount, bitBound, static, frame,
    streamFrame, kinds, progress⟩ := inflate_TYPE_boundary E0 good0 pending0 packet0 globals0 rfl
  exact ⟨outcome, regs, after, stream, state, used, consumed, bound,
    (inflate_DICT_ready_cut E l present).trans run, current, tables, nextPending, packet,
    sizes0.trans sizes, cursor, count, put, left, bitCount, bitBound, static.trans static0, frame, streamFrame, kinds, progress⟩

theorem inflate_DICT_ready_rank {c : Ctx} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (good : LocalGood h cutoff r zs z s) (pending : DataPendingInvariant s)
    (buffers : DispatchBuffers h r l bs) (globals : LibraryGlobals h)
    (mode : s.mode = DICT) (present : s.havedict ≠ 0) (incoming : l.bits.toNat ≤ 39) :
    ∃ outcome regs after stream state used, used ≤ bs.length ∧
      runX (inflate_DICT c) l h = .ok ((outcome, regs), after) ∧
      LocalGood after cutoff r zs stream state ∧ DataTableInvariant after state ∧ DataPendingInvariant state ∧
      DispatchBuffers after r regs (bs.drop used) ∧ ByteViewSizes h after ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = l.put ∧ regs.left = l.left ∧ regs.bits.toNat ≤ 39 ∧ after.static = h.static ∧
      BlockHeaderFrame { s with check := 1, mode := TYPE } state ∧ HeaderStreamFrame { z with adler := 1 } stream ∧
      (outcome = .error Ex.leave ∨ (outcome = .ok () ∧ dispatchRank regs state.mode < dispatchRank l s.mode)) := by
  let ready := { s with check := 1, mode := TYPE }
  let stream0 := { z with adler := 1 }
  let heap0 := setI (r.put h stream0) zs ready
  have good0 : LocalGood heap0 cutoff r zs stream0 ready :=
    good.setZI rfl good.live.zalloc good.live.zfree rfl (by change HEAD ≤ TYPE ∧ TYPE ≤ SYNC; decide)
      (good.inv.of_fields rfl rfl rfl rfl rfl rfl rfl rfl rfl good.inv.bits rfl rfl rfl)
  have views : ∀ ref : BRef, (Space.get heap0 ref : Option (Array UInt8)) = Space.get h ref := by
    intro ref
    rw [byte_view_get_setI, byte_view_get_stream_put]
  have readonly : ∀ ref : BRef, Space.ro heap0 ref = Space.ro h ref := by
    intro ref
    rw [byte_view_ro_setI, byte_view_ro_stream_put]
  have sizes0 : ByteViewSizes h heap0 := by intro ref; rw [views]
  have static0 : heap0.static = h.static := by simp only [heap0, setI, ZStreamRef.put_static]
  have globals0 : LibraryGlobals heap0 := by change heap0.static = _; rw [static0]; exact globals
  have E0 : Env c heap0 r zs stream0 ready := ⟨E.strm, E.st, good0.live.hz, good0.live.hs⟩
  have pending0 : DataPendingInvariant ready := by
    apply dataPendingInvariant_idle (s := ready) (by exact pending.sane)
    change TYPE ≠ LENEXT ∧ TYPE ≠ DIST ∧ TYPE ≠ DISTEXT ∧ TYPE ≠ MATCH
    decide
  have packet0 := dispatch_byte_views_local buffers good good0 rfl views readonly
  obtain ⟨outcome, regs, after, stream, state, used, bound, run, current, tables, nextPending,
    packet, sizes, next, count, put, left, bits, static, frame, streamFrame, kinds⟩ :=
    inflate_TYPE_rank E0 good0 pending0 packet0 globals0 rfl incoming
  have before : dispatchRank l ready.mode < dispatchRank l s.mode := by
    change dispatchRank l TYPE < dispatchRank l s.mode
    rw [mode]
    have credit : dispatchCredit TYPE < dispatchCredit DICT := by decide
    unfold dispatchRank
    omega
  refine ⟨outcome, regs, after, stream, state, used, bound,
    (inflate_DICT_ready_cut E l present).trans run, current, tables, nextPending, packet,
    sizes0.trans sizes, next, count, put, left, bits, static.trans static0, frame, streamFrame, ?_⟩
  rcases kinds with wait | ⟨normal, decreases⟩
  · exact Or.inl wait
  · exact Or.inr ⟨normal, Nat.lt_trans decreases before⟩

theorem inflate_DICT_rank {c : Ctx} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (good : LocalGood h cutoff r zs z s) (pending : DataPendingInvariant s)
    (buffers : DispatchBuffers h r l bs) (globals : LibraryGlobals h)
    (mode : s.mode = DICT) (incoming : l.bits.toNat ≤ 39) :
    ∃ outcome regs after stream state used, used ≤ bs.length ∧
      runX (inflate_DICT c) l h = .ok ((outcome, regs), after) ∧
      LocalGood after cutoff r zs stream state ∧ DataTableInvariant after state ∧ DataPendingInvariant state ∧
      DispatchBuffers after r regs (bs.drop used) ∧ ByteViewSizes h after ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = l.put ∧ regs.left = l.left ∧ regs.bits.toNat ≤ 39 ∧ after.static = h.static ∧
      (outcome = .error (Ex.ret Z_NEED_DICT) ∨ outcome = .error Ex.leave ∨ (outcome = .ok () ∧ dispatchRank regs state.mode < dispatchRank l s.mode)) := by
  by_cases missing : s.havedict = 0
  · obtain ⟨run, current, tables, nextPending, packet, sizes, static, _, _, _⟩ :=
      inflate_DICT_wait_boundary E good pending buffers mode missing incoming
    exact ⟨.error (Ex.ret Z_NEED_DICT), l, setI (r.put h (dictWaitStream z l)) zs (leaveState s l),
      dictWaitStream z l, leaveState s l, 0, by omega, run, current, tables, nextPending,
      by simpa only [List.drop_zero] using packet, sizes, (inputAdvance_zero l.next).symm,
      by rfl, rfl, rfl, incoming, static, Or.inl rfl⟩
  · obtain ⟨outcome, regs, after, stream, state, used, bound, run, current, tables, nextPending,
      packet, sizes, next, count, put, left, bits, static, _, _, kinds⟩ :=
      inflate_DICT_ready_rank E good pending buffers globals mode missing incoming
    exact ⟨outcome, regs, after, stream, state, used, bound, run, current, tables, nextPending,
      packet, sizes, next, count, put, left, bits, static, Or.inr kinds⟩

theorem inflate_DICTID_rank {c : Ctx} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (good : LocalGood h cutoff r zs z s) (pending : DataPendingInvariant s)
    (buffers : DispatchBuffers h r l bs) (globals : LibraryGlobals h)
    (mode : s.mode = DICTID) (incoming : l.bits.toNat ≤ 39) :
    ∃ outcome regs after stream state used, used ≤ bs.length ∧
      runX (inflate_DICTID c) l h = .ok ((outcome, regs), after) ∧
      LocalGood after cutoff r zs stream state ∧ DataTableInvariant after state ∧ DataPendingInvariant state ∧
      DispatchBuffers after r regs (bs.drop used) ∧ ByteViewSizes h after ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = l.put ∧ regs.left = l.left ∧ regs.bits.toNat ≤ 39 ∧ after.static = h.static ∧
      (outcome = .error (Ex.ret Z_NEED_DICT) ∨ outcome = .error Ex.leave ∨
        (outcome = .ok () ∧ dispatchRank regs state.mode < dispatchRank l s.mode)) := by
  obtain ⟨outcome, current, used, pull, usedBound, bitInv, _, _, shape,
    bitBound, _, _, _, kinds, cursor⟩ := NEEDBITS_run_cursor buffers.bits 32 (by decide)
  change current.bits.toNat ≤ max l.bits.toNat 39 at bitBound
  have count : current.have_.toNat + used = l.have_.toNat := by
    rw [bitInv.have_eq, buffers.bits.have_eq, List.length_drop]
    omega
  have put : current.put = l.put := by rw [shape]
  have left : current.left = l.left := by rw [shape]
  have packet : DispatchBuffers h r current (bs.drop used) :=
    dispatch_consume_local buffers good good rfl (fun _ => rfl) (fun _ => rfl) (by rw [shape]; rfl) cursor usedBound bitInv
  rcases kinds with normal | wait
  · rw [normal] at pull
    let value := ZSWAP32 current.hold
    let ready := { s with check := value, mode := DICT }
    let stream0 := { z with adler := value }
    let heap0 := setI (r.put h stream0) zs ready
    let first := { current with hold := 0, bits := 0 }
    have good0 : LocalGood heap0 cutoff r zs stream0 ready :=
      good.setZI rfl good.live.zalloc good.live.zfree rfl (by change HEAD ≤ DICT ∧ DICT ≤ SYNC; decide)
        (good.inv.of_fields rfl rfl rfl rfl rfl rfl rfl rfl rfl good.inv.bits rfl rfl rfl)
    have E0 : Env c heap0 r zs stream0 ready := ⟨E.strm, E.st, good0.live.hz, good0.live.hs⟩
    have pending0 : DataPendingInvariant ready := by
      apply dataPendingInvariant_idle (s := ready) (by exact pending.sane)
      change DICT ≠ LENEXT ∧ DICT ≠ DIST ∧ DICT ≠ DISTEXT ∧ DICT ≠ MATCH
      decide
    have inv0 : BitInv heap0 first (bs.drop used) := by
      have inv := (INITBITS_inv bitInv).1
      apply inv.byte_views
      intro ref
      rw [byte_view_get_setI, byte_view_get_stream_put]
    have packet0 : DispatchBuffers heap0 r first (bs.drop used) :=
      dispatch_consume_local buffers good good0 rfl (fun ref => by rw [byte_view_get_setI, byte_view_get_stream_put])
        (fun ref => by rw [byte_view_ro_setI, byte_view_ro_stream_put])
        (by dsimp only [first]; rw [shape]; rfl) cursor usedBound inv0
    have sizes0 : ByteViewSizes h heap0 := by
      intro ref
      rw [byte_view_get_setI, byte_view_get_stream_put]
    have static0 : heap0.static = h.static := by simp only [heap0, setI, ZStreamRef.put_static]
    have globals0 : LibraryGlobals heap0 := by change heap0.static = _; rw [static0]; exact globals
    obtain ⟨exit, regs, after, stream, state, used2, bound2, run, currentGood, tables, nextPending,
      nextPacket, sizes, next2, count2, put2, left2, bits, static, exits⟩ :=
      inflate_DICT_rank E0 good0 pending0 packet0 globals0 rfl (by change 0 ≤ 39; decide)
    have before : dispatchRank first ready.mode < dispatchRank l s.mode := by
      apply dispatchRank_advance (l := l) (regs := first) (used := used) (made := 0) count
      · change current.left.toNat + 0 = l.left.toNat
        rw [left]
        rfl
      · change 0 ≤ _
        omega
      · right
        change dispatchCredit DICT < dispatchCredit s.mode
        rw [mode]
        decide
    have totalBound : used + used2 ≤ bs.length := by rw [List.length_drop] at bound2; omega
    refine ⟨exit, regs, after, stream, state, used + used2, totalBound,
      (inflate_DICTID_parsed_cut E l current pull).trans run, currentGood, tables, nextPending,
      ?_, sizes0.trans sizes, ?_, ?_, ?_, ?_, bits, static.trans static0, ?_⟩
    · simpa only [List.drop_drop] using nextPacket
    · rw [next2]
      change inputAdvance current.next used2 = _
      rw [cursor, inputAdvance_add]
    · change regs.have_.toNat + used2 = current.have_.toNat at count2
      omega
    · exact put2.trans put
    · exact left2.trans left
    · rcases exits with needed | wait | ⟨normal, decreases⟩
      · exact Or.inl needed
      · exact Or.inr (Or.inl wait)
      · exact Or.inr (Or.inr ⟨normal, Nat.lt_trans decreases before⟩)
  · have run := inflate_DICTID_wait (c := c) (by rwa [wait] at pull)
    exact ⟨.error Ex.leave, current, h, z, s, used, usedBound, run, good,
      dataTableInvariant_inactive (by rw [mode]; unfold DataTableMode; decide), pending,
      packet, ByteViewSizes.refl h, cursor, count, put, left, by omega, rfl, Or.inr (Or.inl rfl)⟩

theorem inflate_dispatch_terminal_boundary {c : Ctx} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (good : LocalGood h cutoff r zs z s) (pending : DataPendingInvariant s)
    (buffers : DispatchBuffers h r l bs) (mode : TerminalMode s.mode) :
    runX (inflate_dispatch c) l h = .ok ((terminalExit s.mode, terminalRegs s.mode l), h) ∧
      LocalGood h cutoff r zs z s ∧ DataTableInvariant h s ∧ DataPendingInvariant s ∧
      DispatchBuffers h r (terminalRegs s.mode l) bs ∧
      (terminalRegs s.mode l).bits = l.bits ∧ (terminalRegs s.mode l).hold = l.hold := by
  have frame : ∀ field, terminalRegs s.mode l = field →
      field.next = l.next ∧ field.have_ = l.have_ ∧ field.put = l.put ∧ field.left = l.left ∧
      field.out_ = l.out_ ∧ field.bits = l.bits ∧ field.hold = l.hold := by
    intro field equal
    subst field
    unfold terminalRegs
    split
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨next, haveCount, put, left, out, bits, hold⟩ := frame (terminalRegs s.mode l) rfl
  have inv : BitInv h (terminalRegs s.mode l) bs := by
    refine ⟨by rw [haveCount]; exact buffers.bits.have_eq, ?_, ?_⟩
    · rw [next]
      exact buffers.bits.next
    · rw [hold, bits]
      exact buffers.bits.hold_lt
  have packet : DispatchBuffers h r (terminalRegs s.mode l) bs := by
    simpa only [List.drop_zero] using dispatch_advance_both_local buffers good good rfl (ByteViewSizes.refl h)
      (fun _ => rfl) (regs := terminalRegs s.mode l) (used := 0) (made := 0)
      (by rw [next, inputAdvance_zero]) (by rw [haveCount]; rfl)
      (by rw [put, inputAdvance_zero]) (by rw [left]; rfl) out
      (by simpa only [List.drop_zero] using inv)
  have tables : DataTableInvariant h s := by
    apply dataTableInvariant_inactive
    rcases mode with mode | mode | mode | mode <;> rw [mode] <;> unfold DataTableMode <;> decide
  exact ⟨inflate_dispatch_terminal_run E l mode, good, tables, pending, packet, bits, hold⟩

#print axioms inflate_DICT_wait_boundary
#print axioms inflate_DICT_ready_boundary
#print axioms inflate_DICT_ready_rank
#print axioms inflate_DICT_rank
#print axioms inflate_DICTID_rank
#print axioms inflate_dispatch_terminal_boundary
end Zlib.Inflate.Local
