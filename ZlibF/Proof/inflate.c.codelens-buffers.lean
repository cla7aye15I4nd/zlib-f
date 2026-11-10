import ZlibF.Proof.«inflate.c.codelens-dispatch»
import ZlibF.Proof.«inflate.c.dispatch-rank»
import ZlibF.Proof.«inflate.c.header-default»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The complete actual code-length reading loop retains the same public
buffer packet, exact input cursor and held-bit budget. Its only heap
writes are the state prefix and an optional error message. -/
theorem clRead_buffers {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (good : Good h r zs z s) (pending : DataPendingInvariant s)
    (codes : CodeLengthInvariant zs s) (buffers : DispatchBuffers h r l bs) (mode : s.mode = CODELENS) :
    ∃ outcome regs after stream state used, used ≤ bs.length ∧
      runX (clRead c) l h = .ok ((outcome, regs), after) ∧
      Good after r zs stream state ∧ DataTableInvariant after state ∧ DataPendingInvariant state ∧
      CodeLengthInvariant zs state ∧ DispatchBuffers after r regs (bs.drop used) ∧
      ByteViewSizes h after ∧ regs.next = inputAdvance l.next used ∧
      regs.have_.toNat + used = l.have_.toNat ∧ regs.put = l.put ∧ regs.left = l.left ∧
      regs.out_ = l.out_ ∧ regs.bits.toNat ≤ max l.bits.toNat 21 ∧
      regs.bits.toNat ≤ l.bits.toNat + 8 * used ∧ after.static = h.static ∧
      state = { s with lens := state.lens, «have» := state.«have», mode := state.mode } ∧
      (state.mode = CODELENS ∨ state.mode = BAD) ∧
      (outcome = .ok () → state.mode = BAD ∨ state.«have».toNat = s.nlen.toNat + s.ndist.toNat) := by
  obtain ⟨outcome, regs, after, state, stream, run, current, nextCodes, tables, result⟩ :=
    clRead_run_good E.strm E.st good mode codes buffers.bits
  obtain ⟨outcome2, regs2, after2, run2, full, used, bound, inv, cursor, budget⟩ :=
    clRead_run_full_cursor E.strm E.st E.hz E.hs good.inv.wf.1 mode codes buffers.bits
  rw [run] at run2
  cases run2
  obtain ⟨readState, _, stateGet, _, _, regFrame, bitBound, stateFrame, _, _, _, modes, complete⟩ := result
  have same : readState = state := Option.some.inj (stateGet.symm.trans current.live.hs)
  subst readState
  obtain ⟨stream2, streamGet, streamFrame, heapState, heapEq⟩ := full.2
  have streamEq : stream2 = stream := Option.some.inj (streamGet.symm.trans current.live.hz)
  subst stream2
  have heapStateEq : heapState = state := by
    have get : after.istates zs = some heapState := by rw [heapEq]; simp
    exact Option.some.inj (get.symm.trans current.live.hs)
  subst heapState
  have views : ∀ ref : BRef, Space.get after ref = Space.get h ref := by
    intro ref
    rw [heapEq, byte_view_get_setI, byte_view_get_stream_put]
  have readonly : ∀ ref : BRef, Space.ro after ref = Space.ro h ref := by
    intro ref
    rw [heapEq, byte_view_ro_setI, byte_view_ro_stream_put]
  have sizes : ByteViewSizes h after := by intro ref; rw [views]
  have count : regs.have_.toNat + used = l.have_.toNat := by
    rw [inv.have_eq, buffers.bits.have_eq, List.length_drop]
    omega
  have nextPending : DataPendingInvariant state := by
    apply dataPendingInvariant_idle (by rw [stateFrame]; exact pending.sane)
    rcases modes with normal | normal <;> rw [normal] <;> decide
  have packet : DispatchBuffers after r regs (bs.drop used) :=
    buffers.advance_both good current (by rw [stateFrame]) sizes readonly cursor count
      (made := 0) (by rw [regFrame, inputAdvance_zero]) (by rw [regFrame]; rfl)
      (by rw [regFrame]) inv
  exact ⟨outcome, regs, after, stream, state, used, bound, run, current, tables, nextPending,
    nextCodes, packet, sizes, cursor, count, by rw [regFrame], by rw [regFrame],
    by rw [regFrame], bitBound, budget, by rw [heapEq]; simp only [setI, ZStreamRef.put_static],
    stateFrame, modes, complete⟩


/-- Constructor metadata writes preserve public byte views and buffers.
The exact heap relation is produced by the actual two table constructors. -/
theorem ClTablesUpdate.buffers {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState} {l : IL} {bs : List UInt8}
    (before : Good h r zs z s) (current : Good after r zs stream state)
    (buffers : DispatchBuffers h r l bs)
    (update : ClTablesUpdate h r zs z s after stream state) (ret : Int32) :
    DispatchBuffers after r { l with ret := ret } bs ∧ ByteViewSizes h after ∧ after.static = h.static := by
  obtain ⟨heapEq, _, frame⟩ := update
  have views : ∀ ref : BRef, Space.get after ref = Space.get h ref := by
    intro ref
    rw [heapEq, byte_view_get_setI, byte_view_get_stream_put]
  have readonly : ∀ ref : BRef, Space.ro after ref = Space.ro h ref := by
    intro ref
    rw [heapEq, byte_view_ro_setI, byte_view_ro_stream_put]
  have sizes : ByteViewSizes h after := by intro ref; rw [views]
  have inv : BitInv after { l with ret := ret } bs :=
    ⟨buffers.bits.have_eq, (buffers.bits.byte_views views).next, buffers.bits.hold_lt⟩
  refine ⟨?_, sizes, by rw [heapEq]; simp only [setI, ZStreamRef.put_static]⟩
  simpa only [List.drop_zero] using buffers.advance_both before current (by rw [frame]) sizes readonly
    (regs := { l with ret := ret }) (used := 0) (made := 0)
    (inputAdvance_zero l.next).symm (by rfl) (inputAdvance_zero l.put).symm (by rfl) rfl
    (by simpa only [List.drop_zero] using inv)

/-- Both actual dynamic table calls retain the complete packet. Refusals
stop at BAD; successful installation reaches the actual LEN_ continuation
or the documented Z_TREES exit, with no callee contract assumed. -/
theorem clTables_buffers {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8}
    (E : Env c h r zs z s) (good : Good h r zs z s) (pending : DataPendingInvariant s)
    (buffers : DispatchBuffers h r l bs)
    (pointer : s.lencode = .ref (.istate_codes zs) 0)
    (nlen : s.nlen.toNat ≤ 286) (ndist : s.ndist.toNat ≤ 30)
    (lengths : ∀ k, k < s.nlen.toNat + s.ndist.toNat → (s.lens.getD k 0).toNat ≤ 15) :
    (∃ ret after stream state,
      runX (clTables c) l h = .ok ((.ok (), { l with ret := ret }), after) ∧
      Good after r zs stream state ∧ state.mode = BAD ∧ DataTableInvariant after state ∧
      DataPendingInvariant state ∧ DispatchBuffers after r { l with ret := ret } bs ∧
      ByteViewSizes h after ∧ after.static = h.static ∧ ClTablesUpdate h r zs z s after stream state) ∨
    (∃ after state,
      Good after r zs z state ∧ state.mode = LEN_ ∧ DataTableInvariant after state ∧
      DataPendingInvariant state ∧ DispatchBuffers after r { l with ret := 0 } bs ∧
      ByteViewSizes h after ∧ after.static = h.static ∧
      (runX (clTables c) l h =
        if c.flush = Z_TREES then .ok ((.error Ex.leave, { l with ret := 0 }), after)
        else runX (inflate_LEN_ c) { l with ret := 0 } after) ∧ ClTablesUpdate h r zs z s after z state) := by
  rcases clTables_run_good_full E.strm E.st good pointer nlen ndist lengths buffers.bits with bad | ready
  · obtain ⟨ret, after, stream, state, run, current, mode, tables, _, update⟩ := bad
    obtain ⟨packet, sizes, static⟩ := update.buffers good current buffers ret
    have nextPending : DataPendingInvariant state := by
      apply dataPendingInvariant_idle (by rw [update.2.2]; exact pending.sane)
      rw [mode]
      decide
    exact Or.inl ⟨ret, after, stream, state, run, current, mode, tables, nextPending, packet, sizes, static, update⟩
  · obtain ⟨after, state, current, mode, tables, _, run, update⟩ := ready
    obtain ⟨packet, sizes, static⟩ := update.buffers good current buffers 0
    have nextPending : DataPendingInvariant state := by
      apply dataPendingInvariant_idle (by rw [update.2.2]; exact pending.sane)
      rw [mode]
      decide
    exact Or.inr ⟨after, state, current, mode, tables, nextPending, packet, sizes, static, run, update⟩


/-- The real end-of-block check and both table constructors retain the
same buffer packet before the actual LEN_ continuation. -/
theorem clTail_buffers {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8}
    (E : Env c h r zs z s) (good : Good h r zs z s) (pending : DataPendingInvariant s)
    (buffers : DispatchBuffers h r l bs) (modes : s.mode = BAD ∨ s.mode = CODELENS)
    (codes : CodeLengthInvariant zs s)
    (done : s.mode = CODELENS → s.«have».toNat = s.nlen.toNat + s.ndist.toNat) :
    (∃ ret after stream state,
      runX (clTail c) l h = .ok ((.ok (), { l with ret := ret }), after) ∧
      Good after r zs stream state ∧ state.mode = BAD ∧ DataTableInvariant after state ∧
      DataPendingInvariant state ∧ DispatchBuffers after r { l with ret := ret } bs ∧
      ByteViewSizes h after ∧ after.static = h.static ∧ ClTablesUpdate h r zs z s after stream state) ∨
    (∃ after state,
      Good after r zs z state ∧ state.mode = LEN_ ∧ DataTableInvariant after state ∧
      DataPendingInvariant state ∧ DispatchBuffers after r { l with ret := 0 } bs ∧
      ByteViewSizes h after ∧ after.static = h.static ∧
      (runX (clTail c) l h =
        if c.flush = Z_TREES then .ok ((.error Ex.leave, { l with ret := 0 }), after)
        else runX (inflate_LEN_ c) { l with ret := 0 } after) ∧ ClTablesUpdate h r zs z s after z state) := by
  have self : { l with ret := l.ret } = l := by cases l; rfl
  have modeRead : rdS c.st (·.mode) h = .ok (s.mode, h) := by rw [E.st, rdI_eq, E.hs]
  by_cases bad : s.mode = BAD
  · have update : ClTablesUpdate h r zs z s h z s := by
      refine ⟨?_, rfl, ?_⟩
      · rw [ZStreamRef.put_self E.hz, tcSetI_same E.hs]
      · rfl
    refine Or.inl ⟨l.ret, h, z, s, ?_, good, bad, ?_, pending,
      by simpa only [self] using buffers, ByteViewSizes.refl h, rfl, update⟩
    · simp [clTail, runX_bind, runX_lift_ok modeRead, bad, runX_pure, self]
    · intro active
      rw [bad] at active
      exact False.elim ((by unfold DataTableMode; decide : ¬ DataTableMode BAD) active)
  · have mode : s.mode = CODELENS := modes.resolve_left bad
    obtain ⟨pointer, _, nlen, ndist, _, initialized⟩ := codes mode
    have lengths : ∀ k, k < s.nlen.toNat + s.ndist.toNat → (s.lens.getD k 0).toNat ≤ 15 := by
      rw [← done mode]
      exact initialized
    have inside : 0 + 256 < s.lens.size := by rw [good.inv.wf.1]; decide
    have read := Ptr.index_ok (off := 0) (i := 256) (WRef.get_istate_lens E.hs) inside
    let value : UInt16 := s.lens[0 + 256]
    have read' : Ptr.index (lensP c.st) 256 h = .ok (value, h) := by rw [E.st]; exact read
    have tailRun : runX (clTail c) l h =
        if value = 0 then runX (do badMode c "invalid code -- missing end-of-block"; pure ()) l h
        else runX (clTables c) l h := by
      by_cases zero : value = 0 <;>
        simp [clTail, runX_bind, runX_lift_ok modeRead, bad, runX_lift_ok read', zero]
    by_cases zero : value = 0
    · obtain ⟨i, _, run⟩ := tcBadMode_run (c := c) "invalid code -- missing end-of-block"
        lit_missing_eob E.strm E.st E.hz E.hs
      obtain ⟨current, tables, nextPending, packet, sizes, static⟩ :=
        head_bad_packet good pending buffers buffers.bits (by rfl) i
      refine Or.inl ⟨l.ret, tcBadHeap h r zs z s i, { z with msg := .ref (.str i) 0 },
        { s with mode := BAD }, ?_, current, rfl, tables, nextPending,
        by rw [self]; exact packet, sizes, static, ?_⟩
      · rw [tailRun, if_pos zero]
        simpa [runX_bind, runX_lift_ok run, runX_pure, self]
      · exact ⟨rfl, rfl, by rfl⟩
    · have tables := clTables_buffers E good pending buffers pointer nlen ndist lengths
      rw [tailRun, if_neg zero]
      exact tables

end Zlib.Inflate.Proofs
