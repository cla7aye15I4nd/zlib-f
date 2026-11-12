import ZlibF.Proof.«inflate.c.default-invariant»
import ZlibF.Proof.«inflate.c.codelens-buffers»
import ZlibF.Proof.«inflate.c.lenlens-input»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The complete actual CODELENS reading loop preserves every clause of
J, including partial input and malformed repeats. Its exact input trace
is retained for subsequent dispatch composition. -/
theorem clRead_default_J_complete {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultDecodeJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = CODELENS) :
    ∃ outcome regs after stream state used, used ≤ bs.length ∧
      runX (clRead c) l h = .ok ((outcome, regs), after) ∧ DefaultDecodeJ after r zs stream state ∧
      DispatchBuffers after r regs (bs.drop used) ∧ ByteViewSizes h after ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = l.put ∧ regs.left = l.left ∧ regs.out_ = l.out_ ∧
      regs.bits.toNat ≤ max l.bits.toNat 21 ∧ regs.bits.toNat ≤ l.bits.toNat + 8 * used ∧
      (state.mode = CODELENS ∨ state.mode = BAD) ∧
      (outcome = .ok () → state.mode = BAD ∨ state.«have».toNat = state.nlen.toNat + state.ndist.toNat) := by
  obtain ⟨outcome, regs, after, stream, state, used, bound, run, current, tables, pending, codes,
    packet, sizes, cursor, count, put, left, total, bits, budget, static, frame, modes, complete⟩ :=
    clRead_buffers E invariant.good invariant.pending invariant.lengths buffers mode
  have next : DefaultDecodeJ after r zs stream state := by
    refine ⟨current, tables, pending, codes, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, sizes.platform invariant.platform⟩
    · intro active
      rcases modes with selected | selected <;> rw [selected] at active <;> contradiction
    · rw [frame]
      exact invariant.held
    · rw [frame]
      exact invariant.window
    · rw [frame]
      exact invariant.wrapper
    · rw [frame]
      exact invariant.header
    · right; left
      rcases modes with selected | selected <;> rw [selected] <;> decide
    · rintro (active | active) <;>
        rcases modes with selected | selected <;> rw [selected] at active <;> contradiction
    · change after.static = _
      rw [static]
      exact invariant.globals
  refine ⟨outcome, regs, after, stream, state, used, bound, run, next,
    packet, sizes, cursor, count, put, left, total, bits, budget, modes, ?_⟩

  intro normal
  rcases complete normal with bad | full
  · exact Or.inl bad
  · right
    rw [show state.nlen = s.nlen by rw [frame], show state.ndist = s.ndist by rw [frame]]
    exact full


/-- Projection retaining the original complete J transport. -/
theorem clRead_default_J {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultDecodeJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = CODELENS) :
    ∃ outcome regs after stream state used, used ≤ bs.length ∧
      runX (clRead c) l h = .ok ((outcome, regs), after) ∧ DefaultDecodeJ after r zs stream state ∧
      DispatchBuffers after r regs (bs.drop used) ∧ ByteViewSizes h after ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = l.put ∧ regs.left = l.left ∧ regs.out_ = l.out_ ∧
      regs.bits.toNat ≤ max l.bits.toNat 21 ∧ regs.bits.toNat ≤ l.bits.toNat + 8 * used := by
  obtain ⟨outcome, regs, after, stream, state, used, bound, run, next,
    packet, sizes, cursor, count, put, left, total, bits, budget, _, _⟩ :=
    clRead_default_J_complete E invariant buffers mode
  exact ⟨outcome, regs, after, stream, state, used, bound, run, next,
    packet, sizes, cursor, count, put, left, total, bits, budget⟩

/-- The entire actual LENLENS reading loop preserves J's initialized
prefix and every other clause. Unused lens cells remain arbitrary. -/
theorem ll1_default_J {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultDecodeJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = LENLENS) :
    ∃ outcome regs after state used, used ≤ bs.length ∧
      runX (xwhile (llCond c) (llBody c)) l h = .ok ((outcome, regs), after) ∧
      DefaultDecodeJ after r zs z state ∧ DispatchBuffers after r regs (bs.drop used) ∧
      ByteViewSizes h after ∧ regs.next = inputAdvance l.next used ∧
      regs.have_.toNat + used = l.have_.toNat ∧ regs.put = l.put ∧ regs.left = l.left ∧
      regs.out_ = l.out_ ∧ regs.bits.toNat ≤ max l.bits.toNat 10 ∧
      regs.bits.toNat ≤ l.bits.toNat + 8 * used := by
  obtain ⟨ncode, haveBound, nlen, ndist, prefixValues⟩ := invariant.headerLengths mode
  obtain ⟨outcome, regs, used, run, bound, inv, stream, shape, _, _, cursor, bits⟩ :=
    ll1_run_cursor E.st E.hs invariant.good.inv.wf.1 ncode haveBound buffers.bits
  let m := min (s.ncode.toNat - s.«have».toNat) ((Zlib.Inflate.Proofs.stream l bs).length / 3)
  let state := llSt s (Zlib.Inflate.Proofs.stream l bs) m
  let after := setI h zs state
  have mBound : s.«have».toNat + m ≤ 19 := by
    have := Nat.min_le_left (s.ncode.toNat - s.«have».toNat) ((Zlib.Inflate.Proofs.stream l bs).length / 3)
    omega
  have stateCount : state.«have».toNat = s.«have».toNat + m := llSt_have s _ m mBound
  have statePrefix : Good3 state.lens state.«have».toNat := by
    rw [stateCount]
    exact lensRead_good _ prefixValues m mBound
  have current : Good after r zs z state := by
    apply good_state invariant.good (st' := state) rfl invariant.good.live.mode
    refine ⟨⟨?_, invariant.good.inv.wf.2.1, invariant.good.inv.wf.2.2⟩, ?_,
      invariant.good.inv.reqbits, invariant.good.inv.bits, invariant.good.inv.ptr⟩
    · change (lensRead s.lens s.«have».toNat _ m).size = 320
      rw [lensRead_size]
      exact invariant.good.inv.wf.1
    · exact ⟨invariant.good.inv.win.wbits, invariant.good.inv.win.block, invariant.good.inv.win.nullws,
        invariant.good.inv.win.ws, invariant.good.inv.win.hv, invariant.good.inv.win.wn, invariant.good.inv.win.eq⟩
  have next : DefaultDecodeJ after r zs z state := by
    refine ⟨current, ?_, ⟨invariant.pending.sane, invariant.pending.lenext, invariant.pending.dist,
      invariant.pending.distext, invariant.pending.matching⟩, ?_, ?_, invariant.held,
      invariant.window, invariant.wrapper, invariant.header, invariant.modes, invariant.trailer,
      invariant.globals, invariant.platform.with_istates _⟩
    · exact dataTableInvariant_inactive (by change ¬ DataTableMode s.mode; rw [mode]; unfold DataTableMode; decide)
    · intro active
      change s.mode = CODELENS at active
      rw [mode] at active
      contradiction
    · intro _
      refine ⟨ncode, ?_, nlen, ndist, statePrefix⟩
      change state.«have».toNat ≤ s.ncode.toNat
      rw [stateCount]
      have := Nat.min_le_left (s.ncode.toNat - s.«have».toNat) ((Zlib.Inflate.Proofs.stream l bs).length / 3)
      omega
  have sizes : ByteViewSizes h after := byte_view_sizes_setI h zs state
  have count : regs.have_.toNat + used = l.have_.toNat := by
    rw [inv.have_eq, buffers.bits.have_eq, List.length_drop]
    omega
  have packet : DispatchBuffers after r regs (bs.drop used) :=
    buffers.advance_both invariant.good current rfl sizes (fun ref => byte_view_ro_setI h zs state ref)
      cursor count (made := 0) (by rw [shape, inputAdvance_zero]) (by rw [shape]; rfl) (by rw [shape]) (inv.decode_update zs state)
  have budget : regs.bits.toNat ≤ l.bits.toNat + 8 * used := by
    have shorter : (Zlib.Inflate.Proofs.stream regs (bs.drop used)).length ≤
        (Zlib.Inflate.Proofs.stream l bs).length := by
      rw [stream, List.length_drop]
      omega
    rw [tcStream_length inv, tcStream_length buffers.bits, List.length_drop] at shorter
    omega
  exact ⟨outcome, regs, after, state, used, bound, run, next, packet, sizes, cursor, count,
    by rw [shape], by rw [shape], by rw [shape], bits, budget⟩


/-- Actual constructor metadata changes retain all other clauses of J. -/
theorem DefaultDecodeJ.table_update {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState} (invariant : DefaultDecodeJ h r zs z s)
    (current : Good after r zs stream state) (tables : DataTableInvariant after state)
    (pending : DataPendingInvariant state) (sizes : ByteViewSizes h after) (static : after.static = h.static)
    (update : ClTablesUpdate h r zs z s after stream state) (modes : state.mode = BAD ∨ state.mode = LEN_) :
    DefaultDecodeJ after r zs stream state := by
  have frame := update.2.2
  refine ⟨current, tables, pending, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, sizes.platform invariant.platform⟩
  · intro active
    rcases modes with selected | selected <;> rw [selected] at active <;> contradiction
  · intro active
    rcases modes with selected | selected <;> rw [selected] at active <;> contradiction
  · rw [frame]
    exact invariant.held
  · rw [frame]
    exact invariant.window
  · rw [frame]
    exact invariant.wrapper
  · rw [frame]
    exact invariant.header
  · right; left
    rcases modes with selected | selected <;> rw [selected] <;> decide
  · rintro (active | active) <;>
      rcases modes with selected | selected <;> rw [selected] at active <;> contradiction
  · change after.static = _
    rw [static]
    exact invariant.globals

/-- The actual end-of-block check and dynamic constructors carry J to
BAD or to the actual LEN_ continuation with checked data tables. -/
theorem clTail_default_J {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultDecodeJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (modes : s.mode = BAD ∨ s.mode = CODELENS)
    (done : s.mode = CODELENS → s.«have».toNat = s.nlen.toNat + s.ndist.toNat) :
    (∃ ret after stream state,
      runX (clTail c) l h = .ok ((.ok (), { l with ret := ret }), after) ∧
      DefaultDecodeJ after r zs stream state ∧ state.mode = BAD ∧
      DispatchBuffers after r { l with ret := ret } bs ∧ ByteViewSizes h after ∧ after.static = h.static) ∨
    (∃ after state, DefaultDecodeJ after r zs z state ∧ state.mode = LEN_ ∧
      DispatchBuffers after r { l with ret := 0 } bs ∧ ByteViewSizes h after ∧ after.static = h.static ∧
      (runX (clTail c) l h = if c.flush = Z_TREES then .ok ((.error Ex.leave, { l with ret := 0 }), after)
        else runX (inflate_LEN_ c) { l with ret := 0 } after)) := by
  rcases clTail_buffers E invariant.good invariant.pending buffers modes invariant.lengths done with bad | ready
  · obtain ⟨ret, after, stream, state, run, current, mode, tables, pending, packet, sizes, static, update⟩ := bad
    exact Or.inl ⟨ret, after, stream, state, run,
      invariant.table_update current tables pending sizes static update (Or.inl mode), mode, packet, sizes, static⟩
  · obtain ⟨after, state, current, mode, tables, pending, packet, sizes, static, run, update⟩ := ready
    exact Or.inr ⟨after, state,
      invariant.table_update current tables pending sizes static update (Or.inr mode), mode, packet, sizes, static, run⟩

end Zlib.Inflate.Proofs
