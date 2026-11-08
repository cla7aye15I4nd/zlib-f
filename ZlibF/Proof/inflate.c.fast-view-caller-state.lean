import ZlibF.Proof.«inflate.c.fast-view-caller-cut»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- At TYPE, updating the diagnostic back counter preserves all default state
clauses and the actual table contents. -/
theorem DefaultStateJ.type_set_back
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (invariant : DefaultStateJ h r zs z s) (mode : s.mode = TYPE) (back : Int32) :
    DefaultStateJ (setI h zs { s with back }) r zs z { s with back } := by
  have frame : DecodeStateFrame s { s with back } := rfl
  have good := invariant.good.decode_update frame invariant.good.live.mode
  have tables : DataTableInvariant (setI h zs { s with back }) { s with back } := by
    intro active
    exact (invariant.tables active).decode_update invariant.good.live.hs frame
  have pending : DataPendingInvariant { s with back } := by
    refine ⟨invariant.pending.sane, ?_, ?_, ?_, ?_⟩
    all_goals intro active; change s.mode = _ at active; rw [mode] at active; contradiction
  have sizes := byte_view_sizes_setI h zs { s with back }
  exact ⟨⟨good, tables, pending, invariant.lengths, invariant.headerLengths,
    invariant.held, invariant.window, invariant.wrapper, invariant.header, invariant.modes,
    invariant.trailer, invariant.globals, sizes.platform invariant.platform⟩,
    invariant.requestedBits, invariant.requestedWrap, invariant.phase⟩

/-- LOAD and the conditional TYPE back-counter update retain J on the
same heap and records returned by the proved fast callee. -/
theorem inflateAfterFast_default_state_run
    {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s) :
    ∃ regs after state,
      runX (inflateAfterFast c) l h = .ok ((.ok (), regs), after) ∧
      DefaultStateJ after r zs z state ∧
      regs = { l with
        put := z.next_out, left := z.avail_out,
        next := z.next_in, have_ := z.avail_in, hold := s.hold, bits := s.bits } := by
  rw [inflateAfterFast_run E]
  by_cases type : s.mode = TYPE
  · rw [if_pos type]
    exact ⟨_, _, _, rfl, invariant.type_set_back type (-1), rfl⟩
  · rw [if_neg type]
    exact ⟨_, _, _, rfl, invariant, rfl⟩

/-- The complete actual fast LEN branch preserves the initialized default
state relation on general public byte views, through RESTORE, fast and LOAD. -/
theorem inflate_LEN_fast_view_state_run
    {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : DataTableMode s.mode)
    (fast : (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    ∃ regs after zNext sNext used made,
      runX (inflate_LEN c) l h = .ok ((.ok (), regs), after) ∧
      DefaultStateJ after r zs zNext sNext ∧
      StreamAccounting (leaveStream z l) zNext used made := by
  obtain ⟨after, zNext, sNext, used, made, cut, current, accounting⟩ :=
    inflate_LEN_fast_view_cut E invariant buffers mode fast
  have environment : Env c after r zs zNext sNext :=
    ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
  obtain ⟨regs, finished, state, suffix, final, shape⟩ :=
    inflateAfterFast_default_state_run (l := l) environment current
  exact ⟨regs, finished, zNext, state, used, made, cut.trans suffix, final, accounting⟩

#print axioms DefaultStateJ.type_set_back
#print axioms inflateAfterFast_default_state_run
#print axioms inflate_LEN_fast_view_state_run
end Zlib.Inflate.Proofs
