import ZlibF.Proof.«inflate.c.fast-view-caller-bit-budget»
import ZlibF.Proof.«inflate.c.fast-view-caller-state»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual RESTORE/fast/LOAD path retains source-bit and cursor
accounting on the caller registers. The interval frame is supplied by its
separate actual fast-call proof, rather than assumed in this theorem. -/
theorem inflate_LEN_fast_view_geometry
    {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = LEN)
    (fast : (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    ∃ regs after stream state used made, used ≤ bs.length ∧
      runX (inflate_LEN c) l h = .ok ((.ok (), regs), after) ∧
      DefaultStateJ after r zs stream state ∧ DataExitMode state.mode ∧
      ByteViewSizes h after ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = inputAdvance l.put made ∧ regs.left.toNat + made = l.left.toNat ∧
      regs.bits.toNat < 8 ∧ regs.bits.toNat ≤ l.bits.toNat + 8 * used ∧
      regs.out_ = l.out_ ∧ state.window = s.window ∧
      regs.bits = state.bits ∧ regs.hold = state.hold := by
  have bitBound : l.bits.toNat ≤ 39 := by
    have facts : (6 ≤ l.have_ ∧ 258 ≤ l.left) ∧ l.bits < 8 := by
      simpa only [Bool.and_eq_true, decide_eq_true_eq] using fast
    have small : l.bits.toNat < 8 := by simpa using UInt32.lt_iff_toNat_lt.mp facts.2
    omega
  obtain ⟨restored, packet⟩ := invariant.leave_restore E buffers bitBound
  have dataMode : DataTableMode (leaveState s l).mode := by
    change DataTableMode s.mode
    rw [mode]; unfold DataTableMode; decide
  obtain ⟨finished, stream, state, used, made, call, current,
    accounting, sizes, window, modes, small, readonly, live, nalloc, budget⟩ :=
    inflate_fast_default_view_caller_budget restored packet dataMode
      rfl rfl rfl rfl rfl rfl fast
  have execution : Zlib.Inffast.inflate_fast c.strm l.out_
      (setI (r.put h (leaveStream z l)) zs (leaveState s l)) = .ok ((), finished) := by
    rw [E.strm]
    exact call
  have cut : runX (inflate_LEN c) l h = runX (inflateAfterFast c) l finished := by
    unfold inflate_LEN
    rw [runX_bind, runX_get]
    simp only [fast, ↓reduceIte]
    rw [runX_bind, RESTORE_pending_run E]
    simp only []
    rw [runX_bind, runX_lift_ok execution]
    rfl
  let regs : IL := { l with
    put := stream.next_out, left := stream.avail_out,
    next := stream.next_in, have_ := stream.avail_in, hold := state.hold, bits := state.bits }
  have usedBound : used ≤ bs.length := by
    have bound : used ≤ l.have_.toNat := accounting.1
    rw [buffers.bits.have_eq] at bound
    exact bound
  have next : regs.next = inputAdvance l.next used := accounting.2.2.2.2.1
  have count : regs.have_.toNat + used = l.have_.toNat := accounting.2.2.1
  have put : regs.put = inputAdvance l.put made := accounting.2.2.2.2.2.1
  have left : regs.left.toNat + made = l.left.toNat := accounting.2.2.2.1
  have finalMode : DataExitMode state.mode := by
    rcases modes with same | type | bad
    · exact Or.inl (by rw [same]; exact dataMode)
    · exact Or.inr (Or.inl type)
    · exact Or.inr (Or.inr bad)
  have originalSizes : ByteViewSizes h finished :=
    ((byte_view_sizes_stream_put h r (leaveStream z l)).trans
      (byte_view_sizes_setI _ zs (leaveState s l))).trans sizes
  have env : Env c finished r zs stream state :=
    ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
  rw [cut, inflateAfterFast_run env]
  by_cases type : state.mode = TYPE
  · rw [if_pos type]
    refine ⟨regs, _, stream, { state with back := -1 }, used, made,
      usedBound, rfl, current.type_set_back type (-1), finalMode,
      originalSizes.trans (byte_view_sizes_setI finished zs _), next, count, put,
      left, small, budget, rfl, window, rfl, rfl⟩
  · rw [if_neg type]
    exact ⟨regs, finished, stream, state, used, made, usedBound, rfl,
      current, finalMode, originalSizes, next, count, put, left, small, budget,
      rfl, window, rfl, rfl⟩

#print axioms inflate_LEN_fast_view_geometry
end Zlib.Inflate.Proofs
