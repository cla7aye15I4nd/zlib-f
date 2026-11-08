import ZlibF.Proof.«inflate.c.fast-view-public-step»
import ZlibF.Proof.«inflate.c.dispatch-rank»
import ZlibF.Proof.«inflate.c.fast-view-caller-state»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual fast LEN path retains the full default state and caller
packet and strictly decreases the outer dispatch rank. Every callee fact
comes from a proved translated execution on general caller byte views. -/
theorem inflate_LEN_fast_view_step
    {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = LEN)
    (fast : (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    ∃ regs after stream state used made, used ≤ bs.length ∧
      runX (inflate_LEN c) l h = .ok ((.ok (), regs), after) ∧
      DefaultStateJ after r zs stream state ∧ DataExitMode state.mode ∧
      DispatchBuffers after r regs (bs.drop used) ∧
      ByteViewSizes h after ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = inputAdvance l.put made ∧ regs.left.toNat + made = l.left.toNat ∧
      regs.bits.toNat < 8 ∧ regs.bits.toNat ≤ l.bits.toNat + 8 * used ∧
      regs.out_ = l.out_ ∧ state.window = s.window ∧
      regs.bits = state.bits ∧ regs.hold = state.hold ∧
      (state.mode = BAD ∨ state.mode = TYPE ∨ 0 < made) ∧
      dispatchRank regs state.mode < dispatchRank l s.mode := by
  have bitBound : l.bits.toNat ≤ 39 := by
    have facts : (6 ≤ l.have_ ∧ 258 ≤ l.left) ∧ l.bits < 8 := by
      simpa only [Bool.and_eq_true, decide_eq_true_eq] using fast
    have small : l.bits.toNat < 8 := by simpa using UInt32.lt_iff_toNat_lt.mp facts.2
    omega
  obtain ⟨restored, packet⟩ := invariant.leave_restore E buffers bitBound
  have dataMode : DataTableMode (leaveState s l).mode := by
    change DataTableMode s.mode
    rw [mode]; unfold DataTableMode; decide
  obtain ⟨finished, stream, state, used, made, loaded, usedBound, call,
    current, fastPacket, sizes, next, count, put, left, small, budget,
    window, modes, shape, progress⟩ :=
    inflate_fast_default_view_buffers_progress restored packet dataMode
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
  have sameRegs : loaded = regs := by simpa only [regs] using shape
  subst loaded
  have finalMode : DataExitMode state.mode := by
    rcases modes with same | type | bad
    · exact Or.inl (by rw [same]; exact dataMode)
    · exact Or.inr (Or.inl type)
    · exact Or.inr (Or.inr bad)
  have decreases : dispatchRank regs state.mode < dispatchRank l s.mode := by
    apply dispatchRank_advance count left budget
    have dataBefore : DataTableMode s.mode := by rw [mode]; unfold DataTableMode; decide
    have nonliteral : s.mode ≠ LIT := by rw [mode]; decide
    rcases progress with bad | type | produced
    · exact Or.inr (data_dispatch_credit_drop dataBefore nonliteral (Or.inr (Or.inr bad)))
    · exact Or.inr (data_dispatch_credit_drop dataBefore nonliteral (Or.inr (Or.inl type)))
    · exact Or.inl produced
  have originalSizes : ByteViewSizes h finished :=
    ((byte_view_sizes_stream_put h r (leaveStream z l)).trans
      (byte_view_sizes_setI _ zs (leaveState s l))).trans sizes
  have env : Env c finished r zs stream state :=
    ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
  rw [cut, inflateAfterFast_run env]
  by_cases type : state.mode = TYPE
  · rw [if_pos type]
    have finalJ := current.type_set_back type (-1)
    have finalPacket := fastPacket.byte_views current.good finalJ.good rfl
      (byte_view_get_setI finished zs { state with back := -1 })
      (byte_view_ro_setI finished zs { state with back := -1 })
    refine ⟨regs, _, stream, { state with back := -1 }, used, made,
      usedBound, rfl, finalJ, finalMode, finalPacket,
      originalSizes.trans (byte_view_sizes_setI finished zs _), next, count, put,
      left, small, budget, rfl, window, rfl, rfl, progress, decreases⟩
  · rw [if_neg type]
    exact ⟨regs, finished, stream, state, used, made, usedBound, rfl,
      current, finalMode, fastPacket, originalSizes, next, count, put, left, small, budget,
      rfl, window, rfl, rfl, progress, decreases⟩

#print axioms inflate_LEN_fast_view_step
end Zlib.Inflate.Proofs
