import ZlibF.Proof.«inflate.c.fast-view-caller-start-step»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- All actual data-mode dispatches preserve the initialized state and
full caller buffer packet. Every normal step strictly decreases the bounded
outer rank, including fast calls on disjoint slices of one byte object. -/
theorem inflate_dispatch_data_view_state_rank
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : DataTableMode s.mode) :
    ∃ outcome regs after stream state used made,
      used ≤ bs.length ∧ runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) ∧
      DefaultStateJ after r zs stream state ∧ DataExitMode state.mode ∧
      DispatchBuffers after r regs (bs.drop used) ∧ ByteViewSizes h after ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = inputAdvance l.put made ∧ regs.left.toNat + made = l.left.toNat ∧
      regs.bits.toNat ≤ max l.bits.toNat 22 ∧
      (outcome = .error Ex.leave ∨
        (outcome = .ok () ∧ dispatchRank regs state.mode < dispatchRank l s.mode)) := by
  by_cases fast : (s.mode = LEN_ ∨ s.mode = LEN) ∧
      (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true
  · rcases fast.1 with start | lengthMode
    · obtain ⟨regs, after, stream, state, used, made, bound, run, current, modes,
        packet, sizes, next, count, put, left, small, budget, total, window,
        bitsEq, holdEq, progress, decreases⟩ :=
        inflate_LEN_start_fast_view_step E invariant buffers start fast.2
      exact ⟨.ok (), regs, after, stream, state, used, made, bound,
        (inflate_dispatch_LEN_start E l start).trans run, current, modes, packet,
        sizes, next, count, put, left, by omega, Or.inr ⟨rfl, decreases⟩⟩
    · obtain ⟨regs, after, stream, state, used, made, bound, run, current, modes,
        packet, sizes, next, count, put, left, small, budget, total, window,
        bitsEq, holdEq, progress, decreases⟩ :=
        inflate_LEN_fast_view_step E invariant buffers lengthMode fast.2
      exact ⟨.ok (), regs, after, stream, state, used, made, bound,
        (inflate_dispatch_LEN E l lengthMode).trans run, current, modes, packet,
        sizes, next, count, put, left, by omega, Or.inr ⟨rfl, decreases⟩⟩
  · exact inflate_dispatch_data_state_rank E invariant buffers mode
      (fun selected => False.elim (fast selected))

#print axioms inflate_dispatch_data_view_state_rank
end Zlib.Inflate.Proofs
