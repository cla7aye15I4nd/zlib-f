import ZlibF.Proof.«inflate.c.default-view-construction-rank»
import ZlibF.Proof.«inflate.c.dispatch-default-state»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Every actual default decoder mode retains its initialized state and
full caller buffer packet. Every normal iteration strictly decreases the
bounded outer rank. All public separated caller byte views are admitted. -/
theorem inflate_dispatch_default_view_state_rank {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (incoming : l.bits.toNat ≤ 39) :
    ∃ outcome regs after stream state used made, used ≤ bs.length ∧
      runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) ∧
      DefaultStateJ after r zs stream state ∧ DispatchBuffers after r regs (bs.drop used) ∧
      ByteViewSizes h after ∧ regs.next = inputAdvance l.next used ∧
      regs.have_.toNat + used = l.have_.toNat ∧ regs.put = inputAdvance l.put made ∧
      regs.left.toNat + made = l.left.toNat ∧ regs.bits.toNat ≤ 39 ∧
      (outcome = .ok () → dispatchRank regs state.mode < dispatchRank l s.mode) := by
  rcases defaultMode_cases invariant.modes with head | dictionary | type | stored | construction | data | trailer | terminal | gzipHeader
  · obtain ⟨outcome, regs, after, stream, state, used, bound, run, final, packet, sizes,
      next, count, put, left, bits, _, _, _, progress⟩ :=
      inflate_dispatch_HEAD_state_rank E invariant buffers head incoming
    exact ⟨outcome, regs, after, stream, state, used, 0, bound, run, final, packet, sizes,
      next, count, by rw [put, inputAdvance_zero], by rw [left]; omega, bits, dispatch_normal_rank progress⟩
  · obtain ⟨outcome, regs, after, stream, state, used, bound, run, final, packet, sizes,
      next, count, put, left, bits, _, progress⟩ :=
      inflate_dispatch_dictionary_state_rank E invariant buffers dictionary incoming
    refine ⟨outcome, regs, after, stream, state, used, 0, bound, run, final, packet, sizes,
      next, count, by rw [put, inputAdvance_zero], by rw [left]; omega, bits, ?_⟩
    intro normal
    rcases progress with needed | leave | completed
    · cases needed.symm.trans normal
    · cases leave.symm.trans normal
    · exact completed.2
  · obtain ⟨outcome, regs, after, stream, state, used, bound, run, final, _, packet, sizes,
      next, count, put, left, bits, _, _, _, progress⟩ :=
      inflate_dispatch_type_state_rank E invariant buffers type incoming
    exact ⟨outcome, regs, after, stream, state, used, 0, bound, run, final, packet, sizes,
      next, count, by rw [put, inputAdvance_zero], by rw [left]; omega, bits, dispatch_normal_rank progress⟩
  · obtain ⟨outcome, regs, after, stream, state, used, made, bound, run, final, _, packet, sizes,
      _, next, count, put, left, bits, progress, _, _⟩ :=
      inflate_dispatch_stored_state_rank E invariant buffers stored incoming
    exact ⟨outcome, regs, after, stream, state, used, made, bound, run, final, packet, sizes,
      next, count, put, left, bits, dispatch_normal_rank progress⟩
  · obtain ⟨outcome, regs, after, stream, state, used, made, bound, run, final, packet, sizes,
      next, count, put, left, bits, progress⟩ :=
      inflate_dispatch_construction_view_state_rank E invariant buffers construction incoming
    exact ⟨outcome, regs, after, stream, state, used, made, bound, run, final, packet, sizes,
      next, count, put, left, bits, dispatch_normal_rank progress⟩
  · obtain ⟨outcome, regs, after, stream, state, used, made, bound, run, final, _, packet, sizes,
      next, count, put, left, bits, progress⟩ :=
      inflate_dispatch_data_view_state_rank E invariant buffers data
    exact ⟨outcome, regs, after, stream, state, used, made, bound, run, final, packet, sizes,
      next, count, put, left, by omega, dispatch_normal_rank progress⟩
  · rcases trailer with check | length
    · obtain ⟨outcome, regs, after, stream, state, used, bound, run, final, packet, sizes,
        next, count, put, left, bits, _, progress⟩ :=
        inflate_CHECK_default_state_rank E invariant buffers check incoming
      exact ⟨outcome, regs, after, stream, state, used, 0, bound,
        (inflate_dispatch_CHECK E l check).trans run, final, packet, sizes,
        next, count, by rw [put, inputAdvance_zero], by rw [left]; omega, bits, dispatch_normal_rank progress⟩
    · obtain ⟨outcome, regs, after, stream, state, used, bound, run, final, packet, sizes,
        next, count, put, left, bits, _, progress, _⟩ :=
        inflate_LENGTH_state_rank E invariant buffers length incoming
      exact ⟨outcome, regs, after, stream, state, used, 0, bound,
        (inflate_dispatch_LENGTH E l length).trans run, final, packet, sizes,
        next, count, by rw [put, inputAdvance_zero], by rw [left]; omega, bits, dispatch_normal_rank progress⟩
  · obtain ⟨run, _, packet, bits, _⟩ := inflate_dispatch_terminal_state E invariant buffers terminal
    have fields : (terminalRegs s.mode l).next = l.next ∧ (terminalRegs s.mode l).have_ = l.have_ ∧
        (terminalRegs s.mode l).put = l.put ∧ (terminalRegs s.mode l).left = l.left := by
      unfold terminalRegs
      split
      · exact ⟨rfl, rfl, rfl, rfl⟩
      · split <;> exact ⟨rfl, rfl, rfl, rfl⟩
    refine ⟨terminalExit s.mode, terminalRegs s.mode l, h, z, s, 0, 0, by omega, run, invariant,
      by simpa only [List.drop_zero] using packet, ByteViewSizes.refl h,
      by rw [fields.1, inputAdvance_zero], by rw [fields.2.1]; omega,
      by rw [fields.2.2.1, inputAdvance_zero], by rw [fields.2.2.2]; omega, by rw [bits]; exact incoming, ?_⟩
    intro normal
    rcases terminal with selected | selected | selected | selected <;>
      rw [selected] at normal <;> simp [terminalExit, DONE, BAD, MEM, SYNC] at normal
  · sorry

#print axioms inflate_dispatch_default_view_state_rank
end Zlib.Inflate.Proofs
