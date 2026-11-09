import ZlibF.Proof.«inflate.c.local-fast-dispatch»
import ZlibF.Proof.«inflate.c.local-construction»

namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- All actual construction branches and their immediate LEN_ continuation
retain the default state and complete generic caller packet, with exact
counts and a strict outer rank decrease on every normal return. -/
theorem inflate_dispatch_construction_view_state_rank {c : Ctx} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : LocalStateJ h cutoff r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = TABLE ∨ s.mode = LENLENS ∨ s.mode = CODELENS)
    (incoming : l.bits.toNat ≤ 39) :
    ∃ outcome regs after stream state used made, used ≤ bs.length ∧
      runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) ∧ LocalStateJ after cutoff r zs stream state ∧
      DispatchBuffers after r regs (bs.drop used) ∧ ByteViewSizes h after ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = inputAdvance l.put made ∧ regs.left.toNat + made = l.left.toNat ∧ regs.bits.toNat ≤ 39 ∧
      (outcome = .error Ex.leave ∨ (outcome = .ok () ∧ dispatchRank regs state.mode < dispatchRank l s.mode)) := by
  obtain ⟨regs, after, stream, state, used, bound, nextJ, config, packet, sizes, cursor, count,
    put, left, total, bits, budget, stopped | continued⟩ :=
    inflate_dispatch_construction_state_boundary E invariant buffers mode
  · obtain ⟨outcome, run, why⟩ := stopped
    refine ⟨outcome, regs, after, stream, state, used, 0, bound, run, nextJ, packet, sizes,
      cursor, count, by rw [put, inputAdvance_zero], by rw [left]; omega, by omega, ?_⟩
    rcases inflate_dispatch_construction_outcomes E mode run with leaves | normal
    · exact Or.inl leaves
    · have bad : state.mode = BAD := why.resolve_left (fun impossible => impossible normal)
      refine Or.inr ⟨normal, ?_⟩
      apply dispatchRank_advance (l := l) (regs := regs) (used := used) (made := 0) count
      · rw [left]; omega
      · exact budget
      · right
        rw [bad]
        rcases mode with selected | selected | selected <;> rw [selected] <;> decide
  · obtain ⟨nextMode, source⟩ := continued
    by_cases trees : c.flush = Z_TREES
    · rw [if_pos trees] at source
      exact ⟨.error Ex.leave, regs, after, stream, state, used, 0, bound, source, nextJ, packet, sizes,
        cursor, count, by rw [put, inputAdvance_zero], by rw [left]; omega, by omega, Or.inl rfl⟩
    · rw [if_neg trees] at source
      have nextEnv : Env c after r zs stream state :=
        ⟨E.strm, E.st, nextJ.good.live.hz, nextJ.good.live.hs⟩
      have dataMode : DataTableMode state.mode := by rw [nextMode]; unfold DataTableMode; decide
      obtain ⟨outcome, finalRegs, finalHeap, finalStream, finalState, used2, made,
        bound2, run, finalJ, _, finalPacket, finalSizes, next, haveCount, output, leftCount, finalBits, progress⟩ :=
        inflate_dispatch_data_view_state_rank nextEnv nextJ packet dataMode
      have prefixRank : dispatchRank regs state.mode < dispatchRank l s.mode := by
        apply dispatchRank_advance (l := l) (regs := regs) (used := used) (made := 0) count
        · rw [left]; omega
        · exact budget
        · right
          rw [nextMode]
          rcases mode with selected | selected | selected <;> rw [selected] <;> decide
      have combined : used + used2 ≤ bs.length := by simp only [List.length_drop] at bound2; omega
      have finalRun : runX (inflate_dispatch c) l h = .ok ((outcome, finalRegs), finalHeap) :=
        source.trans ((inflate_dispatch_LEN_start nextEnv regs nextMode).symm.trans run)
      refine ⟨outcome, finalRegs, finalHeap, finalStream, finalState, used + used2, made, combined,
        finalRun, finalJ, ?_, sizes.trans finalSizes, ?_, ?_, ?_, ?_, by omega, ?_⟩
      · simpa only [List.drop_drop, Nat.add_comm] using finalPacket
      · rw [next, cursor, inputAdvance_add]
      · omega
      · rw [output, put]
      · rw [left] at leftCount
        exact leftCount
      · rcases progress with leaves | ⟨normal, decreases⟩
        · exact Or.inl leaves
        · exact Or.inr ⟨normal, Nat.lt_trans decreases prefixRank⟩

#print axioms inflate_dispatch_construction_view_state_rank
end Zlib.Inflate.Local
