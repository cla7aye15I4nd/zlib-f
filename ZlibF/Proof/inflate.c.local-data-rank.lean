import ZlibF.Proof.«inflate.c.local-slow-progress»
import ZlibF.Proof.«inflate.c.local-construction»
import ZlibF.Proof.«inflate.c.dispatch-rank»

/-! Exact slow-data dispatch rank and full local history on the same run. -/
namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- The original slow paths either leave or consume a strictly bounded rank. -/
theorem slow_dispatch_rank {c : Ctx} {l : IL} {h : Heap} {cutoff : Nat}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8}
    (E : Env c h r zs z s) (good : LocalGood h cutoff r zs z s)
    (tables : DataTableInvariant h s) (buffers : DispatchBuffers h r l bs)
    (pending : DataPendingInvariant s) (mode : DataTableMode s.mode)
    (slow : s.mode = LEN_ ∨ s.mode = LEN → ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    ∃ outcome regs after stream state used made,
      used ≤ bs.length ∧ runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) ∧
      LocalGood after cutoff r zs stream state ∧ DispatchBuffers after r regs (bs.drop used) ∧
      ByteViewSizes h after ∧ DecodeStateFrame s state ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = inputAdvance l.put made ∧ regs.left.toNat + made = l.left.toNat ∧
      regs.bits.toNat ≤ max l.bits.toNat 22 ∧
      (outcome = .error Ex.leave ∨ (outcome = .ok () ∧ dispatchRank regs state.mode < dispatchRank l s.mode)) := by
  by_cases literal : s.mode = LIT
  · obtain ⟨outcome, regs, after, state, run, nextGood, _, nextPacket, sizes, frame,
        regFrame, kinds⟩ := inflate_LIT_dispatch E good (tables mode) buffers
    have haveCount : regs.have_.toNat + 0 = l.have_.toNat := by rw [regFrame]; rfl
    have next : regs.next = inputAdvance l.next 0 := by rw [regFrame, inputAdvance_zero]
    have budget : regs.bits.toNat ≤ l.bits.toNat + 8 * 0 := by rw [regFrame]; simp only [Nat.mul_zero, Nat.add_zero, Nat.le_refl]
    have bitBound : regs.bits.toNat ≤ max l.bits.toNat 22 := by rw [regFrame]; exact Nat.le_max_left _ _
    rcases kinds with ⟨wait, regsEq, _, _⟩ | ⟨ok, _, put, count⟩
    · exact ⟨outcome, regs, after, z, state, 0, 0, by omega,
        (inflate_dispatch_LIT E l literal).trans run, nextGood,
        by simpa only [List.drop_zero] using nextPacket, sizes, frame, next, haveCount,
        by rw [regsEq, inputAdvance_zero], by rw [regsEq]; rfl, bitBound, Or.inl wait⟩
    · exact ⟨outcome, regs, after, z, state, 0, 1, by omega,
        (inflate_dispatch_LIT E l literal).trans run, nextGood,
        by simpa only [List.drop_zero] using nextPacket, sizes, frame, next, haveCount,
        put, count, bitBound, Or.inr ⟨ok, dispatchRank_advance haveCount count budget (Or.inl (by decide))⟩⟩
  · obtain ⟨outcome, regs, after, stream, state, used, consumed, made, bound, _, run,
        current, _, packet, _, sizes, frame, next, left, put, source, kinds, bits⟩ :=
      inflate_dispatch_pending_output_progress E good tables buffers pending mode slow
    have count : regs.have_.toNat + used = l.have_.toNat := by
      rw [packet.bits.have_eq, buffers.bits.have_eq, List.length_drop]
      omega
    have budget := bit_budget_of_stream_drop bound source
    refine ⟨outcome, regs, after, stream, state, used, made, bound, run, current,
      packet, sizes, frame, next, count, put, left, bits, ?_⟩
    rcases kinds with wait | ⟨ok, emitted | boundary⟩
    · exact Or.inl wait
    · exact Or.inr ⟨ok, dispatchRank_advance count left budget (Or.inl emitted)⟩
    · exact Or.inr ⟨ok, dispatchRank_advance count left budget
        (Or.inr (data_dispatch_credit_drop mode literal boundary))⟩

/-- Active data modes have passed their header or entered raw recovery. -/
theorem LocalStateJ.data_format {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (invariant : LocalStateJ h cutoff r zs z s)
    (mode : DataTableMode s.mode) : s.wrap = 0 ∨ s.flags = 0 := by
  rcases invariant.phase with head | bad | mem | sync | format
  · rcases mode with selected | selected | selected | selected | selected | selected | selected <;>
      rw [selected] at head <;> contradiction
  · rcases mode with selected | selected | selected | selected | selected | selected | selected <;>
      rw [selected] at bad <;> contradiction
  · rcases mode with selected | selected | selected | selected | selected | selected | selected <;>
      rw [selected] at mem <;> contradiction
  · rcases mode with selected | selected | selected | selected | selected | selected | selected <;>
      rw [selected] at sync <;> contradiction
  · exact format

/-- One full actual slow-data dispatch preserves all local history and
returns the exact cursor ledger and strict rank on that identical execution. -/
theorem inflate_dispatch_data_slow_state_rank {c : Ctx} {l : IL} {h : Heap} {cutoff : Nat}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : LocalStateJ h cutoff r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : DataTableMode s.mode)
    (slow : s.mode = LEN_ ∨ s.mode = LEN → ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    ∃ outcome regs after stream state used made,
      used ≤ bs.length ∧ runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) ∧
      LocalStateJ after cutoff r zs stream state ∧ DataExitMode state.mode ∧
      DispatchBuffers after r regs (bs.drop used) ∧ ByteViewSizes h after ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = inputAdvance l.put made ∧ regs.left.toNat + made = l.left.toNat ∧
      regs.bits.toNat ≤ max l.bits.toNat 22 ∧
      (outcome = .error Ex.leave ∨ (outcome = .ok () ∧ dispatchRank regs state.mode < dispatchRank l s.mode)) := by
  obtain ⟨outcome, regs, after, stream, state, used, made, bound, actual, current,
      packet, sizes, frame, next, count, put, left, bits, progress⟩ :=
    slow_dispatch_rank E invariant.good invariant.tables buffers invariant.pending mode slow
  obtain ⟨otherOutcome, otherRegs, otherHeap, otherStream, otherState, otherRun, decoded, finalMode⟩ :=
    inflate_dispatch_data_slow_J E invariant.toLocalDecodeJ buffers mode slow
  rw [actual] at otherRun
  cases otherRun
  have streamEq : otherStream = stream := Option.some.inj (decoded.good.live.hz.symm.trans current.live.hz)
  have stateEq : otherState = state := Option.some.inj (decoded.good.live.hs.symm.trans current.live.hs)
  subst otherStream otherState
  have final := invariant.config_update decoded frame.default_config (invariant.data_format mode)
    (by rw [frame])
  exact ⟨outcome, regs, after, stream, state, used, made, bound, actual, final, finalMode,
    packet, sizes, next, count, put, left, bits, progress⟩

#print axioms slow_dispatch_rank
#print axioms inflate_dispatch_data_slow_state_rank
end Zlib.Inflate.Local
