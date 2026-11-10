import ZlibF.Proof.«inflate.c.default-loop»
import ZlibF.Proof.«inflate.c.output-charge-phase»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The complete actual default loop retains the early-charge phase and
exact original cursors. A charged segment can only be terminal and empty. -/
theorem inflate_default_raw_output_charge_loop {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (raw : RawFastIO l) (incoming : l.bits.toNat ≤ 39) :
    ∃ exit regs after stream state used made, used ≤ bs.length ∧
      runX (xwhile (pure true) (inflate_dispatch c)) l h = .ok ((.error exit, regs), after) ∧
      DefaultStateJ after r zs stream state ∧ DispatchBuffers after r regs (bs.drop used) ∧
      RawFastIO regs ∧ regs.bits.toNat ≤ 39 ∧ ByteViewSizes h after ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = inputAdvance l.put made ∧ regs.left.toNat + made = l.left.toNat ∧
      OutputChargePhase z.total_out regs stream state := by
  let P := fun regs heap => DefaultLoopInv r zs h l bs regs heap ∧
    ∀ stream state, r.get heap = some stream → heap.istates zs = some state →
      OutputChargePhase z.total_out regs stream state
  let Q := fun (outcome : Except Ex Unit) (regs : IL) (after : Heap) => outcome ≠ .ok () ∧ P regs after
  have initialCore : DefaultLoopInv r zs h l bs l h := ⟨z, s, 0, 0, by omega, invariant,
    by simpa only [List.drop_zero] using buffers, raw, incoming, ByteViewSizes.refl h,
    (inputAdvance_zero l.next).symm, by rfl, (inputAdvance_zero l.put).symm, by rfl⟩
  have initial : P l h := by
    refine ⟨initialCore, ?_⟩
    intro stream state hz hs
    have sameStream : z = stream := Option.some.inj (E.hz.symm.trans hz)
    exact Or.inl (by rw [← sameStream])
  have step : ∀ regs heap, P regs heap → ∃ test regs1 heap1,
      runX (pure true : X Bool) regs heap = .ok ((test, regs1), heap1) ∧
      (match test with
       | .error fault => Q (.error fault) regs1 heap1
       | .ok false => Q (.ok ()) regs1 heap1
       | .ok true => ∃ result regs2 heap2,
           runX (do inflate_dispatch c; pure false) regs1 heap1 = .ok ((result, regs2), heap2) ∧
           (match result with
            | .error fault => Q (.error fault) regs2 heap2
            | .ok true => Q (.ok ()) regs2 heap2
            | .ok false => P regs2 heap2 ∧ defaultHeapRank zs regs2 heap2 < defaultHeapRank zs regs heap)) := by
    intro regs heap ⟨current, currentPhase⟩
    obtain ⟨stream, state, used, made, bound, currentJ, packet, currentRaw, bits,
      sizes, next, count, put, left⟩ := current
    have currentEnv : Env c heap r zs stream state := ⟨E.strm, E.st, currentJ.good.live.hz, currentJ.good.live.hs⟩
    obtain ⟨outcome, finalRegs, finalHeap, finalStream, finalState, used2, made2, bound2,
      run, finalJ, finalPacket, finalSizes, next2, count2, put2, left2, finalBits, progress⟩ :=
      inflate_dispatch_default_state_rank currentEnv currentJ packet currentRaw bits
    have totalBound : used + used2 ≤ bs.length := by simp only [List.length_drop] at bound2; omega
    have finalCore : DefaultLoopInv r zs h l bs finalRegs finalHeap := by
      refine ⟨finalStream, finalState, used + used2, made + made2, totalBound, finalJ,
        ?_, currentRaw.advance next2 put2, finalBits, sizes.trans finalSizes, ?_, ?_, ?_, ?_⟩
      · simpa only [List.drop_drop, Nat.add_comm] using finalPacket
      · rw [next2, next, inputAdvance_add]
      · omega
      · rw [put2, put, inputAdvance_add]
      · omega
    have phase := inflate_dispatch_default_output_charge_phase currentEnv currentJ packet bits
      (currentPhase stream state currentJ.good.live.hz currentJ.good.live.hs) run
      finalJ.good.live.hz finalJ.good.live.hs
    have final : P finalRegs finalHeap := by
      refine ⟨finalCore, ?_⟩
      intro stream2 state2 hz hs
      have sameStream : finalStream = stream2 := Option.some.inj (finalJ.good.live.hz.symm.trans hz)
      have sameState : finalState = state2 := Option.some.inj (finalJ.good.live.hs.symm.trans hs)
      rwa [← sameStream, ← sameState]
    refine ⟨.ok true, regs, heap, rfl, ?_⟩
    cases outcome with
    | error fault =>
      refine ⟨.error fault, finalRegs, finalHeap, ?_, ?_⟩
      · rw [runX_bind, run]
      · exact ⟨(by intro impossible; cases impossible), final⟩
    | ok unit =>
      cases unit
      refine ⟨.ok false, finalRegs, finalHeap, ?_, final, ?_⟩
      · rw [runX_bind, run]
        rfl
      · rw [defaultHeapRank_eq finalJ.good, defaultHeapRank_eq currentJ.good]
        exact progress rfl
  have budget : defaultHeapRank zs l h + 2 < fuel := by
    rw [defaultHeapRank_eq invariant.good]
    exact dispatchRank_fuel l s.mode incoming
  obtain ⟨outcome, regs, after, run, stopped, final⟩ :=
    xwhileBrk_rank P (defaultHeapRank zs) Q step initial budget
  cases outcome with
  | ok unit => exact False.elim (stopped (by cases unit; rfl))
  | error exit =>
    obtain ⟨stream, state, used, made, bound, finalJ, packet, finalRaw, bits,
      sizes, next, count, put, left⟩ := final.1
    exact ⟨exit, regs, after, stream, state, used, made, bound, run, finalJ, packet,
      finalRaw, bits, sizes, next, count, put, left, final.2 stream state finalJ.good.live.hz finalJ.good.live.hs⟩

end Zlib.Inflate.Proofs
