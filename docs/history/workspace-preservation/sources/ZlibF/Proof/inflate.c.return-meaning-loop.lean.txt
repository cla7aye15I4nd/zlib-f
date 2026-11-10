import ZlibF.Proof.«inflate.c.default-loop»
import ZlibF.Proof.«inflate.c.return-meaning»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The complete actual default loop preserves the continuing phase
and returns with END/DATA_ERROR tied to DONE/BAD on ordinary leave. -/
theorem inflate_default_raw_meaning_loop {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (raw : RawFastIO l) (incoming : l.bits.toNat ≤ 39)
    (initialCode : ContinuingReturn l s) :
    ∃ exit regs after stream state used made, used ≤ bs.length ∧
      runX (xwhile (pure true) (inflate_dispatch c)) l h = .ok ((.error exit, regs), after) ∧
      DefaultStateJ after r zs stream state ∧ DispatchBuffers after r regs (bs.drop used) ∧
      RawFastIO regs ∧ regs.bits.toNat ≤ 39 ∧ ByteViewSizes h after ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = inputAdvance l.put made ∧ regs.left.toNat + made = l.left.toNat ∧
      StepReturnMeaning (.error exit) regs state := by
  let P := fun regs heap => DefaultLoopInv r zs h l bs regs heap ∧
    ∀ observed, heap.istates zs = some observed → ContinuingReturn regs observed
  let Q := fun (outcome : Except Ex Unit) (regs : IL) (after : Heap) => outcome ≠ .ok () ∧ DefaultLoopInv r zs h l bs regs after ∧
    ∀ observed, after.istates zs = some observed → StepReturnMeaning outcome regs observed
  have initialCore : DefaultLoopInv r zs h l bs l h := ⟨z, s, 0, 0, by omega, invariant,
    by simpa only [List.drop_zero] using buffers, raw, incoming, ByteViewSizes.refl h,
    (inputAdvance_zero l.next).symm, by rfl, (inputAdvance_zero l.put).symm, by rfl⟩
  have initial : P l h := ⟨initialCore, by
    intro observed get
    have same : observed = s := Option.some.inj (get.symm.trans E.hs)
    subst observed
    exact initialCode⟩
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
    intro regs heap ⟨current, currentReturn⟩
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
    have meaning := inflate_dispatch_default_return_meaning currentEnv currentJ packet
      (currentReturn state currentJ.good.live.hs) run finalJ.good.live.hs
    have observedMeaning : ∀ observed, finalHeap.istates zs = some observed →
        StepReturnMeaning outcome finalRegs observed := by
      intro observed get
      have same : observed = finalState := Option.some.inj (get.symm.trans finalJ.good.live.hs)
      subst observed
      exact meaning
    refine ⟨.ok true, regs, heap, rfl, ?_⟩
    cases outcome with
    | error fault =>
      refine ⟨.error fault, finalRegs, finalHeap, ?_, ?_⟩
      · rw [runX_bind, run]
      · exact ⟨(by intro impossible; cases impossible), finalCore, observedMeaning⟩
    | ok unit =>
      cases unit
      have final : P finalRegs finalHeap := ⟨finalCore, by
        intro observed get
        exact observedMeaning observed get⟩
      refine ⟨.ok false, finalRegs, finalHeap, ?_, final, ?_⟩
      · rw [runX_bind, run]
        rfl
      · rw [defaultHeapRank_eq finalJ.good, defaultHeapRank_eq currentJ.good]
        exact progress rfl
  have budget : defaultHeapRank zs l h + 2 < fuel := by
    rw [defaultHeapRank_eq invariant.good]
    exact dispatchRank_fuel l s.mode incoming
  obtain ⟨outcome, regs, after, run, stopped, final, finalMeaning⟩ :=
    xwhileBrk_rank P (defaultHeapRank zs) Q step initial budget
  cases outcome with
  | ok unit => exact False.elim (stopped (by cases unit; rfl))
  | error exit =>
    obtain ⟨stream, state, used, made, bound, finalJ, packet, finalRaw, bits,
      sizes, next, count, put, left⟩ := final
    exact ⟨exit, regs, after, stream, state, used, made, bound, run, finalJ, packet,
      finalRaw, bits, sizes, next, count, put, left, finalMeaning state finalJ.good.live.hs⟩

end Zlib.Inflate.Proofs
