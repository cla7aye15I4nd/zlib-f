import ZlibF.Proof.«inflate.c.dispatch-default-state»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- One persistent relation for the actual mode loop. Exact accumulated
input/output counts refer to the original caller cursors. -/
def DefaultLoopInv (r : ZStreamRef) (zs : Nat) (initialHeap : Heap) (initial : IL) (input : List UInt8)
    (regs : IL) (heap : Heap) : Prop :=
  ∃ stream state used made, used ≤ input.length ∧ DefaultStateJ heap r zs stream state ∧
    DispatchBuffers heap r regs (input.drop used) ∧ RawFastIO regs ∧ regs.bits.toNat ≤ 39 ∧
    ByteViewSizes initialHeap heap ∧ regs.next = inputAdvance initial.next used ∧
    regs.have_.toNat + used = initial.have_.toNat ∧ regs.put = inputAdvance initial.put made ∧
    regs.left.toNat + made = initial.left.toNat

/-- The rank reads the live decoder mode from the actual heap. -/
def defaultHeapRank (zs : Nat) (regs : IL) (heap : Heap) : Nat :=
  dispatchRank regs ((heap.istates zs).map (·.mode) |>.getD HEAD)

theorem defaultHeapRank_eq {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (good : Good h r zs z s) (regs : IL) : defaultHeapRank zs regs h = dispatchRank regs s.mode := by
  simp only [defaultHeapRank, good.live.hs, Option.map_some, Option.getD_some]

/-- The actual endless-condition mode loop terminates without a runtime
fault and preserves one complete relation across every default mode.
Its input/output cursors and remaining counts are exact across the whole
loop. The internal fast interface requires distinct raw input/output
blocks. This does not state public inflate or its leave/ownership contract. -/
theorem inflate_default_raw_loop {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (raw : RawFastIO l) (incoming : l.bits.toNat ≤ 39) :
    ∃ exit regs after stream state used made, used ≤ bs.length ∧
      runX (xwhile (pure true) (inflate_dispatch c)) l h = .ok ((.error exit, regs), after) ∧
      DefaultStateJ after r zs stream state ∧ DispatchBuffers after r regs (bs.drop used) ∧
      RawFastIO regs ∧ regs.bits.toNat ≤ 39 ∧ ByteViewSizes h after ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = inputAdvance l.put made ∧ regs.left.toNat + made = l.left.toNat := by
  let P := DefaultLoopInv r zs h l bs
  let Q := fun (outcome : Except Ex Unit) (regs : IL) (after : Heap) => outcome ≠ .ok () ∧ P regs after
  have initial : P l h := ⟨z, s, 0, 0, by omega, invariant,
    by simpa only [List.drop_zero] using buffers, raw, incoming, ByteViewSizes.refl h,
    (inputAdvance_zero l.next).symm, by rfl, (inputAdvance_zero l.put).symm, by rfl⟩
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
    intro regs heap current
    obtain ⟨stream, state, used, made, bound, currentJ, packet, currentRaw, bits,
      sizes, next, count, put, left⟩ := current
    have currentEnv : Env c heap r zs stream state := ⟨E.strm, E.st, currentJ.good.live.hz, currentJ.good.live.hs⟩
    obtain ⟨outcome, finalRegs, finalHeap, finalStream, finalState, used2, made2, bound2,
      run, finalJ, finalPacket, finalSizes, next2, count2, put2, left2, finalBits, progress⟩ :=
      inflate_dispatch_default_state_rank currentEnv currentJ packet currentRaw bits
    have totalBound : used + used2 ≤ bs.length := by simp only [List.length_drop] at bound2; omega
    have final : P finalRegs finalHeap := by
      refine ⟨finalStream, finalState, used + used2, made + made2, totalBound, finalJ,
        ?_, currentRaw.advance next2 put2, finalBits, sizes.trans finalSizes, ?_, ?_, ?_, ?_⟩
      · simpa only [List.drop_drop, Nat.add_comm] using finalPacket
      · rw [next2, next, inputAdvance_add]
      · omega
      · rw [put2, put, inputAdvance_add]
      · omega
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
      sizes, next, count, put, left⟩ := final
    exact ⟨exit, regs, after, stream, state, used, made, bound, run, finalJ, packet,
      finalRaw, bits, sizes, next, count, put, left⟩

end Zlib.Inflate.Proofs
