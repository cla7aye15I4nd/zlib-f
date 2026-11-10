import ZlibF.Proof.«inflate.c.default-loop»
import ZlibF.Proof.«inflate.c.direct-dispatch-cursors»
import ZlibF.Proof.«inflate.c.normal-dispatch-mode»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Direct DICT returns publish final cursors. Other direct returns come
from the loop entry and preserve its registers and heap exactly. -/
def DirectCursorMeaning (r : ZStreamRef) (initialHeap : Heap) (initial : IL)
    (outcome : Except Ex Unit) (regs : IL) (after : Heap) : Prop :=
  match outcome with
  | .error (.ret code) =>
      (code = Z_NEED_DICT → ∀ stream, r.get after = some stream → RestoredCursors stream regs) ∧
      (code ≠ Z_NEED_DICT → regs = initial ∧ after = initialHeap)
  | _ => True

/-- The actual complete mode loop publishes DICT cursors, while other
direct returns preserve its entry heap and registers. The normal-iteration
mode bound rules out entering MEM or SYNC after any continuing iteration. -/
theorem inflate_default_raw_direct_cursor_loop {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (raw : RawFastIO l) (incoming : l.bits.toNat ≤ 39) :
    ∃ exit regs after stream state used made, used ≤ bs.length ∧
      runX (xwhile (pure true) (inflate_dispatch c)) l h = .ok ((.error exit, regs), after) ∧
      DefaultStateJ after r zs stream state ∧ DispatchBuffers after r regs (bs.drop used) ∧
      RawFastIO regs ∧ regs.bits.toNat ≤ 39 ∧ ByteViewSizes h after ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = inputAdvance l.put made ∧ regs.left.toNat + made = l.left.toNat ∧
      DirectCursorMeaning r h l (.error exit) regs after := by
  let P := fun regs heap => DefaultLoopInv r zs h l bs regs heap ∧
    ∀ state, heap.istates zs = some state → state.mode ≤ BAD ∨ (regs = l ∧ heap = h)
  let Q := fun (outcome : Except Ex Unit) (regs : IL) (after : Heap) => outcome ≠ .ok () ∧
    DefaultLoopInv r zs h l bs regs after ∧ DirectCursorMeaning r h l outcome regs after
  have initial : P l h := ⟨⟨z, s, 0, 0, by omega, invariant,
    by simpa only [List.drop_zero] using buffers, raw, incoming, ByteViewSizes.refl h,
    (inputAdvance_zero l.next).symm, by rfl, (inputAdvance_zero l.put).symm, by rfl⟩,
    fun _ _ => Or.inr ⟨rfl, rfl⟩⟩
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
    intro regs heap ⟨current, marker⟩
    obtain ⟨stream, state, used, made, bound, currentJ, packet, currentRaw, bits,
      sizes, next, count, put, left⟩ := current
    have currentEnv : Env c heap r zs stream state := ⟨E.strm, E.st, currentJ.good.live.hz, currentJ.good.live.hs⟩
    obtain ⟨outcome, finalRegs, finalHeap, finalStream, finalState, used2, made2, bound2,
      run, finalJ, finalPacket, finalSizes, next2, count2, put2, left2, finalBits, progress⟩ :=
      inflate_dispatch_default_state_rank currentEnv currentJ packet currentRaw bits
    have totalBound : used + used2 ≤ bs.length := by simp only [List.length_drop] at bound2; omega
    have final : DefaultLoopInv r zs h l bs finalRegs finalHeap := by
      refine ⟨finalStream, finalState, used + used2, made + made2, totalBound, finalJ,
        ?_, currentRaw.advance next2 put2, finalBits, sizes.trans finalSizes, ?_, ?_, ?_, ?_⟩
      · simpa only [List.drop_drop, Nat.add_comm] using finalPacket
      · rw [next2, next, inputAdvance_add]
      · omega
      · rw [put2, put, inputAdvance_add]
      · omega
    have direct : DirectCursorMeaning r h l outcome finalRegs finalHeap := by
      cases outcome with
      | ok value => trivial
      | error exit =>
        cases exit with
        | leave => trivial
        | ret code =>
          have classified := inflate_dispatch_direct_cursors currentEnv currentJ.good packet.bits run finalJ.good.live.hz
          refine ⟨?_, ?_⟩
          · intro needed observed get
            have same : finalStream = observed := Option.some.inj (finalJ.good.live.hz.symm.trans get)
            rw [← same]
            exact classified.1 needed
          · intro notNeeded
            obtain ⟨high, regsEq, heapEq⟩ := classified.2 notNeeded
            rcases marker state currentJ.good.live.hs with low | ⟨originalRegs, originalHeap⟩
            · have lowNat := UInt32.le_iff_toNat_le.mp low
              have highNat := UInt32.lt_iff_toNat_lt.mp high
              omega
            · exact ⟨regsEq.trans originalRegs, heapEq.trans originalHeap⟩
    refine ⟨.ok true, regs, heap, rfl, ?_⟩
    cases outcome with
    | error fault =>
      refine ⟨.error fault, finalRegs, finalHeap, ?_, ?_⟩
      · rw [runX_bind, run]
      · exact ⟨(by intro impossible; cases impossible), final, direct⟩
    | ok value =>
      cases value
      have modeBound := inflate_dispatch_default_normal_mode currentEnv currentJ packet currentRaw bits run finalJ.good.live.hs
      have finalP : P finalRegs finalHeap := by
        refine ⟨final, ?_⟩
        intro observed get
        have same : finalState = observed := Option.some.inj (finalJ.good.live.hs.symm.trans get)
        exact Or.inl (same ▸ modeBound)
      refine ⟨.ok false, finalRegs, finalHeap, ?_, finalP, ?_⟩
      · rw [runX_bind, run]
        rfl
      · rw [defaultHeapRank_eq finalJ.good, defaultHeapRank_eq currentJ.good]
        exact progress rfl
  have budget : defaultHeapRank zs l h + 2 < fuel := by
    rw [defaultHeapRank_eq invariant.good]
    exact dispatchRank_fuel l s.mode incoming
  obtain ⟨outcome, regs, after, run, stopped, final, direct⟩ :=
    xwhileBrk_rank P (defaultHeapRank zs) Q step initial budget
  cases outcome with
  | ok unit => exact False.elim (stopped (by cases unit; rfl))
  | error exit =>
    obtain ⟨stream, state, used, made, bound, finalJ, packet, finalRaw, bits,
      sizes, next, count, put, left⟩ := final
    exact ⟨exit, regs, after, stream, state, used, made, bound, run, finalJ, packet,
      finalRaw, bits, sizes, next, count, put, left, direct⟩

end Zlib.Inflate.Proofs
