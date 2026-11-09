import ZlibF.Proof.«inflate.c.local-public-resources-dispatch»
import ZlibF.Proof.«inflate.c.output-frame-live-compose»
import ZlibF.Proof.«inflate.c.default-loop-output-frame»

namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Persistent exact frame and allocation metadata for the actual loop. -/
def DefaultViewFrameLoopInv (cutoff : Nat) (r : ZStreamRef) (zs : Nat) (initialHeap : Heap) (initial : IL) (input : List UInt8)
    (regs : IL) (heap : Heap) : Prop :=
  ∃ stream state used made, used ≤ input.length ∧ LocalStateJ heap cutoff r zs stream state ∧
    DispatchBuffers heap r regs (input.drop used) ∧ regs.bits.toNat ≤ 39 ∧
    ByteViewSizes initialHeap heap ∧ regs.next = inputAdvance initial.next used ∧
    regs.have_.toNat + used = initial.have_.toNat ∧ regs.put = inputAdvance initial.put made ∧
    regs.left.toNat + made = initial.left.toNat ∧
    FastMemoryMetaFrame r initialHeap heap ∧
    BufferFrame initialHeap heap (fun b => StreamRoot r b ∨ b = zs) [⟨initial.put, made⟩]

/-- The actual complete default mode loop changes only its cumulative
produced output prefix and the private stream/state records. Its proof
retains the same initialized state, caller packet and strict rank. -/
theorem inflate_default_view_frame_loop {c : Ctx} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : LocalStateJ h cutoff r zs z s)
    (buffers : DispatchBuffers h r l bs) (incoming : l.bits.toNat ≤ 39) :
    ∃ exit regs after stream state used made, used ≤ bs.length ∧
      runX (xwhile (pure true) (inflate_dispatch c)) l h = .ok ((.error exit, regs), after) ∧
      LocalStateJ after cutoff r zs stream state ∧ DispatchBuffers after r regs (bs.drop used) ∧
      regs.bits.toNat ≤ 39 ∧ ByteViewSizes h after ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = inputAdvance l.put made ∧ regs.left.toNat + made = l.left.toNat ∧
      FastMemoryMetaFrame r h after ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ b = zs) [⟨l.put, made⟩] := by
  obtain ⟨dest, array, off, pointer, get, write, _⟩ :=
    callerRange_slow_output invariant.good l buffers.output.range buffers.output.nonnull
      buffers.output.count buffers.output.produced
  let P := DefaultViewFrameLoopInv cutoff r zs h l bs
  let Q := fun (outcome : Except Ex Unit) (regs : IL) (after : Heap) => outcome ≠ .ok () ∧ P regs after
  have initial : P l h := ⟨z, s, 0, 0, by omega, invariant,
    by simpa only [List.drop_zero] using buffers, incoming, ByteViewSizes.refl h,
    (inputAdvance_zero l.next).symm, by rfl, (inputAdvance_zero l.put).symm, by rfl, FastMemoryMetaFrame.refl r h,
    bufferFrame_live_refl E.hz E.hs [⟨l.put, 0⟩]⟩
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
            | .ok false => P regs2 heap2 ∧ defaultViewHeapRank zs regs2 heap2 < defaultViewHeapRank zs regs heap)) := by
    intro regs heap current
    obtain ⟨stream, state, used, made, bound, currentJ, packet, bits,
      sizes, next, count, put, left, metadata, frame⟩ := current
    have currentEnv : Env c heap r zs stream state := ⟨E.strm, E.st, currentJ.good.live.hz, currentJ.good.live.hs⟩
    obtain ⟨outcome, finalRegs, finalHeap, finalStream, finalState, used2, made2, bound2,
      run, finalJ, finalPacket, finalSizes, next2, count2, put2, left2, finalBits, progress, frame2⟩ :=
      inflate_dispatch_default_view_state_frame_rank currentEnv currentJ packet bits
    have metadata2 := fastMemoryMetaFrameX_inflate_dispatch r c E.strm regs heap outcome finalRegs finalHeap run
    have totalMetadata := metadata.trans metadata2
    have liveEq : heap.live = h.live := congrArg (fun x => x.2.2.2.2.2.2) metadata
    have writeMiddle : Space.ro heap dest = false := by
      rw [byte_view_ro_of_ro_eq (congrArg Prod.fst metadata) dest]
      exact write
    have writeFinal : Space.ro finalHeap dest = false := by
      rw [byte_view_ro_of_ro_eq (congrArg Prod.fst totalMetadata) dest]
      exact write
    have firstFrame := frame
    rw [pointer] at firstFrame
    have secondFrame := frame2
    rw [put, pointer] at secondFrame
    change BufferFrame heap finalHeap (fun b => StreamRoot r b ∨ b = zs)
      [⟨.ref dest (off + made), made2⟩] at secondFrame
    have totalFrame : BufferFrame h finalHeap (fun b => StreamRoot r b ∨ b = zs) [⟨l.put, made + made2⟩] := by
      rw [pointer]
      exact output_prefix_buffer_frame_trans_live firstFrame secondFrame
        (fun b live => by rw [liveEq]; exact live) get writeMiddle writeFinal
    have totalBound : used + used2 ≤ bs.length := by simp only [List.length_drop] at bound2; omega
    have final : P finalRegs finalHeap := by
      refine ⟨finalStream, finalState, used + used2, made + made2, totalBound, finalJ,
        ?_, finalBits, sizes.trans finalSizes, ?_, ?_, ?_, ?_, totalMetadata, totalFrame⟩
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
      · rw [defaultViewHeapRank_eq finalJ.good, defaultViewHeapRank_eq currentJ.good]
        exact progress rfl
  have budget : defaultViewHeapRank zs l h + 2 < fuel := by
    rw [defaultViewHeapRank_eq invariant.good]
    exact dispatchRank_fuel l s.mode incoming
  obtain ⟨outcome, regs, after, run, stopped, final⟩ :=
    xwhileBrk_rank P (defaultViewHeapRank zs) Q step initial budget
  cases outcome with
  | ok unit => exact False.elim (stopped (by cases unit; rfl))
  | error exit =>
    obtain ⟨stream, state, used, made, bound, finalJ, packet, bits,
      sizes, next, count, put, left, metadata, frame⟩ := final
    exact ⟨exit, regs, after, stream, state, used, made, bound, run, finalJ, packet,
      bits, sizes, next, count, put, left, metadata, frame⟩

#print axioms inflate_default_view_frame_loop
end Zlib.Inflate.Local
