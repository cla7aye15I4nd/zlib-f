import ZlibF.Proof.«inflate.c.fast-view-caller-bit-budget»
import ZlibF.Proof.«inflate.c.fast-view-caller-buffers»
import ZlibF.Proof.«inflate.c.fast-view-entire-tight-frame»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual fast callee returns a complete caller buffer packet on
public byte views. The output interval frame is obtained from its actual
translated execution; no callee contract or RawFastIO premise is assumed. -/
theorem inflate_fast_default_view_buffers
    {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {slow : IL} {bs : List UInt8}
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs) (mode : DataTableMode s.mode)
    (inputCursor : z.next_in = slow.next) (inputCount : z.avail_in = slow.have_)
    (outputCursor : z.next_out = slow.put) (outputCount : z.avail_out = slow.left)
    (stateHold : s.hold = slow.hold) (stateBits : s.bits = slow.bits)
    (fast : (slow.have_ >= 6 && slow.left >= 258 && slow.bits < 8) = true) :
    ∃ finished zNext sNext used made regs, used ≤ bs.length ∧
      C.run (Zlib.Inffast.inflate_fast (some r) slow.out_) h = .ok ((), finished) ∧
      DefaultStateJ finished r zs zNext sNext ∧
      DispatchBuffers finished r regs (bs.drop used) ∧ ByteViewSizes h finished ∧
      regs.next = inputAdvance slow.next used ∧ regs.have_.toNat + used = slow.have_.toNat ∧
      regs.put = inputAdvance slow.put made ∧ regs.left.toNat + made = slow.left.toNat ∧
      regs.bits.toNat < 8 ∧ regs.bits.toNat ≤ slow.bits.toNat + 8 * used ∧
      sNext.window = s.window ∧
      (sNext.mode = s.mode ∨ sNext.mode = TYPE ∨ sNext.mode = BAD) ∧
      regs = { slow with
        put := zNext.next_out, left := zNext.avail_out,
        next := zNext.next_in, have_ := zNext.avail_in, hold := sNext.hold, bits := sNext.bits } := by
  obtain ⟨finished, zNext, sNext, used, made, run, current,
    accounting, sizes, window, modes, small, readonly, live, nalloc, budget⟩ :=
    inflate_fast_default_view_caller_budget invariant buffers mode inputCursor
      inputCount outputCursor outputCount stateHold stateBits fast
  obtain ⟨framed, framedZ, framedS, frameRun, framedJ, frame⟩ :=
    inflate_fast_default_view_tight_frame invariant buffers mode inputCursor
      inputCount outputCursor outputCount stateHold stateBits fast
  have sameHeap : finished = framed := congrArg Prod.snd
    (Except.ok.inj (run.symm.trans frameRun))
  subst framed
  let regs : IL := { slow with
    put := zNext.next_out, left := zNext.avail_out,
    next := zNext.next_in, have_ := zNext.avail_in, hold := sNext.hold, bits := sNext.bits }
  have sameAdvance (pointer : BPtr) (count : Nat) :
      advance pointer count = inputAdvance pointer count := by
    cases pointer <;> rfl
  have next : regs.next = inputAdvance slow.next used := by
    simpa only [inputCursor, regs, sameAdvance] using accounting.2.2.2.2.1
  have count : regs.have_.toNat + used = slow.have_.toNat := by
    simpa only [inputCount] using accounting.2.2.1
  have put : regs.put = inputAdvance slow.put made := by
    simpa only [outputCursor, regs, sameAdvance] using accounting.2.2.2.2.2.1
  have left : regs.left.toNat + made = slow.left.toNat := by
    simpa only [outputCount] using accounting.2.2.2.1
  have usedBound : used ≤ bs.length := by rw [← buffers.bits.have_eq]; omega
  obtain ⟨dest, output, off, pointer, get, write, room, countOld, producedOld, unowned⟩ :=
    callerRange_slow_output invariant.good slow buffers.output.range
      buffers.output.nonnull buffers.output.count buffers.output.produced
  have broadFrame : BufferFrame h finished
      (fun b => StreamRoot r b ∨ InflateOwned zs s b)
      [⟨slow.put, slow.left.toNat⟩] := by
    apply bufferFrame_weaken (fun b changed => ?_) frame
    rcases changed with stream | state
    · exact Or.inl stream
    · exact Or.inr (Or.inl state)
  have packet := buffers.output_frame_advance invariant.good current.good window
    sizes readonly pointer get broadFrame next count put left (by rfl) current.held
  exact ⟨finished, zNext, sNext, used, made, regs, usedBound, run, current,
    packet, sizes, next, count, put, left, small, budget, window, modes, rfl⟩

#print axioms inflate_fast_default_view_buffers
end Zlib.Inflate.Proofs
