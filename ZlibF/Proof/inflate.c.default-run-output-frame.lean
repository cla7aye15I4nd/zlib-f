import ZlibF.Proof.«inflate.c.default-loop-output-frame»
import ZlibF.Proof.«inflate.c.default-view-run»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- TYPE normalization, LOAD and the complete actual default loop preserve
one exact cumulative output frame. This is the real inflate_run body,
before public leave, window update and temporary-storage cleanup. -/
theorem inflate_run_default_view_exact_frame {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s)
    (invariant : DefaultStateJ h r zs z s) (buffers : StreamBuffers h r)
    (nonnull : z.next_out ≠ .null) (inputValid : z.next_in = .null → z.avail_in = 0) :
    ∃ (bs : List UInt8), ∃ exit regs after stream state used made, used ≤ bs.length ∧
      runX (inflate_run c) IL.init h = .ok ((.error exit, regs), after) ∧
      DefaultStateJ after r zs stream state ∧ DispatchBuffers after r regs (bs.drop used) ∧
      regs.bits.toNat ≤ 39 ∧ ByteViewSizes h after ∧
      regs.next = inputAdvance z.next_in used ∧ regs.have_.toNat + used = z.avail_in.toNat ∧
      regs.put = inputAdvance z.next_out made ∧ regs.left.toNat + made = z.avail_out.toNat ∧
      FastMemoryMetaFrame r h after ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ b = zs) [⟨z.next_out, made⟩] := by
  obtain ⟨heap0, state0, bs, entryRun, currentJ, currentEnv, packet, bits, sizes, _, heapEq, _⟩ :=
    inflate_run_default_view_entry E invariant buffers nonnull inputValid
  obtain ⟨exit, regs, after, stream, state, used, made, bound, run, final, finalPacket,
    finalBits, finalSizes, next, count, put, left, _metadata, frame⟩ :=
    inflate_default_view_frame_loop currentEnv currentJ packet bits
  have actual := entryRun.trans run
  have metadata := fastMemoryMetaFrameX_inflate_run r c E.strm IL.init h (.error exit) regs after actual
  obtain ⟨dest, array, off, pointer, get, write, _⟩ :=
    callerRange_slow_output currentJ.good (dispatchRegs z state0) packet.output.range packet.output.nonnull
      packet.output.count packet.output.produced
  change z.next_out = .ref dest off at pointer
  have getBefore : Space.get h dest = some array := by
    rw [heapEq, byte_view_get_setI] at get
    exact get
  have writeBefore : Space.ro h dest = false := by
    rw [heapEq, byte_view_ro_setI] at write
    exact write
  have preFrame : RecordFrame r (some (.tab zs)) h heap0 := by
    rw [heapEq]
    exact RecordFrame.setI r zs E.hs state0
  have writeAfter : Space.ro after dest = false := by
    rw [byte_view_ro_of_ro_eq (congrArg Prod.fst metadata) dest]
    exact writeBefore
  change BufferFrame heap0 after (fun b => StreamRoot r b ∨ b = zs) [⟨z.next_out, made⟩] at frame
  refine ⟨bs, exit, regs, after, stream, state, used, made, bound, actual,
    final, finalPacket, finalBits, sizes.trans finalSizes, next, count, put, left, metadata, ?_⟩
  rw [pointer] at frame ⊢
  exact record_frame_then_output preFrame frame getBefore writeBefore writeAfter

#print axioms inflate_run_default_view_exact_frame
end Zlib.Inflate.Proofs
