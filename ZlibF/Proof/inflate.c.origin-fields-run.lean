import ZlibF.Proof.«inflate.c.origin-fields-loop»
import ZlibF.Proof.«inflate.c.default-view-run»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual public-body entry normalizes TYPE and loads cursors while
retaining both default origins. The complete actual loop carries them to exit. -/
theorem inflate_run_default_origin {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s)
    (before : DefaultOriginState h r zs z s) (buffers : StreamBuffers h r)
    (nonnull : z.next_out ≠ .null) (inputValid : z.next_in = .null → z.avail_in = 0) :
    ∃ (bs : List UInt8), ∃ exit regs after stream state used made, used ≤ bs.length ∧
      runX (inflate_run c) IL.init h = .ok ((.error exit, regs), after) ∧
      DefaultOriginState after r zs stream state ∧ DispatchBuffers after r regs (bs.drop used) ∧
      regs.bits.toNat ≤ 39 ∧ ByteViewSizes h after ∧
      regs.next = inputAdvance z.next_in used ∧ regs.have_.toNat + used = z.avail_in.toNat ∧
      regs.put = inputAdvance z.next_out made ∧ regs.left.toNat + made = z.avail_out.toNat := by
  obtain ⟨heap0, state0, bs, entryRun, currentJ, env, packet, bits, sizes, frame, _⟩ :=
    inflate_run_default_view_entry E before.toDefaultStateJ buffers nonnull inputValid
  have origins := before.decode_update currentJ frame
  obtain ⟨exit, regs, after, stream, state, used, made, bound, run, final, finalPacket,
    finalBits, finalSizes, next, count, put, left⟩ := inflate_default_origin_loop env origins packet bits
  exact ⟨bs, exit, regs, after, stream, state, used, made, bound, entryRun.trans run,
    final, finalPacket, finalBits, sizes.trans finalSizes, next, count, put, left⟩

#print axioms inflate_run_default_origin
end Zlib.Inflate.Proofs
