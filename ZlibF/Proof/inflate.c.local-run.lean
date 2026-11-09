import ZlibF.Proof.«inflate.c.local-loop»
import ZlibF.Proof.«inflate.c.local-run-entry»
namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false
theorem inflate_run_default_view {c : Ctx} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s)
    (invariant : LocalStateJ h cutoff r zs z s) (buffers : StreamBuffers h r)
    (nonnull : z.next_out ≠ .null) (inputValid : z.next_in = .null → z.avail_in = 0)
    :
    ∃ (bs : List UInt8), ∃ exit regs after stream state used made, used ≤ bs.length ∧
      runX (inflate_run c) IL.init h = .ok ((.error exit, regs), after) ∧
      LocalStateJ after cutoff r zs stream state ∧ DispatchBuffers after r regs (bs.drop used) ∧
      regs.bits.toNat ≤ 39 ∧ ByteViewSizes h after ∧
      regs.next = inputAdvance z.next_in used ∧ regs.have_.toNat + used = z.avail_in.toNat ∧
      regs.put = inputAdvance z.next_out made ∧ regs.left.toNat + made = z.avail_out.toNat := by
  obtain ⟨heap0, state0, bs, entryRun, currentJ, currentEnv, packet, bits, sizes, _, _⟩ :=
    inflate_run_default_view_entry E invariant buffers nonnull inputValid
  obtain ⟨exit, regs, after, stream, state, used, made, bound, run, final, finalPacket,
    finalBits, finalSizes, next, count, put, left⟩ :=
    inflate_default_view_loop currentEnv currentJ packet bits
  exact ⟨bs, exit, regs, after, stream, state, used, made, bound, entryRun.trans run,
    final, finalPacket, finalBits, sizes.trans finalSizes, next, count, put, left⟩


#print axioms inflate_run_default_view
end Zlib.Inflate.Local
