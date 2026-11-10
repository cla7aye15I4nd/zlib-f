import ZlibF.Proof.«inflate.c.input-base-loop»
import ZlibF.Proof.«inflate.c.default-run»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual default entry writes the public input count into in_.
All literal macro bodies, modes and the complete loop preserve this value,
including direct dictionary returns. This closes the input-base obligation
for final counter charging without adding a caller counter premise. -/
theorem inflate_run_default_input_base {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {regs : IL} {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0)
    (run : runX (inflate_run c) IL.init h = .ok ((outcome, regs), after)) :
    regs.in_ = z.avail_in := by
  obtain ⟨heap0, state0, bs, cut, current, env0, packet, bits, sizes, frame, heapEq⟩ :=
    inflate_run_default_state_entry E invariant buffers nonnull inputValid
  have executed : runX (xwhile (pure true) (inflate_dispatch c)) (dispatchRegs z state0) heap0 =
      .ok ((outcome, regs), after) := cut.symm.trans run
  exact inflate_loop_input_base executed

end Zlib.Inflate.Proofs
