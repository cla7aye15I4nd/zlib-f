import ZlibF.Proof.«inflate.c.fast-committed-output-segment»
import ZlibF.Proof.«inflate.c.fast-view-prelude-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual translated fast prelude starts its local output cursor at
the caller's `next_out`, independently of input bytes or table contents. -/
theorem fastEntryPrefix_output_of_run
    {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {slow : IL} {bs : List UInt8}
    {c0 : Zlib.Inffast.Ctx} {q : Zlib.Inffast.L}
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (mode : DataTableMode s.mode)
    (inputCursor : z.next_in = slow.next)
    (inputCount : z.avail_in = slow.have_)
    (outputCursor : z.next_out = slow.put)
    (outputCount : z.avail_out = slow.left)
    (stateHold : s.hold = slow.hold)
    (stateBits : s.bits = slow.bits)
    (fast : (slow.have_ >= 6 && slow.left >= 258 &&
      slow.bits < 8) = true)
    (run : C.run (fastEntryPrefix (some r) slow.out_) h =
      .ok ((c0, q), h)) :
    q.out = slow.put := by
  obtain ⟨ir, dest, io, oo, nextPtr, putPtr, actualRun⟩ :=
    fastEntryPrefix_run invariant.good invariant.platform buffers
      (invariant.tables mode) inputCursor inputCount outputCursor
      outputCount stateHold stateBits fast
  have same := Except.ok.inj (run.symm.trans actualRun)
  have qEq := congrArg Prod.snd (congrArg Prod.fst same)
  exact congrArg Zlib.Inffast.L.out qEq

#print axioms fastEntryPrefix_output_of_run
end Zlib.Inflate.Proofs
