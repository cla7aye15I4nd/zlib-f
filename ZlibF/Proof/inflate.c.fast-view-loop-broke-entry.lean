import ZlibF.Proof.«inflate.c.fast-view-prelude-ready-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- The source-order fast prelude starts with a clear break flag. This is
an actual constructor fact, not a caller precondition. -/
theorem fastEntryPrefix_ready_not_broken
    {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState}
    {slow : IL} {bs : List UInt8}
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
      slow.bits < 8) = true) :
    ∃ (ctx : FastLoopContext) (q : Zlib.Inffast.L),
      C.run (fastEntryPrefix (some r) slow.out_) h =
        .ok ((ctx.c, q), h) ∧
      FastLoopReady ctx h q ∧ q.broke = false := by
  obtain ⟨ctx, q, run, ready⟩ :=
    fastEntryPrefix_ready invariant buffers mode inputCursor
      inputCount outputCursor outputCount stateHold stateBits fast
  obtain ⟨ir, dest, io, oo, _, _, sourceRun⟩ :=
    fastEntryPrefix_run invariant.good invariant.platform
      buffers (invariant.tables mode) inputCursor inputCount
      outputCursor outputCount stateHold stateBits fast
  have same := run.symm.trans sourceRun
  simp only [Except.ok.injEq, Prod.mk.injEq] at same
  exact ⟨ctx, q, run, ready, congrArg Zlib.Inffast.L.broke same.1.2⟩

/-- A continuing actual loop condition can only return true with a clear
break flag; it does not modify the local registers or heap. -/
theorem fastLoopCond_true_not_broken
    {ctx : FastLoopContext} {q next : Zlib.Inffast.L}
    {h after : Heap}
    (run : C.run (fastLoopCond ctx q) h = .ok ((true, next), after)) :
    q.broke = false := by
  by_cases broken : q.broke = true
  · simp [fastLoopCond, C.run, broken] at run
  · cases flag : q.broke <;> simp_all

#print axioms fastEntryPrefix_ready_not_broken
#print axioms fastLoopCond_true_not_broken

end Zlib.Inflate.Proofs
