import ZlibF.Proof.«inflate.c.fast-committed-restore-entry»
import ZlibF.Proof.«inflate.c.fast-view-public-buffers»
import ZlibF.Proof.«inflate.c.fast-view-entire-safe»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public ZlibF.Spec
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- The source prefix, finite semantic loop, and source suffix are the same
execution as the complete translated fast callee. The semantic-ready fact
is an internal representation invariant established at this actual prefix. -/
theorem FastCommittedLoop.WordReady.callee_join
    {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState}
    {slow : IL} {bs : List UInt8}
    {ctx : FastLoopContext} {initial : Zlib.Inffast.L}
    {p : FastCommittedLoop.Parameters ctx}
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
    (prefixRun : C.run (fastEntryPrefix (some r) slow.out_) h =
      .ok ((ctx.c, initial), h))
    (semantic : FastCommittedLoop.WordReady p h initial) :
    ∃ finished zNext sNext used made regs result after,
      C.run (Zlib.Inffast.inflate_fast (some r) slow.out_) h =
        .ok ((), finished) ∧
      DefaultStateJ finished r zs zNext sNext ∧
      DispatchBuffers finished r regs (bs.drop used) ∧
      regs.put = zNext.next_out ∧
      used ≤ bs.length ∧
      regs.next = inputAdvance slow.next used ∧
      regs.have_.toNat + used = slow.have_.toNat ∧
      regs.put = inputAdvance slow.put made ∧
      regs.left.toNat + made = slow.left.toNat ∧
      regs.bits.toNat < 8 ∧
      regs.bits.toNat ≤ slow.bits.toNat + 8 * used ∧
      C.run (cdoWhile (Zlib.Inffast.inflate_fast_body ctx.c)
        (fastLoopCond ctx) initial) h = .ok (result, after) ∧
      FastCommittedLoop.WordExit p after result ∧
      C.run (fastAfterLoopView ctx.c result) after =
        .ok ((), finished) := by
  obtain ⟨finished, zNext, sNext, used, made, regs, usedBound, callRun,
    current, finalBuffers, _, next, haveCount, put, left, small, budget, _, _, regsEq⟩ :=
    inflate_fast_default_view_buffers invariant buffers mode
      inputCursor inputCount outputCursor outputCount stateHold
      stateBits fast
  obtain ⟨result, after, loopRun, semanticExit⟩ := semantic.run
  have sourceRun := callRun
  rw [inflate_fast_prefix_split] at sourceRun
  change (do
      let pair ← fastEntryPrefix (some r) slow.out_
      fastAfterPrefix pair.1 pair.2) h = .ok ((), finished) at sourceRun
  unfold fastAfterPrefix at sourceRun
  change C.run (do
      let pair ← fastEntryPrefix (some r) slow.out_
      let q ← cdoWhile (Zlib.Inffast.inflate_fast_body pair.1)
        (fun q => do
          if q.broke then pure (false, q)
          else if ← Ptr.lt q.in_ pair.1.last then
            pure (← Ptr.lt q.out pair.1.end_, q)
          else pure (false, q)) pair.2
      fastAfterLoop pair.1 q) h = .ok ((), finished) at sourceRun
  unfold C.run at sourceRun
  change fastEntryPrefix (some r) slow.out_ h =
    .ok ((ctx.c, initial), h) at prefixRun
  simp only [bind_app, prefixRun] at sourceRun
  change (do
      let q ← cdoWhile (Zlib.Inffast.inflate_fast_body ctx.c)
        (fastLoopCond ctx) initial
      fastAfterLoop ctx.c q) h = .ok ((), finished) at sourceRun
  change (cdoWhile (Zlib.Inffast.inflate_fast_body ctx.c)
    (fastLoopCond ctx) initial) h = .ok (result, after) at loopRun
  simp only [bind_app] at sourceRun
  simp only [loopRun] at sourceRun
  have suffixRun : C.run (fastAfterLoopView ctx.c result) after =
      .ok ((), finished) := sourceRun
  have storedPut : regs.put = zNext.next_out := by
    rw [regsEq]
  exact ⟨finished, zNext, sNext, used, made, regs, result, after,
    callRun, current, finalBuffers, storedPut, usedBound, next, haveCount, put, left,
    small, budget, loopRun, semanticExit, suffixRun⟩

#print axioms FastCommittedLoop.WordReady.callee_join
end Zlib.Inflate.Proofs
