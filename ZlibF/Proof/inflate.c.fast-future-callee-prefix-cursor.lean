import ZlibF.Proof.«inflate.c.fast-future-writeback-views»
import ZlibF.Proof.«inflate.c.fast-future-loop-output-prefix-cursor»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public ZlibF.Spec
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- The translated complete fast call writes back the same physical output
cursor whose bytes form the independent decoded prefix. The source prefix
establishes the initial cursor, bit bound and context identity; the semantic
ready relation is an internal invariant established at that prefix. -/
theorem FastFutureReady.callee_output_prefix_cursor
    {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState}
    {slow : IL} {bs : List UInt8}
    {ctx : FastLoopContext} {initial : Zlib.Inffast.L}
    {L D : List Nat} {dict : List UInt8}
    {future tail : List Bool} {target : List UInt8}
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
    (semantic : FastFutureReady ctx L D dict future tail target h initial) :
    ∃ finished zNext sNext used made regs result after,
    ∃ (array : Array UInt8) (off : Nat) (next : List UInt8),
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
      FastFutureExitCursor ctx L D dict future tail target after result ∧
      C.run (fastAfterLoopView ctx.c result) after = .ok ((), finished) ∧
      zNext.next_out = result.out ∧
      result.out = .ref ctx.dest off ∧
      Space.get after ctx.dest = some array ∧
      Space.get finished ctx.dest = some array ∧
      ZlibF.Math.LZ77Copy.writtenBytes array off (off - ctx.bg) = next ∧
      next <+: target := by
  obtain ⟨finished, zNext, sNext, used, made, regs, result,
    after, callRun, current, finalBuffers, storedPut, usedBound, nextPtr,
    haveCount, putPtr, leftCount, small, budget,
    loopRun, _, suffixRun⟩ :=
    semantic.callee_join invariant buffers mode inputCursor
      inputCount outputCursor outputCount stateHold stateBits
      fast prefixRun
  obtain ⟨semanticResult, semanticAfter, semanticRun, semanticExit⟩ :=
    semantic.run_with_output_cursor
  have sameLoop : (result, after) = (semanticResult, semanticAfter) :=
    Except.ok.inj (loopRun.symm.trans semanticRun)
  cases sameLoop
  obtain ⟨ir, dest, io, oo, nextCursor, putCursor, exactRun⟩ :=
    fastEntryPrefix_run invariant.good invariant.platform buffers
      (invariant.tables mode) inputCursor inputCount outputCursor
      outputCount stateHold stateBits fast
  have samePrefix := Except.ok.inj (prefixRun.symm.trans exactRun)
  have exactStrm : ctx.c.strm = some r := by
    have field := congrArg
      (fun p : (Zlib.Inffast.Ctx × Zlib.Inffast.L) × Heap => p.1.1.strm)
      samePrefix
    simpa using field
  have exactState : ctx.c.state = some (.tab zs) := by
    have field := congrArg
      (fun p : (Zlib.Inffast.Ctx × Zlib.Inffast.L) × Heap => p.1.1.state)
      samePrefix
    simpa using field
  have sameR : ctx.r = r :=
    Option.some.inj (ctx.streamPtr.symm.trans exactStrm)
  have sameZs : ctx.zs = zs := by
    have eq := Option.some.inj (ctx.statePtr.symm.trans exactState)
    cases eq
    rfl
  have initialBits : initial.bits.toNat < 8 := by
    have bitsEq : initial.bits = slow.bits := by
      have field := congrArg
        (fun p : (Zlib.Inffast.Ctx × Zlib.Inffast.L) × Heap => p.1.2.bits)
        samePrefix
      simpa using field
    rw [bitsEq]
    have margins : slow.bits < 8 := by
      have facts : (6 ≤ slow.have_ ∧ 258 ≤ slow.left) ∧
          slow.bits < 8 := by
        simpa only [Bool.and_eq_true, decide_eq_true_eq] using fast
      exact facts.2
    exact UInt32.lt_iff_toNat_lt.mp margins
  have currentCtx : DefaultStateJ finished ctx.r ctx.zs zNext sNext := by
    simpa only [sameR, sameZs] using current
  have storedCursor : zNext.next_out = result.out :=
    semantic.writeback_output_cursor initialBits semanticRun
      suffixRun currentCtx
  obtain ⟨array, off, outputBytes, physical, get, exactBytes,
    outputPrefix⟩ := semanticExit.output_prefix_at_cursor
  have finalGet : Space.get finished ctx.dest = some array := by
    rw [semantic.writeback_byte_views initialBits semanticRun suffixRun ctx.dest]
    exact get
  exact ⟨finished, zNext, sNext, used, made, regs, result,
    after, array, off, outputBytes, callRun, current,
    finalBuffers, storedPut, usedBound, nextPtr, haveCount, putPtr,
    leftCount, small, budget, semanticRun, semanticExit, suffixRun,
    storedCursor, physical, get, finalGet, exactBytes, outputPrefix⟩

#print axioms FastFutureReady.callee_output_prefix_cursor
end Zlib.Inflate.Proofs
