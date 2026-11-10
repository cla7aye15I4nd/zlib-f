import ZlibF.Proof.«inflate.c.fast-view-break-body-account-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- A later fast-loop iteration that sees an end-of-block root code
produces an accounted stopped step of the actual body and condition. -/
theorem FastLoopReady.no_pull_end_step_account
    {ctx : FastLoopContext} {h : Heap}
    {q : Zlib.Inffast.L} {startOff startBits : Nat}
    (ready : FastLoopReady ctx h q)
    (account : FastInputAccount ctx startOff startBits q)
    (held : 15 ≤ q.bits.toNat)
    (indexBound : ctx.baseOff +
      (q.hold &&& ctx.c.lmask.toUInt64).toNat < ctx.codes.size)
    (codeWidth : ctx.codes[ctx.baseOff +
      (q.hold &&& ctx.c.lmask.toUInt64).toNat].bits.toNat ≤ 15)
    (nonzero : ctx.codes[ctx.baseOff +
      (q.hold &&& ctx.c.lmask.toUInt64).toNat].op ≠ 0)
    (notBase : (ctx.codes[ctx.baseOff +
      (q.hold &&& ctx.c.lmask.toUInt64).toNat].op.toUInt32 &&&
      16 != 0) = false)
    (notLink : (ctx.codes[ctx.baseOff +
      (q.hold &&& ctx.c.lmask.toUInt64).toNat].op.toUInt32 &&&
      64 == 0) = false)
    (endCode : (ctx.codes[ctx.baseOff +
      (q.hold &&& ctx.c.lmask.toUInt64).toNat].op.toUInt32 &&&
      32 != 0) = true) :
    ∃ result after,
      C.run (Zlib.Inffast.inflate_fast_body ctx.c q) h =
        .ok (result, after) ∧
      fastLoopCond ctx result after =
        .ok ((false, result), after) ∧
      FastLoopExit ctx after result ∧
      FastInputAccount ctx startOff startBits result := by
  rcases ready with ⟨slow, bs, output, inOff, outOff,
    packet, invariant, buffers, codesGet, distGet,
    bitsBound, leftEq, outEq, putPtr, nextPtr, lastPtr,
    inputMargin, outPtr, outputGet, outputWrite,
    outputSize, current, beginLe, span, guard⟩
  have heldSlow : 15 ≤ slow.bits.toNat := by
    rw [← packet.bits]
    exact held
  have codeBits : ctx.codes[ctx.baseOff +
      (q.hold &&& ctx.c.lmask.toUInt64).toNat].bits.toNat ≤
      slow.bits.toNat := by omega
  obtain ⟨result, slowNext, bodyRun, broke,
    finalAccount, finalPacket, finalJ, finalBuffers⟩ :=
    packet.fast_body_no_pull_end_account_default_state
      account invariant buffers ctx.statePtr ctx.mode
      ctx.lcodePtr codesGet ctx.lenSafe ctx.lenMask
      heldSlow indexBound codeBits codeWidth nonzero
      notBase notLink endCode
  let after := setI h ctx.zs { ctx.s with mode := TYPE }
  have condition : fastLoopCond ctx result after =
        .ok ((false, result), after) := by
    simp [fastLoopCond, broke]
  have final : FastLoopExit ctx after result :=
    ⟨slowNext, bs, ctx.z, { ctx.s with mode := TYPE },
      finalPacket, finalJ, finalBuffers⟩
  exact ⟨result, after, bodyRun, condition,
    final, finalAccount⟩

end Zlib.Inflate.Proofs
