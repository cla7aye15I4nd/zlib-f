import ZlibF.Proof.«inflate.c.fast-view-break-loop-account-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- A stopped actual body result is also the result of the enclosing
fast `do ... while` loop. Keep the monad application explicit so the
kernel checks the one-step composition without expanding `C.run`. -/
theorem fastLoop_stopped_once
    {ctx : FastLoopContext} {h after : Heap}
    {q result : Zlib.Inffast.L}
    (bodyRun : (Zlib.Inffast.inflate_fast_body ctx.c q) h =
      .ok (result, after))
    (condition : fastLoopCond ctx result after =
      .ok ((false, result), after)) :
    (cdoWhile (Zlib.Inffast.inflate_fast_body ctx.c)
      (fun current => do
        if current.broke then pure (false, current)
        else if ← Ptr.lt current.in_ ctx.c.last then
          pure (← Ptr.lt current.out ctx.c.end_, current)
        else pure (false, current)) q) h =
      .ok (result, after) :=
  Zlib.Inffast.Proofs.cdoWhile_one
    (body := Zlib.Inffast.inflate_fast_body ctx.c)
    (cond := fastLoopCond ctx) bodyRun condition

/-- A no-refill end-of-block root code exits the actual fast loop with
the call-entry input account retained. -/
theorem FastLoopReady.no_pull_end_loop_account
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
      (cdoWhile (Zlib.Inffast.inflate_fast_body ctx.c)
        (fun current => do
          if current.broke then pure (false, current)
          else if ← Ptr.lt current.in_ ctx.c.last then
            pure (← Ptr.lt current.out ctx.c.end_, current)
          else pure (false, current)) q) h =
        .ok (result, after) ∧
      FastLoopExit ctx after result ∧
      FastInputAccount ctx startOff startBits result := by
  obtain ⟨result, after, bodyRun, condition,
    final, finalAccount⟩ :=
    ready.no_pull_end_step_account account held indexBound
      codeWidth nonzero notBase notLink endCode
  have directBody :
      (Zlib.Inffast.inflate_fast_body ctx.c q) h =
        .ok (result, after) := bodyRun
  exact ⟨result, after,
    fastLoop_stopped_once directBody condition,
    final, finalAccount⟩

end Zlib.Inflate.Proofs
