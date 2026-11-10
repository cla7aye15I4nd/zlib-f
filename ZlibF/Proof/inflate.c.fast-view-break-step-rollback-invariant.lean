import ZlibF.Proof.«inflate.c.fast-view-break-loop-account-invariant»
import ZlibF.Proof.«inflate.c.fast-view-writeback-rollback-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- The actual no-refill end-of-block body reaches a stopped condition,
then its whole-byte input rollback is safe. The input account is anchored
at the original fast-call entry rather than the current loop iteration. -/
theorem FastLoopReady.no_pull_end_step_rollback
    {ctx : FastLoopContext} {h : Heap}
    {q : Zlib.Inffast.L} {startOff startBits : Nat}
    (ready : FastLoopReady ctx h q)
    (account : FastInputAccount ctx startOff startBits q)
    (initialBits : startBits < 8)
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
    ∃ result after off input,
      C.run (Zlib.Inffast.inflate_fast_body ctx.c q) h =
        .ok (result, after) ∧
      fastLoopCond ctx result after =
        .ok ((false, result), after) ∧
      FastLoopExit ctx after result ∧
      result.in_ = .ref ctx.inputRef off ∧
      Space.get after ctx.inputRef = some input ∧
      startOff ≤ off - (result.bits >>> 3).toNat ∧
      C.run (Zlib.Inffast.subn result.in_
        (result.bits >>> 3)) after =
        .ok (.ref ctx.inputRef
          (off - (result.bits >>> 3).toNat), after) := by
  obtain ⟨result, after, bodyRun, stopped,
    final, finalAccount⟩ :=
    ready.no_pull_end_step_account account held indexBound
      codeWidth nonzero notBase notLink endCode
  obtain ⟨off, input, cursor, inputGet, lower,
    rollback⟩ := final.rollback_accounted finalAccount
      initialBits
  exact ⟨result, after, off, input, bodyRun, stopped,
    final, cursor, inputGet, lower, rollback⟩

end Zlib.Inflate.Proofs
