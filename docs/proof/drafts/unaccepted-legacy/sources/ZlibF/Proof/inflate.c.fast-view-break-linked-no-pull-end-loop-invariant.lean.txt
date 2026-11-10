import ZlibF.Proof.«inflate.c.fast-view-break-linked-no-pull-end-body-invariant»
import ZlibF.Proof.«inflate.c.fast-view-break-loop-run-invariant»
import ZlibF.Proof.«inflate.c.fast-view-writeback-rollback-invariant»
import ZlibF.Proof.«inflate.c.fast-view-break-refill-root-cases-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- A linked end-of-block leaf reached without initial refill exits the
actual outer loop and returns held input bytes within the caller range. -/
theorem FastInputPacket.no_pull_linked_end_loop_rollback
    {ctx : FastLoopContext} {h : Heap} {slow : IL}
    {bs : List UInt8} {q : Zlib.Inffast.L}
    {startOff startBits : Nat}
    (packet : FastInputPacket h slow bs q)
    (invariant : DefaultStateJ h ctx.r ctx.zs ctx.z ctx.s)
    (buffers : DispatchBuffers h ctx.r slow bs)
    (account : FastInputAccount ctx startOff startBits q)
    (initialBits : startBits < 8)
    (held : 15 ≤ slow.bits.toNat)
    (codesGet : Space.get h ctx.codeRef = some ctx.codes)
    (linkedEnd : FastLinkedEnd h ctx.codes ctx.baseOff
      ctx.c q ctx.codeRef) :
    FastLoopRollback ctx h q startOff := by
  obtain ⟨result, slowNext, bodyRun, broke,
    finalAccount, finalPacket, finalJ, finalBuffers⟩ :=
    packet.fast_body_no_pull_linked_end_account_default_state
      account invariant buffers ctx.statePtr ctx.mode
      ctx.lcodePtr codesGet ctx.lenSafe ctx.lenMask
      held linkedEnd
  let after := setI h ctx.zs { ctx.s with mode := TYPE }
  have condition : fastLoopCond ctx result after =
      .ok ((false, result), after) := by
    simp [fastLoopCond, broke]
  have final : FastLoopExit ctx after result :=
    ⟨slowNext, bs, ctx.z, { ctx.s with mode := TYPE },
      finalPacket, finalJ, finalBuffers⟩
  have directBody :
      (Zlib.Inffast.inflate_fast_body ctx.c q) h =
        .ok (result, after) := bodyRun
  have loopRun := fastLoop_stopped_once directBody condition
  obtain ⟨finalOff, input, finalCursor, inputGet,
    lower, rollback⟩ :=
    final.rollback_accounted finalAccount initialBits
  exact ⟨result, after, finalOff, input, loopRun,
    final, finalCursor, inputGet, lower, rollback⟩

end Zlib.Inflate.Proofs
