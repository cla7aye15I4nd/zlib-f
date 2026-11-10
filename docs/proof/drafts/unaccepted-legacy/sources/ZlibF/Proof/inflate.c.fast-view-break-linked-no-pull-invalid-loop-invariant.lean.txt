import ZlibF.Proof.«inflate.c.fast-view-break-linked-no-pull-invalid-body-invariant»
import ZlibF.Proof.«inflate.c.fast-view-break-loop-run-invariant»
import ZlibF.Proof.«inflate.c.fast-view-writeback-rollback-invariant»
import ZlibF.Proof.«inflate.c.fast-view-break-refill-root-cases-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- A linked invalid leaf reached without initial refill exits the
actual outer loop and returns held input bytes within the caller range. -/
theorem FastInputPacket.no_pull_linked_invalid_loop_rollback
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
    (linkedInvalid : FastLinkedInvalid h ctx.codes ctx.baseOff
      ctx.c q ctx.codeRef) :
    FastLoopRollback ctx h q startOff := by
  obtain ⟨result, after, slowNext, bodyRun, broke,
    finalAccount, finalPacket, finalBuffers, i,
    finalJ⟩ :=
    packet.fast_body_no_pull_linked_invalid_account_default_state
      account invariant buffers ctx.streamPtr ctx.statePtr
      ctx.lcodePtr codesGet ctx.lenSafe ctx.lenMask
      held linkedInvalid
  have condition : fastLoopCond ctx result after =
      .ok ((false, result), after) := by
    simp [fastLoopCond, broke]
  have final : FastLoopExit ctx after result :=
    ⟨slowNext, bs, { ctx.z with msg := .ref (.str i) 0 },
      { ctx.s with mode := BAD }, finalPacket,
      finalJ, finalBuffers⟩
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
