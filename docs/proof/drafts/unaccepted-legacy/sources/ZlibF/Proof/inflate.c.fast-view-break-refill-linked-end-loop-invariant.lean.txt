import ZlibF.Proof.«inflate.c.fast-view-break-refill-linked-end-body-invariant»
import ZlibF.Proof.«inflate.c.fast-view-break-loop-run-invariant»
import ZlibF.Proof.«inflate.c.fast-view-writeback-rollback-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- The first fast-loop iteration may pull two caller bytes and then
encounter a linked end-of-block code. The actual loop exits and its
translated whole-byte input rollback stays within the caller range. -/
theorem FastInputPacket.two_pull_linked_end_loop_rollback
    {ctx : FastLoopContext} {h : Heap} {slow : IL}
    {first second third fourth fifth sixth : UInt8}
    {rest : List UInt8} {q : Zlib.Inffast.L}
    {startOff startBits off : Nat}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rest) q)
    (invariant : DefaultStateJ h ctx.r ctx.zs ctx.z ctx.s)
    (buffers : DispatchBuffers h ctx.r slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rest))
    (account : FastInputAccount ctx startOff startBits q)
    (cursor : q.in_ = .ref ctx.inputRef off)
    (initialBits : startBits < 8)
    (small : slow.bits.toNat < 15)
    (codesGet : Space.get h ctx.codeRef = some ctx.codes)
    (linkedEnd : FastLinkedEnd h ctx.codes ctx.baseOff ctx.c
      (fastTwoPulls slow first second q) ctx.codeRef) :
    ∃ result after finalOff input,
      (cdoWhile (Zlib.Inffast.inflate_fast_body ctx.c)
        (fun current => do
          if current.broke then pure (false, current)
          else if ← Ptr.lt current.in_ ctx.c.last then
            pure (← Ptr.lt current.out ctx.c.end_, current)
          else pure (false, current)) q) h =
        .ok (result, after) ∧
      FastLoopExit ctx after result ∧
      result.in_ = .ref ctx.inputRef finalOff ∧
      Space.get after ctx.inputRef = some input ∧
      startOff ≤ finalOff - (result.bits >>> 3).toNat ∧
      (Zlib.Inffast.subn result.in_
        (result.bits >>> 3)) after =
        .ok (.ref ctx.inputRef
          (finalOff - (result.bits >>> 3).toNat), after) := by
  obtain ⟨result, slowNext, bodyRun, broke,
    finalAccount, finalPacket, finalJ, finalBuffers⟩ :=
    packet.fast_body_two_pull_linked_end_account_default_state
      account cursor invariant buffers ctx.statePtr ctx.mode
      ctx.lcodePtr codesGet ctx.lenSafe ctx.lenMask small
      linkedEnd
  let after := setI h ctx.zs { ctx.s with mode := TYPE }
  have condition : fastLoopCond ctx result after =
      .ok ((false, result), after) := by
    simp [fastLoopCond, broke]
  have final : FastLoopExit ctx after result :=
    ⟨slowNext, third :: fourth :: fifth :: sixth :: rest,
      ctx.z, { ctx.s with mode := TYPE }, finalPacket,
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
