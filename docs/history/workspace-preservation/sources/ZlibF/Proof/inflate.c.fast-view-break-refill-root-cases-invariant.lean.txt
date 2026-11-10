import ZlibF.Proof.«inflate.c.fast-view-break-refill-end-loop-invariant»
import ZlibF.Proof.«inflate.c.fast-view-break-refill-invalid-loop-invariant»
import ZlibF.Proof.«inflate.c.fast-view-break-root-classify-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- The source fast loop exits safely and returns whole held input bytes
without moving before its original call-entry cursor. -/
def FastLoopRollback (ctx : FastLoopContext) (h : Heap)
    (q : Zlib.Inffast.L) (startOff : Nat) : Prop :=
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
        (finalOff - (result.bits >>> 3).toNat), after)

/-- The first fast-body root lookup is exhaustive. For end-of-block and
invalid length roots, actual loop rollback is checked; links, literals
and length bases are the remaining continuation cases. -/
theorem FastLoopReady.two_pull_root_cases
    {ctx : FastLoopContext} {h : Heap}
    {q : Zlib.Inffast.L} {startOff startBits : Nat}
    (ready : FastLoopReady ctx h q)
    (account : FastInputAccount ctx startOff startBits q)
    (initialBits : startBits < 8)
    (small : q.bits.toNat < 15) :
    ∃ slow first second third fourth fifth sixth rest,
      FastInputPacket h slow
        (first :: second :: third :: fourth :: fifth :: sixth :: rest)
        q ∧
      ((FastRootEnd ctx.codes ctx.baseOff ctx.c
          (fastTwoPulls slow first second q) ∧
          FastLoopRollback ctx h q startOff) ∨
       (FastRootInvalid ctx.codes ctx.baseOff ctx.c
          (fastTwoPulls slow first second q) ∧
          FastLoopRollback ctx h q startOff) ∨
       FastRootContinues ctx.codes ctx.baseOff ctx.c
          (fastTwoPulls slow first second q)) := by
  rcases ready with ⟨slow, bs, output, off, k,
    packet, invariant, buffers, codesGet, distGet,
    bitsBound, leftEq, outEq, putPtr, nextPtr, lastPtr,
    inputMargin, outPtr, outputGet, outputWrite,
    outputSize, current, beginLe, span, guard⟩
  obtain ⟨first, second, third, fourth, fifth,
    sixth, rest, rfl⟩ := packet.six_unread inputMargin
  have smallSlow : slow.bits.toNat < 15 := by
    rw [← packet.bits]
    exact small
  have cursor : q.in_ = .ref ctx.inputRef off :=
    packet.cursor.trans nextPtr
  have classes := fast_root_cases
    (q := fastTwoPulls slow first second q)
    ctx.lenSafe ctx.lenMask
  refine ⟨slow, first, second, third, fourth, fifth,
    sixth, rest, packet, ?_⟩
  rcases classes with terminal | invalid | continuation
  · exact Or.inl ⟨terminal,
      packet.two_pull_end_loop_rollback invariant buffers
        account cursor initialBits smallSlow codesGet
        terminal⟩
  · exact Or.inr (Or.inl ⟨invalid,
      packet.two_pull_invalid_loop_rollback invariant
        buffers account cursor initialBits smallSlow
        codesGet invalid⟩)
  · exact Or.inr (Or.inr continuation)

end Zlib.Inflate.Proofs
