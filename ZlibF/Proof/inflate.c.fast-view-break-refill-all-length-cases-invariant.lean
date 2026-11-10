import ZlibF.Proof.«inflate.c.fast-view-break-refill-linked-cases-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- A first-root literal or length base continues normal decoding. -/
def FastRootLeafContinues (codes : Array Code) (baseOff : Nat)
    (c : Zlib.Inffast.Ctx) (q : Zlib.Inffast.L) : Prop :=
  let index := baseOff + (q.hold &&& c.lmask.toUInt64).toNat
  let entry := codes.getD index default
  entry.op = 0 ∨ entry.op &&& 16 ≠ 0

/-- The checked first length lookup from an actual fast-loop-ready state
is exhaustive. Four block-end or invalid-code cases execute the actual
outer loop and byte rollback; the remaining two classes decode normally. -/
theorem FastLoopReady.two_pull_all_length_cases
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
       (FastLinkedEnd h ctx.codes ctx.baseOff ctx.c
          (fastTwoPulls slow first second q) ctx.codeRef ∧
          FastLoopRollback ctx h q startOff) ∨
       (FastLinkedInvalid h ctx.codes ctx.baseOff ctx.c
          (fastTwoPulls slow first second q) ctx.codeRef ∧
          FastLoopRollback ctx h q startOff) ∨
       FastRootLeafContinues ctx.codes ctx.baseOff ctx.c
          (fastTwoPulls slow first second q) ∨
       FastLinkedContinues h ctx.codes ctx.baseOff ctx.c
          (fastTwoPulls slow first second q) ctx.codeRef) := by
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
  · rcases continuation with link | literal | base
    · have linked := packet.two_pull_linked_root_cases
        invariant buffers account cursor initialBits
        smallSlow codesGet link
      rcases linked with endCase | invalidCase | ongoing
      · exact Or.inr (Or.inr (Or.inl endCase))
      · exact Or.inr (Or.inr (Or.inr (Or.inl invalidCase)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr ongoing))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl (Or.inl literal)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl (Or.inr base)))))

end Zlib.Inflate.Proofs
