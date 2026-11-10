import ZlibF.Proof.«inflate.c.fast-view-break-refill-all-length-cases-invariant»
import ZlibF.Proof.«inflate.c.fast-view-break-linked-no-pull-cases-invariant»
import ZlibF.Proof.«inflate.c.fast-view-break-loop-rollback-invariant»
import ZlibF.Proof.«inflate.c.fast-view-break-invalid-loop-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- The checked first length lookup with enough held bits is exhaustive.
Root and linked terminal or invalid codes execute the actual fast loop and
its byte rollback. Literal and length codes continue decoding. -/
theorem FastLoopReady.no_pull_all_length_cases
    {ctx : FastLoopContext} {h : Heap}
    {q : Zlib.Inffast.L} {startOff startBits : Nat}
    (ready : FastLoopReady ctx h q)
    (account : FastInputAccount ctx startOff startBits q)
    (initialBits : startBits < 8)
    (held : 15 ≤ q.bits.toNat) :
    (FastRootEnd ctx.codes ctx.baseOff ctx.c q ∧
      FastLoopRollback ctx h q startOff) ∨
    (FastRootInvalid ctx.codes ctx.baseOff ctx.c q ∧
      FastLoopRollback ctx h q startOff) ∨
    (FastLinkedEnd h ctx.codes ctx.baseOff ctx.c q ctx.codeRef ∧
      FastLoopRollback ctx h q startOff) ∨
    (FastLinkedInvalid h ctx.codes ctx.baseOff ctx.c q ctx.codeRef ∧
      FastLoopRollback ctx h q startOff) ∨
    FastRootLeafContinues ctx.codes ctx.baseOff ctx.c q ∨
    FastLinkedContinues h ctx.codes ctx.baseOff ctx.c q
      ctx.codeRef := by
  have ready0 := ready
  rcases ready with ⟨slow, bs, output, off, k,
    packet, invariant, buffers, codesGet, distGet,
    bitsBound, leftEq, outEq, putPtr, nextPtr, lastPtr,
    inputMargin, outPtr, outputGet, outputWrite,
    outputSize, current, beginLe, span, guard⟩
  have heldSlow : 15 ≤ slow.bits.toNat := by
    rw [← packet.bits]
    exact held
  have classes := fast_root_cases (q := q)
    ctx.lenSafe ctx.lenMask
  rcases classes with terminal | invalid | continuation
  · have rollback : FastLoopRollback ctx h q startOff := by
      rcases terminal with ⟨bound, width, nonzero,
        notBase, notLink, endCode⟩
      let index := ctx.baseOff +
        (q.hold &&& ctx.c.lmask.toUInt64).toNat
      have entryEq : ctx.codes.getD index default =
          ctx.codes[index] := by
        rw [Array.getD_eq_getD_getElem?]
        rw [Array.getElem?_eq_getElem bound]
        rfl
      rw [entryEq] at width nonzero notBase notLink endCode
      exact ready0.no_pull_end_loop_rollback account
        initialBits held bound width nonzero notBase
        notLink endCode
    exact Or.inl ⟨terminal, rollback⟩
  · have rollback : FastLoopRollback ctx h q startOff := by
      rcases invalid with ⟨bound, width, nonzero,
        notBase, notLink, notEnd⟩
      let index := ctx.baseOff +
        (q.hold &&& ctx.c.lmask.toUInt64).toNat
      have entryEq : ctx.codes.getD index default =
          ctx.codes[index] := by
        rw [Array.getD_eq_getD_getElem?]
        rw [Array.getElem?_eq_getElem bound]
        rfl
      rw [entryEq] at width nonzero notBase notLink notEnd
      exact ready0.no_pull_invalid_loop_rollback account
        initialBits held bound width nonzero notBase
        notLink notEnd
    exact Or.inr (Or.inl ⟨invalid, rollback⟩)
  · rcases continuation with link | literal | base
    · have linked := packet.no_pull_linked_root_cases
        invariant buffers account initialBits heldSlow
        codesGet link
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
