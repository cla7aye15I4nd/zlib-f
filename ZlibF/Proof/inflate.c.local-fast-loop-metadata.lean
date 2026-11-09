import ZlibF.Proof.«inflate.c.local-fast-loop-step»
import ZlibF.Proof.«inflate.c.output-frame-live-compose»

namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- One observed actual body retains the entry-relative input ledger,
all byte sizes, the fixed output interval frame and the physical bounds.
The mode/progress alternatives use the real incoming nonbreaking flag. -/
theorem FastLoopBodyObserved.metadata
    {cutoff : Nat} {ctx : FastLoopContext} {h after : Heap}
    {q result : Zlib.Inffast.L} {startOff startBits : Nat}
    (observed : FastLoopBodyObserved cutoff ctx h q result after)
    (account : FastLoopInputBudget ctx startOff startBits q)
    (notBroken : q.broke = false) :
    FastLoopInputBudget ctx startOff startBits result ∧
    FastLoopOutputRange ctx after result ∧ FastLoopInputLimit ctx result ∧
    ByteViewSizes h after ∧
    BufferFrame h after (fun b => StreamRoot ctx.r b ∨ b = ctx.zs)
      [⟨.ref ctx.dest ctx.oo, ctx.leftTotal.toNat⟩] ∧
    FastMemoryMetaFrame ctx.r h after ∧
    (∀ zNext sNext, LocalStateJ after cutoff ctx.r ctx.zs zNext sNext →
      sNext.window = ctx.s.window ∧
      (sNext.mode = ctx.s.mode ∨ sNext.mode = TYPE ∨ sNext.mode = BAD) ∧
      (sNext.mode = BAD ∨ sNext.mode = TYPE ∨
        ∃ finish, result.out = .ref ctx.dest finish ∧ ctx.oo < finish)) := by
  rcases observed with ⟨slow, bs, output, off, start, packet,
    invariant, buffers, codesGet, distGet, bitsBound,
    leftEq, outEq, putPtr, nextPtr, lastPtr, inputMargin,
    outPtr, outputGet, outputWrite, outputSize, current,
    beginLe, span, guard, zNext, sNext, witness, witnessBytes, run, nextJ, oldPacket, sizes, effect⟩
  have initialCursor : q.in_ = .ref ctx.inputRef off := packet.cursor.trans nextPtr
  obtain ⟨pulled, pulledBound, cursor, budget⟩ := effect.input
  have finalCursor : result.in_ = .ref ctx.inputRef (off + pulled) := by
    rw [cursor, initialCursor]
    rfl
  obtain ⟨oldOff, oldPtr, oldLower, oldBudget⟩ := account
  have same : oldOff = off := (Ptr.ref.inj (oldPtr.symm.trans initialCursor)).2
  subst oldOff
  have input : FastLoopInputBudget ctx startOff startBits result :=
    ⟨off + pulled, finalCursor, by omega, by omega⟩
  have limit : FastLoopInputLimit ctx result :=
    ⟨off + pulled, off + slow.have_.toNat - 5, finalCursor, lastPtr, by omega⟩
  obtain ⟨finish, outputPtr, outputLower, outputUpper⟩ := effect.output
  have endPtr : ctx.c.end_ = .ref ctx.dest (ctx.oo + slow.left.toNat - 257) := by
    rw [leftEq]
    exact ctx.endPtr
  have avail : 258 ≤ slow.left.toNat := by rw [leftEq]; exact ctx.avail
  have room := fast_output_max_room_of_guard outPtr endPtr outputGet outputSize current avail guard
  obtain ⟨array, arrayGet, arraySize⟩ := sizes.view outputGet
  have output : FastLoopOutputRange ctx after result := by
    refine ⟨finish, array, outputPtr, by omega, ?_, arrayGet, ?_⟩
    · rw [← leftEq]
      omega
    · rw [← leftEq]
      omega
  have frame := effect.heap.output_effect.buffer_frame invariant.good.live.hz invariant.good.live.hs
  have fixedFrame : BufferFrame h after (fun b => StreamRoot ctx.r b ∨ b = ctx.zs)
      [⟨.ref ctx.dest ctx.oo, ctx.leftTotal.toNat⟩] := by
    simpa only [putPtr, leftEq] using frame
  refine ⟨input, output, limit, sizes, fixedFrame,
    fastMemoryMetaFrameM_fast_body ctx.r ctx.c ctx.streamPtr q h result after run, ?_⟩
  intro finalZ finalS finalJ
  have windowModes := effect.heap.window_mode invariant.good.live.hs finalJ
  refine ⟨windowModes.1, windowModes.2, ?_⟩
  rcases effect.heap with ⟨_, _, _, sameFlag⟩ | ⟨i, _, heapEq⟩ | ⟨_, heapEq⟩
  · have resultNotBroken : result.broke = false := sameFlag.trans notBroken
    obtain ⟨finish, ptr, strict⟩ := effect.progress resultNotBroken
    exact Or.inr (Or.inr ⟨finish, ptr, by omega⟩)
  · have mode : finalS = { ctx.s with mode := BAD } := by
      have get := finalJ.good.live.hs
      simp only [heapEq, badHeap, setI_istates_same] at get
      exact Option.some.inj get.symm
    exact Or.inl (by rw [mode])
  · have mode : finalS = { ctx.s with mode := TYPE } := by
      have get := finalJ.good.live.hs
      simp only [heapEq, setI_istates_same] at get
      exact Option.some.inj get.symm
    exact Or.inr (Or.inl (by rw [mode]))

end Zlib.Inflate.Local
