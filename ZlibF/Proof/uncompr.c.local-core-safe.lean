import ZlibF.Proof.«uncompr.c.local-wrapper-ranges»
import ZlibF.Proof.«uncompr.c.local-loop-resources»

namespace Zlib.Uncompr.Proof.LocalWrapperRanges
open C ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inflate.Local
open Zlib.Uncompr.Proof.Wrapper Zlib.Uncompr.Proof.PostRanges
set_option autoImplicit false

theorem initialized_core_safe (h : Heap) (source dest : BPtr) (n capacity : UInt64) (xs : List UInt8)
    (fresh : Fresh h) (globals : LibraryGlobals h)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit h) (allocation : h.allocOk h.nalloc = true)
    (readable : Bytes h source n.toNat xs) (writable : Writable h dest capacity.toNat)
    (separate : Separate source n.toNat dest capacity.toNat)
    (validInput : source = .null → n = 0) (validOutput : dest = .null → capacity = 0) :
    ∃ last after stream state used made,
      C.run (cdoWhile (Zlib.Uncompr.Proof.Loop.loopBody (some (.tab h.nextBlk)))
        Zlib.Uncompr.Proof.Loop.loopCondition { err := Z_OK, len := n, left := capacity })
        (coreHeap h source dest capacity) = .ok (last, after) ∧
      LocalStateJ after h.nextBlk (.tab h.nextBlk) (h.nextBlk + 2) stream state ∧ DefAlloc stream ∧
      RemainingBuffers after h.nextBlk stream last ∧ stream.next_out ≠ .null ∧
      last.err ≠ Z_OK ∧ PublicInflateCode last.err ∧
      remainingInput stream last + used = n.toNat ∧ remainingOutput stream last + made = capacity.toNat ∧
      LiveChange (coreHeap h source dest capacity) after
        (fun x => InflateOwned (h.nextBlk + 2) state x ∧ ¬ (coreHeap h source dest capacity).live x) (fun _ => False) ∧
      (∀ x, (coreHeap h source dest capacity).live x →
        (InflateOwned (h.nextBlk + 2) state x ↔ InflateOwned (h.nextBlk + 2) (initializedState h) x)) := by
  have initial := LocalDefaultEntry.core_state h source dest capacity fresh allocation globals platform
  have allocator := (LocalInitialization.core_local h source dest capacity fresh allocation).2
  have ranges := core_remaining_buffers h fresh source dest n capacity xs initial.good readable writable separate validOutput
  have nonnull : (coreStream h source dest capacity).next_out ≠ .null := normalizedDest_nonnull h dest capacity validOutput
  have inputNull : (coreStream h source dest capacity).next_in = .null →
      remainingInput (coreStream h source dest capacity) { err := Z_OK, len := n, left := capacity } = 0 := by
    intro null
    have sourceNull : source = .null := null
    simp [remainingInput, coreStream, outputStream, initializedStream, resetKeepStream,
      initStream2, initStream, Wrapper.preparedStream, validInput sourceNull]
  obtain ⟨last, after, stream, state, used, made, run, final, finalAllocator,
    finalRanges, finalNonnull, stop, codes, input, output⟩ :=
    LocalLoop.loop_safe (coreHeap h source dest capacity) h.nextBlk h.nextBlk (h.nextBlk + 2)
      (coreStream h source dest capacity) (initializedState h)
      { err := Z_OK, len := n, left := capacity } initial allocator ranges nonnull inputNull
  obtain ⟨ledger, owner⟩ := LocalLoop.loop_go_resources C.fuel
    (coreHeap h source dest capacity) after h.nextBlk h.nextBlk (h.nextBlk + 2)
    (coreStream h source dest capacity) stream (initializedState h) state
    { err := Z_OK, len := n, left := capacity } last initial allocator ranges nonnull run final.good
  refine ⟨last, after, stream, state, used, made, run, final, finalAllocator,
    finalRanges, finalNonnull, stop, codes, ?_, ?_, ledger, owner⟩
  · simpa [remainingInput, coreStream, outputStream, initializedStream, resetKeepStream,
      initStream2, initStream, Wrapper.preparedStream] using input
  · simpa [remainingOutput, coreStream, outputStream] using output


#print axioms initialized_core_safe
end Zlib.Uncompr.Proof.LocalWrapperRanges
