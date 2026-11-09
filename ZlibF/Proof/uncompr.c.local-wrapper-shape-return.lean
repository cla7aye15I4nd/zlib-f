import ZlibF.Proof.«uncompr.c.local-wrapper-shape-finish»

namespace Zlib.Uncompr.Proof.LocalWrapperShape
open C Zlib.Gzguts ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inflate.Local
open Zlib.Uncompr.Proof.Wrapper Zlib.Uncompr.Proof.WrapperRanges
open Zlib.Uncompr.Proof.Loop Zlib.Uncompr.Proof.PostRanges Zlib.Uncompr.Proof.Cells
open Zlib.Uncompr.Proof.Finish Zlib.Uncompr.Proof.InitialRefusal
set_option autoImplicit false

theorem initialized_core_shape (h after : Heap) (source dest : BPtr) (n capacity : UInt64)
    (xs : List UInt8) (last : UncLoop) (stream : ZStream) (state : InflateState)
    (fresh : Fresh h) (globals : LibraryGlobals h) (platform : ZlibF.PlatformMemory.ByteObjectsFit h)
    (allocation : h.allocOk h.nalloc = true)
    (readable : Bytes h source n.toNat xs) (writable : Writable h dest capacity.toNat)
    (separate : Separate source n.toNat dest capacity.toNat)
    (validOutput : dest = .null → capacity = 0)
    (run : C.run (cdoWhile (loopBody (some (.tab h.nextBlk))) loopCondition
      { err := Z_OK, len := n, left := capacity }) (coreHeap h source dest capacity) = .ok (last, after))
    (current : LocalStateJ after h.nextBlk (.tab h.nextBlk) (h.nextBlk + 2) stream state) :
    ShapeBelow h after h.nextBlk := by
  have initial := Zlib.Uncompr.Proof.LocalDefaultEntry.core_state h source dest capacity
    fresh allocation globals platform
  have allocator := (Zlib.Uncompr.Proof.LocalInitialization.core_local h source dest capacity fresh allocation).2
  have ranges := Zlib.Uncompr.Proof.LocalWrapperRanges.core_remaining_buffers h fresh source dest n capacity xs initial.good
    readable writable separate validOutput
  have nonnull : (coreStream h source dest capacity).next_out ≠ .null :=
    normalizedDest_nonnull h dest capacity validOutput
  have loopShape := loop_go_shape C.fuel (coreHeap h source dest capacity) after
    h.nextBlk h.nextBlk (h.nextBlk + 2) (coreStream h source dest capacity) stream
    (initializedState h) state { err := Z_OK, len := n, left := capacity } last
    initial allocator ranges nonnull run current
  exact (core_shapeBelow h source dest capacity).trans loopShape

/-- The same complete actual wrapper retains every caller allocation type.
Any earlier caller cutoff is transported by typed shape, including caller
scalar temporaries allocated before the decoder's own initialization. No
uniqueness premise on old objects is needed to obtain Shape or Fresh. -/
theorem uncompress2_z_return_shape (h after : Heap) (source dest sourceLen destLen : BPtr)
    (n capacity : UInt64) (xs : List UInt8) (rc : Int32)
    (fresh : Fresh h) (globals : LibraryGlobals h)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit h)
    (inputCell : LengthCell h sourceLen n) (outputCell : LengthCell h destLen capacity)
    (readable : Bytes h source n.toNat xs) (writable : Writable h dest capacity.toNat)
    (separate : Separate source n.toNat dest capacity.toNat)
    (sourceSeparate : Separate sourceLen 8 dest capacity.toNat)
    (destSeparate : Separate destLen 8 dest capacity.toNat)
    (cellSeparate : Separate sourceLen 8 destLen 8)
    (validInput : source = .null → n = 0) (validOutput : dest = .null → capacity = 0)
    (run : C.run (uncompress2_z dest destLen source sourceLen) h = .ok (rc, after)) :
    Shape h after ∧ Fresh after ∧ ZlibF.PlatformMemory.ByteObjectsFit after ∧
      (∀ callerCutoff, UniqueFrom h callerCutoff → UniqueFrom after callerCutoff) := by
  obtain ⟨finalFresh, finalPlatform⟩ := uncompress2_z_return_fresh_platform h after
    source dest sourceLen destLen n capacity xs rc fresh globals platform inputCell outputCell
    readable writable separate sourceSeparate destSeparate cellSeparate validInput validOutput run
  obtain ⟨otherRc, otherHeap, otherRun, ledger, _, _⟩ :=
    Zlib.Uncompr.Proof.LocalWrapperSafe.uncompress2_z_memory h source dest sourceLen destLen n capacity xs
      fresh globals platform inputCell outputCell readable writable separate sourceSeparate destSeparate
      cellSeparate validInput validOutput
  have same := Except.ok.inj (otherRun.symm.trans run)
  cases same
  have noNew (x : Nat) (live : after.live x) : h.live x := by
    simpa only [LiveChange, not_false_eq_true, and_true, or_false] using (ledger x).mp live
  have oldShape : ShapeBelow h after h.nextBlk := by
    by_cases allocation : h.allocOk h.nalloc = true
    · obtain ⟨last, coreAfter, stream, state, used, made, coreRun, current, allocator,
        ranges, nonnull, stopped, code, countIn, countOut, coreLedger, owners⟩ :=
        Zlib.Uncompr.Proof.LocalWrapperRanges.initialized_core_safe h source dest n capacity xs
          fresh globals platform allocation readable writable separate validInput validOutput
      have coreShape := initialized_core_shape h coreAfter source dest n capacity xs last stream state
        fresh globals platform allocation readable writable separate validOutput coreRun current
      obtain ⟨inputRange, inputCell1, outputRange, outputCell1⟩ :=
        Zlib.Uncompr.Proof.LocalObjects.initialized_loop_cells h coreAfter source dest sourceLen destLen n capacity xs last stream state
          fresh globals platform allocation inputCell outputCell readable writable separate
          sourceSeparate destSeparate validOutput coreRun current
      obtain ⟨reservedRange, reservedBytes⟩ := Zlib.Uncompr.Proof.LocalObjects.initialized_loop_reserved h coreAfter source dest n capacity xs
        last stream state fresh globals platform allocation readable writable separate validOutput coreRun current
      have reservedSource := reserved_separate_old h fresh sourceLen 8 (lengthBytes n) inputCell.1
      have reservedDest := reserved_separate_old h fresh destLen 8 (lengthBytes capacity) outputCell.1
      obtain ⟨mid, written, clean, finishRun, storeIn, storeOut, writtenJ, inputCell2, outputCell2,
        storeLedger, endLedger, cleanUnique, cleanFresh, cleanStream, localGet, finalPlatform, tailShape⟩ :=
        finish_safe_shape_platform coreAfter h.nextBlk h.nextBlk (h.nextBlk + 2) (h.nextBlk + 1) stream state
          sourceLen destLen n capacity last (junkBytes h).toList current allocator inputCell1 outputCell1
          inputRange outputRange cellSeparate reservedBytes reservedRange reservedSource reservedDest (by omega)
      let final := releasedHeap clean h.nextBlk (h.nextBlk + 1)
      have fullRun : C.run (uncompress2_z dest destLen source sourceLen) h =
          .ok (resultCode last.err (last.len + stream.avail_in.toUInt64), final) := by
        rw [Zlib.Uncompr.Proof.FreshCoreEntry.uncompress2_z_to_core h source dest sourceLen destLen n capacity fresh
          allocation inputCell outputCell validInput validOutput]
        simp only [C.run] at coreRun finishRun
        simpa only [bind_app, coreRun] using finishRun
      have heaps : final = after := congrArg Prod.snd (Except.ok.inj (fullRun.symm.trans run))
      rw [← heaps]
      exact coreShape.trans tailShape
    · have actual := uncompress2_z_initial_refusal h source dest sourceLen destLen n capacity fresh allocation
        inputCell outputCell validInput validOutput
      have heaps : refusedHeap h = after := congrArg Prod.snd (Except.ok.inj (actual.symm.trans run))
      rw [← heaps]
      intro b below
      have a : b ≠ h.nextBlk := by omega
      have c : b ≠ h.nextBlk + 1 := by omega
      simp [SlotShape,refusedHeap,upd_ne _ _ _ _ a,upd_ne _ _ _ _ c]
  have typed : Shape h after := by
    intro b
    by_cases below : b < h.nextBlk
    · exact oldShape b below
    · have initialDead : ¬ h.live b := fresh b (by omega)
      exact slotShape_of_dead initialDead (fun live => initialDead (noNew b live))
  exact ⟨typed, finalFresh, finalPlatform, fun callerCutoff unique => Shape.uniqueFrom typed callerCutoff unique⟩

#print axioms initialized_core_shape
#print axioms uncompress2_z_return_shape
end Zlib.Uncompr.Proof.LocalWrapperShape
