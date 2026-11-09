import ZlibF.Proof.«uncompr.c.local-caller-object-tail»
import ZlibF.Proof.«uncompr.c.local-wrapper-memory»

/-! Disjoint old caller intervals on the same complete actual counted call,
including separate intervals in one array and every allocator outcome. -/
namespace Zlib.Uncompr.Proof.LocalCallerObjects
open C Zlib.Gzguts ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inflate.Local
open Zlib.Uncompr.Proof.Wrapper Zlib.Uncompr.Proof.WrapperRanges
open Zlib.Uncompr.Proof.Finish Zlib.Uncompr.Proof.Cells
open Zlib.Uncompr.Proof.Loop Zlib.Uncompr.Proof.PostRanges Zlib.Uncompr.Proof.CallerObjects
set_option autoImplicit false

theorem uncompress2_z_object (h after : Heap) (source dest sourceLen destLen : BPtr)
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
    (q : BPtr) (count : Nat) (ys : List UInt8) (write : Bool)
    (objectBytes : Bytes h q count ys) (objectWrite : write = true → Writable h q count)
    (objectOutput : Separate q count dest capacity.toNat)
    (objectSourceCell : Separate q count sourceLen 8) (objectDestCell : Separate q count destLen 8)
    (run : C.run (uncompress2_z dest destLen source sourceLen) h = .ok (rc, after)) :
    Bytes after q count ys ∧ (write = true → Writable after q count) := by
  by_cases allocation : h.allocOk h.nalloc = true
  ·
    obtain ⟨last, coreAfter, stream, state, used, made, coreRun, current, allocator,
      ranges, nonnull, stopped, code, countIn, countOut, coreLedger, owners⟩ :=
      LocalWrapperRanges.initialized_core_safe h source dest n capacity xs fresh globals platform allocation
        readable writable separate validInput validOutput
    obtain ⟨inputRange, inputCell1, outputRange, outputCell1⟩ :=
      LocalObjects.initialized_loop_cells h coreAfter source dest sourceLen destLen n capacity xs last stream state
        fresh globals platform allocation inputCell outputCell readable writable separate
        sourceSeparate destSeparate validOutput coreRun current
    obtain ⟨reservedRange, reservedBytes⟩ := LocalObjects.initialized_loop_reserved h coreAfter source dest n capacity xs
      last stream state fresh globals platform allocation readable writable separate validOutput coreRun current
    have reservedSource := reserved_separate_old h fresh sourceLen 8 (lengthBytes n) inputCell.1
    have reservedDest := reserved_separate_old h fresh destLen 8 (lengthBytes capacity) outputCell.1
    have initial := LocalDefaultEntry.core_state h source dest capacity fresh allocation globals platform
    have initialAllocator := (LocalInitialization.core_local h source dest capacity fresh allocation).2
    have initialRanges := LocalWrapperRanges.core_remaining_buffers h fresh source dest n capacity xs initial.good readable writable separate validOutput
    have initialRange := LocalWrapperRanges.core_old_range h fresh source dest q capacity count ys write initial.good objectBytes objectWrite
    have initialBytes := core_original_bytes h source dest q capacity fresh count ys objectBytes
    have initialOutput : Separate q count (coreStream h source dest capacity).next_out
        (remainingOutput (coreStream h source dest capacity) { err := Z_OK, len := n, left := capacity }) := by
      simpa [remainingOutput, coreStream, outputStream] using separate_normalized h q dest count capacity objectOutput validOutput
    obtain ⟨objectRange1, objectBytes1, _objectSeparate1⟩ := LocalObjects.loop_go_object C.fuel
      (coreHeap h source dest capacity) coreAfter h.nextBlk h.nextBlk (h.nextBlk + 2)
      (coreStream h source dest capacity) stream (initializedState h) state
      { err := Z_OK, len := n, left := capacity } last q count ys write
      initial initialAllocator initialRanges (normalizedDest_nonnull h dest capacity validOutput)
      initialRange initialBytes initialOutput coreRun current
    have outside := old_not_newblock h fresh (h.nextBlk + 1) (by omega) q count ys objectBytes
    obtain ⟨_mid, _written, clean, finishRun, _storeIn, _storeOut, _writtenJ, _cellIn, _cellOut,
      _storesLive, _endLive, _unique, _fresh, _streamGet, _reservedGet, objectBytes2, objectWrite2⟩ :=
      finish_safe_object coreAfter h.nextBlk h.nextBlk (h.nextBlk + 2) (h.nextBlk + 1) stream state
        sourceLen destLen n capacity last (junkBytes h).toList current allocator inputCell1 outputCell1
        inputRange outputRange cellSeparate reservedBytes reservedRange reservedSource reservedDest
        q count ys write objectBytes1 objectRange1 objectSourceCell objectDestCell outside
    have fullRun : C.run (uncompress2_z dest destLen source sourceLen) h =
        .ok (resultCode last.err (last.len + stream.avail_in.toUInt64), releasedHeap clean h.nextBlk (h.nextBlk + 1)) := by
      rw [FreshCoreEntry.uncompress2_z_to_core h source dest sourceLen destLen n capacity fresh
        allocation inputCell outputCell validInput validOutput]
      simp only [C.run] at coreRun finishRun
      simpa only [bind_app, coreRun] using finishRun
    have same := Except.ok.inj (fullRun.symm.trans run)
    have heaps : releasedHeap clean h.nextBlk (h.nextBlk + 1) = after := congrArg Prod.snd same
    rw [← heaps]
    exact ⟨objectBytes2, objectWrite2⟩
  · have actual := Zlib.Uncompr.Proof.InitialRefusal.uncompress2_z_initial_refusal h source dest sourceLen destLen
      n capacity fresh allocation inputCell outputCell validInput validOutput
    have heaps : Zlib.Uncompr.Proof.InitialRefusal.refusedHeap h = after :=
      congrArg Prod.snd (Except.ok.inj (actual.symm.trans run))
    rw [← heaps]
    exact refused_object h fresh q count ys write objectBytes objectWrite

#print axioms uncompress2_z_object
end Zlib.Uncompr.Proof.LocalCallerObjects
