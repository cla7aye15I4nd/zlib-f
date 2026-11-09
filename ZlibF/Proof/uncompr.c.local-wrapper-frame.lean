import ZlibF.Proof.«uncompr.c.local-wrapper-memory»
import ZlibF.Proof.«uncompr.c.local-loop-frame»
import ZlibF.Proof.«uncompr.c.local-tail-frame»
import ZlibF.Proof.«uncompr.c.final-frame»

namespace Zlib.Uncompr.Proof.LocalWrapperFrame
open C Zlib.Gzguts ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inflate.Local
open Zlib.Uncompr.Proof.Wrapper Zlib.Uncompr.Proof.WrapperRanges
open Zlib.Uncompr.Proof.Loop Zlib.Uncompr.Proof.PostRanges Zlib.Uncompr.Proof.Cells
open Zlib.Uncompr.Proof.Finish
set_option autoImplicit false

/-- On the same actual complete wrapper execution, every original allocation
outside output and the two length-cell roots retains all seven typed tables,
read-only flags and static data. This is the ordinary root frame; it does not
replace the separate exact byte-Store/SameObjects or independent format goals. -/
theorem uncompress2_z_frame_of_run (h : Heap) (source dest sourceLen destLen : BPtr)
    (n capacity : UInt64) (xs : List UInt8)
    (fresh : Fresh h) (globals : LibraryGlobals h)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit h) (allocation : h.allocOk h.nalloc = true)
    (inputCell : LengthCell h sourceLen n) (outputCell : LengthCell h destLen capacity)
    (readable : Bytes h source n.toNat xs) (writable : Writable h dest capacity.toNat)
    (separate : Separate source n.toNat dest capacity.toNat)
    (sourceSeparate : Separate sourceLen 8 dest capacity.toNat)
    (destSeparate : Separate destLen 8 dest capacity.toNat)
    (cellSeparate : Separate sourceLen 8 destLen 8)
    (validInput : source = .null → n = 0) (validOutput : dest = .null → capacity = 0)
    (rc : Int32) (after : Heap)
    (actual : C.run (uncompress2_z dest destLen source sourceLen) h = .ok (rc, after)) :
    Frame h after (fun x => ByteRoot dest x ∨ ByteRoot sourceLen x ∨ ByteRoot destLen x) := by
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
  obtain ⟨mid, written, clean, finishRun, storeIn, storeOut, writtenJ, inputFinal, outputFinal,
      storeLedger, endLedger, unique, cleanFresh, streamGet, reservedGet, tailFrame⟩ :=
    LocalTailFrame.finish_framed coreAfter h.nextBlk h.nextBlk (h.nextBlk + 2) (h.nextBlk + 1) stream state
      sourceLen destLen n capacity last (junkBytes h).toList current allocator inputCell1 outputCell1
      inputRange outputRange cellSeparate reservedBytes reservedRange reservedSource reservedDest
  have complete : C.run (uncompress2_z dest destLen source sourceLen) h =
      .ok (resultCode last.err (last.len + stream.avail_in.toUInt64), releasedHeap clean h.nextBlk (h.nextBlk + 1)) := by
    rw [FreshCoreEntry.uncompress2_z_to_core h source dest sourceLen destLen n capacity fresh
      allocation inputCell outputCell validInput validOutput]
    simp only [C.run] at coreRun finishRun
    simpa only [bind_app, coreRun] using finishRun
  cases Except.ok.inj (complete.symm.trans actual)
  have coreFrame := LocalLoop.loop_go_frame C.fuel (coreHeap h source dest capacity) coreAfter
    h.nextBlk h.nextBlk (h.nextBlk + 2) (coreStream h source dest capacity) stream
    (initializedState h) state { err := Z_OK, len := n, left := capacity } last
    (LocalDefaultEntry.core_state h source dest capacity fresh allocation globals platform)
    (LocalInitialization.core_local h source dest capacity fresh allocation).2
    (LocalWrapperRanges.core_remaining_buffers h fresh source dest n capacity xs
      (LocalDefaultEntry.core_state h source dest capacity fresh allocation globals platform).good
      readable writable separate validOutput)
    (normalizedDest_nonnull h dest capacity validOutput) coreRun current.good
  have bodyFrame : Frame h coreAfter (fun x => ByteRoot dest x ∨ ByteRoot sourceLen x ∨ ByteRoot destLen x) := by
    apply CallerFrame.frame_trans_restrict (CallerFrame.core_frame h source dest capacity fresh) coreFrame
    intro x live outside
    refine ⟨by simp, ?_⟩
    have below := fresh.lt live
    rintro ((root | owner) | output)
    · change x = h.nextBlk at root
      omega
    · rcases owner with stateRoot | window
      · omega
      · rw [initial_window_null] at window
        cases window
    · change ByteRoot (normalizedDest h dest capacity) x at output
      unfold normalizedDest at output
      split at output
      · change x = h.nextBlk + 1 at output
        omega
      · exact outside (Or.inl output)
  have notOwned := FinalFrame.owner_outside_old h source dest capacity state fresh owners
  apply CallerFrame.frame_trans_restrict bodyFrame tailFrame
  intro x live outside
  refine ⟨outside, ?_⟩
  have below := fresh.lt live
  rintro (sourceCell | destCell | (root | owner) | atStream | atReserved)
  · exact outside (Or.inr (Or.inl sourceCell))
  · exact outside (Or.inr (Or.inr destCell))
  · change x = h.nextBlk at root
    omega
  · exact notOwned x live owner
  · omega
  · omega

theorem uncompress2_z_framed_memory (h : Heap) (source dest sourceLen destLen : BPtr)
    (n capacity : UInt64) (xs : List UInt8)
    (fresh : Fresh h) (globals : LibraryGlobals h)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit h)
    (inputCell : LengthCell h sourceLen n) (outputCell : LengthCell h destLen capacity)
    (readable : Bytes h source n.toNat xs) (writable : Writable h dest capacity.toNat)
    (separate : Separate source n.toNat dest capacity.toNat)
    (sourceSeparate : Separate sourceLen 8 dest capacity.toNat)
    (destSeparate : Separate destLen 8 dest capacity.toNat)
    (cellSeparate : Separate sourceLen 8 destLen 8)
    (validInput : source = .null → n = 0) (validOutput : dest = .null → capacity = 0) :
    ∃ rc after,
      C.run (uncompress2_z dest destLen source sourceLen) h = .ok (rc, after) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧
      (h.allocOk h.nalloc = false → rc = Z_MEM_ERROR ∧ LengthCell after sourceLen n ∧
        LengthCell after destLen capacity ∧ after.nalloc = h.nalloc + 1 ∧ Frame h after (fun _ => False)) ∧
      (h.allocOk h.nalloc = true → ∃ used made,
        LengthCell after sourceLen (UInt64.ofNat used) ∧ LengthCell after destLen (UInt64.ofNat made) ∧
        used ≤ n.toNat ∧ made ≤ capacity.toNat ∧
        ∃ err remainIn, err ≠ Z_OK ∧ PublicInflateCode err ∧ rc = resultCode err remainIn ∧
          used + remainIn.toNat = n.toNat) ∧
      Frame h after (fun x => ByteRoot dest x ∨ ByteRoot sourceLen x ∨ ByteRoot destLen x) := by
  obtain ⟨rc,after,run,live,refused,counted⟩ :=
    LocalWrapperSafe.uncompress2_z_memory h source dest sourceLen destLen n capacity xs
      fresh globals platform inputCell outputCell readable writable separate
      sourceSeparate destSeparate cellSeparate validInput validOutput
  refine ⟨rc,after,run,live,refused,counted,?_⟩
  by_cases allocation : h.allocOk h.nalloc = true
  · exact uncompress2_z_frame_of_run h source dest sourceLen destLen n capacity xs
      fresh globals platform allocation inputCell outputCell readable writable separate
      sourceSeparate destSeparate cellSeparate validInput validOutput rc after run
  · have no : h.allocOk h.nalloc = false := by cases bit : h.allocOk h.nalloc <;> simp_all
    have frame := (refused no).2.2.2.2
    obtain ⟨static, alloc, garbage, next, allocations, slots⟩ := frame
    refine ⟨static,alloc,garbage,next,allocations,?_⟩
    intro x alive outside
    exact slots x alive (by simp)

#print axioms uncompress2_z_framed_memory

#print axioms uncompress2_z_frame_of_run
end Zlib.Uncompr.Proof.LocalWrapperFrame
