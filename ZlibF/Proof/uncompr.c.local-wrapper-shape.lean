import ZlibF.Proof.«uncompr.c.local-wrapper-memory»
import ZlibF.Proof.«uncompr.c.wrapper-shape»

namespace Zlib.Uncompr.Proof.LocalWrapperShape
open C Zlib.Gzguts ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inflate.Local
open Zlib.Uncompr.Proof.Wrapper Zlib.Uncompr.Proof.WrapperRanges
open Zlib.Uncompr.Proof.Loop Zlib.Uncompr.Proof.PostRanges Zlib.Uncompr.Proof.Cells
open Zlib.Uncompr.Proof.Finish Zlib.Uncompr.Proof.LocalFinish Zlib.Uncompr.Proof.Writeback
open Zlib.Uncompr.Proof.InitialRefusal
set_option autoImplicit false

private theorem m_bind_assoc {α β γ : Type} (a : M α) (b : α → M β) (c : β → M γ) :
    ((a >>= b) >>= c) = (a >>= fun x => b x >>= c) := by
  funext h
  simp only [bind_app]
  cases first : a h with
  | error fault => rfl
  | ok pair => rcases pair with ⟨x, next⟩; rfl

theorem finish_safe_platform (h : Heap) (cutoff b zs reserved : Nat) (z : ZStream) (s : InflateState)
    (sourceLen destLen : BPtr) (n capacity : UInt64) (l : UncLoop) (junk : List UInt8)
    (invariant : LocalStateJ h cutoff (.tab b) zs z s) (allocator : DefAlloc z)
    (inputCell : LengthCell h sourceLen n) (outputCell : LengthCell h destLen capacity)
    (inputRange : CallerRange h (.tab b) sourceLen 8 true)
    (outputRange : CallerRange h (.tab b) destLen 8 true)
    (separate : Separate sourceLen 8 destLen 8)
    (reservedBytes : Bytes h (.ref (.blk reserved) 0) 8 junk)
    (reservedRange : CallerRange h (.tab b) (.ref (.blk reserved) 0) 8 true)
    (reservedSource : Separate (.ref (.blk reserved) 0) 8 sourceLen 8)
    (reservedDest : Separate (.ref (.blk reserved) 0) 8 destLen 8) :
    ∃ mid written clean,
      C.run (finish (some (.tab b)) (.ref (.blk reserved) 0) destLen sourceLen l) h =
        .ok (resultCode l.err (l.len + z.avail_in.toUInt64), releasedHeap clean b reserved) ∧
      Store h sourceLen (lengthBytes (n - (l.len + z.avail_in.toUInt64))) mid ∧
      Store mid destLen (lengthBytes (capacity - (l.left + z.avail_out.toUInt64))) written ∧
      LocalStateJ written cutoff (.tab b) zs z s ∧
      LengthCell clean sourceLen (n - (l.len + z.avail_in.toUInt64)) ∧
      LengthCell clean destLen (capacity - (l.left + z.avail_out.toUInt64)) ∧
      LiveChange h written (fun _ => False) (fun _ => False) ∧
      LiveChange written clean (fun _ => False) (InflateOwned zs s) ∧
      UniqueFrom clean cutoff ∧ Fresh clean ∧
      clean.streams b = some { z with state := none } ∧
      (∃ a, clean.bytes reserved = some a ∧ clean.ro reserved = false) ∧
      ZlibF.PlatformMemory.ByteObjectsFit (releasedHeap clean b reserved) := by
  obtain ⟨mid, written, stores, current, finalAllocator, storeIn, storeOut, cellIn, cellOut, live, ownership⟩ :=
    LocalWriteback.ordered_length_writeback invariant allocator inputCell outputCell inputRange outputRange separate
      (l.len + z.avail_in.toUInt64) (l.left + z.avail_out.toUInt64)
  have rangeIn := cell_range_of_same_ownership cellIn inputRange ownership
  have rangeOut := cell_range_of_same_ownership cellOut outputRange ownership
  obtain ⟨reservedBytes1, reservedRange1⟩ := ordered_stores_keep_object storeIn storeOut ownership
    reservedBytes reservedRange reservedSource reservedDest
  obtain ⟨clean, endRun, same, fresh, unique, streamGet, endLive, frame, _, _⟩ :=
    inflateEnd_local current.good current.roots finalAllocator.2
  obtain ⟨inputBytes2, inputWrite2⟩ := frame_caller_object current.good current.roots cellIn.1 rangeIn frame
  obtain ⟨outputBytes2, outputWrite2⟩ := frame_caller_object current.good current.roots cellOut.1 rangeOut frame
  obtain ⟨reservedBytes2, reservedWrite2⟩ := frame_caller_object current.good current.roots reservedBytes1 reservedRange1 frame
  obtain ⟨a, reservedGet, reservedRo⟩ : ∃ a, clean.bytes reserved = some a ∧ clean.ro reserved = false := by
    rcases reservedWrite2 rfl with null | ⟨ref, off, a, ptr, get, ro, room⟩
    · cases null.1
    · cases ptr
      exact ⟨a, get, ro⟩
  have cleanPlatform : ZlibF.PlatformMemory.ByteObjectsFit clean := by
    rw [same]
    exact Zlib.Uncompr.Proof.WrapperShape.ended_platform written zs b s z current.platform
  have finalPlatform := Zlib.Uncompr.Proof.WrapperShape.released_platform clean b reserved cleanPlatform
  have cleanup := freeLocals_run clean b reserved _ a streamGet reservedGet reservedRo
  refine ⟨mid, written, clean, ?_, storeIn, storeOut, current,
    ⟨inputBytes2, inputWrite2 rfl⟩, ⟨outputBytes2, outputWrite2 rfl⟩, live, ?_,
    unique, fresh, streamGet, ⟨a, reservedGet, reservedRo⟩, finalPlatform⟩
  · have ld : Zlib.Gzguts.ldZ (some (.tab b)) h = .ok (z, h) := by
      simp [Zlib.Gzguts.ldZ, ldZ_eq, show ZStreamRef.get h (.tab b) = some z from invariant.good.live.hz]
    change finish (some (.tab b)) (.ref (.blk reserved) 0) destLen sourceLen l h = _
    unfold finish
    rw [bind_app, ld]
    dsimp only
    have seq : ((do
      (do store64 sourceLen ((← load64 sourceLen) - (l.len + z.avail_in.toUInt64))
          store64 destLen ((← load64 destLen) - (l.left + z.avail_out.toUInt64)))
      let _ ← Zlib.Inflate.inflateEnd (some (.tab b))
      freeLocals (some (.tab b)) (.ref (.blk reserved) 0)
      pure (resultCode l.err (l.len + z.avail_in.toUInt64))) h) =
        .ok (resultCode l.err (l.len + z.avail_in.toUInt64), releasedHeap clean b reserved) := by
      simp only [C.run] at endRun
      rw [bind_app, stores]
      dsimp only
      rw [bind_app, endRun]
      dsimp only
      rw [bind_app, cleanup]
      rfl
    simpa only [m_bind_assoc, resultCode] using seq
  · intro x
    simpa [LiveChange, InflateOwned, OwnedBy, WinBlk, and_comm] using endLive x



theorem uncompress2_z_return_fresh_platform (h after : Heap) (source dest sourceLen destLen : BPtr)
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
    Fresh after ∧ ZlibF.PlatformMemory.ByteObjectsFit after := by
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
    obtain ⟨mid, written, clean, finishRun, storeIn, storeOut, writtenJ, inputCell2, outputCell2,
      storeLedger, endLedger, cleanUnique, cleanFresh, cleanStream, localGet, finalPlatform⟩ :=
      finish_safe_platform coreAfter h.nextBlk h.nextBlk (h.nextBlk + 2) (h.nextBlk + 1) stream state
        sourceLen destLen n capacity last (junkBytes h).toList current allocator inputCell1 outputCell1
        inputRange outputRange cellSeparate reservedBytes reservedRange reservedSource reservedDest
    let final := releasedHeap clean h.nextBlk (h.nextBlk + 1)
    have fullRun : C.run (uncompress2_z dest destLen source sourceLen) h =
        .ok (resultCode last.err (last.len + stream.avail_in.toUInt64), final) := by
      rw [Zlib.Uncompr.Proof.FreshCoreEntry.uncompress2_z_to_core h source dest sourceLen destLen n capacity fresh
        allocation inputCell outputCell validInput validOutput]
      simp only [C.run] at coreRun finishRun
      simpa only [bind_app, coreRun] using finishRun
    have same := Except.ok.inj (fullRun.symm.trans run)
    have heaps : final = after := congrArg Prod.snd same
    rw [← heaps]
    exact ⟨Zlib.Uncompr.Proof.WrapperShape.released_fresh clean h.nextBlk (h.nextBlk + 1) cleanFresh, finalPlatform⟩
  · have actual := uncompress2_z_initial_refusal h source dest sourceLen destLen n capacity fresh allocation
      inputCell outputCell validInput validOutput
    have same := Except.ok.inj (actual.symm.trans run)
    cases same
    have fit : ZlibF.PlatformMemory.ByteObjectsFit (refusedHeap h) :=
      (Zlib.Uncompr.Proof.WrapperShape.removed_bytes_platform h (h.nextBlk + 1) platform).of_storage_eq rfl rfl rfl
    exact ⟨Zlib.Uncompr.Proof.WrapperShape.refused_fresh h fresh, fit⟩


#print axioms finish_safe_platform
#print axioms uncompress2_z_return_fresh_platform
end Zlib.Uncompr.Proof.LocalWrapperShape
