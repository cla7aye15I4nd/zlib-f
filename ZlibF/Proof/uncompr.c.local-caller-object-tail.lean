import ZlibF.Proof.«uncompr.c.local-wrapper-shape»
import ZlibF.Proof.«uncompr.c.caller-objects»

/-! Exact caller observations through the actual local decoder cleanup. -/
namespace Zlib.Uncompr.Proof.LocalCallerObjects
open C Zlib.Gzguts ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inflate.Local
open Zlib.Uncompr.Proof.Wrapper Zlib.Uncompr.Proof.WrapperRanges
open Zlib.Uncompr.Proof.Finish Zlib.Uncompr.Proof.Cells Zlib.Uncompr.Proof.Writeback
open Zlib.Uncompr.Proof.CallerObjects
set_option autoImplicit false

private theorem m_bind_assoc {α β γ : Type} (a : M α) (b : α → M β) (c : β → M γ) :
    ((a >>= b) >>= c) = (a >>= fun x => b x >>= c) := by
  funext h
  simp only [bind_app]
  cases first : a h with
  | error fault => rfl
  | ok pair => rcases pair with ⟨x, next⟩; rfl

theorem finish_safe_object (h : Heap) (cutoff b zs reserved : Nat) (z : ZStream) (s : InflateState)
    (sourceLen destLen : BPtr) (n capacity : UInt64) (l : UncLoop) (junk : List UInt8)
    (invariant : LocalStateJ h cutoff (.tab b) zs z s) (allocator : DefAlloc z)
    (inputCell : LengthCell h sourceLen n) (outputCell : LengthCell h destLen capacity)
    (inputRange : CallerRange h (.tab b) sourceLen 8 true)
    (outputRange : CallerRange h (.tab b) destLen 8 true)
    (separate : Separate sourceLen 8 destLen 8)
    (reservedBytes : Bytes h (.ref (.blk reserved) 0) 8 junk)
    (reservedRange : CallerRange h (.tab b) (.ref (.blk reserved) 0) 8 true)
    (reservedSource : Separate (.ref (.blk reserved) 0) 8 sourceLen 8)
    (reservedDest : Separate (.ref (.blk reserved) 0) 8 destLen 8)
    (q : BPtr) (count : Nat) (xs : List UInt8) (write : Bool)
    (objectBytes : Bytes h q count xs) (objectRange : CallerRange h (.tab b) q count write)
    (objectSource : Separate q count sourceLen 8) (objectDest : Separate q count destLen 8)
    (outside : ∀ off, q ≠ .ref (.blk reserved) off) :
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
      Bytes (releasedHeap clean b reserved) q count xs ∧
      (write = true → Writable (releasedHeap clean b reserved) q count) := by
  obtain ⟨mid, written, stores, current, finalAllocator, storeIn, storeOut, cellIn, cellOut, live, ownership⟩ :=
    LocalWriteback.ordered_length_writeback invariant allocator inputCell outputCell inputRange outputRange separate
      (l.len + z.avail_in.toUInt64) (l.left + z.avail_out.toUInt64)
  have rangeIn := cell_range_of_same_ownership cellIn inputRange ownership
  have rangeOut := cell_range_of_same_ownership cellOut outputRange ownership
  obtain ⟨reservedBytes1, reservedRange1⟩ := ordered_stores_keep_object storeIn storeOut ownership
    reservedBytes reservedRange reservedSource reservedDest
  obtain ⟨objectBytes1, objectRange1⟩ := ordered_stores_keep_object storeIn storeOut ownership
    objectBytes objectRange objectSource objectDest
  obtain ⟨clean, endRun, same, fresh, unique, streamGet, endLive, frame, _, _⟩ :=
    inflateEnd_local current.good current.roots finalAllocator.2
  obtain ⟨objectBytes2, objectWrite2⟩ := LocalFinish.frame_caller_object current.good current.roots objectBytes1 objectRange1 frame (end_borrow_of_heap same)
  have finalObject := released_object clean b reserved q count xs write objectBytes2 objectWrite2 outside
  obtain ⟨inputBytes2, inputWrite2⟩ := LocalFinish.frame_caller_object current.good current.roots cellIn.1 rangeIn frame (end_borrow_of_heap same)
  obtain ⟨outputBytes2, outputWrite2⟩ := LocalFinish.frame_caller_object current.good current.roots cellOut.1 rangeOut frame (end_borrow_of_heap same)
  obtain ⟨reservedBytes2, reservedWrite2⟩ := LocalFinish.frame_caller_object current.good current.roots reservedBytes1 reservedRange1 frame (end_borrow_of_heap same)
  obtain ⟨a, reservedGet, reservedRo⟩ : ∃ a, clean.bytes reserved = some a ∧ clean.ro reserved = false := by
    rcases reservedWrite2 rfl with null | ⟨ref, off, a, ptr, get, ro, room⟩
    · cases null.1
    · cases ptr
      exact ⟨a, get, ro⟩
  have cleanup := freeLocals_run clean b reserved _ a streamGet reservedGet reservedRo
  refine ⟨mid, written, clean, ?_, storeIn, storeOut, current,
    ⟨inputBytes2, inputWrite2 rfl⟩, ⟨outputBytes2, outputWrite2 rfl⟩, live, ?_,
    unique, fresh, streamGet, ⟨a, reservedGet, reservedRo⟩, finalObject⟩
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

#print axioms finish_safe_object
end Zlib.Uncompr.Proof.LocalCallerObjects
