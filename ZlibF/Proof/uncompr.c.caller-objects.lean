import ZlibF.Proof.«uncompr.c.single-length»

/-!
# Caller observations across the actual counted wrapper

An old caller byte range separate from the output and both scalar writeback
intervals retains its exact bytes and writability on the same actual final heap.
The proof follows real init, all loop calls, ordered scalar stores, End and both
local frees. Initial allocation refusal is included. Shared byte allocations are
admitted when their intervals are disjoint. Whole public framing and independent
format correctness remain separate obligations.
-/

namespace Zlib.Uncompr.Proof.CallerObjects
open C Zlib.Gzguts ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs
open Zlib.Uncompr.Proof.Wrapper Zlib.Uncompr.Proof.WrapperRanges Zlib.Uncompr.Proof.Objects
open Zlib.Uncompr.Proof.Finish Zlib.Uncompr.Proof.Cells Zlib.Uncompr.Proof.Writeback
open Zlib.Uncompr.Proof.Loop Zlib.Uncompr.Proof.PostRanges

theorem released_object (h : Heap) (stream reserved : Nat) (p : BPtr) (count : Nat) (xs : List UInt8) (write : Bool)
    (bytes : Bytes h p count xs) (writable : write = true → Writable h p count)
    (outside : ∀ off, p ≠ .ref (.blk reserved) off) :
    Bytes (releasedHeap h stream reserved) p count xs ∧
    (write = true → Writable (releasedHeap h stream reserved) p count) := by
  have view {ref : BRef} {off : Nat} {a : Array UInt8}
      (ptr : p = .ref ref off) (get : Space.get h ref = some a) :
      Space.get (releasedHeap h stream reserved) ref = some a := by
    cases ref with
    | blk b =>
      have different : b ≠ reserved := by intro same; subst b; exact outside off ptr
      simpa [Space.get, releasedHeap, different] using get
    | dstate_depth b => exact get
    | str i => exact get
    | st_dist_code => exact get
    | st_length_code => exact get
  constructor
  · rcases bytes with null | ⟨ref, off, a, ptr, get, room, values⟩
    · exact Or.inl null
    · exact Or.inr ⟨ref, off, a, ptr, view ptr get, room, values⟩
  · intro writing
    rcases writable writing with null | ⟨ref, off, a, ptr, get, ro, room⟩
    · exact Or.inl null
    · exact Or.inr ⟨ref, off, a, ptr, view ptr get, ro, room⟩

private theorem m_bind_assoc {α β γ : Type} (a : M α) (b : α → M β) (c : β → M γ) :
    ((a >>= b) >>= c) = (a >>= fun x => b x >>= c) := by
  funext h
  simp only [bind_app]
  cases first : a h with
  | error fault => rfl
  | ok pair => rcases pair with ⟨x, next⟩; rfl

theorem finish_safe_object (h : Heap) (b zs reserved : Nat) (z : ZStream) (s : InflateState)
    (sourceLen destLen : BPtr) (n capacity : UInt64) (l : UncLoop) (junk : List UInt8)
    (invariant : DefaultStateJ h (.tab b) zs z s) (allocator : DefAlloc z)
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
      DefaultStateJ written (.tab b) zs z s ∧
      LengthCell clean sourceLen (n - (l.len + z.avail_in.toUInt64)) ∧
      LengthCell clean destLen (capacity - (l.left + z.avail_out.toUInt64)) ∧
      LiveChange h written (fun _ => False) (fun _ => False) ∧
      LiveChange written clean (fun _ => False) (InflateOwned zs s) ∧
      Uniq clean ∧ Fresh clean ∧
      clean.streams b = some { z with state := none } ∧
      (∃ a, clean.bytes reserved = some a ∧ clean.ro reserved = false) ∧
      Bytes (releasedHeap clean b reserved) q count xs ∧
      (write = true → Writable (releasedHeap clean b reserved) q count) := by
  obtain ⟨mid, written, stores, current, finalAllocator, storeIn, storeOut, cellIn, cellOut, live, ownership⟩ :=
    ordered_length_writeback invariant allocator inputCell outputCell inputRange outputRange separate
      (l.len + z.avail_in.toUInt64) (l.left + z.avail_out.toUInt64)
  have rangeIn := cell_range_of_same_ownership cellIn inputRange ownership
  have rangeOut := cell_range_of_same_ownership cellOut outputRange ownership
  obtain ⟨reservedBytes1, reservedRange1⟩ := ordered_stores_keep_object storeIn storeOut ownership
    reservedBytes reservedRange reservedSource reservedDest
  obtain ⟨objectBytes1, objectRange1⟩ := ordered_stores_keep_object storeIn storeOut ownership
    objectBytes objectRange objectSource objectDest
  obtain ⟨clean, endRun, same, unique, fresh, streamGet, allocations, _check⟩ :=
    inflateEnd_safe current.good finalAllocator.2
  have frame : Frame written clean (fun x => StreamRoot (.tab b) x ∨ InflateOwned zs s x) := by
    rw [same]
    exact ZlibF.Spec.Public.InflateEndProof.end_frame current.good.live.hz (windowBlock current.good.inv.win)
  obtain ⟨objectBytes2, objectWrite2⟩ := frame_caller_object current.good objectBytes1 objectRange1 frame
  have finalObject := released_object clean b reserved q count xs write objectBytes2 objectWrite2 outside
  obtain ⟨inputBytes2, inputWrite2⟩ := frame_caller_object current.good cellIn.1 rangeIn frame
  obtain ⟨outputBytes2, outputWrite2⟩ := frame_caller_object current.good cellOut.1 rangeOut frame
  obtain ⟨reservedBytes2, reservedWrite2⟩ := frame_caller_object current.good reservedBytes1 reservedRange1 frame
  obtain ⟨a, reservedGet, reservedRo⟩ : ∃ a, clean.bytes reserved = some a ∧ clean.ro reserved = false := by
    rcases reservedWrite2 rfl with null | ⟨ref, off, a, ptr, get, ro, room⟩
    · cases null.1
    · cases ptr
      exact ⟨a, get, ro⟩
  have cleanup := freeLocals_run clean b reserved _ a streamGet reservedGet reservedRo
  have endLive := allocations (fun x => written.live x) (fun _ => Iff.rfl)
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

theorem core_original_bytes (h : Heap) (source dest p : BPtr) (capacity : UInt64)
    (fresh : Fresh h) (count : Nat) (xs : List UInt8) (bytes : Bytes h p count xs) :
    Bytes (coreHeap h source dest capacity) p count xs := by
  rcases bytes with null | ⟨ref, off, a, ptr, get, room, values⟩
  · exact Or.inl null
  · exact Or.inr ⟨ref, off, a, ptr, core_get h fresh source dest capacity ref a get, room, values⟩

theorem old_not_newblock (h : Heap) (fresh : Fresh h) (block : Nat) (new : h.nextBlk ≤ block)
    (p : BPtr) (count : Nat) (xs : List UInt8) (bytes : Bytes h p count xs) :
    ∀ off, p ≠ .ref (.blk block) off := by
  intro off ptr
  rw [ptr] at bytes
  rcases bytes with null | ⟨ref, start, a, same, get, _⟩
  · cases null.1
  · cases same
    have live : h.live block := Or.inl (by simp [show h.bytes block = some a from get])
    exact fresh block new live

theorem refused_object (h : Heap) (fresh : Fresh h) (p : BPtr) (count : Nat) (xs : List UInt8) (write : Bool)
    (bytes : Bytes h p count xs) (writable : write = true → Writable h p count) :
    Bytes (Zlib.Uncompr.Proof.InitialRefusal.refusedHeap h) p count xs ∧
    (write = true → Writable (Zlib.Uncompr.Proof.InitialRefusal.refusedHeap h) p count) := by
  have view {ref : BRef} {a : Array UInt8} (get : Space.get h ref = some a) :
      Space.get (Zlib.Uncompr.Proof.InitialRefusal.refusedHeap h) ref = some a ∧
      Space.ro (Zlib.Uncompr.Proof.InitialRefusal.refusedHeap h) ref = Space.ro h ref := by
    cases ref with
    | blk b =>
      have below : b < h.nextBlk := fresh.lt (Or.inl (by simp [show h.bytes b = some a from get]))
      constructor
      · simpa [Space.get, Zlib.Uncompr.Proof.InitialRefusal.refusedHeap, show b ≠ h.nextBlk + 1 by omega] using get
      · simp [Space.ro, Zlib.Uncompr.Proof.InitialRefusal.refusedHeap, show b ≠ h.nextBlk + 1 by omega]
    | dstate_depth b => exact ⟨get, rfl⟩
    | str i => exact ⟨get, rfl⟩
    | st_dist_code => exact ⟨get, rfl⟩
    | st_length_code => exact ⟨get, rfl⟩
  constructor
  · rcases bytes with null | ⟨ref, off, a, ptr, get, room, values⟩
    · exact Or.inl null
    · exact Or.inr ⟨ref, off, a, ptr, (view get).1, room, values⟩
  · intro writing
    rcases writable writing with null | ⟨ref, off, a, ptr, get, ro, room⟩
    · exact Or.inl null
    · exact Or.inr ⟨ref, off, a, ptr, (view get).1, (view get).2.trans ro, room⟩

theorem uncompress2_z_object (h after : Heap) (source dest sourceLen destLen : BPtr)
    (n capacity : UInt64) (xs : List UInt8) (rc : Int32)
    (fresh : Fresh h) (uniq : Uniq h) (globals : LibraryGlobals h)
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
      initialized_core_safe h source dest n capacity xs fresh uniq globals platform allocation
        readable writable separate validInput validOutput
    obtain ⟨inputRange, inputCell1, outputRange, outputCell1⟩ :=
      initialized_loop_cells h coreAfter source dest sourceLen destLen n capacity xs last stream state
        fresh uniq globals platform allocation inputCell outputCell readable writable separate
        sourceSeparate destSeparate validOutput coreRun current.good
    obtain ⟨reservedRange, reservedBytes⟩ := initialized_loop_reserved h coreAfter source dest n capacity xs
      last stream state fresh uniq globals platform allocation readable writable separate validOutput coreRun current.good
    have reservedSource := reserved_separate_old h fresh sourceLen 8 (lengthBytes n) inputCell.1
    have reservedDest := reserved_separate_old h fresh destLen 8 (lengthBytes capacity) outputCell.1
    obtain ⟨initial, initialAllocator⟩ := core_boundary h source dest capacity fresh uniq globals platform allocation
    have initialRanges := core_remaining_buffers h fresh source dest n capacity xs initial.good readable writable separate validOutput
    have initialRange := core_old_range h fresh source dest q capacity count ys write initial.good objectBytes objectWrite
    have initialBytes := core_original_bytes h source dest q capacity fresh count ys objectBytes
    have initialOutput : Separate q count (coreStream h source dest capacity).next_out
        (remainingOutput (coreStream h source dest capacity) { err := Z_OK, len := n, left := capacity }) := by
      simpa [remainingOutput, coreStream, outputStream] using separate_normalized h q dest count capacity objectOutput validOutput
    obtain ⟨objectRange1, objectBytes1, _objectSeparate1⟩ := loop_go_object C.fuel
      (coreHeap h source dest capacity) coreAfter h.nextBlk (h.nextBlk + 2)
      (coreStream h source dest capacity) stream (initializedState h) state
      { err := Z_OK, len := n, left := capacity } last q count ys write
      initial initialAllocator initialRanges (normalizedDest_nonnull h dest capacity validOutput)
      initialRange initialBytes initialOutput coreRun current.good
    have outside := old_not_newblock h fresh (h.nextBlk + 1) (by omega) q count ys objectBytes
    obtain ⟨_mid, _written, clean, finishRun, _storeIn, _storeOut, _writtenJ, _cellIn, _cellOut,
      _storesLive, _endLive, _unique, _fresh, _streamGet, _reservedGet, objectBytes2, objectWrite2⟩ :=
      finish_safe_object coreAfter h.nextBlk (h.nextBlk + 2) (h.nextBlk + 1) stream state
        sourceLen destLen n capacity last (junkBytes h).toList current allocator inputCell1 outputCell1
        inputRange outputRange cellSeparate reservedBytes reservedRange reservedSource reservedDest
        q count ys write objectBytes1 objectRange1 objectSourceCell objectDestCell outside
    have fullRun : C.run (uncompress2_z dest destLen source sourceLen) h =
        .ok (resultCode last.err (last.len + stream.avail_in.toUInt64), releasedHeap clean h.nextBlk (h.nextBlk + 1)) := by
      rw [uncompress2_z_to_core h source dest sourceLen destLen n capacity fresh uniq globals platform
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
#print axioms finish_safe_object
end Zlib.Uncompr.Proof.CallerObjects
