import ZlibF.Proof.«uncompr.c.initial-refusal»

/-!
# Heap shape after the actual uncompress wrapper

The same actual returning execution retains allocation-type uniqueness,
freshness and the byte-object platform scope. Both first refusal and later
allocation failures are included. These observations support callers that
free their own temporary scalar objects after the wrapper returns. The
public functional goal remains separate.
-/

namespace Zlib.Uncompr.Proof.WrapperShape
open C Zlib.Gzguts ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs
open Zlib.Uncompr.Proof.Wrapper Zlib.Uncompr.Proof.WrapperRanges Zlib.Uncompr.Proof.Objects
open Zlib.Uncompr.Proof.Finish Zlib.Uncompr.Proof.Cells Zlib.Uncompr.Proof.InitialRefusal
open Zlib.Uncompr.Proof.Writeback
open Zlib.Uncompr.Proof.Loop Zlib.Uncompr.Proof.PostRanges

theorem released_uniq (h : Heap) (stream reserved : Nat) (uniq : Uniq h) :
    Uniq (releasedHeap h stream reserved) := by
  intro x
  have count := uniq x
  by_cases atBytes : x = reserved <;> by_cases atStream : x = stream
  all_goals simp_all only [releasedHeap, upd_apply, ↓reduceIte, cnt_none]
  all_goals omega

theorem released_subset (h : Heap) (stream reserved x : Nat) :
    (releasedHeap h stream reserved).live x → h.live x := by
  intro live
  simp only [releasedHeap, Heap.live] at live
  rcases live with byte | word | strm | header | dstate | istate | gzstate
  · left
    by_cases same : x = reserved
    · simp [same] at byte
    · simpa [same] using byte
  · exact Or.inr (Or.inl word)
  · right; right; left
    by_cases same : x = stream
    · simp [same] at strm
    · simpa [same] using strm
  · exact Or.inr (Or.inr (Or.inr (Or.inl header)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl dstate))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl istate)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr gzstate)))))

theorem released_fresh (h : Heap) (stream reserved : Nat) (fresh : Fresh h) :
    Fresh (releasedHeap h stream reserved) := by
  intro x bound live
  exact fresh x bound (released_subset h stream reserved x live)

theorem refused_uniq (h : Heap) (uniq : Uniq h) : Uniq (refusedHeap h) := by
  simpa only [Uniq, refusedHeap, releasedHeap] using released_uniq h h.nextBlk (h.nextBlk + 1) uniq

theorem refused_fresh (h : Heap) (fresh : Fresh h) : Fresh (refusedHeap h) := by
  intro x bound live
  have oldLive := (refused_live h fresh x).mp live
  have old : h.live x := by simpa using oldLive
  have next : h.nextBlk ≤ x := by change h.nextBlk + 2 ≤ x at bound; omega
  exact fresh x next old

theorem removed_bytes_platform (h : Heap) (block : Nat)
    (fit : ZlibF.PlatformMemory.ByteObjectsFit h) :
    ZlibF.PlatformMemory.ByteObjectsFit { h with bytes := upd h.bytes block none } := by
  apply fit.of_sizes_le
  intro ref a get
  refine ⟨a, ?_, Nat.le_refl _⟩
  cases ref with
  | blk b =>
    by_cases same : b = block
    · simp [Space.get, same] at get
    · simpa [Space.get, same] using get
  | dstate_depth b => exact get
  | str i => exact get
  | st_dist_code => exact get
  | st_length_code => exact get

theorem freeWin_platform (h : Heap) (window : BPtr)
    (fit : ZlibF.PlatformMemory.ByteObjectsFit h) :
    ZlibF.PlatformMemory.ByteObjectsFit (freeWin h window) := by
  cases window with
  | null => exact fit
  | ref ref off =>
    cases ref <;> cases off <;>
      first | exact fit | exact removed_bytes_platform h _ fit

theorem ended_platform (h : Heap) (zs b : Nat) (s : InflateState) (z : ZStream)
    (fit : ZlibF.PlatformMemory.ByteObjectsFit h) :
    ZlibF.PlatformMemory.ByteObjectsFit ((.tab b : ZStreamRef).put (endHeap h zs s) { z with state := none }) := by
  have win := freeWin_platform h s.window fit
  have state : ZlibF.PlatformMemory.ByteObjectsFit (endHeap h zs s) := win.of_storage_eq rfl rfl rfl
  exact state.put_stream (.tab b) _

theorem released_platform (h : Heap) (stream reserved : Nat)
    (fit : ZlibF.PlatformMemory.ByteObjectsFit h) :
    ZlibF.PlatformMemory.ByteObjectsFit (releasedHeap h stream reserved) :=
  (removed_bytes_platform h reserved fit).of_storage_eq rfl rfl rfl

private theorem m_bind_assoc {α β γ : Type} (a : M α) (b : α → M β) (c : β → M γ) :
    ((a >>= b) >>= c) = (a >>= fun x => b x >>= c) := by
  funext h
  simp only [bind_app]
  cases first : a h with
  | error fault => rfl
  | ok pair => rcases pair with ⟨x, next⟩; rfl

theorem finish_safe_platform (h : Heap) (b zs reserved : Nat) (z : ZStream) (s : InflateState)
    (sourceLen destLen : BPtr) (n capacity : UInt64) (l : UncLoop) (junk : List UInt8)
    (invariant : DefaultStateJ h (.tab b) zs z s) (allocator : DefAlloc z)
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
      DefaultStateJ written (.tab b) zs z s ∧
      LengthCell clean sourceLen (n - (l.len + z.avail_in.toUInt64)) ∧
      LengthCell clean destLen (capacity - (l.left + z.avail_out.toUInt64)) ∧
      LiveChange h written (fun _ => False) (fun _ => False) ∧
      LiveChange written clean (fun _ => False) (InflateOwned zs s) ∧
      Uniq clean ∧ Fresh clean ∧
      clean.streams b = some { z with state := none } ∧
      (∃ a, clean.bytes reserved = some a ∧ clean.ro reserved = false) ∧
      ZlibF.PlatformMemory.ByteObjectsFit (releasedHeap clean b reserved) := by
  obtain ⟨mid, written, stores, current, finalAllocator, storeIn, storeOut, cellIn, cellOut, live, ownership⟩ :=
    ordered_length_writeback invariant allocator inputCell outputCell inputRange outputRange separate
      (l.len + z.avail_in.toUInt64) (l.left + z.avail_out.toUInt64)
  have rangeIn := cell_range_of_same_ownership cellIn inputRange ownership
  have rangeOut := cell_range_of_same_ownership cellOut outputRange ownership
  obtain ⟨reservedBytes1, reservedRange1⟩ := ordered_stores_keep_object storeIn storeOut ownership
    reservedBytes reservedRange reservedSource reservedDest
  obtain ⟨clean, endRun, same, unique, fresh, streamGet, allocations, _check⟩ :=
    inflateEnd_safe current.good finalAllocator.2
  have frame : Frame written clean (fun x => StreamRoot (.tab b) x ∨ InflateOwned zs s x) := by
    rw [same]
    exact ZlibF.Spec.Public.InflateEndProof.end_frame current.good.live.hz (windowBlock current.good.inv.win)
  obtain ⟨inputBytes2, inputWrite2⟩ := frame_caller_object current.good cellIn.1 rangeIn frame (end_borrow_of_heap same)
  obtain ⟨outputBytes2, outputWrite2⟩ := frame_caller_object current.good cellOut.1 rangeOut frame (end_borrow_of_heap same)
  obtain ⟨reservedBytes2, reservedWrite2⟩ := frame_caller_object current.good reservedBytes1 reservedRange1 frame (end_borrow_of_heap same)
  obtain ⟨a, reservedGet, reservedRo⟩ : ∃ a, clean.bytes reserved = some a ∧ clean.ro reserved = false := by
    rcases reservedWrite2 rfl with null | ⟨ref, off, a, ptr, get, ro, room⟩
    · cases null.1
    · cases ptr
      exact ⟨a, get, ro⟩
  have cleanup := freeLocals_run clean b reserved _ a streamGet reservedGet reservedRo
  have endLive := allocations (fun x => written.live x) (fun _ => Iff.rfl)
  have cleanPlatform : ZlibF.PlatformMemory.ByteObjectsFit clean := by
    rw [same]
    exact ended_platform written zs b s z current.platform
  have finalPlatform := released_platform clean b reserved cleanPlatform
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


/-- The same returning actual wrapper retains a fresh, unique heap.
The actual first allocation refusal is included. -/
theorem uncompress2_z_return_shape (h after : Heap) (source dest sourceLen destLen : BPtr)
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
    (run : C.run (uncompress2_z dest destLen source sourceLen) h = .ok (rc, after)) :
    Uniq after ∧ Fresh after ∧ ZlibF.PlatformMemory.ByteObjectsFit after := by
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
    obtain ⟨mid, written, clean, finishRun, storeIn, storeOut, writtenJ, inputCell2, outputCell2,
      storeLedger, endLedger, cleanUnique, cleanFresh, cleanStream, localGet, finalPlatform⟩ :=
      finish_safe_platform coreAfter h.nextBlk (h.nextBlk + 2) (h.nextBlk + 1) stream state
        sourceLen destLen n capacity last (junkBytes h).toList current allocator inputCell1 outputCell1
        inputRange outputRange cellSeparate reservedBytes reservedRange reservedSource reservedDest
    let final := releasedHeap clean h.nextBlk (h.nextBlk + 1)
    have fullRun : C.run (uncompress2_z dest destLen source sourceLen) h =
        .ok (resultCode last.err (last.len + stream.avail_in.toUInt64), final) := by
      rw [uncompress2_z_to_core h source dest sourceLen destLen n capacity fresh uniq globals platform
        allocation inputCell outputCell validInput validOutput]
      simp only [C.run] at coreRun finishRun
      simpa only [bind_app, coreRun] using finishRun
    have same := Except.ok.inj (fullRun.symm.trans run)
    have heaps : final = after := congrArg Prod.snd same
    rw [← heaps]
    exact ⟨released_uniq clean h.nextBlk (h.nextBlk + 1) cleanUnique,
      released_fresh clean h.nextBlk (h.nextBlk + 1) cleanFresh, finalPlatform⟩
  · have actual := uncompress2_z_initial_refusal h source dest sourceLen destLen n capacity fresh allocation
      inputCell outputCell validInput validOutput
    have same := Except.ok.inj (actual.symm.trans run)
    cases same
    have fit : ZlibF.PlatformMemory.ByteObjectsFit (refusedHeap h) :=
      (removed_bytes_platform h (h.nextBlk + 1) platform).of_storage_eq rfl rfl rfl
    exact ⟨refused_uniq h uniq, refused_fresh h fresh, fit⟩

#print axioms finish_safe_platform
#print axioms uncompress2_z_return_shape
end Zlib.Uncompr.Proof.WrapperShape
