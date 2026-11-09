import ZlibF.Proof.«uncompr.c.final-frame»
import ZlibF.Proof.«uncompr.c.output-observation»
import ZlibF.Proof.«uncompr.c.scalar-frame-mirror»

/-!
# Actual counted-wrapper stores and complete caller frame

The same full execution yields explicit output bytes, exact scalar counts and
three ordered pure expected Stores from the original caller heap. Mirroring the
actual Stores and composing real decoder, End and local-free frames gives Frame
from that final expected heap to the actual final heap. The live allocation set
also returns to the original set. First refusal retains incoming scalar values;
NULL+zero and partial output before late memory failure are included. SameObjects,
independent format evidence and valid-stream END are separate targets.
-/

set_option autoImplicit false

namespace Zlib.Uncompr.Proof.WrapperStoreFrame
open C Zlib.Gzguts ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs
open Zlib.Uncompr.Proof.Wrapper Zlib.Uncompr.Proof.WrapperRanges Zlib.Uncompr.Proof.Objects
open Zlib.Uncompr.Proof.Loop Zlib.Uncompr.Proof.PostRanges Zlib.Uncompr.Proof.Buffers
open Zlib.Uncompr.Proof.Finish Zlib.Uncompr.Proof.CallerObjects Zlib.Uncompr.Proof.Cells
open Zlib.Uncompr.Proof.Writeback Zlib.Uncompr.Proof.CallerFrame Zlib.Uncompr.Proof.FinalFrame

private theorem separate_symm (p q : BPtr) (n m : Nat) (separate : Separate p n q m) :
    Separate q m p n := by
  cases p <;> cases q <;> simp_all [Separate, ne_comm, or_comm, or_left_comm, or_assoc]

private theorem bytes_root_live (h : Heap) (p : BPtr) (count : Nat) (xs : List UInt8)
    (bytes : Bytes h p count xs) (b : Nat) (root : ByteRoot p b) : h.live b := by
  rcases bytes with null | ⟨ref, off, array, ptr, get, _⟩
  · rw [null.1] at root
    cases root
  · subst p
    cases ref with
    | blk i =>
      change b = i at root
      subst b
      exact Or.inl (by simp [show h.bytes i = some array from get])
    | dstate_depth i =>
      change b = i at root
      subst b
      cases state : h.dstates i with
      | none => simp [Space.get, state] at get
      | some s => simp [Heap.live, state]
    | str i => cases root
    | st_dist_code => cases root
    | st_length_code => cases root

private theorem old_root_outside (h : Heap) (fresh : Fresh h) (p : BPtr) (count : Nat) (xs : List UInt8)
    (bytes : Bytes h p count xs) (b : Nat) (root : ByteRoot p b) :
    h.live b ∧ ¬ (StreamRoot (.tab h.nextBlk) b ∨ InflateOwned (h.nextBlk + 2) (initializedState h) b) := by
  have live := bytes_root_live h p count xs bytes b root
  have below := fresh.lt live
  refine ⟨live, ?_⟩
  rintro (stream | state | window)
  · change b = h.nextBlk at stream
    omega
  · omega
  · rw [initial_window_null] at window
    cases window

private theorem m_bind_assoc {α β γ : Type} (a : M α) (b : α → M β) (c : β → M γ) :
    ((a >>= b) >>= c) = (a >>= fun x => b x >>= c) := by
  funext h
  simp only [bind_app]
  cases first : a h with
  | error fault => rfl
  | ok pair => rcases pair with ⟨x, next⟩; rfl


private theorem finish_output_frame (h : Heap) (b zs reserved : Nat) (z : ZStream) (s : InflateState)
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
      (write = true → Writable (releasedHeap clean b reserved) q count) ∧
      Frame written clean (fun x => StreamRoot (.tab b) x ∨ InflateOwned zs s x) := by
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
    unique, fresh, streamGet, ⟨a, reservedGet, reservedRo⟩, finalObject.1, finalObject.2, frame⟩
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

theorem uncompress2_z_store_frame (h after : Heap) (source dest sourceLen destLen : BPtr)
    (n capacity : UInt64) (xs : List UInt8) (rc : Int32)
    (fresh : Fresh h) (uniq : Uniq h) (globals : LibraryGlobals h)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit h) (allocation : h.allocOk h.nalloc = true)
    (inputCell : LengthCell h sourceLen n) (outputCell : LengthCell h destLen capacity)
    (readable : Bytes h source n.toNat xs) (writable : Writable h dest capacity.toNat)
    (separate : Separate source n.toNat dest capacity.toNat)
    (sourceSeparate : Separate sourceLen 8 dest capacity.toNat)
    (destSeparate : Separate destLen 8 dest capacity.toNat)
    (cellSeparate : Separate sourceLen 8 destLen 8)
    (validInput : source = .null → n = 0) (validOutput : dest = .null → capacity = 0)
    (run : C.run (uncompress2_z dest destLen source sourceLen) h = .ok (rc, after)) :
    ∃ output used first second expected,
      Store h dest output first ∧ Store first sourceLen (lengthBytes (UInt64.ofNat used)) second ∧
      Store second destLen (lengthBytes (UInt64.ofNat output.length)) expected ∧ Frame expected after (fun _ => False) ∧
      Bytes after dest output.length output ∧ LengthCell after sourceLen (UInt64.ofNat used) ∧
      LengthCell after destLen (UInt64.ofNat output.length) ∧ used ≤ n.toNat ∧ output.length ≤ capacity.toNat := by
  obtain ⟨last, coreAfter, stream, state, used, produced, coreRun, current, allocator,
    ranges, nonnull, stopped, code, countIn, countOut, coreLedger, owners⟩ :=
    initialized_core_safe h source dest n capacity xs fresh uniq globals platform allocation
      readable writable separate validInput validOutput
  obtain ⟨inputRange, inputCell1, outputRange0, outputCell1⟩ :=
    initialized_loop_cells h coreAfter source dest sourceLen destLen n capacity xs last stream state
      fresh uniq globals platform allocation inputCell outputCell readable writable separate
      sourceSeparate destSeparate validOutput coreRun current.good
  obtain ⟨reservedRange, reservedBytes⟩ := initialized_loop_reserved h coreAfter source dest n capacity xs
    last stream state fresh uniq globals platform allocation readable writable separate validOutput coreRun current.good
  have reservedSource := reserved_separate_old h fresh sourceLen 8 (lengthBytes n) inputCell.1
  have reservedDest := reserved_separate_old h fresh destLen 8 (lengthBytes capacity) outputCell.1
  obtain ⟨initial, initialAllocator⟩ := core_boundary h source dest capacity fresh uniq globals platform allocation
  have initialRanges := core_remaining_buffers h fresh source dest n capacity xs initial.good readable writable separate validOutput
  obtain ⟨made, output, expectedCore, madeCount, _cursor, length, normalizedBytes, normalizedRange,
    _frame, normalizedStore, coreExpectedFrame, _array, _objects⟩ :=
    Zlib.Uncompr.Proof.OutputPrefix.loop_output_store (coreHeap h source dest capacity) coreAfter
      h.nextBlk (h.nextBlk + 2) (coreStream h source dest capacity) stream (initializedState h) state
      { err := Z_OK, len := n, left := capacity } last initial initialAllocator initialRanges
      (normalizedDest_nonnull h dest capacity validOutput) coreRun current.good
  change remainingOutput stream last + made = capacity.toNat at madeCount
  have madeBound : made ≤ capacity.toNat := by omega
  have originalObservation : Bytes coreAfter dest made output ∧
      CallerRange coreAfter (.tab h.nextBlk) dest made true ∧
      Store (coreHeap h source dest capacity) dest output expectedCore := by
    by_cases null : dest = .null
    · have zero : made = 0 := by
        have bound : made ≤ 0 := by simpa [validOutput null] using madeBound
        omega
      subst made
      have empty : output = [] := List.length_eq_zero_iff.mp (by omega)
      subst output
      have expectedSame := normalizedStore.empty_eq
      exact ⟨Or.inl ⟨null, rfl, rfl⟩, Or.inl null, Or.inl ⟨rfl, expectedSame⟩⟩
    · have originalOut : (coreStream h source dest capacity).next_out = dest := by
        simp [coreStream, outputStream, normalizedDest, null]
      simpa only [originalOut] using And.intro normalizedBytes (And.intro normalizedRange normalizedStore)
  obtain ⟨observed, outputRange, outputStore⟩ := originalObservation
  have inputBound : used ≤ n.toNat := by omega
  have sameMade : produced = made := by omega
  have outputSource : Separate dest made sourceLen 8 := separate_prefix dest sourceLen capacity.toNat 8 made 8
    (separate_symm _ _ _ _ sourceSeparate) madeBound (Nat.le_refl _)
  have outputDest : Separate dest made destLen 8 := separate_prefix dest destLen capacity.toNat 8 made 8
    (separate_symm _ _ _ _ destSeparate) madeBound (Nat.le_refl _)
  obtain ⟨oldOutput, oldReadable⟩ := writable_bytes h dest capacity.toNat writable
  have outside := old_not_newblock h fresh (h.nextBlk + 1) (by omega) dest capacity.toNat oldOutput oldReadable
  obtain ⟨mid, written, clean, finishRun, sourceStore, destStore, _writtenJ, cellIn, cellOut,
    _storeLive, _endLive, _unique, _fresh, _streamGet, _reservedGet, finalOutput, _outputWrite, endFrame⟩ :=
    finish_output_frame coreAfter h.nextBlk (h.nextBlk + 2) (h.nextBlk + 1) stream state
      sourceLen destLen n capacity last (junkBytes h).toList current allocator inputCell1 outputCell1
      inputRange outputRange0 cellSeparate reservedBytes reservedRange reservedSource reservedDest
      dest made output true observed outputRange outputSource outputDest outside

  have inputFinal := released_cell clean h.nextBlk (h.nextBlk + 1) sourceLen _ cellIn
    (old_not_newblock h fresh (h.nextBlk + 1) (by omega) sourceLen 8 (lengthBytes n) inputCell.1)
  have outputFinal := released_cell clean h.nextBlk (h.nextBlk + 1) destLen _ cellOut
    (old_not_newblock h fresh (h.nextBlk + 1) (by omega) destLen 8 (lengthBytes capacity) outputCell.1)
  have countedIn := final_count_exact n last.len stream.avail_in (by unfold remainingInput at countIn; omega)
  have countedOut := final_count_exact capacity last.left stream.avail_out (by unfold remainingOutput at countOut; omega)
  have usedValue : n - (last.len + stream.avail_in.toUInt64) = UInt64.ofNat used := by
    apply UInt64.toNat_inj.mp
    rw [countedIn.2, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by have := n.toNat_lt; omega)]
    unfold remainingInput at countIn
    omega
  have madeValue : capacity - (last.left + stream.avail_out.toUInt64) = UInt64.ofNat made := by
    apply UInt64.toNat_inj.mp
    rw [countedOut.2, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by have := capacity.toNat_lt; omega)]
    unfold remainingOutput at madeCount
    omega
  rw [usedValue] at sourceStore
  rw [madeValue, ← length] at destStore
  have outputRoots : ∀ b, ByteRoot dest b → h.live b ∧ ¬ (fun _ => False) b := by
    intro b root
    exact ⟨bytes_root_live h dest capacity.toNat oldOutput oldReadable b root, by simp⟩
  obtain ⟨first, outputExpectedStore, initialExpectedFrame⟩ :=
    Zlib.Uncompr.Proof.FrameMirror.store_mirror (core_frame h source dest capacity fresh) outputRoots outputStore
  have sourceCoreRoots : ∀ b, ByteRoot sourceLen b → expectedCore.live b ∧
      ¬ (StreamRoot (.tab h.nextBlk) b ∨ InflateOwned (h.nextBlk + 2) (initializedState h) b) := by
    intro b root
    obtain ⟨oldLive, outside⟩ := old_root_outside h fresh sourceLen 8 (lengthBytes n) inputCell.1 b root
    have coreLive := (frame_live_at (core_frame h source dest capacity fresh) b oldLive (by simp)).mpr oldLive
    exact ⟨(outputStore.shape.live b).mpr coreLive, outside⟩
  obtain ⟨sourceExpectedCore, sourceExpectedCoreStore, sourceCoreFrame⟩ :=
    Zlib.Uncompr.Proof.FrameMirror.store_mirror coreExpectedFrame sourceCoreRoots sourceStore
  have destCoreRoots : ∀ b, ByteRoot destLen b → sourceExpectedCore.live b ∧
      ¬ (StreamRoot (.tab h.nextBlk) b ∨ InflateOwned (h.nextBlk + 2) (initializedState h) b) := by
    intro b root
    obtain ⟨oldLive, outside⟩ := old_root_outside h fresh destLen 8 (lengthBytes capacity) outputCell.1 b root
    have coreLive := (frame_live_at (core_frame h source dest capacity fresh) b oldLive (by simp)).mpr oldLive
    exact ⟨(sourceExpectedCoreStore.shape.live b).mpr ((outputStore.shape.live b).mpr coreLive), outside⟩
  obtain ⟨bothExpectedCore, destExpectedCoreStore, bothCoreFrame⟩ :=
    Zlib.Uncompr.Proof.FrameMirror.store_mirror sourceCoreFrame destCoreRoots destStore
  have sourceOriginalRoots : ∀ b, ByteRoot sourceLen b → first.live b ∧ ¬ (fun _ => False) b := by
    intro b root
    have oldLive := bytes_root_live h sourceLen 8 (lengthBytes n) inputCell.1 b root
    exact ⟨(outputExpectedStore.shape.live b).mpr oldLive, by simp⟩
  obtain ⟨second, sourceExpectedStore, sourceExpectedFrame⟩ :=
    Zlib.Uncompr.Proof.FrameMirror.store_mirror initialExpectedFrame sourceOriginalRoots sourceExpectedCoreStore
  have destOriginalRoots : ∀ b, ByteRoot destLen b → second.live b ∧ ¬ (fun _ => False) b := by
    intro b root
    have oldLive := bytes_root_live h destLen 8 (lengthBytes capacity) outputCell.1 b root
    exact ⟨(sourceExpectedStore.shape.live b).mpr ((outputExpectedStore.shape.live b).mpr oldLive), by simp⟩
  obtain ⟨expected, destExpectedStore, bothExpectedFrame⟩ :=
    Zlib.Uncompr.Proof.FrameMirror.store_mirror sourceExpectedFrame destOriginalRoots destExpectedCoreStore
  have callerShape : Shape h expected :=
    (outputExpectedStore.shape.trans sourceExpectedStore.shape).trans destExpectedStore.shape
  have finalFrame := cleanup_caller_frame h expected bothExpectedCore written clean source dest capacity state
    fresh callerShape bothExpectedFrame bothCoreFrame endFrame owners
  have fullRun : C.run (uncompress2_z dest destLen source sourceLen) h =
      .ok (resultCode last.err (last.len + stream.avail_in.toUInt64), releasedHeap clean h.nextBlk (h.nextBlk + 1)) := by
    rw [uncompress2_z_to_core h source dest sourceLen destLen n capacity fresh uniq globals platform
      allocation inputCell outputCell validInput validOutput]
    simp only [C.run] at coreRun finishRun
    simpa only [bind_app, coreRun] using finishRun
  have heaps : releasedHeap clean h.nextBlk (h.nextBlk + 1) = after :=
    congrArg Prod.snd (Except.ok.inj (fullRun.symm.trans run))
  rw [← heaps]
  refine ⟨output, used, first, second, expected, outputExpectedStore, sourceExpectedStore,
    destExpectedStore, finalFrame, ?_, ?_, ?_, inputBound, by omega⟩
  · simpa only [length] using finalOutput
  · simpa only [usedValue] using inputFinal
  · simpa only [madeValue, length] using outputFinal

private theorem length_cell_store_self (h : Heap) (p : BPtr) (value : UInt64)
    (cell : LengthCell h p value) : Store h p (lengthBytes value) h := by
  rcases cell.2 with null | ⟨ref, off, array, ptr, get, write, room⟩
  · simp at null
  · subst p
    rcases cell.1 with null | ⟨ref', off', other, pointer, otherGet, _bound, values⟩
    · cases null.1
    · cases pointer
      have same : other = array := Option.some.inj (otherGet.symm.trans get)
      subst other
      have listExtract : (array.extract off (off + 8)).toList = (array.toList.drop off).take 8 := by
        simp only [Array.toList_extract, List.extract, Nat.add_sub_cancel_left]
      have encoding : (lengthBytes value).toArray = array.extract off (off + 8) := by
        rw [show lengthBytes value = (array.extract off (off + 8)).toList from values.trans listExtract.symm,
          Array.toArray_toList]
      have restored : array.extract 0 off ++ (lengthBytes value).toArray ++ array.extract (off + 8) array.size = array := by
        rw [encoding]
        exact (Zlib.Uncompr.Proof.OutputPrefix.array_eq_prefix_slice_suffix array array off 8 rfl room
          (fun _ _ _ => rfl)).symm
      refine Or.inr ⟨ref, off, array, rfl, get, write, ?_, ?_⟩
      · simpa [lengthBytes] using room
      · simp only [lengthBytes, List.length_map, List.length_range]
        change h = Space.put h ref (array.extract 0 off ++ (lengthBytes value).toArray ++ array.extract (off + 8) array.size)
        rw [restored, byte_view_put_self get write]

private theorem empty_bytes_of_writable (h : Heap) (p : BPtr) (capacity : Nat)
    (writable : Writable h p capacity) : Bytes h p 0 [] := by
  rcases writable with null | ⟨ref, off, array, ptr, get, _write, room⟩
  · exact Or.inl ⟨null.1, rfl, rfl⟩
  · exact Or.inr ⟨ref, off, array, ptr, get, by omega, by simp⟩

theorem uncompress2_z_store_frame_allocation (h after : Heap) (source dest sourceLen destLen : BPtr)
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
    ∃ output used got consumed first second expected,
      Store h dest output first ∧ Store first sourceLen (lengthBytes consumed) second ∧
      Store second destLen (lengthBytes got) expected ∧ Frame expected after (fun _ => False) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ Bytes after dest output.length output ∧
      LengthCell after sourceLen consumed ∧ LengthCell after destLen got ∧
      used ≤ n.toNat ∧ output.length ≤ capacity.toNat ∧
      ((got.toNat = output.length ∧ consumed.toNat = used) ∨
        (rc = Z_MEM_ERROR ∧ output = [] ∧ got = capacity ∧ consumed = n)) := by
  obtain ⟨rc', returned, actual, ledger, _initial, _counted⟩ :=
    Zlib.Uncompr.Proof.InitialRefusal.uncompress2_z_memory h source dest sourceLen destLen n capacity xs
      fresh uniq globals platform inputCell outputCell readable writable separate
      sourceSeparate destSeparate cellSeparate validInput validOutput
  have returnedEq : returned = after := congrArg Prod.snd (Except.ok.inj (actual.symm.trans run))
  have sameLive : LiveChange h after (fun _ => False) (fun _ => False) := by simpa only [returnedEq] using ledger
  by_cases allocation : h.allocOk h.nalloc = true
  · obtain ⟨output, used, first, second, expected, outputStore, sourceStore, destStore, frame,
      observed, input, produced, usedBound, madeBound⟩ :=
      uncompress2_z_store_frame h after source dest sourceLen destLen n capacity xs rc fresh uniq globals platform allocation
        inputCell outputCell readable writable separate sourceSeparate destSeparate cellSeparate validInput validOutput run
    refine ⟨output, used, UInt64.ofNat output.length, UInt64.ofNat used, first, second, expected,
      outputStore, sourceStore, destStore, frame, sameLive, observed, input, produced,
      usedBound, madeBound, Or.inl ⟨?_, ?_⟩⟩
    · rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by have := capacity.toNat_lt; omega)]
    · rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by have := n.toNat_lt; omega)]

  · have actualRefusal := Zlib.Uncompr.Proof.InitialRefusal.uncompress2_z_initial_refusal h source dest sourceLen destLen
      n capacity fresh allocation inputCell outputCell validInput validOutput
    have equal := Except.ok.inj (actualRefusal.symm.trans run)
    have heaps : Zlib.Uncompr.Proof.InitialRefusal.refusedHeap h = after := congrArg Prod.snd equal
    have result : rc = Z_MEM_ERROR := (congrArg Prod.fst equal).symm
    obtain ⟨old, oldReadable⟩ := writable_bytes h dest capacity.toNat writable
    have retained := refused_object h fresh dest capacity.toNat old true oldReadable (fun _ => writable)
    rw [← heaps] at sameLive ⊢
    exact ⟨[], 0, capacity, n, h, h, h, Or.inl ⟨rfl, rfl⟩,
      length_cell_store_self h sourceLen n inputCell, length_cell_store_self h destLen capacity outputCell,
      Zlib.Uncompr.Proof.InitialRefusal.refused_frame h fresh, sameLive,
      empty_bytes_of_writable _ dest capacity.toNat (retained.2 rfl),
      Zlib.Uncompr.Proof.InitialRefusal.refused_cell h fresh sourceLen n inputCell,
      Zlib.Uncompr.Proof.InitialRefusal.refused_cell h fresh destLen capacity outputCell,
      Nat.zero_le _, Nat.zero_le _, Or.inr ⟨result, rfl, rfl, rfl⟩⟩

theorem uncompress2_z_framed_memory (h : Heap) (source dest sourceLen destLen : BPtr)
    (n capacity : UInt64) (xs : List UInt8)
    (fresh : Fresh h) (uniq : Uniq h) (globals : LibraryGlobals h)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit h)
    (inputCell : LengthCell h sourceLen n) (outputCell : LengthCell h destLen capacity)
    (readable : Bytes h source n.toNat xs) (writable : Writable h dest capacity.toNat)
    (separate : Separate source n.toNat dest capacity.toNat)
    (sourceSeparate : Separate sourceLen 8 dest capacity.toNat)
    (destSeparate : Separate destLen 8 dest capacity.toNat)
    (cellSeparate : Separate sourceLen 8 destLen 8)
    (validInput : source = .null → n = 0) (validOutput : dest = .null → capacity = 0)
 :
    ∃ rc after output used got consumed first second expected,
      C.run (uncompress2_z dest destLen source sourceLen) h = .ok (rc, after) ∧
      Store h dest output first ∧ Store first sourceLen (lengthBytes consumed) second ∧
      Store second destLen (lengthBytes got) expected ∧ Frame expected after (fun _ => False) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ Bytes after dest output.length output ∧
      LengthCell after sourceLen consumed ∧ LengthCell after destLen got ∧
      used ≤ n.toNat ∧ output.length ≤ capacity.toNat ∧
      ((got.toNat = output.length ∧ consumed.toNat = used) ∨
        (rc = Z_MEM_ERROR ∧ output = [] ∧ got = capacity ∧ consumed = n)) := by
  obtain ⟨rc, after, run, _ledger, _initial, _counted⟩ :=
    Zlib.Uncompr.Proof.InitialRefusal.uncompress2_z_memory h source dest sourceLen destLen n capacity xs
      fresh uniq globals platform inputCell outputCell readable writable separate
      sourceSeparate destSeparate cellSeparate validInput validOutput
  obtain ⟨output, used, got, consumed, first, second, expected, stores⟩ :=
    uncompress2_z_store_frame_allocation h after source dest sourceLen destLen n capacity xs rc
      fresh uniq globals platform inputCell outputCell readable writable separate
      sourceSeparate destSeparate cellSeparate validInput validOutput run
  exact ⟨rc, after, output, used, got, consumed, first, second, expected, run, stores⟩

#print axioms uncompress2_z_framed_memory

#print axioms uncompress2_z_store_frame_allocation

#print axioms uncompress2_z_store_frame
end Zlib.Uncompr.Proof.WrapperStoreFrame
