import ZlibF.Proof.«uncompr.c.caller-objects»
import ZlibF.Proof.«uncompr.c.output-store»

/-!
# Output bytes and scalar accounting on the final actual heap

The exact output prefix survives both real scalar Stores, End and both local
frees. A pure expected Store starts from the original caller heap; the final
actual Bytes and length-cell values describe that same produced byte list.
First allocation refusal preserves the incoming scalar values with empty output.
NULL+zero output uses the real reserved binding internally and has empty NULL
Bytes after cleanup. A complete expected-to-actual Frame and independent format
correctness remain open; no SameObjects conclusion is asserted here.
-/

namespace Zlib.Uncompr.Proof.OutputObservation
open C ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs
open Zlib.Uncompr.Proof.Wrapper Zlib.Uncompr.Proof.WrapperRanges Zlib.Uncompr.Proof.Objects
open Zlib.Uncompr.Proof.Loop Zlib.Uncompr.Proof.PostRanges Zlib.Uncompr.Proof.Buffers
open Zlib.Uncompr.Proof.Finish Zlib.Uncompr.Proof.CallerObjects Zlib.Uncompr.Proof.Cells

private theorem separate_symm (p q : BPtr) (n m : Nat) (separate : Separate p n q m) :
    Separate q m p n := by
  cases p <;> cases q <;> simp_all [Separate, ne_comm, or_comm, or_left_comm, or_assoc]

private theorem writable_store_expected (h : Heap) (p : BPtr) (capacity : Nat) (out : List UInt8)
    (writable : Writable h p capacity) (bound : out.length ≤ capacity) :
    ∃ expected, Store h p out expected := by
  rcases writable with null | ⟨ref, off, array, ptr, get, write, room⟩
  · have empty : out = [] := List.length_eq_zero_iff.mp (by omega)
    exact ⟨h, Or.inl ⟨empty, rfl⟩⟩
  · refine ⟨Space.put h ref (array.extract 0 off ++ out.toArray ++ array.extract (off + out.length) array.size),
      Or.inr ⟨ref, off, array, ptr, get, write, by omega, rfl⟩⟩

theorem uncompress2_z_nonnull_output (h after : Heap) (source dest sourceLen destLen : BPtr)
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
    (destNonnull : dest ≠ .null)
    (run : C.run (uncompress2_z dest destLen source sourceLen) h = .ok (rc, after)) :
    ∃ output used expected,
      Store h dest output expected ∧ Bytes after dest output.length output ∧
      LengthCell after sourceLen (UInt64.ofNat used) ∧ LengthCell after destLen (UInt64.ofNat output.length) ∧
      used ≤ n.toNat ∧ output.length ≤ capacity.toNat := by
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
  have originalOut : (coreStream h source dest capacity).next_out = dest := by
    simp [coreStream, outputStream, normalizedDest, destNonnull]
  obtain ⟨made, output, _expectedCore, madeCount, _cursor, length, observed, outputRange,
    _frame, _storeCore, _expectedFrame, _array, _objects⟩ :=
    Zlib.Uncompr.Proof.OutputPrefix.loop_output_store (coreHeap h source dest capacity) coreAfter
      h.nextBlk (h.nextBlk + 2) (coreStream h source dest capacity) stream (initializedState h) state
      { err := Z_OK, len := n, left := capacity } last initial initialAllocator initialRanges
      (normalizedDest_nonnull h dest capacity validOutput) coreRun current.good
  rw [originalOut] at observed outputRange
  change remainingOutput stream last + made = capacity.toNat at madeCount
  have madeBound : made ≤ capacity.toNat := by omega
  have inputBound : used ≤ n.toNat := by omega
  have sameMade : produced = made := by omega
  have outputSource : Separate dest made sourceLen 8 := separate_prefix dest sourceLen capacity.toNat 8 made 8
    (separate_symm _ _ _ _ sourceSeparate) madeBound (Nat.le_refl _)
  have outputDest : Separate dest made destLen 8 := separate_prefix dest destLen capacity.toNat 8 made 8
    (separate_symm _ _ _ _ destSeparate) madeBound (Nat.le_refl _)
  obtain ⟨oldOutput, oldReadable⟩ := writable_bytes h dest capacity.toNat writable
  have outside := old_not_newblock h fresh (h.nextBlk + 1) (by omega) dest capacity.toNat oldOutput oldReadable
  obtain ⟨_mid, _written, clean, finishRun, _storeIn, _storeOut, _writtenJ, cellIn, cellOut,
    _storeLive, _endLive, _unique, _fresh, _streamGet, _reservedGet, finalOutput, _outputWrite⟩ :=
    finish_safe_object coreAfter h.nextBlk (h.nextBlk + 2) (h.nextBlk + 1) stream state
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
  have fullRun : C.run (uncompress2_z dest destLen source sourceLen) h =
      .ok (resultCode last.err (last.len + stream.avail_in.toUInt64), releasedHeap clean h.nextBlk (h.nextBlk + 1)) := by
    rw [uncompress2_z_to_core h source dest sourceLen destLen n capacity fresh uniq globals platform
      allocation inputCell outputCell validInput validOutput]
    simp only [C.run] at coreRun finishRun
    simpa only [bind_app, coreRun] using finishRun
  have heaps : releasedHeap clean h.nextBlk (h.nextBlk + 1) = after :=
    congrArg Prod.snd (Except.ok.inj (fullRun.symm.trans run))
  obtain ⟨expected, stored⟩ := writable_store_expected h dest capacity.toNat output writable (by omega)
  rw [← heaps]
  refine ⟨output, used, expected, stored, ?_, ?_, ?_, inputBound, by omega⟩
  · simpa only [length] using finalOutput
  · simpa only [usedValue] using inputFinal
  · simpa only [madeValue, length] using outputFinal

theorem uncompress2_z_output (h after : Heap) (source dest sourceLen destLen : BPtr)
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
    ∃ output used expected,
      Store h dest output expected ∧ Bytes after dest output.length output ∧
      LengthCell after sourceLen (UInt64.ofNat used) ∧ LengthCell after destLen (UInt64.ofNat output.length) ∧
      used ≤ n.toNat ∧ output.length ≤ capacity.toNat := by
  by_cases null : dest = .null
  · obtain ⟨rc', final, used, made, actual, input, output, usedBound, madeBound, _live, _code⟩ :=
      Zlib.Uncompr.Proof.WrapperSafe.uncompress2_z_safe h source dest sourceLen destLen n capacity xs
        fresh uniq globals platform allocation inputCell outputCell readable writable separate
        sourceSeparate destSeparate cellSeparate validInput validOutput
    have zero : made = 0 := by
      have bound : made ≤ 0 := by simpa [validOutput null] using madeBound
      omega
    subst made
    have heaps : final = after := congrArg Prod.snd (Except.ok.inj (actual.symm.trans run))
    rw [← heaps]
    exact ⟨[], used, h, Or.inl ⟨rfl, rfl⟩, Or.inl ⟨null, rfl, rfl⟩, input, output, usedBound, Nat.zero_le _⟩
  · exact uncompress2_z_nonnull_output h after source dest sourceLen destLen n capacity xs rc
      fresh uniq globals platform allocation inputCell outputCell readable writable separate
      sourceSeparate destSeparate cellSeparate validInput validOutput null run

private theorem empty_bytes_of_writable (h : Heap) (p : BPtr) (capacity : Nat)
    (writable : Writable h p capacity) : Bytes h p 0 [] := by
  rcases writable with null | ⟨ref, off, array, ptr, get, _write, room⟩
  · exact Or.inl ⟨null.1, rfl, rfl⟩
  · exact Or.inr ⟨ref, off, array, ptr, get, by omega, by simp⟩

theorem uncompress2_z_output_allocation (h after : Heap) (source dest sourceLen destLen : BPtr)
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
    ∃ output used got consumed expected,
      Store h dest output expected ∧ Bytes after dest output.length output ∧
      LengthCell after sourceLen consumed ∧ LengthCell after destLen got ∧
      used ≤ n.toNat ∧ output.length ≤ capacity.toNat ∧
      ((got.toNat = output.length ∧ consumed.toNat = used) ∨
        (rc = Z_MEM_ERROR ∧ output = [] ∧ got = capacity ∧ consumed = n)) := by
  by_cases allocation : h.allocOk h.nalloc = true
  · obtain ⟨output, used, expected, store, observed, input, produced, usedBound, madeBound⟩ :=
      uncompress2_z_output h after source dest sourceLen destLen n capacity xs rc fresh uniq globals platform allocation
        inputCell outputCell readable writable separate sourceSeparate destSeparate cellSeparate validInput validOutput run
    refine ⟨output, used, UInt64.ofNat output.length, UInt64.ofNat used, expected,
      store, observed, input, produced, usedBound, madeBound, Or.inl ⟨?_, ?_⟩⟩
    · rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by have := capacity.toNat_lt; omega)]
    · rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by have := n.toNat_lt; omega)]

  · have actual := Zlib.Uncompr.Proof.InitialRefusal.uncompress2_z_initial_refusal h source dest sourceLen destLen
      n capacity fresh allocation inputCell outputCell validInput validOutput
    have equal := Except.ok.inj (actual.symm.trans run)
    have heaps : Zlib.Uncompr.Proof.InitialRefusal.refusedHeap h = after := congrArg Prod.snd equal
    have result : rc = Z_MEM_ERROR := (congrArg Prod.fst equal).symm
    obtain ⟨old, oldReadable⟩ := writable_bytes h dest capacity.toNat writable
    have retained := refused_object h fresh dest capacity.toNat old true oldReadable (fun _ => writable)
    rw [← heaps]
    exact ⟨[], 0, capacity, n, h, Or.inl ⟨rfl, rfl⟩,
      empty_bytes_of_writable _ dest capacity.toNat (retained.2 rfl),
      Zlib.Uncompr.Proof.InitialRefusal.refused_cell h fresh sourceLen n inputCell,
      Zlib.Uncompr.Proof.InitialRefusal.refused_cell h fresh destLen capacity outputCell,
      Nat.zero_le _, Nat.zero_le _, Or.inr ⟨result, rfl, rfl, rfl⟩⟩

#print axioms uncompress2_z_output_allocation

#print axioms uncompress2_z_output

#print axioms uncompress2_z_nonnull_output
end Zlib.Uncompr.Proof.OutputObservation
