import ZlibF.Proof.«uncompr.c.local-core-stores»
import ZlibF.Proof.«uncompr.c.local-tail-stores»

namespace Zlib.Uncompr.Proof.LocalWrapperStores
open C Zlib.Gzguts ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inflate.Local
open Zlib.Uncompr.Proof.Wrapper Zlib.Uncompr.Proof.WrapperRanges
open Zlib.Uncompr.Proof.Loop Zlib.Uncompr.Proof.PostRanges Zlib.Uncompr.Proof.Cells
open Zlib.Uncompr.Proof.Finish
set_option autoImplicit false

private theorem bytes_root_live (h : Heap) (p : BPtr) (count : Nat) (xs : List UInt8)
    (bytes : Bytes h p count xs) (b : Nat) (root : ByteRoot p b) : h.live b := by
  rcases bytes with null | ⟨ref, off, array, ptr, get, _⟩
  · rw [null.1] at root; cases root
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

/-- Successful real initialization, every actual core call, ordered scalar
writeback and actual End/local releases yield three exact expected Stores.
This is the successful-init branch; it claims Frame, not structural SameObjects
or independent decoder format correctness. Nullable zero output is included. -/
theorem uncompress2_z_stores_of_run (h : Heap) (source dest sourceLen destLen : BPtr)
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
    ∃ output consumed produced first second expected,
      Store h dest output first ∧ Store first sourceLen (lengthBytes consumed) second ∧
      Store second destLen (lengthBytes produced) expected ∧
      Frame expected after (fun _ => False) ∧
      output.length = produced.toNat ∧ consumed.toNat ≤ n.toNat ∧ produced.toNat ≤ capacity.toNat := by
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
    LocalTailStores.finish_stored coreAfter h.nextBlk h.nextBlk (h.nextBlk + 2) (h.nextBlk + 1) stream state
      sourceLen destLen n capacity last (junkBytes h).toList current allocator inputCell1 outputCell1
      inputRange outputRange cellSeparate reservedBytes reservedRange reservedSource reservedDest
  have complete : C.run (uncompress2_z dest destLen source sourceLen) h =
      .ok (resultCode last.err (last.len + stream.avail_in.toUInt64), releasedHeap clean h.nextBlk (h.nextBlk + 1)) := by
    rw [FreshCoreEntry.uncompress2_z_to_core h source dest sourceLen destLen n capacity fresh
      allocation inputCell outputCell validInput validOutput]
    simp only [C.run] at coreRun finishRun
    simpa only [bind_app, coreRun] using finishRun
  cases Except.ok.inj (complete.symm.trans actual)
  obtain ⟨output, first, outCount, outputStore, shape, outputFrame⟩ :=
    LocalCoreStores.core_output_store h coreAfter source dest n capacity xs last stream state
      fresh globals platform allocation readable writable separate validOutput coreRun current
  have outsideInitial (x : Nat) (alive : first.live x) :
      ¬ (StreamRoot (.tab h.nextBlk) x ∨ InflateOwned (h.nextBlk + 2) (initializedState h) x) := by
    have original := (shape.live x).mp alive
    have below := fresh.lt original
    rintro (root | owner)
    · change x = h.nextBlk at root
      omega
    · rcases owner with stateRoot | window
      · omega
      · rw [initial_window_null] at window
        cases window
  have sourceOutside (x : Nat) (root : ByteRoot sourceLen x) : first.live x ∧
      ¬ (StreamRoot (.tab h.nextBlk) x ∨ InflateOwned (h.nextBlk + 2) (initializedState h) x) := by
    have live := (shape.live x).mpr (bytes_root_live h sourceLen 8 (lengthBytes n) inputCell.1 x root)
    exact ⟨live,outsideInitial x live⟩
  obtain ⟨second, sourceStore, sourceFrame⟩ := FrameMirror.store_mirror outputFrame sourceOutside storeIn
  have shape2 := shape.trans sourceStore.shape
  have destOutside (x : Nat) (root : ByteRoot destLen x) : second.live x ∧
      ¬ (StreamRoot (.tab h.nextBlk) x ∨ InflateOwned (h.nextBlk + 2) (initializedState h) x) := by
    have live := (shape2.live x).mpr (bytes_root_live h destLen 8 (lengthBytes capacity) outputCell.1 x root)
    exact ⟨live, outsideInitial x ((sourceStore.shape.live x).mp live)⟩
  obtain ⟨expected, destStore, destFrame⟩ := FrameMirror.store_mirror sourceFrame destOutside storeOut
  have shape3 := shape2.trans destStore.shape
  have old (x : Nat) (live : expected.live x) : h.live x := (shape3.live x).mp live
  have notOwned := FinalFrame.owner_outside_old h source dest capacity state fresh owners
  have finalFrame : Frame expected (releasedHeap clean h.nextBlk (h.nextBlk + 1)) (fun _ => False) := by
    apply CallerFrame.frame_trans_restrict destFrame tailFrame
    intro x live _
    have below := fresh.lt (old x live)
    refine ⟨outsideInitial x ((sourceStore.shape.live x).mp ((destStore.shape.live x).mp live)), ?_⟩
    rintro ((root | owner) | atStream | atReserved)
    · change x = h.nextBlk at root
      omega
    · exact notOwned x (old x live) owner
    · omega
    · omega
  have countedIn := final_count_exact n last.len stream.avail_in (by unfold remainingInput at countIn; omega)
  have countedOut := final_count_exact capacity last.left stream.avail_out (by unfold remainingOutput at countOut; omega)
  refine ⟨output, n - (last.len + stream.avail_in.toUInt64),
    capacity - (last.left + stream.avail_out.toUInt64), first, second, expected,
    outputStore, sourceStore, destStore, finalFrame, ?_, ?_, ?_⟩
  · rw [countedOut.2]
    unfold remainingOutput at outCount
    omega
  · rw [countedIn.2]
    omega
  · rw [countedOut.2]
    omega

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


/-- Both real initialization outcomes. First failure keeps the original
scalar values and is represented by identity Stores; every later return
has an exact output Store followed by the two actual scalar values. This
is Frame on all original objects, not structural table equality. -/
theorem uncompress2_z_stores_allocation (h : Heap) (source dest sourceLen destLen : BPtr)
    (n capacity : UInt64) (xs : List UInt8)
    (fresh : Fresh h) (globals : LibraryGlobals h)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit h)
    (inputCell : LengthCell h sourceLen n) (outputCell : LengthCell h destLen capacity)
    (readable : Bytes h source n.toNat xs) (writable : Writable h dest capacity.toNat)
    (separate : Separate source n.toNat dest capacity.toNat)
    (sourceSeparate : Separate sourceLen 8 dest capacity.toNat)
    (destSeparate : Separate destLen 8 dest capacity.toNat)
    (cellSeparate : Separate sourceLen 8 destLen 8)
    (validInput : source = .null → n = 0) (validOutput : dest = .null → capacity = 0)
    (rc : Int32) (after : Heap)
    (actual : C.run (uncompress2_z dest destLen source sourceLen) h = .ok (rc, after)) :
    ∃ output consumed produced first second expected,
      Store h dest output first ∧ Store first sourceLen (lengthBytes consumed) second ∧
      Store second destLen (lengthBytes produced) expected ∧
      Frame expected after (fun _ => False) ∧
      ((output.length = produced.toNat ∧ consumed.toNat ≤ n.toNat ∧ produced.toNat ≤ capacity.toNat) ∨
        (rc = Z_MEM_ERROR ∧ output = [] ∧ consumed = n ∧ produced = capacity)) := by
  by_cases allocation : h.allocOk h.nalloc = true
  · obtain ⟨output,consumed,produced,first,second,expected,storeOutput,storeSource,storeDest,
      frame,length,inputBound,outputBound⟩ := uncompress2_z_stores_of_run h source dest sourceLen destLen
      n capacity xs fresh globals platform allocation inputCell outputCell readable writable separate
      sourceSeparate destSeparate cellSeparate validInput validOutput rc after actual
    exact ⟨output,consumed,produced,first,second,expected,storeOutput,storeSource,storeDest,
      frame,Or.inl ⟨length,inputBound,outputBound⟩⟩
  · have refusal := InitialRefusal.uncompress2_z_initial_refusal h source dest sourceLen destLen
      n capacity fresh allocation inputCell outputCell validInput validOutput
    have same := Except.ok.inj (refusal.symm.trans actual)
    have code : rc = Z_MEM_ERROR := (congrArg Prod.fst same).symm
    have heap : InitialRefusal.refusedHeap h = after := congrArg Prod.snd same
    refine ⟨[],n,capacity,h,h,h,Or.inl ⟨rfl,rfl⟩,
      length_cell_store_self h sourceLen n inputCell,
      length_cell_store_self h destLen capacity outputCell,?_,Or.inr ⟨code,rfl,rfl,rfl⟩⟩
    rw [←heap]
    exact InitialRefusal.refused_frame h fresh

#print axioms uncompress2_z_stores_of_run
#print axioms uncompress2_z_stores_allocation
end Zlib.Uncompr.Proof.LocalWrapperStores
