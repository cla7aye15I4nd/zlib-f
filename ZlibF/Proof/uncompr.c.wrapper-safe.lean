import ZlibF.Proof.«uncompr.c.finish»

/-!
# Actual initialized uncompress wrapper safety and accounting

Real initialization establishes the same representation used by every actual
core iteration, both scalar stores, End and both automatic frees. The final run
has exact returned scalar counts and no allocation loss or residue. The internal
domain explicitly adds Uniq, ByteObjectsFit and successful initial allocation.
It does not replace the unchanged public goal; independent format evidence and
valid-input completion remain open.
-/

namespace Zlib.Uncompr.Proof.WrapperSafe
open C Zlib.Gzguts ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs
open Zlib.Uncompr.Proof.Wrapper Zlib.Uncompr.Proof.WrapperRanges
open Zlib.Uncompr.Proof.Loop Zlib.Uncompr.Proof.PostRanges Zlib.Uncompr.Proof.Objects
open Zlib.Uncompr.Proof.Finish Zlib.Uncompr.Proof.Cells

private theorem core_live (h : Heap) (source dest : BPtr) (capacity : UInt64) (x : Nat) :
    (coreHeap h source dest capacity).live x ↔
      h.live x ∨ x = h.nextBlk ∨ x = h.nextBlk + 1 ∨ x = h.nextBlk + 2 := by
  by_cases a : x = h.nextBlk
  · subst x; simp [Heap.live, coreHeap_eq]
  · by_cases b : x = h.nextBlk + 1
    · subst x; simp [Heap.live, coreHeap_eq]
    · by_cases c : x = h.nextBlk + 2
      · subst x; simp [Heap.live, coreHeap_eq]
      · simp [Heap.live, coreHeap_eq, a, b, c]

private theorem old_not_reserved (h : Heap) (fresh : Fresh h) (p : BPtr) (n : Nat) (xs : List UInt8)
    (bytes : Bytes h p n xs) : ∀ off, p ≠ .ref (.blk (h.nextBlk + 1)) off := by
  intro off ptr
  rw [ptr] at bytes
  rcases bytes with null | ⟨ref, off', a, equal, get, _⟩
  · cases null.1
  · cases equal
    have live : h.live (h.nextBlk + 1) := Or.inl (by simp [show h.bytes (h.nextBlk + 1) = some a from get])
    exact fresh (h.nextBlk + 1) (by omega) live

/-- The real valid-entry wrapper with successful initial state allocation is safe
through every actual iteration, exact scalar writeback, End and local cleanup.
Later allocation failures and partial output are included. This internal domain
explicitly requires Uniq and ByteObjectsFit; it does not replace the broader
public utility goal or assert independent compressed-format correctness. -/
theorem uncompress2_z_safe (h : Heap) (source dest sourceLen destLen : BPtr)
    (n capacity : UInt64) (xs : List UInt8)
    (fresh : Fresh h) (uniq : Uniq h) (globals : LibraryGlobals h)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit h) (allocation : h.allocOk h.nalloc = true)
    (inputCell : LengthCell h sourceLen n) (outputCell : LengthCell h destLen capacity)
    (readable : Bytes h source n.toNat xs) (writable : Writable h dest capacity.toNat)
    (separate : Separate source n.toNat dest capacity.toNat)
    (sourceSeparate : Separate sourceLen 8 dest capacity.toNat)
    (destSeparate : Separate destLen 8 dest capacity.toNat)
    (cellSeparate : Separate sourceLen 8 destLen 8)
    (validInput : source = .null → n = 0) (validOutput : dest = .null → capacity = 0) :
    ∃ rc after used made,
      C.run (uncompress2_z dest destLen source sourceLen) h = .ok (rc, after) ∧
      LengthCell after sourceLen (UInt64.ofNat used) ∧
      LengthCell after destLen (UInt64.ofNat made) ∧
      used ≤ n.toNat ∧ made ≤ capacity.toNat ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧
      ∃ err remainIn, err ≠ Z_OK ∧ PublicInflateCode err ∧ rc = resultCode err remainIn ∧
        used + remainIn.toNat = n.toNat := by
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
    storeLedger, endLedger, cleanUnique, cleanFresh, cleanStream, localGet⟩ :=
    finish_safe coreAfter h.nextBlk (h.nextBlk + 2) (h.nextBlk + 1) stream state
      sourceLen destLen n capacity last (junkBytes h).toList current allocator inputCell1 outputCell1
      inputRange outputRange cellSeparate reservedBytes reservedRange reservedSource reservedDest
  let final := releasedHeap clean h.nextBlk (h.nextBlk + 1)
  have inputFinal := released_cell clean h.nextBlk (h.nextBlk + 1) sourceLen _ inputCell2
    (old_not_reserved h fresh sourceLen 8 (lengthBytes n) inputCell.1)
  have outputFinal := released_cell clean h.nextBlk (h.nextBlk + 1) destLen _ outputCell2
    (old_not_reserved h fresh destLen 8 (lengthBytes capacity) outputCell.1)
  obtain ⟨a, reservedGet, _reservedWrite⟩ := localGet
  have freeLedger := released_live clean h.nextBlk (h.nextBlk + 1) _ a cleanUnique cleanStream reservedGet
  have fullRun : C.run (uncompress2_z dest destLen source sourceLen) h =
      .ok (resultCode last.err (last.len + stream.avail_in.toUInt64), final) := by
    rw [uncompress2_z_to_core h source dest sourceLen destLen n capacity fresh uniq globals platform
      allocation inputCell outputCell validInput validOutput]
    simp only [C.run] at coreRun finishRun
    simpa only [bind_app, coreRun] using finishRun
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
    unfold remainingOutput at countOut
    omega
  have oldOwner (x : Nat) : InflateOwned (h.nextBlk + 2) (initializedState h) x ↔ x = h.nextBlk + 2 := by
    simp [InflateOwned, initial_window_null]
  have finalLedger : LiveChange h final (fun _ => False) (fun _ => False) := by
    intro x
    have finalEq := freeLedger x
    have endEq := endLedger x
    have storesEq : written.live x ↔ coreAfter.live x := by
      simpa only [not_false_eq_true, and_true, or_false] using storeLedger x
    have loopEq := coreLedger x
    have startEq := core_live h source dest capacity x
    constructor
    · intro live
      obtain ⟨cleanLive, notLocal⟩ := (finalEq.mp live).resolve_right (by simp)
      obtain ⟨writtenLive, notOwner⟩ := (endEq.mp cleanLive).resolve_right (by simp)
      have coreLive := storesEq.mp writtenLive
      rcases loopEq.mp coreLive with ⟨initialLive, _⟩ | ⟨owner, _⟩
      · have initialNotOwner : ¬ InflateOwned (h.nextBlk + 2) (initializedState h) x :=
          fun owner => notOwner ((owners x initialLive).mpr owner)
        rcases startEq.mp initialLive with old | atStream | atReserved | atState
        · exact Or.inl ⟨old, by simp⟩
        · exact False.elim (notLocal (Or.inl atStream))
        · exact False.elim (notLocal (Or.inr atReserved))
        · exact False.elim (initialNotOwner ((oldOwner x).mpr atState))
      · exact False.elim (notOwner owner)
    · rintro (⟨old, _⟩ | impossible)
      · have below := fresh.lt old
        have initialLive := startEq.mpr (Or.inl old)
        have coreLive := loopEq.mpr (Or.inl ⟨initialLive, by simp⟩)
        have notOwner : ¬ InflateOwned (h.nextBlk + 2) state x := by
          intro owner
          have eq := (oldOwner x).mp ((owners x initialLive).mp owner)
          omega
        have cleanLive := endEq.mpr (Or.inl ⟨storesEq.mpr coreLive, notOwner⟩)
        exact finalEq.mpr (Or.inl ⟨cleanLive, by omega⟩)
      · exact False.elim impossible
  refine ⟨_, final, used, made, fullRun, ?_, ?_, by omega, by omega, finalLedger,
    last.err, last.len + stream.avail_in.toUInt64, stopped, code, rfl, ?_⟩
  · simpa only [usedValue] using inputFinal
  · simpa only [madeValue] using outputFinal
  · rw [countedIn.1]
    unfold remainingInput at countIn
    omega

#print axioms uncompress2_z_safe
end Zlib.Uncompr.Proof.WrapperSafe
