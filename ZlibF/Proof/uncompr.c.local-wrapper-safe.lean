import ZlibF.Proof.«uncompr.c.local-core-safe»
import ZlibF.Proof.«uncompr.c.local-initialized-objects»
import ZlibF.Proof.«uncompr.c.local-release»

/-! Same actual whole wrapper: real initialization, all core calls, ordered
length stores, inflateEnd and both automatic frees. The explicit scalar/range
separation and per-object platform premises are retained; old caller Uniq is
absent. Independent format and valid-stream END completion remain separate. -/
namespace Zlib.Uncompr.Proof.LocalWrapperSafe
open C Zlib.Gzguts ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inflate.Local
open Zlib.Uncompr.Proof.Wrapper Zlib.Uncompr.Proof.WrapperRanges
open Zlib.Uncompr.Proof.Loop Zlib.Uncompr.Proof.PostRanges Zlib.Uncompr.Proof.Cells
open Zlib.Uncompr.Proof.Finish
set_option autoImplicit false

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

theorem uncompress2_z_safe (h : Heap) (source dest sourceLen destLen : BPtr)
    (n capacity : UInt64) (xs : List UInt8)
    (fresh : Fresh h) (globals : LibraryGlobals h)
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
  obtain ⟨mid, written, clean, finishRun, storeIn, storeOut, inputFinal, outputFinal, tailLedger⟩ :=
    LocalRelease.finish_full coreAfter h.nextBlk (h.nextBlk + 2) stream state
      sourceLen destLen n capacity last (junkBytes h).toList current allocator inputCell1 outputCell1
      inputRange outputRange cellSeparate reservedBytes reservedRange reservedSource reservedDest
      (LocalRelease.length_cell_old_roots fresh inputCell) (LocalRelease.length_cell_old_roots fresh outputCell)
  let final := releasedHeap clean h.nextBlk (h.nextBlk + 1)
  have fullRun : C.run (uncompress2_z dest destLen source sourceLen) h =
      .ok (resultCode last.err (last.len + stream.avail_in.toUInt64), final) := by
    rw [FreshCoreEntry.uncompress2_z_to_core h source dest sourceLen destLen n capacity fresh
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
    have tailEq : final.live x ↔ coreAfter.live x ∧
        ¬ (InflateOwned (h.nextBlk + 2) state x ∨ x = h.nextBlk ∨ x = h.nextBlk + 1) := by
      simpa only [LiveChange, not_false_eq_true, and_true, or_false, final] using tailLedger x
    have startEq := core_live h source dest capacity x
    constructor
    · intro live
      obtain ⟨coreLive, notRemoved⟩ := tailEq.mp live
      rcases (coreLedger x).mp coreLive with ⟨initialLive, _⟩ | ⟨owner, _⟩
      · rcases startEq.mp initialLive with old | atStream | atReserved | atState
        · exact Or.inl ⟨old, by simp⟩
        · exact False.elim (notRemoved (Or.inr (Or.inl atStream)))
        · exact False.elim (notRemoved (Or.inr (Or.inr atReserved)))
        · have initialLive := startEq.mpr (Or.inr (Or.inr (Or.inr atState)))
          have owner := (owners x initialLive).mpr ((oldOwner x).mpr atState)
          exact False.elim (notRemoved (Or.inl owner))
      · exact False.elim (notRemoved (Or.inl owner))
    · rintro (⟨old, _⟩ | impossible)
      · have below := fresh.lt old
        have initialLive := startEq.mpr (Or.inl old)
        have coreLive := (coreLedger x).mpr (Or.inl ⟨initialLive, by simp⟩)
        apply tailEq.mpr
        refine ⟨coreLive, ?_⟩
        rintro (owner | atStream | atReserved)
        · have eq := (oldOwner x).mp ((owners x initialLive).mp owner)
          omega
        · omega
        · omega
      · exact False.elim impossible
  refine ⟨_, final, used, made, fullRun, ?_, ?_, by omega, by omega, finalLedger,
    last.err, last.len + stream.avail_in.toUInt64, stopped, code, rfl, ?_⟩
  · simpa only [usedValue] using inputFinal
  · simpa only [madeValue] using outputFinal
  · rw [countedIn.1]
    unfold remainingInput at countIn
    omega

#print axioms uncompress2_z_safe
end Zlib.Uncompr.Proof.LocalWrapperSafe
