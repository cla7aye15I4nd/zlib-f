import ZlibF.Proof.«uncompr.c.single-frame»
import ZlibF.Proof.«uncompr.c.compat-tail»
import ZlibF.Proof.«uncompr.c.caller-objects»
import ZlibF.Proof.«uncompr.c.legacy-prefix-frame»

/-!
# Actual traditional counted-wrapper stores and complete caller frame

The same real prepared heap feeds the counted callee. Its exact output Store is
mirrored; its two fresh local scalar Stores are private to this wrapper. Actual
external scalar writebacks are then mirrored in source order. The two real frees
finish a complete original-caller Frame and live ledger. Exact output intervals,
shared caller byte objects, every allocation outcome and count fallback remain
visible. SameObjects and independent format/END remain separate targets.
-/

set_option autoImplicit false

namespace Zlib.Uncompr.Proof.LegacyFrame
open C Zlib.Gzguts ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs
open Zlib.Uncompr.Proof.SingleLength Zlib.Uncompr.Proof.OuterFrame Zlib.Uncompr.Proof.ScalarWriteback
open Zlib.Uncompr.Proof.CallerObjects Zlib.Uncompr.Proof.Writeback
open Zlib.Uncompr.Proof.CompatPrefix
open Zlib.Uncompr.Proof.Buffers
open Zlib.Uncompr.Proof.Cells Zlib.Uncompr.Proof.CompatibilityTail Zlib.Uncompr.Proof.CallerFrame

private theorem separate_symm (p q : BPtr) (n m : Nat) (separate : Separate p n q m) :
    Separate q m p n := by
  cases p <;> cases q <;> simp_all [Separate, ne_comm, or_comm, or_left_comm, or_assoc]

private theorem outside_separate (p : BPtr) (count block : Nat)
    (outside : ∀ off, p ≠ .ref (.blk block) off) :
    Separate p count (.ref (.blk block) 0) 8 := by
  cases p with
  | null => simp [Separate]
  | ref ref off =>
    have different : ref ≠ .blk block := by intro same; subst ref; exact outside off rfl
    exact Or.inr (Or.inr (Or.inl different))


private theorem finish_framed (h : Heap) (gotBlock usedBlock : Nat) (destLen sourceLen : BPtr)
    (sourceOld destOld gotValue usedValue : UInt64) (rc : Int32)
    (uniq : Uniq h) (fresh : Fresh h) (platform : ZlibF.PlatformMemory.ByteObjectsFit h)
    (sourceCell : LengthCell h sourceLen sourceOld) (destCell : LengthCell h destLen destOld)
    (gotCell : LengthCell h (.ref (.blk gotBlock) 0) gotValue)
    (usedCell : LengthCell h (.ref (.blk usedBlock) 0) usedValue)
    (distinct : gotBlock ≠ usedBlock) (separate : Separate sourceLen 8 destLen 8)
    (sourceGot : ∀ off, sourceLen ≠ .ref (.blk gotBlock) off)
    (sourceUsed : ∀ off, sourceLen ≠ .ref (.blk usedBlock) off)
    (destGot : ∀ off, destLen ≠ .ref (.blk gotBlock) off)
    (destUsed : ∀ off, destLen ≠ .ref (.blk usedBlock) off) :
    ∃ first second after,
      C.run (Zlib.Uncompr.Proof.CompatibilityTail.finish destLen sourceLen (.ref (.blk gotBlock) 0) (.ref (.blk usedBlock) 0) rc) h = .ok (rc, after) ∧
      Store h sourceLen (lengthBytes usedValue) first ∧ Store first destLen (lengthBytes gotValue) second ∧
      LengthCell after sourceLen usedValue ∧ LengthCell after destLen gotValue ∧
      LiveChange h after (fun _ => False) (fun x => x = gotBlock ∨ x = usedBlock) ∧
      Uniq after ∧ Fresh after ∧ ZlibF.PlatformMemory.ByteObjectsFit after ∧
      Frame second after (fun x => x = gotBlock ∨ x = usedBlock) := by
  have srcGot := outside_separate sourceLen 8 gotBlock sourceGot
  have srcUsed := outside_separate sourceLen 8 usedBlock sourceUsed
  have dstGot := outside_separate destLen 8 gotBlock destGot
  have dstUsed := outside_separate destLen 8 usedBlock destUsed
  obtain ⟨first, sourceRun, sourceStore, writtenSource, sourceLive, unique1, fresh1, fit1, keep1⟩ :=
    writable_scalar_store h sourceLen usedValue sourceCell.2 uniq fresh platform
  have got1 := keep1 (.ref (.blk gotBlock) 0) gotValue gotCell (separate_symm _ _ _ _ srcGot)
  have used1 := keep1 (.ref (.blk usedBlock) 0) usedValue usedCell (separate_symm _ _ _ _ srcUsed)
  have dest1 := keep1 destLen destOld destCell (separate_symm _ _ _ _ separate)
  obtain ⟨second, destRun, destStore, writtenDest, destLive, unique2, fresh2, fit2, keep2⟩ :=
    writable_scalar_store first destLen gotValue dest1.2 unique1 fresh1 fit1
  have source2 := keep2 sourceLen usedValue writtenSource separate
  have got2 := keep2 (.ref (.blk gotBlock) 0) gotValue got1 (separate_symm _ _ _ _ dstGot)
  have used2 := keep2 (.ref (.blk usedBlock) 0) usedValue used1 (separate_symm _ _ _ _ dstUsed)
  obtain ⟨freeGot, gotLive⟩ := free_scalar second gotBlock gotValue unique2 got2
  have unique3 := freed_uniq second gotBlock unique2
  have fresh3 := freed_fresh second gotBlock fresh2
  have fit3 := Zlib.Uncompr.Proof.WrapperShape.removed_bytes_platform second gotBlock fit2
  have used3 := freed_cell second gotBlock (.ref (.blk usedBlock) 0) usedValue used2 (by
    intro off same
    have blocks : usedBlock = gotBlock := BRef.blk.inj (Ptr.ref.inj same).1
    exact distinct blocks.symm)
  obtain ⟨freeUsed, usedLive⟩ := free_scalar (freedHeap second gotBlock) usedBlock usedValue unique3 used3
  let final := freedHeap (freedHeap second gotBlock) usedBlock
  have sourceFinal := freed_cell (freedHeap second gotBlock) usedBlock sourceLen usedValue
    (freed_cell second gotBlock sourceLen usedValue source2 sourceGot) sourceUsed
  have destFinal := freed_cell (freedHeap second gotBlock) usedBlock destLen gotValue
    (freed_cell second gotBlock destLen gotValue writtenDest destGot) destUsed
  have cleanupFrame : Frame second final (fun x => x = gotBlock ∨ x = usedBlock) := by
    apply frame_trans_restrict (local_free_frame second gotBlock) (local_free_frame (freedHeap second gotBlock) usedBlock)
    intro b _ outside
    exact ⟨fun eq => outside (Or.inl eq), fun eq => outside (Or.inr eq)⟩
  refine ⟨first, second, final, ?_, sourceStore, destStore, sourceFinal, destFinal, ?_,
    freed_uniq _ usedBlock unique3, freed_fresh _ usedBlock fresh3,
    Zlib.Uncompr.Proof.WrapperShape.removed_bytes_platform _ usedBlock fit3, cleanupFrame⟩
  · have readUsed := load64_lengthCell h (.ref (.blk usedBlock) 0) usedValue usedCell
    have readGot := load64_lengthCell first (.ref (.blk gotBlock) 0) gotValue got1
    simp only [C.run] at sourceRun destRun readUsed readGot
    simp [C.run, Zlib.Uncompr.Proof.CompatibilityTail.finish, readUsed, sourceRun, readGot, destRun, freeGot, freeUsed, final]
  · intro x
    have firstEq : first.live x ↔ h.live x := by
      simpa only [not_false_eq_true, and_true, or_false] using sourceLive x
    have secondEq : second.live x ↔ first.live x := by
      simpa only [not_false_eq_true, and_true, or_false] using destLive x
    have gotEq : (freedHeap second gotBlock).live x ↔ second.live x ∧ x ≠ gotBlock := by
      simpa only [or_false] using gotLive x
    have usedEq : final.live x ↔ (freedHeap second gotBlock).live x ∧ x ≠ usedBlock := by
      simpa only [or_false] using usedLive x
    change final.live x ↔ (h.live x ∧ ¬ (x = gotBlock ∨ x = usedBlock)) ∨ False
    rw [usedEq, gotEq, secondEq, firstEq]
    simp [not_or, and_assoc]

private theorem bytes_forward_frame {before after : Heap} {changed : Nat → Prop} {p : BPtr}
    {count : Nat} {xs : List UInt8} (frame : Frame before after changed)
    (outside : ∀ b, ByteRoot p b → before.live b ∧ ¬ changed b)
    (bytes : Bytes before p count xs) : Bytes after p count xs := by
  rcases bytes with null | ⟨ref, off, array, pointer, get, room, values⟩
  · exact Or.inl null
  · subst p
    have equal := frame.byte_view_eq outside
    exact Or.inr ⟨ref, off, array, rfl, equal.1.trans get, room, values⟩

private theorem local_separate_old (h : Heap) (fresh : Fresh h) (block : Nat) (new : h.nextBlk ≤ block)
    (p : BPtr) (count : Nat) (xs : List UInt8) (bytes : Bytes h p count xs) :
    Separate (.ref (.blk block) 0) 8 p count := by
  rcases bytes with null | ⟨ref, off, array, pointer, get, _, _⟩
  · simp [Separate, null.1]
  · subst p
    have different : (.blk block : BRef) ≠ ref := by
      intro same
      subst ref
      exact fresh block new (Or.inl (by simp [show h.bytes block = some array from get]))
    exact Or.inr (Or.inr (Or.inl different))

theorem uncompress2_framed_memory (h : Heap) (source dest sourceLen destLen : BPtr)
    (n capacity : UInt64) (xs : List UInt8)
    (fresh : Fresh h) (uniq : Uniq h) (globals : LibraryGlobals h)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit h)
    (inputCell : LengthCell h sourceLen n) (outputCell : LengthCell h destLen capacity)
    (readable : Bytes h source n.toNat xs) (writable : Writable h dest capacity.toNat)
    (separate : Separate source n.toNat dest capacity.toNat)
    (sourceOutput : Separate sourceLen 8 dest capacity.toNat)
    (destOutput : Separate destLen 8 dest capacity.toNat)
    (cellSeparate : Separate sourceLen 8 destLen 8)
    (validInput : source = .null → n = 0) (validOutput : dest = .null → capacity = 0) :
    ∃ rc after output used got consumed first second expected,
      C.run (uncompress2 dest destLen source sourceLen) h = .ok (rc, after) ∧
      Store h dest output first ∧ Store first sourceLen (lengthBytes consumed) second ∧
      Store second destLen (lengthBytes got) expected ∧ Frame expected after (fun _ => False) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ Bytes after dest output.length output ∧
      LengthCell after sourceLen consumed ∧ LengthCell after destLen got ∧
      used ≤ n.toNat ∧ output.length ≤ capacity.toNat ∧
      ((got.toNat = output.length ∧ consumed.toNat = used) ∨
        (rc = Z_MEM_ERROR ∧ output = [] ∧ got = capacity ∧ consumed = n)) ∧
      Uniq after ∧ Fresh after ∧ ZlibF.PlatformMemory.ByteObjectsFit after := by
  obtain ⟨prepared, prefixRun, fresh0, unique0, globals0, fit0, gotCell, usedCell,
    sourceCell0, destCell0, _next, _nalloc, _oracle, prefixLive, _views, oldBytes, oldWritable⟩ :=
    prepare_boundary h destLen sourceLen n capacity fresh uniq globals platform inputCell outputCell
  obtain ⟨out, destRead⟩ := Zlib.Uncompr.Proof.WrapperRanges.writable_bytes h dest capacity.toNat writable
  have gotOutput := local_separate_old h fresh h.nextBlk (Nat.le_refl _) dest capacity.toNat out destRead
  have usedOutput := local_separate_old h fresh (h.nextBlk + 1) (by omega) dest capacity.toNat out destRead
  have sourceGot := old_not_newblock h fresh h.nextBlk (Nat.le_refl _) sourceLen 8 (lengthBytes n) inputCell.1
  have sourceUsed := old_not_newblock h fresh (h.nextBlk + 1) (by omega) sourceLen 8 (lengthBytes n) inputCell.1
  have destGot := old_not_newblock h fresh h.nextBlk (Nat.le_refl _) destLen 8 (lengthBytes capacity) outputCell.1
  have destUsed := old_not_newblock h fresh (h.nextBlk + 1) (by omega) destLen 8 (lengthBytes capacity) outputCell.1
  have prefixFrame : Frame h prepared (fun _ => False) :=
    Zlib.Uncompr.Proof.CompatPrefixFrame.prepare_frame h prepared destLen sourceLen
      (.ref (.blk h.nextBlk) 0) (.ref (.blk (h.nextBlk + 1)) 0) n capacity
      fresh uniq platform inputCell outputCell prefixRun

  have localSeparate : Separate (.ref (.blk (h.nextBlk + 1)) 0) 8 (.ref (.blk h.nextBlk) 0) 8 := by
    simp [Separate]
  obtain ⟨rc, inner, output, used, got, consumed, calleeFirst, calleeSecond, calleeExpected,
    innerRun, outputStore, usedStore, gotStore, calleeFrame, innerLive, observed, usedAfter, gotAfter,
    usedBound, madeBound, counts⟩ :=
    Zlib.Uncompr.Proof.WrapperStoreFrame.uncompress2_z_framed_memory prepared source dest
      (.ref (.blk (h.nextBlk + 1)) 0) (.ref (.blk h.nextBlk) 0) n capacity xs
      fresh0 unique0 globals0 fit0 usedCell gotCell (oldBytes source n.toNat xs readable)
      (oldWritable dest capacity.toNat writable) separate usedOutput gotOutput localSeparate validInput validOutput
  have innerShape := Zlib.Uncompr.Proof.WrapperShape.uncompress2_z_return_shape prepared inner source dest
    (.ref (.blk (h.nextBlk + 1)) 0) (.ref (.blk h.nextBlk) 0) n capacity xs rc
    fresh0 unique0 globals0 fit0 usedCell gotCell (oldBytes source n.toNat xs readable)
    (oldWritable dest capacity.toNat writable) separate usedOutput gotOutput localSeparate validInput validOutput innerRun
  have sourceObject := uncompress2_z_object prepared inner source dest (.ref (.blk (h.nextBlk + 1)) 0) (.ref (.blk h.nextBlk) 0)
    n capacity xs rc fresh0 unique0 globals0 fit0 usedCell gotCell (oldBytes source n.toNat xs readable)
    (oldWritable dest capacity.toNat writable) separate usedOutput gotOutput localSeparate validInput validOutput
    sourceLen 8 (lengthBytes n) true sourceCell0.1 (fun _ => sourceCell0.2) sourceOutput
    (outside_separate sourceLen 8 (h.nextBlk + 1) sourceUsed) (outside_separate sourceLen 8 h.nextBlk sourceGot) innerRun
  have destObject := uncompress2_z_object prepared inner source dest (.ref (.blk (h.nextBlk + 1)) 0) (.ref (.blk h.nextBlk) 0)
    n capacity xs rc fresh0 unique0 globals0 fit0 usedCell gotCell (oldBytes source n.toNat xs readable)
    (oldWritable dest capacity.toNat writable) separate usedOutput gotOutput localSeparate validInput validOutput
    destLen 8 (lengthBytes capacity) true destCell0.1 (fun _ => destCell0.2) destOutput
    (outside_separate destLen 8 (h.nextBlk + 1) destUsed) (outside_separate destLen 8 h.nextBlk destGot) innerRun
  have sourceAfter : LengthCell inner sourceLen n := ⟨sourceObject.1, sourceObject.2 rfl⟩
  have destAfter : LengthCell inner destLen capacity := ⟨destObject.1, destObject.2 rfl⟩
  obtain ⟨written1, written2, after, tailRun, sourceStore, destStore, sourceFinal, destFinal,
    tailLive, uniqueFinal, freshFinal, fitFinal, cleanupFrame⟩ :=
    finish_framed inner h.nextBlk (h.nextBlk + 1) destLen sourceLen n capacity got consumed rc
      innerShape.1 innerShape.2.1 innerShape.2.2 sourceAfter destAfter gotAfter usedAfter
      (by omega) cellSeparate sourceGot sourceUsed destGot destUsed

  have outputRoots : ∀ b, ByteRoot dest b → h.live b ∧ ¬ (fun _ => False) b := by
    intro b root
    exact ⟨bytes_root_live h dest capacity.toNat out destRead b root, by simp⟩
  obtain ⟨first, expectedOutputStore, dataFrame⟩ :=
    Zlib.Uncompr.Proof.FrameMirror.store_mirror prefixFrame outputRoots outputStore
  have afterUsed := hide_local_store fresh expectedOutputStore.shape (by omega) dataFrame usedStore
  have afterGot := hide_local_store fresh expectedOutputStore.shape (Nat.le_refl _) afterUsed gotStore
  have beforeOuter : Frame first inner (fun _ => False) :=
    frame_trans_restrict afterGot calleeFrame (fun _ _ _ => ⟨by simp, by simp⟩)
  have sourceRoots : ∀ b, ByteRoot sourceLen b → first.live b ∧ ¬ (fun _ => False) b := by
    intro b root
    exact ⟨(expectedOutputStore.shape.live b).mpr (bytes_root_live h sourceLen 8 (lengthBytes n) inputCell.1 b root), by simp⟩
  obtain ⟨second, expectedSourceStore, sourceFrame⟩ :=
    Zlib.Uncompr.Proof.FrameMirror.store_mirror beforeOuter sourceRoots sourceStore
  have destRoots : ∀ b, ByteRoot destLen b → second.live b ∧ ¬ (fun _ => False) b := by
    intro b root
    have oldLive := bytes_root_live h destLen 8 (lengthBytes capacity) outputCell.1 b root
    exact ⟨(expectedSourceStore.shape.live b).mpr ((expectedOutputStore.shape.live b).mpr oldLive), by simp⟩
  obtain ⟨expected, expectedDestStore, beforeCleanup⟩ :=
    Zlib.Uncompr.Proof.FrameMirror.store_mirror sourceFrame destRoots destStore
  have callerShape : Shape h expected := (expectedOutputStore.shape.trans expectedSourceStore.shape).trans expectedDestStore.shape
  have finalFrame : Frame expected after (fun _ => False) := by
    apply frame_trans_restrict beforeCleanup cleanupFrame
    intro b live _
    have below := fresh.lt ((callerShape.live b).mp live)
    exact ⟨by simp, by omega⟩
  have outSource : Separate dest output.length sourceLen 8 := separate_prefix dest sourceLen capacity.toNat 8 output.length 8
    (separate_symm _ _ _ _ sourceOutput) madeBound (Nat.le_refl _)
  have outDest : Separate dest output.length destLen 8 := separate_prefix dest destLen capacity.toNat 8 output.length 8
    (separate_symm _ _ _ _ destOutput) madeBound (Nat.le_refl _)
  have writtenOutput := store_length_keep_bytes destStore (store_length_keep_bytes sourceStore observed outSource) outDest
  have writtenRoots : ∀ b, ByteRoot dest b → written2.live b ∧ ¬ (b = h.nextBlk ∨ b = h.nextBlk + 1) := by
    intro b root
    have oldLive := bytes_root_live h dest capacity.toNat out destRead b root
    have expectedLive := (callerShape.live b).mpr oldLive
    have writtenLive := (frame_live_at beforeCleanup b expectedLive (by simp)).mpr expectedLive
    have below := fresh.lt oldLive
    exact ⟨writtenLive, by omega⟩
  have finalObserved := bytes_forward_frame cleanupFrame writtenRoots writtenOutput

  refine ⟨rc, after, output, used, got, consumed, first, second, expected, ?_,
    expectedOutputStore, expectedSourceStore, expectedDestStore, finalFrame, ?_, finalObserved,
    sourceFinal, destFinal, usedBound, madeBound, counts, uniqueFinal, freshFinal, fitFinal⟩
  · rw [uncompress2_after_prepare h prepared dest destLen source sourceLen _ _ prefixRun]
    simp only [C.run] at innerRun tailRun
    simpa only [bind_app, innerRun, CompatPrefix.finish, Zlib.Uncompr.Proof.CompatibilityTail.finish] using tailRun
  · intro x
    have middle : inner.live x ↔ prepared.live x := by
      simpa only [not_false_eq_true, and_true, or_false] using innerLive x
    have start := prefixLive x
    have finish := tailLive x
    constructor
    · intro live
      obtain ⟨current, outside⟩ := (finish.mp live).resolve_right (by simp)
      rcases start.mp (middle.mp current) with ⟨old, _⟩ | temporary
      · exact Or.inl ⟨old, by simp⟩
      · exact False.elim (outside temporary)
    · rintro (⟨old, _⟩ | impossible)
      · have below := fresh.lt old
        exact finish.mpr (Or.inl ⟨middle.mpr (start.mpr (Or.inl ⟨old, by simp⟩)), by omega⟩)
      · exact False.elim impossible

#print axioms uncompress2_framed_memory

#print axioms finish_framed
end Zlib.Uncompr.Proof.LegacyFrame
