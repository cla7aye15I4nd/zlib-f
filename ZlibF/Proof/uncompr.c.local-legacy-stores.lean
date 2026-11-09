import ZlibF.Proof.«uncompr.c.local-store-observations»
import ZlibF.Proof.«uncompr.c.local-compat-tail-stores»
import ZlibF.Proof.«uncompr.c.local-legacy-frame»
import ZlibF.Proof.«uncompr.c.single-frame»

namespace Zlib.Uncompr.Proof.LocalLegacyStores
open C Zlib.Gzguts ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inflate.Local
open Zlib.Uncompr.Proof.Cells Zlib.Uncompr.Proof.SingleLength Zlib.Uncompr.Proof.OuterFrame
open Zlib.Uncompr.Proof.LocalCompatPrefix Zlib.Uncompr.Proof.CallerObjects Zlib.Uncompr.Proof.CallerFrame
set_option autoImplicit false

private theorem outside_separate (p : BPtr) (count block : Nat)
    (outside : ∀ off,p ≠ .ref (.blk block) off) : Separate p count (.ref (.blk block) 0) 8 := by
  cases p with
  | null => simp [Separate]
  | ref ref off =>
    have different : ref ≠ .blk block := by intro same;subst ref;exact outside off rfl
    exact Or.inr (Or.inr (Or.inl different))

private theorem local_separate_old (h : Heap) (fresh : Fresh h) (block : Nat) (new : h.nextBlk ≤ block)
    (p : BPtr) (count : Nat) (xs : List UInt8) (bytes : Bytes h p count xs) :
    Separate (.ref (.blk block) 0) 8 p count := by
  rcases bytes with null | ⟨ref, off, a, ptr, get, _, _⟩
  · simp [Separate, null.1]
  · subst p
    have distinct : (.blk block : BRef) ≠ ref := by
      intro same
      subst ref
      have live : h.live block := Or.inl (by simp [show h.bytes block = some a from get])
      exact fresh block new live
    exact Or.inr (Or.inr (Or.inl distinct))

/-- The actual traditional counted utility yields three expected Stores
and complete Frame after the real two local frees. All allocation outcomes,
shared but disjoint caller slices, and nullable zero data buffers are included. -/
theorem uncompress2_stores (h : Heap) (source dest sourceLen destLen : BPtr)
    (n capacity : UInt64) (xs : List UInt8)
    (fresh : Fresh h) (globals : LibraryGlobals h)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit h)
    (inputCell : LengthCell h sourceLen n) (outputCell : LengthCell h destLen capacity)
    (readable : Bytes h source n.toNat xs) (writable : Writable h dest capacity.toNat)
    (separate : Separate source n.toNat dest capacity.toNat)
    (sourceOutput : Separate sourceLen 8 dest capacity.toNat)
    (destOutput : Separate destLen 8 dest capacity.toNat)
    (cellSeparate : Separate sourceLen 8 destLen 8)
    (validInput : source = .null → n = 0) (validOutput : dest = .null → capacity = 0) :
    ∃ rc after output consumed produced first second expected,
      C.run (uncompress2 dest destLen source sourceLen) h = .ok (rc,after) ∧
      Store h dest output first ∧ Store first sourceLen (lengthBytes consumed) second ∧
      Store second destLen (lengthBytes produced) expected ∧ Frame expected after (fun _ => False) ∧
      LengthCell after sourceLen consumed ∧ LengthCell after destLen produced ∧
      ((output.length = produced.toNat ∧ consumed.toNat ≤ n.toNat ∧ produced.toNat ≤ capacity.toNat) ∨
        (rc = Z_MEM_ERROR ∧ output = [] ∧ consumed = n ∧ produced = capacity)) := by
  let prepared := preparedHeap h capacity n
  have fresh0 := prepared_fresh h capacity n fresh
  have unique0 := prepared_uniqueFrom h capacity n fresh
  have globals0 := prepared_globals h capacity n globals
  have fit0 := prepared_platform h capacity n platform
  have gotCell := prepared_got_cell h capacity n fresh
  have usedCell := prepared_used_cell h capacity n
  have sourceCell0 := prepared_old_cell h capacity n fresh sourceLen n inputCell
  have destCell0 := prepared_old_cell h capacity n fresh destLen capacity outputCell
  have oldBytes := prepared_old_bytes h capacity n fresh
  have oldWritable := prepared_old_writable h capacity n fresh
  obtain ⟨out, destRead⟩ := Zlib.Uncompr.Proof.WrapperRanges.writable_bytes h dest capacity.toNat writable
  have gotOutput := local_separate_old h fresh h.nextBlk (Nat.le_refl _) dest capacity.toNat out destRead
  have usedOutput := local_separate_old h fresh (h.nextBlk + 1) (by omega) dest capacity.toNat out destRead
  have sourceGot := old_not_newblock h fresh h.nextBlk (Nat.le_refl _) sourceLen 8 (lengthBytes n) inputCell.1
  have sourceUsed := old_not_newblock h fresh (h.nextBlk + 1) (by omega) sourceLen 8 (lengthBytes n) inputCell.1
  have destGot := old_not_newblock h fresh h.nextBlk (Nat.le_refl _) destLen 8 (lengthBytes capacity) outputCell.1
  have destUsed := old_not_newblock h fresh (h.nextBlk + 1) (by omega) destLen 8 (lengthBytes capacity) outputCell.1
  have prefixFrame := LocalLegacyFrame.prepared_frame h capacity n fresh
  have localSeparate : Separate (.ref (.blk (h.nextBlk + 1)) 0) 8 (.ref (.blk h.nextBlk) 0) 8 := by
    simp [Separate]
  obtain ⟨rc,inner,used,got,innerRun,usedAfter,gotAfter,_inputBound,_outputBound,
      _live,_shape,innerFresh,innerFit,kept⟩ :=
    LocalCallerCells.uncompress2_z_caller_cells prepared source dest (.ref (.blk (h.nextBlk + 1)) 0)
      (.ref (.blk h.nextBlk) 0) n capacity xs fresh0 globals0 fit0 usedCell gotCell
      (oldBytes source n.toNat xs readable) (oldWritable dest capacity.toNat writable)
      separate usedOutput gotOutput localSeparate validInput validOutput
  have unique := kept h.nextBlk unique0
  obtain ⟨output,consumed,produced,calleeFirst,calleeSecond,calleeExpected,outputStore,
      usedStore,gotStore,calleeFrame,counts⟩ :=
    LocalWrapperStores.uncompress2_z_stores_allocation prepared source dest (.ref (.blk (h.nextBlk + 1)) 0)
      (.ref (.blk h.nextBlk) 0) n capacity xs fresh0 globals0 fit0 usedCell gotCell
      (oldBytes source n.toNat xs readable) (oldWritable dest capacity.toNat writable)
      separate usedOutput gotOutput localSeparate validInput validOutput rc inner innerRun
  have calleeCells := LocalStoreObservations.counted_cells usedStore gotStore calleeFrame localSeparate
  have sourceObject := LocalCallerObjects.uncompress2_z_object prepared inner source dest
    (.ref (.blk (h.nextBlk + 1)) 0) (.ref (.blk h.nextBlk) 0) n capacity xs rc fresh0 globals0 fit0
    usedCell gotCell (oldBytes source n.toNat xs readable) (oldWritable dest capacity.toNat writable)
    separate usedOutput gotOutput localSeparate validInput validOutput sourceLen 8 (lengthBytes n) true
    sourceCell0.1 (fun _ => sourceCell0.2) sourceOutput
    (outside_separate sourceLen 8 (h.nextBlk + 1) sourceUsed) (outside_separate sourceLen 8 h.nextBlk sourceGot) innerRun
  have destObject := LocalCallerObjects.uncompress2_z_object prepared inner source dest
    (.ref (.blk (h.nextBlk + 1)) 0) (.ref (.blk h.nextBlk) 0) n capacity xs rc fresh0 globals0 fit0
    usedCell gotCell (oldBytes source n.toNat xs readable) (oldWritable dest capacity.toNat writable)
    separate usedOutput gotOutput localSeparate validInput validOutput destLen 8 (lengthBytes capacity) true
    destCell0.1 (fun _ => destCell0.2) destOutput
    (outside_separate destLen 8 (h.nextBlk + 1) destUsed) (outside_separate destLen 8 h.nextBlk destGot) innerRun
  have sourceAfter : LengthCell inner sourceLen n := ⟨sourceObject.1,sourceObject.2 rfl⟩
  have destAfter : LengthCell inner destLen capacity := ⟨destObject.1,destObject.2 rfl⟩
  obtain ⟨written1,written2,after,tailRun,sourceStore,destStore,cleanupFrame⟩ :=
    LocalCompatibilityStores.finish_stores inner h.nextBlk h.nextBlk (h.nextBlk + 1) destLen sourceLen
      n capacity produced consumed rc unique innerFresh (Nat.le_refl _) (by omega) innerFit
      sourceAfter destAfter calleeCells.2 calleeCells.1 (by omega) cellSeparate sourceGot sourceUsed destGot destUsed
  have outputRoots : ∀ b,ByteRoot dest b → h.live b ∧ ¬ (fun _ => False) b := by
    intro b root
    exact ⟨bytes_root_live h dest capacity.toNat out destRead b root,by simp⟩
  obtain ⟨first,expectedOutputStore,dataFrame⟩ := FrameMirror.store_mirror prefixFrame outputRoots outputStore
  have afterUsed := hide_local_store fresh expectedOutputStore.shape (by omega) dataFrame usedStore
  have afterGot := hide_local_store fresh expectedOutputStore.shape (Nat.le_refl _) afterUsed gotStore
  have beforeOuter : Frame first inner (fun _ => False) :=
    frame_trans_restrict afterGot calleeFrame (fun _ _ _ => ⟨by simp,by simp⟩)
  have sourceRoots : ∀ b,ByteRoot sourceLen b → first.live b ∧ ¬ (fun _ => False) b := by
    intro b root
    exact ⟨(expectedOutputStore.shape.live b).mpr (bytes_root_live h sourceLen 8 (lengthBytes n) inputCell.1 b root),by simp⟩
  obtain ⟨second,expectedSourceStore,sourceFrame⟩ := FrameMirror.store_mirror beforeOuter sourceRoots sourceStore
  have destRoots : ∀ b,ByteRoot destLen b → second.live b ∧ ¬ (fun _ => False) b := by
    intro b root
    have oldLive := bytes_root_live h destLen 8 (lengthBytes capacity) outputCell.1 b root
    exact ⟨(expectedSourceStore.shape.live b).mpr ((expectedOutputStore.shape.live b).mpr oldLive),by simp⟩
  obtain ⟨expected,expectedDestStore,beforeCleanup⟩ := FrameMirror.store_mirror sourceFrame destRoots destStore
  have callerShape := (expectedOutputStore.shape.trans expectedSourceStore.shape).trans expectedDestStore.shape
  have finalFrame : Frame expected after (fun _ => False) := by
    apply frame_trans_restrict beforeCleanup cleanupFrame
    intro b live _
    have below := fresh.lt ((callerShape.live b).mp live)
    exact ⟨by simp,by omega⟩
  have finalCells := LocalStoreObservations.counted_cells expectedSourceStore expectedDestStore finalFrame cellSeparate
  refine ⟨rc,after,output,consumed,produced,first,second,expected,?_,
    expectedOutputStore,expectedSourceStore,expectedDestStore,finalFrame,finalCells.1,finalCells.2,counts⟩
  rw [uncompress2_to_continuation h dest destLen source sourceLen capacity n fresh outputCell inputCell]
  dsimp only [prepared] at innerRun
  simp only [C.run] at innerRun tailRun
  simpa only [C.run,CompatibilityContinuation.continuation,bind_app,innerRun] using tailRun

#print axioms uncompress2_stores
end Zlib.Uncompr.Proof.LocalLegacyStores
