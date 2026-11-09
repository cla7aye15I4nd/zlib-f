import ZlibF.Proof.«uncompr.c.wrapper-return-causes»
import ZlibF.Proof.«uncompr.c.compat-continuation»
import ZlibF.Proof.«uncompr.c.legacy-prefix»

namespace Zlib.Uncompr.Proof.LegacyReturnCauses
open C Zlib.Gzguts Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
open Zlib.Uncompr.Proof.Cells Zlib.Uncompr.Proof.SingleLength Zlib.Uncompr.Proof.ScalarWriteback
open Zlib.Uncompr.Proof.CompatPrefix Zlib.Uncompr.Proof.CallerCells Zlib.Uncompr.Proof.CallerObjects
open Zlib.Uncompr.Proof.ReturnCauses
set_option autoImplicit false

private theorem separate_symm (p q : BPtr) (n m : Nat) (separate : Separate p n q m) :
    Separate q m p n := by
  cases p <;> cases q <;> simp_all [Separate, ne_comm, or_comm, or_left_comm, or_assoc]

private theorem outside_separate (p : BPtr) (count block : Nat)
    (outside : ∀ off, p ≠ .ref (.blk block) off) : Separate p count (.ref (.blk block) 0) 8 := by
  cases p with
  | null => simp [Separate]
  | ref ref off =>
    have different : ref ≠ .blk block := by intro same; subst ref; exact outside off rfl
    exact Or.inr (Or.inr (Or.inl different))

private theorem cell_value_unique {h : Heap} {p : BPtr} {a b : UInt64}
    (first : LengthCell h p a) (second : LengthCell h p b) : a = b := by
  have left := load64_lengthCell h p a first
  have right := load64_lengthCell h p b second
  exact congrArg Prod.fst (Except.ok.inj (left.symm.trans right))

private theorem freeB_metadata (p : BPtr) {h after : Heap} {value : Unit}
    (run : freeB p h = .ok (value, after)) : after.nalloc = h.nalloc ∧ after.allocOk = h.allocOk := by
  unfold freeB at run
  repeat' first | split at run | (cases run <;> exact ⟨rfl, rfl⟩)

/-- The real two scalar writes and two automatic frees preserve allocation
metadata, and return the actual callee result unchanged. -/
theorem compatibility_finish_metadata
    (h after : Heap) (gotBlock usedBlock : Nat) (destLen sourceLen : BPtr)
    (sourceOld destOld gotValue usedValue : UInt64) (callee rc : Int32)
    (uniq : Uniq h) (fresh : Fresh h) (platform : ZlibF.PlatformMemory.ByteObjectsFit h)
    (sourceCell : LengthCell h sourceLen sourceOld) (destCell : LengthCell h destLen destOld)
    (gotCell : LengthCell h (.ref (.blk gotBlock) 0) gotValue)
    (usedCell : LengthCell h (.ref (.blk usedBlock) 0) usedValue)
    (separate : Separate sourceLen 8 destLen 8)
    (sourceGot : ∀ off, sourceLen ≠ .ref (.blk gotBlock) off)
    (run : C.run (Zlib.Uncompr.Proof.CompatibilityTail.finish destLen sourceLen
      (.ref (.blk gotBlock) 0) (.ref (.blk usedBlock) 0) callee) h = .ok (rc, after)) :
    rc = callee ∧ after.nalloc = h.nalloc ∧ after.allocOk = h.allocOk := by
  obtain ⟨first, sourceRun, sourceStore, _sourceCell, _sourceLive, uniq1, fresh1, fit1, keep1⟩ :=
    writable_scalar_store h sourceLen usedValue sourceCell.2 uniq fresh platform
  have got1 := keep1 (.ref (.blk gotBlock) 0) gotValue gotCell
    (separate_symm _ _ _ _ (outside_separate sourceLen 8 gotBlock sourceGot))
  have dest1 := keep1 destLen destOld destCell (separate_symm _ _ _ _ separate)
  obtain ⟨second, destRun, destStore, _destCell, _destLive, _uniq2, _fresh2, _fit2, _keep2⟩ :=
    writable_scalar_store first destLen gotValue dest1.2 uniq1 fresh1 fit1
  have usedRead := load64_lengthCell h (.ref (.blk usedBlock) 0) usedValue usedCell
  have gotRead := load64_lengthCell first (.ref (.blk gotBlock) 0) gotValue got1
  simp only [C.run] at usedRead gotRead sourceRun destRun run
  unfold Zlib.Uncompr.Proof.CompatibilityTail.finish at run
  simp only [bind_app, usedRead, sourceRun, gotRead, destRun] at run
  cases freeGot : freeB (.ref (.blk gotBlock) 0) second with
  | error fault => rw [freeGot] at run; cases run
  | ok pair =>
    obtain ⟨value, middle⟩ := pair
    rw [freeGot] at run
    dsimp only at run
    cases freeUsed : freeB (.ref (.blk usedBlock) 0) middle with
    | error fault => rw [freeUsed] at run; cases run
    | ok pair =>
      obtain ⟨value2, final⟩ := pair
      rw [freeUsed] at run
      cases run
      have one := scalar_store_metadata sourceStore
      have two := scalar_store_metadata destStore
      have three := freeB_metadata _ freeGot
      have four := freeB_metadata _ freeUsed
      exact ⟨rfl, four.1.trans (three.1.trans (two.2.1.trans one.2.1)),
        four.2.trans (three.2.trans (two.2.2.trans one.2.2))⟩

private theorem continuation_causes (h : Heap) (gotBlock usedBlock : Nat) (dest destLen source sourceLen : BPtr)
    (n capacity : UInt64) (xs : List UInt8)
    (fresh : Fresh h) (uniq : Uniq h) (globals : LibraryGlobals h)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit h)
    (sourceCell : LengthCell h sourceLen n) (destCell : LengthCell h destLen capacity)
    (gotCell : LengthCell h (.ref (.blk gotBlock) 0) capacity)
    (usedCell : LengthCell h (.ref (.blk usedBlock) 0) n)
    (readable : Bytes h source n.toNat xs) (writable : Writable h dest capacity.toNat)
    (separate : Separate source n.toNat dest capacity.toNat)
    (gotOutput : Separate (.ref (.blk gotBlock) 0) 8 dest capacity.toNat)
    (usedOutput : Separate (.ref (.blk usedBlock) 0) 8 dest capacity.toNat)
    (sourceOutput : Separate sourceLen 8 dest capacity.toNat)
    (destOutput : Separate destLen 8 dest capacity.toNat)
    (distinct : gotBlock ≠ usedBlock) (cellSeparate : Separate sourceLen 8 destLen 8)
    (sourceGot : ∀ off, sourceLen ≠ .ref (.blk gotBlock) off)
    (sourceUsed : ∀ off, sourceLen ≠ .ref (.blk usedBlock) off)
    (destGot : ∀ off, destLen ≠ .ref (.blk gotBlock) off)
    (destUsed : ∀ off, destLen ≠ .ref (.blk usedBlock) off)
    (validInput : source = .null → n = 0) (validOutput : dest = .null → capacity = 0) :
    ∃ rc after consumed produced,
      C.run (Zlib.Uncompr.Proof.CompatibilityContinuation.continuation dest destLen source sourceLen (.ref (.blk gotBlock) 0) (.ref (.blk usedBlock) 0)) h = .ok (rc, after) ∧
      LengthCell after sourceLen consumed ∧ LengthCell after destLen produced ∧
      consumed.toNat ≤ n.toNat ∧ produced.toNat ≤ capacity.toNat ∧
      UncompressCode rc ∧ (rc = Z_MEM_ERROR → AllocationFailed h after) ∧
      (rc = Z_BUF_ERROR → LengthCell after destLen capacity) := by
  have localSeparate : Separate (.ref (.blk usedBlock) 0) 8 (.ref (.blk gotBlock) 0) 8 := by
    simp [Separate, Ne.symm distinct]
  obtain ⟨rc, inner, consumed, produced, run, usedAfter, gotAfter, inputBound, outputBound, live, unique, freshAfter, fit⟩ :=
    uncompress2_z_caller_cells h source dest (.ref (.blk usedBlock) 0) (.ref (.blk gotBlock) 0) n capacity xs
      fresh uniq globals platform usedCell gotCell readable writable separate usedOutput gotOutput localSeparate validInput validOutput
  have causes := uncompress2_z_return_causes h inner source dest (.ref (.blk usedBlock) 0)
    (.ref (.blk gotBlock) 0) n capacity xs rc fresh uniq globals platform usedCell gotCell readable writable
    separate usedOutput gotOutput localSeparate validInput validOutput run
  have sourceObject := uncompress2_z_object h inner source dest (.ref (.blk usedBlock) 0) (.ref (.blk gotBlock) 0)
    n capacity xs rc fresh uniq globals platform usedCell gotCell readable writable separate
    usedOutput gotOutput localSeparate validInput validOutput sourceLen 8 (lengthBytes n) true
    sourceCell.1 (fun _ => sourceCell.2) sourceOutput
    (outside_separate sourceLen 8 usedBlock sourceUsed) (outside_separate sourceLen 8 gotBlock sourceGot) run
  have destObject := uncompress2_z_object h inner source dest (.ref (.blk usedBlock) 0) (.ref (.blk gotBlock) 0)
    n capacity xs rc fresh uniq globals platform usedCell gotCell readable writable separate
    usedOutput gotOutput localSeparate validInput validOutput destLen 8 (lengthBytes capacity) true
    destCell.1 (fun _ => destCell.2) destOutput
    (outside_separate destLen 8 usedBlock destUsed) (outside_separate destLen 8 gotBlock destGot) run
  have sourceAfter : LengthCell inner sourceLen n := ⟨sourceObject.1, sourceObject.2 rfl⟩
  have destAfter : LengthCell inner destLen capacity := ⟨destObject.1, destObject.2 rfl⟩
  obtain ⟨_first, _second, after, tailRun, _storeSource, _storeDest, sourceFinal, destFinal,
    tailLedger, uniqueFinal, freshFinal, fitFinal⟩ :=
    Zlib.Uncompr.Proof.CompatibilityTail.finish_safe inner gotBlock usedBlock destLen sourceLen
      n capacity produced consumed rc unique freshAfter fit sourceAfter destAfter gotAfter usedAfter distinct cellSeparate
      sourceGot sourceUsed destGot destUsed
  have metadata := compatibility_finish_metadata inner after gotBlock usedBlock destLen sourceLen
    n capacity produced consumed rc rc unique freshAfter fit sourceAfter destAfter gotAfter usedAfter
    cellSeparate sourceGot tailRun
  refine ⟨rc, after, consumed, produced, ?_, sourceFinal, destFinal, inputBound, outputBound,
    causes.1, ?_, ?_⟩
  · simp only [C.run] at run tailRun
    simpa only [C.run, Zlib.Uncompr.Proof.CompatibilityContinuation.continuation, bind_app, run] using tailRun
  · intro memory
    obtain ⟨i, lower, upper, rejected⟩ := causes.2.1 memory
    exact ⟨i, lower, by rw [metadata.2.1]; exact upper, rejected⟩
  · intro buffer
    have same : produced = capacity := cell_value_unique gotAfter (causes.2.2 buffer)
    rw [←same]
    exact destFinal

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


/-- `int uncompress2(Bytef *, uLongf *, const Bytef *, uLong *)`.
The actual automatic-scalar prefix, counted call and ordered writeback/free
tail retain the counted result causes on this same final heap. The
original internal domain explicitly retains Uniq and ByteObjectsFit. -/
theorem uncompress2_return_causes (h after : Heap) (source dest sourceLen destLen : BPtr)
    (n capacity : UInt64) (xs : List UInt8) (rc : Int32)
    (fresh : Fresh h) (uniq : Uniq h) (globals : LibraryGlobals h)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit h)
    (inputCell : LengthCell h sourceLen n) (outputCell : LengthCell h destLen capacity)
    (readable : Bytes h source n.toNat xs) (writable : Writable h dest capacity.toNat)
    (separate : Separate source n.toNat dest capacity.toNat)
    (sourceOutput : Separate sourceLen 8 dest capacity.toNat)
    (destOutput : Separate destLen 8 dest capacity.toNat)
    (cellSeparate : Separate sourceLen 8 destLen 8)
    (validInput : source = .null → n = 0) (validOutput : dest = .null → capacity = 0)
    (observed : C.run (uncompress2 dest destLen source sourceLen) h = .ok (rc, after)) :
    UncompressCode rc ∧ (rc = Z_MEM_ERROR → AllocationFailed h after) ∧
      (rc = Z_BUF_ERROR → LengthCell after destLen capacity) := by
  obtain ⟨prepared, prefixRun, fresh0, unique0, globals0, fit0, gotCell, usedCell,
    sourceCell0, destCell0, _next, nalloc, oracle, prefixLive, _views, oldBytes, oldWritable⟩ :=
    prepare_boundary h destLen sourceLen n capacity fresh uniq globals platform inputCell outputCell
  obtain ⟨out, destRead⟩ := Zlib.Uncompr.Proof.WrapperRanges.writable_bytes h dest capacity.toNat writable
  have gotOutput := local_separate_old h fresh h.nextBlk (Nat.le_refl _) dest capacity.toNat out destRead
  have usedOutput := local_separate_old h fresh (h.nextBlk + 1) (by omega) dest capacity.toNat out destRead
  have sourceGot := old_not_newblock h fresh h.nextBlk (Nat.le_refl _) sourceLen 8 (lengthBytes n) inputCell.1
  have sourceUsed := old_not_newblock h fresh (h.nextBlk + 1) (by omega) sourceLen 8 (lengthBytes n) inputCell.1
  have destGot := old_not_newblock h fresh h.nextBlk (Nat.le_refl _) destLen 8 (lengthBytes capacity) outputCell.1
  have destUsed := old_not_newblock h fresh (h.nextBlk + 1) (by omega) destLen 8 (lengthBytes capacity) outputCell.1
  obtain ⟨expectedCode, final, consumed, produced, run, _sourceFinal, _destFinal, _inputBound,
      _outputBound, code, memory, buffer⟩ :=
    continuation_causes prepared h.nextBlk (h.nextBlk + 1) dest destLen source sourceLen n capacity xs
      fresh0 unique0 globals0 fit0 sourceCell0 destCell0 gotCell usedCell
      (oldBytes source n.toNat xs readable) (oldWritable dest capacity.toNat writable)
      separate gotOutput usedOutput sourceOutput destOutput (by omega) cellSeparate
      sourceGot sourceUsed destGot destUsed validInput validOutput
  have sourceRun : C.run (uncompress2 dest destLen source sourceLen) h = .ok (expectedCode, final) := by
    rw [uncompress2_after_prepare h prepared dest destLen source sourceLen _ _ prefixRun]
    simpa only [C.run, Zlib.Uncompr.Proof.CompatibilityContinuation.continuation,
      CompatPrefix.finish, Zlib.Uncompr.Proof.CompatibilityTail.finish] using run
  have same := Except.ok.inj (sourceRun.symm.trans observed)
  have codes : expectedCode = rc := congrArg Prod.fst same
  have heaps : final = after := congrArg Prod.snd same
  subst expectedCode final
  refine ⟨code, ?_, buffer⟩
  intro selected
  obtain ⟨i, lower, upper, rejected⟩ := memory selected
  refine ⟨i, ?_, upper, ?_⟩
  · rw [nalloc] at lower
    exact lower
  · rw [oracle] at rejected
    exact rejected

end Zlib.Uncompr.Proof.LegacyReturnCauses
