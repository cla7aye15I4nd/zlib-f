import ZlibF.Proof.«gz.position-overflow-regression»

/-!
# `"position overflow"` regression

Patch 0004 added the C literal `"position overflow"`, but the runtime table `strTable` lacked it. So
`strLit "position overflow"` was a fault, and each patch-0004 refusal faulted in the model, where the C returns
with `Z_DATA_ERROR`. The literal is now in the table. The four refusal sites run through their public entries
(`ZlibF/Proof/gz.position-overflow-regression.lean`, built with the library); this file restates the results.
`scripts/check-strlit.py` (fast gate) keeps every literal of the translations in the table.
-/
open C Zlib.GzFs Zlib.Gzread Zlib.Gzwrite Zlib.Gzwrite.BorrowRegression Zlib.Gz.PositionOverflowRegression

/-- `strLit "position overflow"` no longer faults: it is the static array of the literal. -/
theorem strlit_position_overflow (h : Heap) :
    ∃ i, Zlib.GzFs.strLit "position overflow" h = .ok (.ref (.str i) 0, h) ∧
      strTable[i]? = some "position overflow" :=
  strLitRef_of_mem (by decide +kernel)

/-- `gz_read` (through `gzread`): `Z_DATA_ERROR` and the message, return -1. -/
theorem regression_gz_read (statics : Statics) :
    ∃ fs' after, gzread (some (.in_gzstate_x 2)) (.ref (.blk 0) 0) 1 initialFs (readerHeap statics) =
      .ok ((-1, fs'), after) ∧ Refused after := gzread_refused statics

/-- `gzgets`: `Z_DATA_ERROR` and the message, return NULL. -/
theorem regression_gzgets (statics : Statics) :
    ∃ fs' after, gzgets (some (.in_gzstate_x 2)) (.ref (.blk 0) 0) 2 initialFs (readerHeap statics) =
      .ok ((.null, fs'), after) ∧ Refused after := gzgets_refused statics

/-- `gz_write` (through `gzwrite`): `Z_DATA_ERROR` and the message, return 0. -/
theorem regression_gz_write (statics : Statics) :
    ∃ fs' after, gzwrite (some (.in_gzstate_x 2)) (.ref (.blk 0) 0) 1 openedFs (writerHeap statics) =
      .ok ((0, fs'), after) ∧ Refused after := gzwrite_refused statics

/-- `gzvprintf` (through `gzprintf`): `Z_DATA_ERROR` and the message, return `Z_DATA_ERROR`. -/
theorem regression_gzvprintf (statics : Statics) :
    ∃ fs' after, gzprintf (some (.in_gzstate_x 2)) (.ref (.blk 0) 0) [] openedFs (writerHeap statics) =
      .ok ((Z_DATA_ERROR, fs'), after) ∧ Refused after := gzprintf_refused statics

#print axioms strlit_position_overflow
#print axioms regression_gz_read
#print axioms regression_gzgets
#print axioms regression_gz_write
#print axioms regression_gzvprintf
