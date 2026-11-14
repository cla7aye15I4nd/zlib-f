import ZlibF.Proof.«gz.position-copy-overflow-regression»

/-!
# `gz_look` COPY past `GZ_OFF_MAX` regression

Patch 0004 bounded `gz_fetch`'s loads by the room left before `GZ_OFF_MAX`, but not the bytes that `gz_look`'s COPY
branch exposes. From a reader at `GZ_OFF_MAX - 3` after a gzip member with trailing data and `gzclearerr` (the
shape of `gz-copy-direct.c`), `gzread(file, buf, 3)` returned 3 with `x.pos = GZ_OFF_MAX` and five bytes buffered,
and a following `gzgetc` overflowed `x.pos`. Patch 0004 now bounds that branch; the theorems check the fixed runs. The runs are in `ZlibF/Proof/gz.position-copy-overflow-regression.lean`,
built with the library; this file restates them. Finding: `docs/findings/gz-position-copy-overflow.md`.
-/
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib Zlib.Gzread Zlib.Gz.PositionCopyOverflowRegression

/-- The start state satisfies the position clauses of the reader invariant. -/
theorem regression_start : PosClauses lookState := start_clauses

/-- `gzread(file, buf, 3)` returns 3 with `x.pos = GZ_OFF_MAX`, nothing buffered and `Z_DATA_ERROR`; before the
extension of patch 0004 it left five bytes buffered there. -/
theorem regression_gzread (statics : Statics) :
    ∃ fs' after s, gzread (some (.in_gzstate_x 2)) (.ref (.blk 0) 0) 3 lookFs (lookHeap statics) =
      .ok ((3, fs'), after) ∧ after.gzstates 2 = some s ∧ s.x.pos = GZ_OFF_MAX ∧ s.x.have = 0 ∧
      s.err = Z_DATA_ERROR ∧ PosClauses s :=
  gzread_within_room statics

/-- A following `gzgetc` returns -1 with no fault; before the extension it faulted on `x.pos++`. -/
theorem regression_gzgetc (statics : Statics) :
    ∃ fs' after, (gzread (some (.in_gzstate_x 2)) (.ref (.blk 0) 0) 3 >>= fun _ => gzgetc (some (.in_gzstate_x 2)))
      lookFs (lookHeap statics) = .ok ((-1, fs'), after) :=
  gzgetc_after_refused statics
