import ZlibF.Proof.«gz.position-copy-overflow-regression»

/-!
# `gz_look` COPY past `GZ_OFF_MAX` regression

Patch 0004 bounded `gz_fetch`'s loads by the room left before `GZ_OFF_MAX`, but not the bytes that `gz_look`'s COPY
branch exposes. From a reader at `GZ_OFF_MAX - 3` after a gzip member with trailing data and `gzclearerr` (the
shape of `gz-copy-direct.c`), `gzread(file, buf, 3)` returns 3 with `x.pos = GZ_OFF_MAX` and five bytes buffered,
and a following `gzgetc` overflows `x.pos`. The runs are in `ZlibF/Proof/gz.position-copy-overflow-regression.lean`,
built with the library; this file restates them. Finding: `docs/findings/gz-position-copy-overflow.md`.
-/
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib Zlib.Gzread Zlib.Gz.PositionCopyOverflowRegression

/-- The start state satisfies the position clauses of the reader invariant. -/
theorem regression_start : PosClauses lookState := start_clauses

/-- `gzread(file, buf, 3)` returns 3 with `x.pos + x.have` past `GZ_OFF_MAX`. -/
theorem regression_gzread (statics : Statics) :
    ∃ fs' after s, gzread (some (.in_gzstate_x 2)) (.ref (.blk 0) 0) 3 lookFs (lookHeap statics) =
      .ok ((3, fs'), after) ∧ after.gzstates 2 = some s ∧ s.x.pos = GZ_OFF_MAX ∧ s.x.have = 5 ∧
      s.err = Z_OK ∧ ¬ PosClauses s :=
  gzread_leaves_overflow statics

/-- A following `gzgetc` faults with undefined behaviour on `x.pos++`. -/
theorem regression_gzgetc (statics : Statics) :
    (gzread (some (.in_gzstate_x 2)) (.ref (.blk 0) 0) 3 >>= fun _ => gzgetc (some (.in_gzstate_x 2)))
      lookFs (lookHeap statics) = .error (.ub "signed overflow (long)") :=
  gzgetc_after_faults statics
