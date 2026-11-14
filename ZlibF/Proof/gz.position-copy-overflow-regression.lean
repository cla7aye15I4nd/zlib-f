import ZlibF.Zlib.«gzread.c»

/-!
# gz: `gz_look`'s COPY branch keeps `x.pos + x.have` within `GZ_OFF_MAX`

Patch 0004 bounds what `gz_fetch` loads by the room left before `GZ_OFF_MAX` (`gz_room`), and `gz_read` and `gzgets`
drop buffered output when `x.pos` is at `GZ_OFF_MAX`. Before its extension, `gz_look`'s transparent COPY branch was
not bounded: it exposed all of `strm.avail_in` (up to `size` bytes) as `x.have`, and the drop in `gz_read` runs only
on the next trip of its loop. So a reading call could return with `x.pos + x.have > GZ_OFF_MAX`, and the buffered
path of `gzgetc` (the function, and the zlib.h macro, which does the same `(file)->pos++`) overflowed `x.pos`.
Finding: `docs/findings/gz-position-copy-overflow.md`.

The start state is the shape that `tests/verification/regressions/gz-copy-direct.c` reaches in the real C: a reader
after a gzip member with trailing non-gzip data and a `gzclearerr`. Then `how = LOOK`, `direct = 0`, `junk = 1`,
`eof = 0`, no pending input, and the next fetch takes `gz_look`'s COPY branch. Here the member is taken to have
decoded to `GZ_OFF_MAX - 3` bytes, so `x.pos = GZ_OFF_MAX - 3`; the input buffer has 8 bytes and the trailing data
is eight `'A'` bytes. The state satisfies the position clauses of the reader invariant (`GzCommon.pos`,
`GzReadInv.posHave`, `GzReadInv.haveSkip`).

`gzread(file, buf, 3)`. Before the extension: `gz_look` set `x.have = 8`, trip 2 copied 3 bytes, and `gzread`
returned 3 with `x.pos = GZ_OFF_MAX` and `x.have = 5`; a following `gzgetc` faulted with `Fault.ub` on `x.pos + 1`.
Now: `gz_look` buffers `gz_room(8) = 3` bytes and records `Z_DATA_ERROR`; trip 2 copies them and stops on the
deferred error. `gzread` returns 3 with `x.pos = GZ_OFF_MAX`, `x.have = 0`, and the position clauses hold. A following
`gzgetc` returns -1 (the error), with no fault.

The state is constructed, not reached by a public history: reaching it needs about `2^63` decoded bytes.
-/

namespace Zlib.Gz.PositionCopyOverflowRegression
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib Zlib.Gzread

/-- A reader after a gzip member and `gzclearerr`, at `GZ_OFF_MAX - 3`, before its next fetch. -/
def lookState : GzState :=
  { GzState.zeroed with
    mode := GZ_READ, fd := 3, path := .ref (.blk 3) 0, want := 8, size := 8
    «in» := .ref (.blk 4) 0, out := .ref (.blk 1) 0
    how := LOOK, direct := 0, junk := 1
    x := { GzState.zeroed.x with pos := GZ_OFF_MAX - 3 } }

/-- Block 0 is the caller's buffer, block 1 the output buffer, block 2 the record, block 3 the path `"p"`, block 4
the input buffer. -/
def lookHeap (statics : Statics) : Heap :=
  { Heap.empty with
    bytes := ⟨#[some #[0, 0, 0, 0], some (Array.replicate 16 0), none, some #[112, 0], some (Array.replicate 8 0)]⟩
    ro := ⟨#[false, false, false, false, false]⟩
    gzstates := ⟨#[none, none, some lookState]⟩
    static := statics, nextBlk := 5, nalloc := 3 }

/-- Descriptor 3 reads the rest of the file: eight bytes `'A'`, not a gzip header. -/
def lookFs : Fs :=
  { names := #[(#[112], 0)], nodes := #[{ data := Array.replicate 8 65, isDir := false }]
    fds := #[none, none, none, some { node := 0, pos := 0, rd := true, wr := false, append := false }] }

/-- The position clauses of the reader invariant: `GzCommon.pos`, `GzReadInv.posHave` and `GzReadInv.haveSkip`. -/
def PosClauses (s : GzState) : Prop :=
  0 ≤ s.skip.toInt ∧ s.x.pos.toInt + s.skip.toInt ≤ 9223372036854775807 ∧ 0 ≤ s.x.pos.toInt + s.x.have.toNat ∧
    s.x.pos.toInt + s.x.have.toNat ≤ 9223372036854775807 ∧ (s.x.have ≠ 0 → s.skip = 0)

instance (s : GzState) : Decidable (PosClauses s) := by unfold PosClauses; infer_instance

/-- The start state satisfies the position clauses. -/
theorem start_clauses : PosClauses lookState := by decide

set_option maxRecDepth 20000 in
/-- `gzread(file, buf, 3)` returns 3 with `x.pos = GZ_OFF_MAX`, nothing buffered and `Z_DATA_ERROR` recorded: the
position clauses hold on return. -/
theorem gzread_within_room (statics : Statics) :
    ∃ fs' after s, gzread (some (.in_gzstate_x 2)) (.ref (.blk 0) 0) 3 lookFs (lookHeap statics) =
      .ok ((3, fs'), after) ∧ after.gzstates 2 = some s ∧ s.x.pos = GZ_OFF_MAX ∧ s.x.have = 0 ∧
      s.err = Z_DATA_ERROR ∧ PosClauses s := by
  have e : gzread (some (.in_gzstate_x 2)) (.ref (.blk 0) 0) 3 lookFs (lookHeap statics) =
      gzread (some (.in_gzstate_x 2)) (.ref (.blk 0) 0) 3 lookFs (lookHeap statics) := rfl
  conv at e => rhs; cbv
  exact ⟨_, _, _, e, rfl, rfl, rfl, rfl, by decide⟩

set_option maxRecDepth 20000 in
/-- The same `gzread`, then `gzgetc(file)`: no buffered byte, so it reports the error with -1, and nothing faults. -/
theorem gzgetc_after_refused (statics : Statics) :
    ∃ fs' after, (gzread (some (.in_gzstate_x 2)) (.ref (.blk 0) 0) 3 >>= fun _ => gzgetc (some (.in_gzstate_x 2)))
      lookFs (lookHeap statics) = .ok ((-1, fs'), after) := by
  have e : (gzread (some (.in_gzstate_x 2)) (.ref (.blk 0) 0) 3 >>= fun _ => gzgetc (some (.in_gzstate_x 2)))
      lookFs (lookHeap statics) =
      (gzread (some (.in_gzstate_x 2)) (.ref (.blk 0) 0) 3 >>= fun _ => gzgetc (some (.in_gzstate_x 2)))
      lookFs (lookHeap statics) := rfl
  conv at e => rhs; cbv
  exact ⟨_, _, e⟩

#print axioms start_clauses
#print axioms gzread_within_room
#print axioms gzgetc_after_refused

end Zlib.Gz.PositionCopyOverflowRegression
