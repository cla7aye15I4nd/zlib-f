import ZlibF.Zlib.«gzread.c»

/-!
# gz: `gz_look`'s COPY branch can leave `x.pos + x.have` past `GZ_OFF_MAX`

Patch 0004 bounds what `gz_fetch` loads by the room left before `GZ_OFF_MAX` (`gz_room`), and `gz_read` and `gzgets`
drop buffered output when `x.pos` is at `GZ_OFF_MAX`. `gz_look`'s transparent COPY branch is not bounded: it exposes
all of `strm.avail_in` (up to `size` bytes) as `x.have`. The drop runs only on the next trip of the reading loop, so
a reading call can return with `x.pos + x.have > GZ_OFF_MAX`. The buffered path of `gzgetc` (the function, and the
zlib.h macro, which does the same `(file)->pos++`) then overflows `x.pos`: undefined behaviour.

The start state is the shape that `tests/verification/regressions/gz-copy-direct.c` reaches in the real C: a reader
after a gzip member with trailing non-gzip data and a `gzclearerr`. Then `how = LOOK`, `direct = 0`, `junk = 1`,
`eof = 0`, no pending input, and the next fetch takes `gz_look`'s COPY branch. Here the member is taken to have
decoded to `GZ_OFF_MAX - 3` bytes, so `x.pos = GZ_OFF_MAX - 3`; the input buffer has 8 bytes and the trailing data
is eight `'A'` bytes. The state satisfies the position clauses of the reader invariant (`GzCommon.pos`,
`GzReadInv.posHave`, `GzReadInv.haveSkip`).

`gzread(file, buf, 3)`: trip 1 has `n = gz_room(3) = 3` and no output, so it fetches; `gz_look` takes COPY with
`x.have = 8`. Trip 2 copies 3 bytes, `x.pos = GZ_OFF_MAX`, `x.have = 5`, and the loop ends with `len = 0`. `gzread`
returns 3. A following `gzgetc` takes its buffered path and faults with `Fault.ub` on `x.pos + 1`.

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
/-- `gzread(file, buf, 3)` returns 3 and leaves `x.pos = GZ_OFF_MAX` with five bytes buffered, so `x.pos + x.have`
is past `GZ_OFF_MAX` and the position clauses fail on return. -/
theorem gzread_leaves_overflow (statics : Statics) :
    ∃ fs' after s, gzread (some (.in_gzstate_x 2)) (.ref (.blk 0) 0) 3 lookFs (lookHeap statics) =
      .ok ((3, fs'), after) ∧ after.gzstates 2 = some s ∧ s.x.pos = GZ_OFF_MAX ∧ s.x.have = 5 ∧
      s.err = Z_OK ∧ ¬ PosClauses s := by
  have e : gzread (some (.in_gzstate_x 2)) (.ref (.blk 0) 0) 3 lookFs (lookHeap statics) =
      gzread (some (.in_gzstate_x 2)) (.ref (.blk 0) 0) 3 lookFs (lookHeap statics) := rfl
  conv at e => rhs; cbv
  exact ⟨_, _, _, e, rfl, rfl, rfl, rfl, by decide⟩

set_option maxRecDepth 20000 in
/-- The same `gzread`, then `gzgetc(file)`: its buffered path (`x.have--; x.pos++`, as in the zlib.h macro)
overflows `x.pos`, undefined behaviour. -/
theorem gzgetc_after_faults (statics : Statics) :
    (gzread (some (.in_gzstate_x 2)) (.ref (.blk 0) 0) 3 >>= fun _ => gzgetc (some (.in_gzstate_x 2)))
      lookFs (lookHeap statics) = .error (.ub "signed overflow (long)") := by
  conv => lhs; cbv

#print axioms start_clauses
#print axioms gzread_leaves_overflow
#print axioms gzgetc_after_faults

end Zlib.Gz.PositionCopyOverflowRegression
