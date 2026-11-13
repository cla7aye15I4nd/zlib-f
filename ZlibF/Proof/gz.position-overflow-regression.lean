import ZlibF.Zlib.«gzread.c»
import ZlibF.Proof.«gzwrite.c.borrowed-error-regression»

/-!
# gz: the patch 0004 refusals run in the model

Patch 0004 (`patches/0004-gz-position-overflow.patch`) refuses a read or a write that would carry `x.pos` past
`GZ_OFF_MAX`, with `gz_error(state, Z_DATA_ERROR, "position overflow")`. The runtime table of string literals
(`strTable`) lacked that literal, so `strLit "position overflow"` was a fault and each refusal faulted in the model,
where the C returns with `Z_DATA_ERROR`. This regression runs each of the four refusal sites on a concrete state at
`x.pos = GZ_OFF_MAX` through its public entry: `gzread` (`gz_read`), `gzgets`, `gzwrite` (`gz_write`) and
`gzprintf` (`gzvprintf`). Each call completes, sets `err = Z_DATA_ERROR` and stores the message
`"p: position overflow"` (path `"p"`) in a fresh block.

The states are constructed, not reached by a public history: reaching `x.pos = GZ_OFF_MAX` needs about `2^63` bytes.
The point is that the branches of the patched translation run, not that the states are reachable.
-/

namespace Zlib.Gz.PositionOverflowRegression
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib Zlib.Gzread Zlib.Gzwrite
open Zlib.Gzwrite.BorrowRegression

/-- The literal is in the runtime table: `strLit` gives the static array, with no fault. -/
theorem position_overflow_literal (h : Heap) :
    ∃ i, Zlib.Zutil.strLit "position overflow" h = .ok (.ref (.str i) 0, h) ∧
      strTable[i]? = some "position overflow" :=
  strLitRef_of_mem (by decide +kernel)

/-! ## Readers: `gz_read` and `gzgets` -/

/-- A reader at `GZ_OFF_MAX` with one byte (`'A'`) left in its output buffer. -/
def readerState : GzState :=
  { GzState.zeroed with
    mode := GZ_READ, fd := 3, path := .ref (.blk 3) 0, want := 8, size := 8, out := .ref (.blk 1) 0
    x := { GzState.zeroed.x with «have» := 1, next := .ref (.blk 1) 0, pos := GZ_OFF_MAX } }

/-- Block 0 is the caller's buffer, block 1 the reader's output buffer, block 3 the path `"p"`. -/
def readerHeap (statics : Statics) : Heap :=
  { Heap.empty with
    bytes := ⟨#[some #[0, 0, 0, 0], some #[65, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], none, some #[112, 0]]⟩
    ro := ⟨#[false, false, false, false]⟩
    gzstates := ⟨#[none, none, some readerState]⟩
    static := statics, nextBlk := 4, nalloc := 2 }

/-- The state after a refusal holds `Z_DATA_ERROR` and the message `"p: position overflow"` in a block. -/
def Refused (after : Heap) : Prop :=
  ∃ s b, after.gzstates 2 = some s ∧ s.err = Z_DATA_ERROR ∧ s.msg = .ref (.blk b) 0 ∧
    after.bytes b = some (strBytes "p: position overflow")

set_option maxRecDepth 20000 in
/-- `gzread(file, buf, 1)` at `GZ_OFF_MAX`: `gz_read` refuses the byte, and `gzread` returns -1. -/
theorem gzread_refused (statics : Statics) :
    ∃ fs' after, gzread (some (.in_gzstate_x 2)) (.ref (.blk 0) 0) 1 initialFs (readerHeap statics) =
      .ok ((-1, fs'), after) ∧ Refused after := by
  have e : gzread (some (.in_gzstate_x 2)) (.ref (.blk 0) 0) 1 initialFs (readerHeap statics) =
      gzread (some (.in_gzstate_x 2)) (.ref (.blk 0) 0) 1 initialFs (readerHeap statics) := rfl
  conv at e => rhs; cbv
  exact ⟨_, _, e, _, _, rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 20000 in
/-- `gzgets(file, buf, 2)` at `GZ_OFF_MAX`: the refusal stores nothing, and `gzgets` returns NULL. -/
theorem gzgets_refused (statics : Statics) :
    ∃ fs' after, gzgets (some (.in_gzstate_x 2)) (.ref (.blk 0) 0) 2 initialFs (readerHeap statics) =
      .ok ((.null, fs'), after) ∧ Refused after := by
  have e : gzgets (some (.in_gzstate_x 2)) (.ref (.blk 0) 0) 2 initialFs (readerHeap statics) =
      gzgets (some (.in_gzstate_x 2)) (.ref (.blk 0) 0) 2 initialFs (readerHeap statics) := rfl
  conv at e => rhs; cbv
  exact ⟨_, _, e, _, _, rfl, rfl, rfl, rfl⟩

/-! ## Writers: `gz_write` and `gzvprintf`

The transparent writer of the borrowed-error regression after `gzopen("p", "wT")` and `gzbuffer(8)`, moved to
`GZ_OFF_MAX`. -/

def writerState : GzState := { smallState with x := { smallState.x with pos := GZ_OFF_MAX } }

def writerHeap (statics : Statics) : Heap :=
  { openedHeap statics with gzstates := upd (openedHeap statics).gzstates 2 (some writerState) }

set_option maxRecDepth 20000 in
/-- `gzwrite(file, "p", 1)` at `GZ_OFF_MAX`: `gz_write` refuses the byte and returns 0. -/
theorem gzwrite_refused (statics : Statics) :
    ∃ fs' after, gzwrite (some (.in_gzstate_x 2)) (.ref (.blk 0) 0) 1 openedFs (writerHeap statics) =
      .ok ((0, fs'), after) ∧ Refused after := by
  have e : gzwrite (some (.in_gzstate_x 2)) (.ref (.blk 0) 0) 1 openedFs (writerHeap statics) =
      gzwrite (some (.in_gzstate_x 2)) (.ref (.blk 0) 0) 1 openedFs (writerHeap statics) := rfl
  conv at e => rhs; cbv
  exact ⟨_, _, e, _, _, rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 20000 in
/-- `gzprintf(file, "p")` at `GZ_OFF_MAX`: `gzvprintf` formats one byte, refuses it, and returns `Z_DATA_ERROR`. -/
theorem gzprintf_refused (statics : Statics) :
    ∃ fs' after, gzprintf (some (.in_gzstate_x 2)) (.ref (.blk 0) 0) [] openedFs (writerHeap statics) =
      .ok ((Z_DATA_ERROR, fs'), after) ∧ Refused after := by
  have e : gzprintf (some (.in_gzstate_x 2)) (.ref (.blk 0) 0) [] openedFs (writerHeap statics) =
      gzprintf (some (.in_gzstate_x 2)) (.ref (.blk 0) 0) [] openedFs (writerHeap statics) := rfl
  conv at e => rhs; cbv
  exact ⟨_, _, e, _, _, rfl, rfl, rfl, rfl⟩

#print axioms position_overflow_literal
#print axioms gzread_refused
#print axioms gzgets_refused
#print axioms gzwrite_refused
#print axioms gzprintf_refused

end Zlib.Gz.PositionOverflowRegression
