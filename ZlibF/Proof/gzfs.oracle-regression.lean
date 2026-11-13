import ZlibF.Proof.«gzwrite.c.borrowed-error-regression»

/-!
# gzfs: the OS-call oracle is live inside the proved domain

One checked execution per system call shows a behaviour the regular-file model cannot produce and the C can
meet: an `open` that fails or returns a chosen descriptor number, a `read` that fails with an errno glibc does not
know, an `lseek` that returns a value unrelated to the file, a nonempty `write` that succeeds where the regular file
is full, and a `close` that reports an error but releases the descriptor. Every world here is admitted by
`FileSystem` (the oracle fields are not constrained), so each execution lies inside the domain the gz goals
quantify over. These are regressions, not proofs of the goals.
-/

namespace Zlib.GzFs.OracleRegression
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib Zlib.Gzread Zlib.Gzwrite
open Zlib.Gzwrite.BorrowRegression

/-! ## open (M5) -/

/-- The writer world of the borrowed-error regression, with the first `open` failing with `EACCES`. -/
def openFailFs : Fs := { initialFs with openFail := fun n => if n = 0 then some 13 else none }

set_option maxRecDepth 20000 in
/-- `gzopen("p", "wT")` returns NULL when `open` fails, with errno `EACCES` and no descriptor opened. -/
theorem open_fails (statics : Statics) :
    ∃ fs' after, gzopen (.ref (.blk 0) 0) (.ref (.blk 1) 0) openFailFs (callerHeap statics) =
      .ok ((none, fs'), after) ∧ fs'.errno = 13 ∧ fs'.fds = #[] := by
  have e : gzopen (.ref (.blk 0) 0) (.ref (.blk 1) 0) openFailFs (callerHeap statics) =
      gzopen (.ref (.blk 0) 0) (.ref (.blk 1) 0) openFailFs (callerHeap statics) := rfl
  conv at e => rhs; cbv
  exact ⟨_, _, e, rfl, rfl⟩

/-- The same world, with the first `open` returning descriptor 1000. -/
def openFdFs : Fs := { initialFs with openFd := fun n => if n = 0 then some 1000 else none }

set_option maxRecDepth 20000 in
/-- `gzopen("p", "wT")` keeps the descriptor number the system chose (1000, not the lowest free one). -/
theorem open_chosen_fd (statics : Statics) :
    ∃ fs' after, gzopen (.ref (.blk 0) 0) (.ref (.blk 1) 0) openFdFs (callerHeap statics) =
      .ok ((some (.in_gzstate_x 2), fs'), after) ∧ (after.gzstates 2).map (·.fd) = some 1000 := by
  have e : gzopen (.ref (.blk 0) 0) (.ref (.blk 1) 0) openFdFs (callerHeap statics) =
      gzopen (.ref (.blk 0) 0) (.ref (.blk 1) 0) openFdFs (callerHeap statics) := rfl
  conv at e => rhs; cbv
  exact ⟨_, _, e, rfl⟩

/-! ## write (M2) and close (M4) -/

/-- The world after the open of the borrowed-error regression (a full file: `fsizeLimit = 0`), with every
`write` accepting one byte. -/
def countFs : Fs := { openedFs with writeChoice := fun _ => .count 1 }

set_option maxRecDepth 20000 in
/-- On a full file the regular `write` fails with `EFBIG` (`actual_close` returns `Z_ERRNO`); a `write` that
succeeds anyway lets `gzclose_w` finish with `Z_OK`. -/
theorem write_succeeds (statics : Statics) :
    ∃ fs' after, gzclose_w (some (.in_gzstate_x 2)) countFs (writtenHeap statics) =
      .ok ((Z_OK, fs'), after) := by
  have e : gzclose_w (some (.in_gzstate_x 2)) countFs (writtenHeap statics) =
      gzclose_w (some (.in_gzstate_x 2)) countFs (writtenHeap statics) := rfl
  conv at e => rhs; cbv
  exact ⟨_, _, e⟩

/-- As `countFs`, with every `close` reporting `EIO`. -/
def closeFailFs : Fs := { countFs with closeFail := fun _ => some 5 }

set_option maxRecDepth 20000 in
/-- `gzclose_w` reports `Z_ERRNO` when `close` fails, and the descriptor is released anyway. -/
theorem close_fails_releases (statics : Statics) :
    ∃ fs' after, gzclose_w (some (.in_gzstate_x 2)) closeFailFs (writtenHeap statics) =
      .ok ((Z_ERRNO, fs'), after) ∧ fs'.fds[3]? = some none ∧ fs'.errno = 5 := by
  have e : gzclose_w (some (.in_gzstate_x 2)) closeFailFs (writtenHeap statics) =
      gzclose_w (some (.in_gzstate_x 2)) closeFailFs (writtenHeap statics) := rfl
  conv at e => rhs; cbv
  exact ⟨_, _, e, rfl, rfl⟩

/-! ## lseek (M3) and read (M1) -/

/-- Caller memory for a reader: the path `"p"`, the mode `"r"` and a 4-byte read buffer. -/
def readerCallerHeap (statics : Statics) : Heap :=
  { Heap.empty with bytes := ⟨#[some #[112, 0], some #[114, 0], some #[0, 0, 0, 0]]⟩
                    nextBlk := 3, static := statics }

/-- A world with the file `p` holding `"hi"`. -/
def readerFs : Fs := ({} : Fs).put #[112] #[104, 105]

/-- The reader's `lseek(fd, 0, SEEK_CUR)` (call 1, after the `open`) returns 77 without moving. -/
def lseekValueFs : Fs := { readerFs with lseekChoice := fun n => if n = 1 then .value 77 else .regular }

set_option maxRecDepth 20000 in
/-- `gzopen("p", "r")` records the start position `lseek` reported (77), though the descriptor is at 0. -/
theorem lseek_value (statics : Statics) :
    ∃ fs' after, gzopen (.ref (.blk 0) 0) (.ref (.blk 1) 0) lseekValueFs (readerCallerHeap statics) =
      .ok ((some (.in_gzstate_x 3), fs'), after) ∧ (after.gzstates 3).map (·.start) = some 77 := by
  have e : gzopen (.ref (.blk 0) 0) (.ref (.blk 1) 0) lseekValueFs (readerCallerHeap statics) =
      gzopen (.ref (.blk 0) 0) (.ref (.blk 1) 0) lseekValueFs (readerCallerHeap statics) := rfl
  conv at e => rhs; cbv
  exact ⟨_, _, e, rfl⟩

/-- The first `read` (call 2) fails with errno 1000, a number glibc does not know. -/
def readFailFs : Fs := { readerFs with readChoice := fun n => if n = 2 then .fail 1000 else .regular }

set_option maxRecDepth 20000 in
/-- On the reader just opened, `gz_load` (the function of `gzread.c` that calls `read`) reports the failing read:
it returns -1 with nothing read and records `Z_ERRNO` (the message is `"p: Unknown error 1000"`, the text glibc
gives). -/
theorem read_fails (statics : Statics) :
    ∃ fs' after,
      (do let file ← gzopen (.ref (.blk 0) 0) (.ref (.blk 1) 0)
          gz_load (castState file) (.ref (.blk 2) 0) 4) readFailFs (readerCallerHeap statics) =
        .ok (((-1, 0), fs'), after) ∧ (after.gzstates 3).map (·.err) = some Z_ERRNO := by
  have e : (do let file ← gzopen (.ref (.blk 0) 0) (.ref (.blk 1) 0)
               gz_load (castState file) (.ref (.blk 2) 0) 4) readFailFs (readerCallerHeap statics) =
      (do let file ← gzopen (.ref (.blk 0) 0) (.ref (.blk 1) 0)
          gz_load (castState file) (.ref (.blk 2) 0) 4) readFailFs (readerCallerHeap statics) := rfl
  conv at e => rhs; cbv
  exact ⟨_, _, e, rfl⟩

#print axioms open_fails
#print axioms open_chosen_fd
#print axioms write_succeeds
#print axioms close_fails_releases
#print axioms lseek_value
#print axioms read_fails
end Zlib.GzFs.OracleRegression
