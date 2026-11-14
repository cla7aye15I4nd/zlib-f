import ZlibF.Proof.«gzfs.oracle»

/-!
# open fails with EMFILE when no descriptor below 2^31 is free

A descriptor is a C `int`. Real `open` never returns a number that does not fit; when no number is free it
fails with `EMFILE`. The regular-file `open` of the model took the lowest free slot of its table without a bound,
and `FileSystem` does not bound the table. It then cast the slot to `Int32`, which wraps.

The world below has the file `p` and `2^32` open descriptors, numbers 0 to `2^32 - 1`. The lowest free slot is
`2^32`. The old model opened slot `2^32` and returned its cast, 0: a descriptor that was already open, for another
file description. The model now returns -1 with errno `EMFILE`, and the world is otherwise unchanged: nothing is
opened, created or truncated. These regressions fail if the bound is dropped again.
-/

namespace Zlib.GzFs.OpenEmfileRegression
open C Zlib.GzFs

/-- An open read-only description of node 0. -/
def taken : OFile := { node := 0, pos := 0, rd := true, wr := false, append := false }

/-- The file `p` (empty) and `2^32` open descriptors. -/
def fullFs : Fs :=
  { names := #[(#[112], 0)], nodes := #[{ data := #[], isDir := false }],
    fds := Array.replicate (2 ^ 32) (some taken) }

/-- The slot search returns the table size when every slot from `i` on is taken. -/
theorem lowestFd_go_full (w : Fs) (hall : ∀ j, j < w.fds.size → (w.fds[j]!).isSome = true) :
    ∀ k i, i ≤ w.fds.size → w.fds.size ≤ i + k → lowestFd.go w i k = w.fds.size := by
  intro k
  induction k with
  | zero =>
    intro i h1 h2
    simp only [lowestFd.go]
    omega
  | succ k ih =>
    intro i h1 h2
    by_cases hi : i < w.fds.size
    · have hn : (w.fds[i]!).isNone = false := by
        have hs := hall i hi
        generalize w.fds[i]! = o at hs ⊢
        cases o <;> simp_all
      simp only [lowestFd.go, hi, hn, ite_true, Bool.false_eq_true, ite_false]
      exact ih (i + 1) (by omega) (by omega)
    · simp only [lowestFd.go, hi, ite_false]
      omega

/-- In a world whose table has at least 3 slots, all taken, the lowest free slot is the table size. -/
theorem lowestFd_full (w : Fs) (hall : ∀ j, j < w.fds.size → (w.fds[j]!).isSome = true)
    (h3 : 3 ≤ w.fds.size) : lowestFd w = w.fds.size :=
  lowestFd_go_full w hall (w.fds.size + 3) 3 h3 (by omega)

/-- The regular-file `open` fails with `EMFILE`, and changes nothing else, when the flags and the path pass the
first checks and no slot below `2^31` is free. -/
theorem fsOpenReg_emfile (path : Array UInt8) (oflag : Int32) (w : Fs) (hacc : ¬ (oflag &&& 3 ≥ 2))
    (hp : path.isEmpty = false) (hfd : 2 ^ 31 ≤ lowestFd w) :
    fsOpenReg path oflag w = (pure (-1, { w with errno := EMFILE }) : M (Int32 × Fs)) := by
  unfold fsOpenReg
  dsimp only
  split
  · rename_i h
    exact absurd h hacc
  · split
    · rename_i h
      rw [hp] at h
      contradiction
    · first
        | rfl
        | split
          · rfl
          · rename_i h
            exact absurd hfd h

theorem fullFs_fds : fullFs.fds = Array.replicate (2 ^ 32) (some taken) := rfl

theorem fullFs_all (w : Fs) (hw : w.fds = fullFs.fds) :
    ∀ j, j < w.fds.size → (w.fds[j]!).isSome = true := by
  intro j hj
  rw [hw, fullFs_fds] at hj ⊢
  rw [getElem!_pos (Array.replicate (2 ^ 32) (some taken)) j hj]
  simp

/-- Every descriptor of `fullFs` is open, and the lowest free slot is `2^32`. -/
theorem fullFs_lowest (w : Fs) (hw : w.fds = fullFs.fds) : lowestFd w = 2 ^ 32 := by
  rw [lowestFd_full w (fullFs_all w hw) (by rw [hw, fullFs_fds, Array.size_replicate]; decide), hw,
    fullFs_fds, Array.size_replicate]

/-- The old model: the slot it opened casts to 0, and descriptor 0 was already open. -/
theorem old_result_was_open :
    Int32.ofNat (lowestFd fullFs) = 0 ∧ fullFs.fds[0]? = some (some taken) := by
  rw [fullFs_lowest fullFs rfl, fullFs_fds]
  refine ⟨by decide +kernel, ?_⟩
  simp

/-- The regular-file `open("p", O_RDONLY)` on `fullFs` returns -1 with `EMFILE` and opens nothing. -/
theorem open_full_fails_reg :
    fsOpenReg #[112] 0 fullFs = (pure (-1, { fullFs with errno := EMFILE }) : M (Int32 × Fs)) :=
  fsOpenReg_emfile #[112] 0 fullFs (by decide) rfl (by rw [fullFs_lowest fullFs rfl]; decide)

/-- The same through the OS-call oracle with its regular entries (the defaults of `fullFs`): `open` returns -1,
the descriptor table is unchanged, and errno is `EMFILE`. -/
theorem open_full_fails (h : Heap) :
    fsOpen #[112] 0 fullFs h = .ok ((-1, { tickW fullFs with errno := EMFILE }), h) := by
  rw [Zlib.GzFs.Proofs.fsOpen_regular #[112] 0 fullFs rfl rfl,
    fsOpenReg_emfile #[112] 0 (tickW fullFs) (by decide) rfl
      (by rw [fullFs_lowest (tickW fullFs) rfl]; decide)]
  rfl

#print axioms lowestFd_full
#print axioms fsOpenReg_emfile
#print axioms old_result_was_open
#print axioms open_full_fails_reg
#print axioms open_full_fails
end Zlib.GzFs.OpenEmfileRegression
