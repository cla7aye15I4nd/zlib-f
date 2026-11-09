import ZlibF.Proof.«gzlib.c.error-noescape»
import ZlibF.Proof.«gzfs.borrowed-error»

/-! # The common actual errno-reporting call has a bounded borrow lifetime

Source reading (**to confirm** in each whole-caller proof): the four errno
sites use this adjacent call pair:
strerror, then gz_error. The result below relates their same actual heaps,
keeps the external view readable through the handler, excludes it from the
owned message slot, and invalidates it at the next strerror call. It is a
returning-execution lifetime fact, not a complete caller termination contract.
-/
namespace Zlib.Gzlib.ErrnoLifetime
open C C.LibcBorrow Zlib.Gzguts Zlib.GzFs Zlib.GzFs.Proofs

def errnoHeap (h : Heap) (fs : Fs) : Heap :=
  { h with libcErrorBorrow := some (nextErrorEpoch h, fs.errno) }

def errnoPointer (h : Heap) (fs : Fs) : BPtr :=
  .ref (.str (libcErrnoIndex (nextErrorEpoch h) fs.errno)) 0

private theorem report_bind_app {α β : Type} (m : G α) (f : α → G β) (fs : Fs) (h : Heap) :
    (m >>= f) fs h = match m fs h with
      | .ok ((a, fs1), h1) => f a fs1 h1 | .error e => .error e := by
  simp only [bind, StateT.bind]
  cases he : m fs h with
  | error e => rfl
  | ok result => obtain ⟨⟨a, fs1⟩, h1⟩ := result; rfl

private theorem report_lift_app {α : Type} (m : M α) (fs : Fs) (h : Heap) :
    (StateT.lift m : G α) fs h = match m h with
      | .ok (a, h1) => .ok ((a, fs), h1) | .error e => .error e := rfl

/-- Kernel source identity for the exact adjacent expression used at all four
translated errno sites. No operation intervenes that could invalidate the view. -/
theorem report_source (i : Nat) (h : Heap) (fs : Fs) :
    ((do gz_error (some (.tab i)) Z_ERRNO (← zstrerror)) : G Unit) fs h =
      match gz_error (some (.tab i)) Z_ERRNO (errnoPointer h fs) (errnoHeap h fs) with
      | .error fault => .error fault
      | .ok (v, after) => .ok ((v, fs), after) := by
  rw [report_bind_app, zstrerror_run]
  simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift]
  rw [report_lift_app]
  cases he : gz_error (some (.tab i)) Z_ERRNO (errnoPointer h fs) (errnoHeap h fs)
  all_goals dsimp only [errnoPointer, errnoHeap] at he
  all_goals rw [he]

/-- On every returning execution, the handler has consumed the actual current
borrow without retaining its pointer as an owned message. Both malloc outcomes
are admitted. The next external call, rather than malloc cleanup, ends its life. -/
theorem report_lifetime (i : Nat) (h after : Heap) (fs fs' : Fs) (v : Unit)
    (hr : ((do gz_error (some (.tab i)) Z_ERRNO (← zstrerror)) : G Unit) fs h =
      .ok ((v, fs'), after)) :
    fs' = fs ∧
    after.libcErrorBorrow = some (nextErrorEpoch h, fs.errno) ∧
    Space.get after (BRef.str (libcErrnoIndex (nextErrorEpoch h) fs.errno)) =
      some (strBytes (strerrorText fs.errno)) ∧
    (∀ s, after.gzstates i = some s → s.msg ≠ errnoPointer h fs) ∧
    (∀ nextFs : Fs,
      Space.get { after with libcErrorBorrow := some (nextErrorEpoch after, nextFs.errno) }
        (BRef.str (libcErrnoIndex (nextErrorEpoch h) fs.errno)) = none) := by
  rw [report_source] at hr
  cases he : gz_error (some (.tab i)) Z_ERRNO (errnoPointer h fs) (errnoHeap h fs) with
  | error fault => simp [he] at hr
  | ok result =>
    rcases result with ⟨value, final⟩
    rw [he] at hr
    cases hr
    have hb := gz_error_borrow_stable (some (.tab i)) Z_ERRNO (errnoPointer h fs)
      (errnoHeap h fs) v after he
    refine ⟨rfl, hb, ?_, ?_, ?_⟩
    · exact (current_view after (nextErrorEpoch h) fs.errno hb).1
    · intro s hs
      exact gz_error_message_not_str i Z_ERRNO (errnoPointer h fs) (errnoHeap h fs)
        after v he s hs _ _
    · intro nextFs
      exact zstrerror_invalidates_old after (nextErrorEpoch h) fs.errno nextFs hb

#print axioms report_source
#print axioms report_lifetime
end Zlib.Gzlib.ErrnoLifetime
