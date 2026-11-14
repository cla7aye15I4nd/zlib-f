import ZlibF.Zlib.«gzread.c»
import ZlibF.Proof.«gzlib.c.base»
import ZlibF.Proof.«gzlib.c.errno-call-lifetime»
import ZlibF.Spec.Public.GzState
import ZlibF.Spec.Functional.Api.Compress

/-! # gzread's deferred errno report on the zero-length retry path

This is an explicit internal execution domain: mode READ, again nonzero,
no old message, and len zero. The fixed external model never emits EAGAIN,
so no initialized public-history producer for again nonzero is claimed here.
The public goal is unchanged. No inflate or callee contract is assumed.
-/
namespace Zlib.Gzread.ErrnoRetry
open C C.LibcBorrow Zlib.Gzguts Zlib.GzFs Zlib.Gzlib Zlib.Gzread
open Zlib.Gzlib.Spec Zlib.Gzlib.Proofs Zlib.Gzlib.ErrnoLifetime

private theorem retry_bind_app {α β : Type} (m : G α) (f : α → G β) (fs : Fs) (h : Heap) :
    (m >>= f) fs h = match m fs h with
      | .ok ((a, fs1), h1) => f a fs1 h1 | .error e => .error e := by
  simp only [bind, StateT.bind]
  cases he : m fs h with
  | error e => rfl
  | ok result => obtain ⟨⟨a, fs1⟩, h1⟩ := result; rfl

private theorem retry_lift_app {α : Type} (m : M α) (fs : Fs) (h : Heap) :
    (StateT.lift m : G α) fs h = match m h with
      | .ok (a, h1) => .ok ((a, fs), h1) | .error e => .error e := rfl

private theorem retry_pure_app {α : Type} (a : α) (fs : Fs) (h : Heap) :
    (pure a : G α) fs h = .ok ((a, fs), h) := rfl

def clearRetryHeap (h : Heap) (i : Nat) (s : GzState) : Heap :=
  setS h i { s with err := Z_OK }

def retryReport (i : Nat) : G Int32 := do
  gz_error (some (.tab i)) Z_ERRNO (← zstrerror)
  return -1

private theorem clear_error (h : Heap) (i : Nat) (s : GzState)
    (hs : h.gzstates i = some s) (hm : s.msg = .null) :
    gz_error (some (.tab i)) Z_OK .null h = .ok ((), clearRetryHeap h i s) := by
  simp [gz_error, bind_app, ldS_eq, updS_eq, hs, hm, clearRetryHeap]

private theorem read_zero (i : Nat) (buf : BPtr) :
    gz_read (some (.tab i)) buf 0 = (pure 0 : G UInt64) := rfl

/-- The actual complete public wrapper reaches its fourth errno call site.
The same heap is threaded through clear, zero-length gz_read, and report. -/
theorem gzread_zero_retry_source (h : Heap) (fs : Fs) (i : Nat) (s : GzState) (buf : BPtr)
    (hs : h.gzstates i = some s) (hr : s.mode = GZ_READ)
    (ha : s.again ≠ 0) (hm : s.msg = .null) :
    gzread (some (.in_gzstate_x i)) buf 0 fs h =
      retryReport i fs (clearRetryHeap h i s) := by
  have hc : castState (some (.in_gzstate_x i)) = some (.tab i) := rfl
  unfold gzread
  simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift,
    retry_bind_app, retry_lift_app, retry_pure_app, hc,
    Option.isNone_some, Bool.false_eq_true, ite_false, ldS_eq, hs]
  have hagain : (s.again != 0) = true := by simp [ha]
  have hnotagain : (s.again == 0) = false := by simp [ha]
  have hzero : ¬ (0 : UInt32).toInt32 < 0 := by decide
  have hwiden : (0 : UInt32).toUInt64 = 0 := rfl
  simp only [hr, bne_self_eq_false, hagain, hnotagain, Bool.and_false,
    Bool.false_and, Bool.false_eq_true, ite_false, ite_true, hzero, hwiden,
    retry_bind_app, retry_lift_app, retry_pure_app, read_zero]
  rw [clear_error h i s hs hm]
  simp [hr, ha, read_zero, retryReport, liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift,
    retry_bind_app, retry_lift_app, retry_pure_app, clearRetryHeap, ldS_eq,
    setS_gz_same, Z_OK, Z_BUF_ERROR]

/-- Exact continuation after the complete wrapper's actual clear/read prefix. -/
theorem retry_report_source (i : Nat) (h : Heap) (fs : Fs) :
    retryReport i fs h = match gz_error (some (.tab i)) Z_ERRNO (errnoPointer h fs) (errnoHeap h fs) with
      | .error e => .error e
      | .ok (_, after) => .ok ((-1, fs), after) := by
  unfold retryReport
  simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift,
    retry_bind_app, retry_lift_app, retry_pure_app, Zlib.GzFs.Proofs.zstrerror_run]
  cases he : gz_error (some (.tab i)) Z_ERRNO (errnoPointer h fs) (errnoHeap h fs)
  all_goals dsimp only [errnoPointer, errnoHeap] at he
  all_goals rw [he]

/-- The real prefix keeps every original allocation and changes only the
handle record. The error handler's subsequent allocation ledger is separate. -/
theorem clear_retry_frame (h : Heap) (i : Nat) (s : GzState) :
    ZlibF.Spec.Public.Frame h (clearRetryHeap h i s) (fun b => b = i) := by
  refine ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, ?_⟩
  intro b _ hb
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, by simp [clearRetryHeap, setS, upd_ne _ _ _ _ hb], rfl⟩

theorem clear_retry_live (h : Heap) (i : Nat) (s : GzState) (hs : h.gzstates i = some s) :
    ZlibF.Spec.Public.LiveChange h (clearRetryHeap h i s) (fun _ => False) (fun _ => False) := by
  intro b
  simpa [ZlibF.Spec.Public.LiveChange, clearRetryHeap] using
    (Shape.live (shape_setS hs { s with err := Z_OK }) b)

/-- Borrow observations come from the same complete actual wrapper execution.
This is a returning-execution property on the stated internal branch, not an
unproved caller contract or an initialized-public-history claim. -/
theorem gzread_zero_retry_lifetime (h after : Heap) (fs fs' : Fs) (i : Nat)
    (s : GzState) (buf : BPtr) (rc : Int32) (hs : h.gzstates i = some s)
    (hr : s.mode = GZ_READ) (ha : s.again ≠ 0) (hm : s.msg = .null)
    (run : gzread (some (.in_gzstate_x i)) buf 0 fs h = .ok ((rc, fs'), after)) :
    rc = -1 ∧ fs' = fs ∧
    after.libcErrorBorrow = some (Zlib.GzFs.Proofs.nextErrorEpoch h, fs.errno) ∧
    Space.get after (BRef.str (libcErrnoIndex (Zlib.GzFs.Proofs.nextErrorEpoch h) fs.errno)) =
      some (strBytes (strerrorText fs.errno)) ∧
    (∀ final, after.gzstates i = some final → final.msg ≠ errnoPointer h fs) ∧
    (∀ nextFs : Fs,
      Space.get { after with libcErrorBorrow := some (Zlib.GzFs.Proofs.nextErrorEpoch after, nextFs.errno) }
        (BRef.str (libcErrnoIndex (Zlib.GzFs.Proofs.nextErrorEpoch h) fs.errno)) = none) := by
  rw [gzread_zero_retry_source h fs i s buf hs hr ha hm, retry_report_source] at run
  cases he : gz_error (some (.tab i)) Z_ERRNO
      (errnoPointer (clearRetryHeap h i s) fs) (errnoHeap (clearRetryHeap h i s) fs) with
  | error e => simp [he] at run
  | ok result =>
    rcases result with ⟨v, final⟩
    rw [he] at run
    cases run
    have hreport : ((do gz_error (some (.tab i)) Z_ERRNO (← zstrerror)) : G Unit)
        fs (clearRetryHeap h i s) = .ok ((v, fs), after) := by
      rw [report_source, he]
    have life := report_lifetime i (clearRetryHeap h i s) after fs fs v hreport
    exact ⟨rfl, life⟩

#print axioms gzread_zero_retry_source
#print axioms gzread_zero_retry_lifetime
#print axioms clear_retry_frame
#print axioms clear_retry_live
end Zlib.Gzread.ErrnoRetry
