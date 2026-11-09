import ZlibF.Zlib.«gzread.c»
import ZlibF.Proof.«gzlib.c.base»
import ZlibF.Proof.«gzlib.c.errno-call-lifetime»
import ZlibF.Spec.Public.GzState

/-!
# gzread.c: real first-read failure and synchronous errno lifetime

The fixed OS model produces EBADF or EISDIR here, never EAGAIN. The complete
actual gz_load run reaches its adjacent strerror/gz_error pair after its actual
first read fails. Prefix allocation accounting is separate from the handler's
subsequent owned-message allocation; it is not reported as a final frame.
-/
namespace Zlib.Gzread.LoadErrno
open C C.LibcBorrow Zlib.Gzguts Zlib.GzFs Zlib.Gzlib Zlib.Gzread
open Zlib.Gzlib.Spec Zlib.Gzlib.Proofs Zlib.Gzlib.ErrnoLifetime

/-- The actual external read's failure branches, including an existing
unreadable descriptor and a directory. This is an internal branch predicate. -/
def ReadRefusal (fd : Int32) (fs : Fs) (e : Int32) : Prop :=
  if fd < 0 ∨ fd.toInt ≥ fs.fds.size then e = EBADF
  else match fs.fds[fd.toInt.toNat]! with
    | none => e = EBADF
    | some f => if f.rd = false then e = EBADF
      else fs.nodes[f.node]!.isDir = true ∧ e = EISDIR

/-- Every refusal is computed by the actual fsRead implementation and changes
only errno. No abstract OS or library callee contract is supplied by callers. -/
theorem fsRead_refusal (h : Heap) (fs : Fs) (fd : Int32) (n : UInt64) (e : Int32)
    (hr : ReadRefusal fd fs e) :
    fsRead fd n fs h = .ok (((-1, #[]), {fs with errno := e}), h) := by
  unfold ReadRefusal at hr
  unfold fsRead
  by_cases hb : fd < 0 ∨ fd.toInt ≥ fs.fds.size
  · simp [hb] at hr
    subst e
    simp [hb, Bool.or_eq_true, decide_eq_true_eq]
  · simp only [hb, ite_false] at hr
    simp only [Bool.or_eq_true, decide_eq_true_eq, hb, ite_false]
    split at hr
    · subst e; simp_all
    · split at hr
      · subst e
        simp_all
      · rcases hr with ⟨hd, rfl⟩
        simp_all

theorem ReadRefusal.not_blocked {fd : Int32} {fs : Fs} {e : Int32}
    (hr : ReadRefusal fd fs e) : BLOCKED e = false := by
  unfold ReadRefusal at hr
  split at hr
  · subst e; decide
  · split at hr
    · subst e; decide
    · split at hr
      · subst e; decide
      · rw [hr.2]; decide

/-- The actual only record write before the external read. -/
def loadPrefixHeap (h : Heap) (i : Nat) (s : GzState) : Heap :=
  setS h i {s with again := 0}

def loadReport (i : Nat) : G (Int32 × UInt32) := do
  gz_error (some (.tab i)) Z_ERRNO (← zstrerror)
  return (-1, 0)

private theorem load_bind_app {α β : Type} (m : G α) (f : α → G β) (fs : Fs) (h : Heap) :
    (m >>= f) fs h = match m fs h with
      | .ok ((a, fs1), h1) => f a fs1 h1 | .error e => .error e := by
  simp only [bind, StateT.bind]
  cases he : m fs h with
  | error e => rfl
  | ok result => obtain ⟨⟨a, fs1⟩, h1⟩ := result; rfl

private theorem load_lift_app {α : Type} (m : M α) (fs : Fs) (h : Heap) :
    (StateT.lift m : G α) fs h = match m h with
      | .ok (a, h1) => .ok ((a, fs), h1) | .error e => .error e := rfl

private theorem load_pure_app {α : Type} (a : α) (fs : Fs) (h : Heap) :
    (pure a : G α) fs h = .ok ((a, fs), h) := rfl

private theorem setErrno_app (e : Int32) (fs : Fs) (h : Heap) :
    setErrno e fs h = .ok (((), {fs with errno := e}), h) := rfl

private theorem getErrno_app (fs : Fs) (h : Heap) :
    getErrno fs h = .ok ((fs.errno, fs), h) := rfl

private theorem bytes_loadPrefix (h : Heap) (i : Nat) (s : GzState) (r : BRef) :
    Space.get (loadPrefixHeap h i s) r = Space.get h r := by cases r <;> rfl

/-- Whole actual function, not just its error cut: clear again/errno, perform
the real pointer addition/read/store-empty, terminate the first loop trip and
enter the adjacent errno report. No compression/decoder operation is reached. -/
theorem gz_load_refusal_source (h : Heap) (fs : Fs) (i : Nat) (s : GzState)
    (r : BRef) (off : Nat) (a : Array UInt8) (len : UInt32) (e : Int32)
    (hs : h.gzstates i = some s) (ha : Space.get h r = some a) (hb : off ≤ a.size)
    (he : ReadRefusal s.fd fs e) :
    gz_load (some (.tab i)) (.ref r off) len fs h =
      loadReport i {fs with errno := e} (loadPrefixHeap h i s) := by
  have read := fsRead_refusal (loadPrefixHeap h i s) {fs with errno := 0} s.fd
    (if len > (((0 : UInt32) - 1) >>> 2) + 1 then (((0 : UInt32) - 1) >>> 2) + 1 else len).toUInt64 e he
  have ha' := bytes_loadPrefix h i s r |>.trans ha
  dsimp only [loadPrefixHeap] at ha' read
  have hadd : 0 ≤ (off : Int) ∧ (off : Int) ≤ a.size := by omega
  have hmax : (((0 : UInt32) - 1) >>> 2) + 1 = 1073741824 := by decide
  by_cases hcap : len > (1073741824 : UInt32)
  all_goals
    simp only [hmax, hcap, ite_true, ite_false, show (1073741824 : UInt32).toUInt64 = 1073741824 by rfl] at read
    unfold gz_load
    simp only [hmax]
    simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift,
      load_bind_app, load_lift_app, updS_eq, hs]
    unfold gdoWhile
    rw [show fuel = 18446744073709551615 + 1 by rfl, gdoWhile.go]
    simp [hcap, liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift,
      load_bind_app, load_lift_app, load_pure_app, setErrno_app,
      ldS_eq, setS_gz_same, Ptr.add, ha', hadd, read, storeBytes,
      getErrno_app, ReadRefusal.not_blocked he, loadReport]
    rfl
/-- The exact report result exposes the real handler's same execution heap. -/
theorem load_report_source (i : Nat) (h : Heap) (fs : Fs) :
    loadReport i fs h = match gz_error (some (.tab i)) Z_ERRNO (errnoPointer h fs) (errnoHeap h fs) with
      | .error e => .error e
      | .ok (_, after) => .ok (((-1, 0), fs), after) := by
  unfold loadReport
  simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift,
    load_bind_app, load_lift_app, load_pure_app, Zlib.GzFs.Proofs.zstrerror_run]
  cases he : gz_error (some (.tab i)) Z_ERRNO (errnoPointer h fs) (errnoHeap h fs)
  all_goals dsimp only [errnoPointer, errnoHeap] at he
  all_goals rw [he]

/-- A successful whole-call result supplies the actual handler run on its
precisely computed borrow heap. Later frame/ownership composition can use this
execution fact instead of taking a callee specification as a hypothesis. -/
theorem gz_load_refusal_handler_run (h after : Heap) (fs fs' : Fs) (i : Nat) (s : GzState)
    (r : BRef) (off : Nat) (a : Array UInt8) (len : UInt32) (e rc : Int32) (got : UInt32)
    (hs : h.gzstates i = some s) (ha : Space.get h r = some a) (hb : off ≤ a.size)
    (he : ReadRefusal s.fd fs e)
    (run : gz_load (some (.tab i)) (.ref r off) len fs h = .ok (((rc, got), fs'), after)) :
    rc = -1 ∧ got = 0 ∧ fs' = {fs with errno := e} ∧
    ∃ v, gz_error (some (.tab i)) Z_ERRNO
      (errnoPointer (loadPrefixHeap h i s) {fs with errno := e})
      (errnoHeap (loadPrefixHeap h i s) {fs with errno := e}) = .ok (v, after) := by
  rw [gz_load_refusal_source h fs i s r off a len e hs ha hb he, load_report_source] at run
  cases herr : gz_error (some (.tab i)) Z_ERRNO
      (errnoPointer (loadPrefixHeap h i s) {fs with errno := e})
      (errnoHeap (loadPrefixHeap h i s) {fs with errno := e}) with
  | error err => simp [herr] at run
  | ok result =>
    rcases result with ⟨v, final⟩
    rw [herr] at run
    cases run
    exact ⟨rfl, rfl, rfl, v, rfl⟩

/-- The actual pre-report prefix preserves all objects and creates/removes no
allocation. This is explicitly only the prefix, not the final handler frame. -/
theorem load_prefix_frame (h : Heap) (i : Nat) (s : GzState) :
    ZlibF.Spec.Public.Frame h (loadPrefixHeap h i s) (fun b => b = i) := by
  refine ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, ?_⟩
  intro b _ hb
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, by simp [loadPrefixHeap, setS, upd_ne _ _ _ _ hb], rfl⟩

theorem load_prefix_live (h : Heap) (i : Nat) (s : GzState) (hs : h.gzstates i = some s) :
    ZlibF.Spec.Public.LiveChange h (loadPrefixHeap h i s) (fun _ => False) (fun _ => False) := by
  intro b
  simpa [ZlibF.Spec.Public.LiveChange, loadPrefixHeap] using
    Shape.live (shape_setS hs {s with again := 0}) b

/-- Every successful whole-function run on these actual error branches has
consumed the real borrow; no owned message points at it, and the next strerror
invalidates that view. All handler malloc outcomes are included in this fact. -/
theorem gz_load_refusal_lifetime (h after : Heap) (fs fs' : Fs) (i : Nat) (s : GzState)
    (r : BRef) (off : Nat) (a : Array UInt8) (len : UInt32) (e rc : Int32) (got : UInt32)
    (hs : h.gzstates i = some s) (ha : Space.get h r = some a) (hb : off ≤ a.size)
    (he : ReadRefusal s.fd fs e)
    (run : gz_load (some (.tab i)) (.ref r off) len fs h = .ok (((rc, got), fs'), after)) :
    rc = -1 ∧ got = 0 ∧ fs' = {fs with errno := e} ∧
    after.libcErrorBorrow = some (Zlib.GzFs.Proofs.nextErrorEpoch h, e) ∧
    Space.get after (BRef.str (libcErrnoIndex (Zlib.GzFs.Proofs.nextErrorEpoch h) e)) =
      some (strBytes (strerrorText e)) ∧
    (∀ final, after.gzstates i = some final → final.msg ≠ errnoPointer h {fs with errno := e}) ∧
    (∀ nextFs : Fs,
      Space.get {after with libcErrorBorrow := some (Zlib.GzFs.Proofs.nextErrorEpoch after, nextFs.errno)}
        (BRef.str (libcErrnoIndex (Zlib.GzFs.Proofs.nextErrorEpoch h) e)) = none) := by
  rw [gz_load_refusal_source h fs i s r off a len e hs ha hb he, load_report_source] at run
  cases herr : gz_error (some (.tab i)) Z_ERRNO
      (errnoPointer (loadPrefixHeap h i s) {fs with errno := e})
      (errnoHeap (loadPrefixHeap h i s) {fs with errno := e}) with
  | error err => simp [herr] at run
  | ok result =>
    rcases result with ⟨v, final⟩
    rw [herr] at run
    cases run
    have hreport : ((do gz_error (some (.tab i)) Z_ERRNO (← zstrerror)) : G Unit)
        {fs with errno := e} (loadPrefixHeap h i s) = .ok ((v, {fs with errno := e}), after) := by
      rw [report_source, herr]
    have life := report_lifetime i (loadPrefixHeap h i s) after _ _ v hreport
    exact ⟨rfl, rfl, life⟩

#print axioms fsRead_refusal
#print axioms ReadRefusal.not_blocked
#print axioms gz_load_refusal_source
#print axioms gz_load_refusal_handler_run
#print axioms load_prefix_frame
#print axioms load_prefix_live
#print axioms gz_load_refusal_lifetime
end Zlib.Gzread.LoadErrno
