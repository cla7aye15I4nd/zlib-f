import ZlibF.Zlib.«gzwrite.c»
import ZlibF.Proof.«gzlib.c.base»
import ZlibF.Proof.«gzlib.c.errno-call-lifetime»
import ZlibF.Spec.Public.GzState
import ZlibF.Proof.«gzfs.oracle»
import ZlibF.Spec.Functional.Api.Compress

/-! # Compressed pending output reaches the real errno handler

This internal branch starts with one cached output byte, a live initialized
buffer, reset zero, an invalid modeled descriptor, and the regular branch of the write oracle. It returns from the
actual nested loops before deflate is called. Initialization/history production
and arbitrary cached-output lengths are separate obligations, not public API
restrictions. No deflate contract is assumed.
-/
namespace Zlib.Gzwrite.CompErrno
open C C.LibcBorrow Zlib.Gzguts Zlib.GzFs Zlib.Gzlib Zlib.Gzwrite
open Zlib.Gzlib.Spec Zlib.Gzlib.Proofs Zlib.Gzlib.ErrnoLifetime

private theorem comp_bind_app {α β : Type} (m : G α) (f : α → G β) (fs : Fs) (h : Heap) :
    (m >>= f) fs h = match m fs h with
      | .ok ((a, fs1), h1) => f a fs1 h1 | .error e => .error e := by
  simp only [bind, StateT.bind]
  cases he : m fs h with
  | error e => rfl
  | ok result => obtain ⟨⟨a, fs1⟩, h1⟩ := result; rfl

private theorem comp_lift_app {α : Type} (m : M α) (fs : Fs) (h : Heap) :
    (StateT.lift m : G α) fs h = match m h with
      | .ok (a, h1) => .ok ((a, fs), h1) | .error e => .error e := rfl

private theorem comp_pure_app {α : Type} (a : α) (fs : Fs) (h : Heap) :
    (pure a : G α) fs h = .ok ((a, fs), h) := rfl

macro "comperr_simp" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift,
    comp_bind_app, comp_pure_app, comp_lift_app, bind_app, pure_app,
    ldS_eq, updS_eq, updX_eq, ldZ_eq, updZ_eq, $ts,*])

private def outputSlice (a : Array UInt8) (n : Nat) : Array UInt8 :=
  (List.range' 0 n).foldl (fun out i => out.push a[i]!) #[]

private theorem loadList_run {h : Heap} {r : BRef} {a : Array UInt8}
    (ha : Space.get h r = some a) (xs : List Nat)
    (hb : ∀ i ∈ xs, i < a.size) (out : Array UInt8) :
    (forIn' xs out (fun (i : Nat) _ (out : Array UInt8) => do
      let v ← index8 (.ref r 0) (i : Int)
      pure (ForInStep.yield (out.push v)))) h =
      .ok (xs.foldl (fun out i => out.push a[i]!) out, h) := by
  induction xs generalizing out with
  | nil => rfl
  | cons i xs ih =>
    have hi : index8 (.ref r 0) i h = .ok (a[i]!, h) := by
      rw [getElem!_pos a i (hb i (by simp))]
      simpa [OkOn] using Ptr.index_ok (off := 0) (i := i) ha (by simpa using hb i (by simp))
    simp only [List.forIn'_cons, bind_app, hi, pure_app, List.foldl_cons]
    exact ih (fun j hj => hb j (by simp [hj])) _

private theorem loadBytes_slice {h : Heap} {r : BRef} {a : Array UInt8} {n : Nat}
    (ha : Space.get h r = some a) (hb : n ≤ a.size) :
    loadBytes (.ref r 0) n h = .ok (outputSlice a n, h) := by
  unfold loadBytes
  simp only [forIn, Std.Legacy.Range.forIn'_eq_forIn'_range', Std.Legacy.Range.size]
  have hr : ∀ i ∈ List.range' 0 n, i < a.size := by
    intro i hi
    simp only [List.mem_range'] at hi
    omega
  simp only [Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  rw [bind_app, loadList_run ha _ hr]
  rfl

private theorem fsWriteReg_invalid (fs : Fs) (fd : Int32) (bs : Array UInt8) (h : Heap)
    (hfd : fd < 0 ∨ (fs.fds.size : Int) ≤ fd.toInt) :
    fsWriteReg fd bs fs h = .ok ((-1, { fs with errno := EBADF }), h) := by
  rcases hfd with hn | hs
  · simp [fsWriteReg, hn, pure_app]
  · simp [fsWriteReg, hs, pure_app]

private theorem fsWrite_invalid (fs : Fs) (fd : Int32) (bs : Array UInt8) (h : Heap)
    (hc : fs.writeChoice fs.nos = .regular) (hfd : fd < 0 ∨ (fs.fds.size : Int) ≤ fd.toInt) :
    fsWrite fd bs fs h = .ok ((-1, { tickW fs with errno := EBADF }), h) := by
  have reg := fsWriteReg_invalid (tickW fs) fd bs h hfd
  unfold fsWrite
  dsimp only
  rw [hc]
  simp only [bind_app, reg, pure_app, ite_true]

def pendingReport (i : Nat) : G Int32 := do
  gz_error (some (.tab i)) Z_ERRNO (← zstrerror)
  return -1

/-- The actual compressed-output branch reaches its distinct strerror site,
then exits both loops without calling deflate or consuming cached bytes.
The RHS executes the real handler; no handler-success contract is a premise. -/
theorem gz_comp_cached_one_badfd_source {h : Heap} {i b : Nat} {s : GzState} {a : Array UInt8}
    (hs : h.gzstates i = some s) (hsize : s.size ≠ 0) (hdir : s.direct = 0)
    (hreset : s.reset = 0) (hav : s.strm.avail_out = 0)
    (hx : s.x.next = .ref (.blk b) 0) (hz : s.strm.next_out = .ref (.blk b) 1)
    (hbytes : h.bytes b = some a) (hfit : 1 ≤ a.size)
    (fs : Fs) (hc : fs.writeChoice fs.nos = .regular) (hfd : s.fd < 0 ∨ (fs.fds.size : Int) ≤ s.fd.toInt)
    (flush : Int32) :
    gz_comp (some (.tab i)) flush fs h =
      pendingReport i { tickW fs with errno := EBADF } (setS h i { s with again := 0 }) := by
  let h1 := setS h i { s with again := 0 }
  have hload : loadBytes (.ref (.blk b) 0) 1 h1 = .ok (outputSlice a 1, h1) :=
    loadBytes_slice (show Space.get h1 (BRef.blk b) = some a from hbytes) hfit
  have hlt : Ptr.lt (Ptr.ref (BRef.blk b) 0) (.ref (.blk b) 1) h = .ok (true, h) := by
    simp [Ptr.lt, hbytes, hfit]
  have hdiff : Ptr.diff (Ptr.ref (BRef.blk b) 1) (.ref (.blk b) 0) h1 = .ok (1, h1) := by
    simp [Ptr.diff, hbytes, h1, hfit]
  have hw := fsWrite_invalid { fs with errno := 0 } s.fd (outputSlice a 1) h1 hc hfd
  have hset (w : Fs) (hh : Heap) : setErrno 0 w hh = .ok (((), { w with errno := 0 }), hh) := rfl
  have hget (w : Fs) (hh : Heap) : getErrno w hh = .ok ((w.errno, w), hh) := rfl
  have hwide : (1 : Int64).toUInt64 = 1 := by decide
  unfold gz_comp
  comperr_simp [hs, hsize]
  simp only [ite_eq_left hdir]
  comperr_simp [hs]
  simp only [ite_eq_left hreset]
  comperr_simp [hs]
  rw [gdoWhile]
  rw [show fuel = 18446744073709551615 + 1 by decide, gdoWhile.go]
  comperr_simp [hs, hav]
  rw [gwhile]
  rw [show fuel = 18446744073709551615 + 1 by decide, gwhile.go]
  comperr_simp [hs, hx, hz, hlt, hset, hget, hdiff, h1, hload, hw, hwide, BLOCKED, EBADF, EAGAIN, pendingReport, Zlib.GzFs.Proofs.zstrerror_run]
  cases he : gz_error (some (.tab i)) Z_ERRNO (errnoPointer h1 { tickW fs with errno := EBADF })
      (errnoHeap h1 { tickW fs with errno := EBADF }) with
  | error e =>
    dsimp only [errnoPointer, errnoHeap, h1, setS, EBADF] at he ⊢
    rw [he]
  | ok result =>
    rcases result with ⟨v, final⟩
    cases v
    dsimp only [errnoPointer, errnoHeap, h1, setS, EBADF] at he ⊢
    rw [he]
    dsimp only
    rw [gwhile.go.eq_def]
    rfl

/-- Exact actual handler continuation, after errno was set by fsWrite. -/
theorem pending_report_source (i : Nat) (h : Heap) (fs : Fs) :
    pendingReport i fs h = match gz_error (some (.tab i)) Z_ERRNO (errnoPointer h fs) (errnoHeap h fs) with
      | .error e => .error e
      | .ok (_, after) => .ok ((-1, fs), after) := by
  unfold pendingReport
  simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift,
    comp_bind_app, comp_lift_app, comp_pure_app, Zlib.GzFs.Proofs.zstrerror_run]
  cases he : gz_error (some (.tab i)) Z_ERRNO (errnoPointer h fs) (errnoHeap h fs)
  all_goals dsimp only [errnoPointer, errnoHeap] at he
  all_goals rw [he]

/-- No buffer is consumed before the error handler. The actual prefix changes
only the gzip record's again field; final message-allocation accounting is separate. -/
theorem pending_prefix_frame (h : Heap) (i : Nat) (s : GzState) :
    ZlibF.Spec.Public.Frame h (setS h i { s with again := 0 }) (fun b => b = i) := by
  refine ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, ?_⟩
  intro b _ hb
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, by simp [setS, upd_ne _ _ _ _ hb], rfl⟩

theorem pending_prefix_live (h : Heap) (i : Nat) (s : GzState) (hs : h.gzstates i = some s) :
    ZlibF.Spec.Public.LiveChange h (setS h i { s with again := 0 }) (fun _ => False) (fun _ => False) := by
  intro b
  simpa [ZlibF.Spec.Public.LiveChange] using
    (Shape.live (shape_setS hs { s with again := 0 }) b)

/-- The same complete compressed-branch execution produces the current borrowed
view and cannot retain it in msg. A subsequent strerror invalidates that view.
This returning-execution theorem assumes no callee contract. -/
theorem gz_comp_cached_one_badfd_lifetime {h after : Heap} {i b : Nat} {s : GzState} {a : Array UInt8}
    (hs : h.gzstates i = some s) (hsize : s.size ≠ 0) (hdir : s.direct = 0)
    (hreset : s.reset = 0) (hav : s.strm.avail_out = 0)
    (hx : s.x.next = .ref (.blk b) 0) (hz : s.strm.next_out = .ref (.blk b) 1)
    (hbytes : h.bytes b = some a) (hfit : 1 ≤ a.size)
    (fs fs' : Fs) (hc : fs.writeChoice fs.nos = .regular) (hfd : s.fd < 0 ∨ (fs.fds.size : Int) ≤ s.fd.toInt)
    (flush rc : Int32)
    (run : gz_comp (some (.tab i)) flush fs h = .ok ((rc, fs'), after)) :
    rc = -1 ∧ fs' = { tickW fs with errno := EBADF } ∧
    after.libcErrorBorrow = some (Zlib.GzFs.Proofs.nextErrorEpoch h, EBADF) ∧
    Space.get after (BRef.str (libcErrnoIndex (Zlib.GzFs.Proofs.nextErrorEpoch h) EBADF)) =
      some (strBytes (strerrorText EBADF)) ∧
    (∀ final, after.gzstates i = some final →
      final.msg ≠ errnoPointer h { tickW fs with errno := EBADF }) ∧
    (∀ nextFs : Fs,
      Space.get { after with libcErrorBorrow := some (Zlib.GzFs.Proofs.nextErrorEpoch after, nextFs.errno) }
        (BRef.str (libcErrnoIndex (Zlib.GzFs.Proofs.nextErrorEpoch h) EBADF)) = none) := by
  rw [gz_comp_cached_one_badfd_source hs hsize hdir hreset hav hx hz hbytes hfit fs hc hfd flush,
    pending_report_source] at run
  let prepared :=  setS h i { s with again := 0 }
  cases he : gz_error (some (.tab i)) Z_ERRNO
      (errnoPointer prepared { tickW fs with errno := EBADF }) (errnoHeap prepared { tickW fs with errno := EBADF }) with
  | error e => simp only [prepared] at he; rw [he] at run; contradiction
  | ok result =>
    rcases result with ⟨v, final⟩
    simp only [prepared] at he
    rw [he] at run
    cases run
    have hreport : ((do gz_error (some (.tab i)) Z_ERRNO (← zstrerror)) : G Unit)
        { tickW fs with errno := EBADF } prepared = .ok ((v, { tickW fs with errno := EBADF }), after) := by
      rw [report_source]
      dsimp only [prepared]
      rw [he]
    have life := report_lifetime i prepared after { tickW fs with errno := EBADF } { tickW fs with errno := EBADF } v hreport
    exact ⟨rfl, life⟩

#print axioms gz_comp_cached_one_badfd_source
#print axioms gz_comp_cached_one_badfd_lifetime
#print axioms pending_prefix_frame
#print axioms pending_prefix_live
end Zlib.Gzwrite.CompErrno
