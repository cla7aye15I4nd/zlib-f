import ZlibF.Zlib.gzfs
import ZlibF.Proof.LibcBorrow

/-!
# gzfs: the real borrowed error-text result

Borrowed libc storage is metadata outside the malloc live ledger. The actual
call advances one epoch. Other primitives keep it by their actual execution,
not by a stronger public malloc Frame or a restricted caller domain.
-/

namespace Zlib.GzFs.Proofs
open C C.LibcBorrow Zlib.GzFs

def nextErrorEpoch (h : Heap) : Nat :=
  match h.libcErrorBorrow with | none => 1 | some (k, _) => k + 1

/-- Exact result of the actual external call. No heap object is allocated. -/
theorem libcStr_run (h : Heap) (e : Int32) :
    libcStr e h = .ok (.ref (.str (libcErrnoIndex (nextErrorEpoch h) e)) 0,
      { h with libcErrorBorrow := some (nextErrorEpoch h, e) }) := rfl

/-- `strerror` returns the old model's identical text as the currently valid
borrow. It leaves malloc tables, allocator calls and errno untouched. -/
theorem zstrerror_run (h : Heap) (fs : Fs) :
    zstrerror fs h = .ok ((.ref (.str (libcErrnoIndex (nextErrorEpoch h) fs.errno)) 0, fs),
      { h with libcErrorBorrow := some (nextErrorEpoch h, fs.errno) }) := rfl

/-- A returning strerror call keeps every malloc identity, readonly flag,
allocator oracle and allocation count. The borrow itself is not Heap.live. -/
theorem zstrerror_no_malloc (h : Heap) (fs : Fs) :
    let after := { h with libcErrorBorrow := some (nextErrorEpoch h, fs.errno) }
    after.bytes = h.bytes ∧ after.words = h.words ∧ after.streams = h.streams ∧
    after.gzheaders = h.gzheaders ∧ after.dstates = h.dstates ∧ after.istates = h.istates ∧
    after.gzstates = h.gzstates ∧ after.ro = h.ro ∧ after.static = h.static ∧
    after.nextBlk = h.nextBlk ∧ after.nalloc = h.nalloc ∧ after.allocOk = h.allocOk ∧
    after.garbage = h.garbage ∧ after.byteBase = h.byteBase ∧
    ∀ b, after.live b ↔ h.live b := by
  dsimp only
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => Iff.rfl⟩

/-- The real current borrow has the exact preceding model's text and a small
object size, even for unknown or negative errno values. -/
theorem zstrerror_readable (h : Heap) (fs : Fs) :
    let after := { h with libcErrorBorrow := some (nextErrorEpoch h, fs.errno) }
    Space.get after (BRef.str (libcErrnoIndex (nextErrorEpoch h) fs.errno)) =
      some (strBytes (strerrorText fs.errno)) ∧
    (strBytes (strerrorText fs.errno)).size < 64 := by
  exact ⟨(current_view _ _ _ rfl).1, C.LibcStrings.Proofs.errno_bytes_lt64 _⟩

/-- Every second actual call advances the epoch, including the same errno. -/
theorem nextErrorEpoch_strict (h : Heap) (e : Int32) :
    nextErrorEpoch { h with libcErrorBorrow := some (nextErrorEpoch h, e) } = nextErrorEpoch h + 1 := rfl

/-- Old external views become invalid on the next actual call; this cannot
resurrect an old view during library execution. -/
theorem zstrerror_invalidates_old (h : Heap) (old : Nat) (oldError : Int32) (fs : Fs)
    (hb : h.libcErrorBorrow = some (old, oldError)) :
    Space.get { h with libcErrorBorrow := some (nextErrorEpoch h, fs.errno) }
      (BRef.str (libcErrnoIndex old oldError)) = none := by
  apply old_view_invalid _ old (nextErrorEpoch h) oldError fs.errno rfl
  simp only [nextErrorEpoch, hb]
  omega

/-- The first error's borrowed pointer is invalid after the second actual
strerror call, regardless of whether both error texts are equal. -/
theorem two_calls_invalidate (h : Heap) (first second : Int32) :
    let h1 := { h with libcErrorBorrow := some (nextErrorEpoch h, first) }
    let h2 := { h1 with libcErrorBorrow := some (nextErrorEpoch h1, second) }
    Space.get h2 (BRef.str (libcErrnoIndex (nextErrorEpoch h) first)) = none := by
  apply old_view_invalid _ _ _ _ _ rfl
  change nextErrorEpoch h ≠ nextErrorEpoch h + 1
  omega

/-- Source literals stay readable through an actual strerror call. -/
theorem zstrerror_source_preserved (h : Heap) (e : Int32) (i : Nat) (hi : i < strTable.size) :
    Space.get { h with libcErrorBorrow := some (nextErrorEpoch h, e) } (BRef.str i) =
      Space.get h (BRef.str i) := by
  rw [source_view _ i hi, source_view _ i hi]

/-- Syscall output storage remains in the malloc heap; updating errno or Fs
alone cannot alter the active borrowed view. -/
theorem stable_setErrno (e : Int32) (fs : Fs) (h : Heap) :
    setErrno e fs h = .ok (((), { fs with errno := e }), h) := rfl

/-- The fixed filesystem write never invokes strerror. Even its failure
result keeps the same borrow observation for later synchronous copying. -/
theorem fsWrite_borrow_stable {h after : Heap} {fs fs' : Fs} {fd : Int32}
    {bs : Array UInt8} {rc : Int64} (run : fsWrite fd bs fs h = .ok ((rc, fs'), after)) :
    after.libcErrorBorrow = h.libcErrorBorrow := by
  unfold fsWrite at run
  split at run
  · cases run; rfl
  · cases he : fs.fds[fd.toInt.toNat]! with
    | none => rw [he] at run; cases run; rfl
    | some file =>
      rw [he] at run
      cases hw : file.wr with
      | false => simp only [hw, Bool.not_false, ite_true] at run; cases run; rfl
      | true =>
        simp only [hw, Bool.not_true, Bool.false_eq_true, ite_false] at run
        cases hb : bs.isEmpty with
        | true => simp only [hb, ite_true] at run; cases run; rfl
        | false =>
          simp only [hb, Bool.false_eq_true, ite_false] at run
          by_cases lim : (if file.append then fs.nodes[file.node]!.data.size else file.pos) ≥ fs.fsizeLimit
          · simp only [lim, ite_true] at run; cases run; rfl
          · simp only [lim, ite_false] at run; cases run; rfl

/-- File close also preserves borrow metadata on both actual fd outcomes. -/
theorem fsClose_borrow_stable {h after : Heap} {fs fs' : Fs} {fd rc : Int32}
    (run : fsClose fd fs h = .ok ((rc, fs'), after)) :
    after.libcErrorBorrow = h.libcErrorBorrow := by
  unfold fsClose at run
  split at run
  · cases run; rfl
  · cases he : fs.fds[fd.toInt.toNat]! with
    | none => rw [he] at run; cases run; rfl
    | some file => rw [he] at run; cases run; rfl

#print axioms zstrerror_run
#print axioms zstrerror_no_malloc
#print axioms zstrerror_readable
#print axioms zstrerror_invalidates_old
#print axioms two_calls_invalidate
#print axioms fsWrite_borrow_stable
#print axioms fsClose_borrow_stable
end Zlib.GzFs.Proofs
