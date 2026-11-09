import ZlibF.Proof.«gzwrite.c.direct-errno-source»
import ZlibF.Proof.«gzwrite.c.buffered»
import ZlibF.Proof.«gzwrite.c.comp-errno-owned»
import ZlibF.Proof.«gzlib.c.errno-owned-observations»

/-! # Complete ordinary transparent flush error

The input is live buffered data and the real descriptor write reports EBADF.
The public flush's clear, actual write and errno report share one heap. No old
message is present at entry; both later message-allocation outcomes are covered.
History initialization and final close remain separate.
-/
namespace Zlib.Gzwrite.DirectErrno
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib Zlib.Gzwrite Zlib.Gzlib.Spec Zlib.Gzlib.Proofs
open ZlibF.Spec.Public ZlibF.Spec.Public.OffsetProof Zlib.Gzlib.ErrnoLifetime
open Zlib.Gzlib.ErrnoOwned Zlib.Gzlib.MessageCopy Zlib.Gzlib.MessageRefusal

theorem report_failure_owned_run {h : Heap} {fs : Fs} {i : Nat} {s : GzState} {xs : List UInt8}
    (hs : h.gzstates i = some s) (hm : s.msg = .null) (hp : CString h s.path xs)
    (hpath : MallocBuffer h s.path (xs.length+1)) (hf : Fresh h)
    (hcap : h.allocOk h.nalloc = true → xs.length+(errnoCharacters fs.errno).length+2 ≤ 2147483647) :
    reportFailure i fs h = .ok ((-1,fs),ownedReportHeap h fs i s xs) := by
  have handler := report_owned_handler_run hs hm hp hpath hf hcap
  dsimp only [errnoPointer,errnoHeap] at handler
  unfold reportFailure
  offsetsimp [Zlib.GzFs.Proofs.zstrerror_run,handler]

def failedFlushHeap (h : Heap) (fs : Fs) (i : Nat) (s : GzState) (xs : List UInt8) : Heap :=
  ownedReportHeap (setS h i {s with again := 0}) {fs with errno := EBADF} i {s with again := 0} xs

def failedFlushCode (h : Heap) : Int32 := if h.allocOk h.nalloc then Z_ERRNO else Z_MEM_ERROR

/-- The complete real public flush returns its defined errno or memory-error
code and the exact owned message heap. The valid direct input reaches the
actual fsWrite EBADF branch before any compressor operation. -/
theorem gzflush_direct_badfd_owned_run {h : Heap} {i b off : Nat} {s : GzState}
    {a : Array UInt8} {xs : List UInt8}
    (hs : h.gzstates i = some s) (hm : s.mode = GZ_WRITE) (he : s.err = Z_OK)
    (hmsg : s.msg = .null) (hskip : s.skip = 0) (hsize : s.size ≠ 0) (hdir : s.direct ≠ 0)
    (n : UInt32) (hav : s.strm.avail_in = n) (hn : n ≠ 0) (hmax : n ≤ 1073741824)
    (hin : s.strm.next_in = .ref (.blk b) off) (ha : h.bytes b = some a)
    (hfit : off+n.toNat ≤ a.size) (fs : Fs)
    (hfd : s.fd < 0 ∨ (fs.fds.size : Int) ≤ s.fd.toInt)
    (hp : CString h s.path xs) (hpath : MallocBuffer h s.path (xs.length+1)) (hf : Fresh h)
    (hcap : h.allocOk h.nalloc = true → xs.length+(errnoCharacters EBADF).length+2 ≤ 2147483647) :
    gzflush (hnd i) Z_SYNC_FLUSH fs h =
      .ok ((failedFlushCode h,{fs with errno := EBADF}),failedFlushHeap h fs i s xs) := by
  let prepared := setS h i {s with again := 0}
  have hs' : prepared.gzstates i = some {s with again := 0} := by simp [prepared]
  have hf' : Fresh prepared := Shape.fresh (shape_setS hs {s with again := 0}) rfl hf
  have hp' : CString prepared s.path xs := cstring_of_same_malloc_bytes hp hpath rfl
  have hpbuf : MallocBuffer prepared s.path (xs.length+1) := hpath
  have handler := report_failure_owned_run (fs := {fs with errno := EBADF}) hs' hmsg hp' hpbuf hf' hcap
  have comp := gz_comp_direct_badfd_source hs hsize hdir n hav hn hmax hin ha hfit fs hfd Z_SYNC_FLUSH
  rw [show setS h i {s with again := 0} = prepared from rfl,handler] at comp
  dsimp only [Z_SYNC_FLUSH,prepared] at comp
  simp only [hm,he,hskip] at comp
  have clear := Zlib.Gzwrite.Proofs.gz_error_clear hs he hmsg
  have outcome := report_owned_message_outcome (fs := {fs with errno := EBADF}) (xs := xs) hs' hf'
  unfold gzflush
  cases accept : h.allocOk h.nalloc with
  | false =>
    have no : prepared.allocOk prepared.nalloc = false := accept
    simp only [ReportMessageOutcome,no,Bool.false_eq_true,ite_false] at outcome
    have state := outcome.1
    dsimp only [prepared] at state
    simp only [hm,he,hskip] at state
    offsetsimp [hs,hm,he,clear,hskip,Z_SYNC_FLUSH,Z_FINISH,comp,state,
      failedFlushHeap,failedFlushCode,prepared,accept,refusedMessageState]
  | true =>
    have yes : prepared.allocOk prepared.nalloc = true := accept
    simp only [ReportMessageOutcome,yes,ite_true] at outcome
    have state := outcome.1
    dsimp only [prepared] at state
    simp only [hm,he,hskip] at state
    offsetsimp [hs,hm,he,clear,hskip,Z_SYNC_FLUSH,Z_FINISH,comp,state,
      failedFlushHeap,failedFlushCode,prepared,accept,copiedMessageState]

/-- The full flush result has the original caller-owned frame. The reused
heap theorem is independent of compressed/direct control flow; both actual
error call sites produce exactly this heap expression. -/
theorem failed_flush_frame {h : Heap} {fs : Fs} {i : Nat} {s : GzState} {xs : List UInt8}
    (hs : h.gzstates i = some s) (hf : Fresh h) :
    Frame h (failedFlushHeap h fs i s xs) (GzOwned h i s) :=
  Zlib.Gzwrite.CompErrnoOwned.pending_owned_frame hs hf

theorem failed_flush_live {h : Heap} {fs : Fs} {i : Nat} {s : GzState} {xs : List UInt8}
    (hs : h.gzstates i = some s) (hf : Fresh h) :
    LiveChange h (failedFlushHeap h fs i s xs)
      (fun b => h.allocOk h.nalloc = true ∧ b = h.nextBlk) (fun _ => False) :=
  Zlib.Gzwrite.CompErrnoOwned.pending_owned_live hs hf

/-- The same exact flushed heap has full copied content/refusal observations,
current borrowed text, no borrowed msg pointer, and invalidation on the next
actual strerror while owned bytes and all malloc identities survive. -/
theorem failed_flush_content_lifetime {h : Heap} {fs : Fs} {i : Nat} {s : GzState} {xs : List UInt8}
    (hs : h.gzstates i = some s) (hm : s.msg = .null) (hp : CString h s.path xs)
    (hpath : MallocBuffer h s.path (xs.length+1)) (hf : Fresh h)
    (hcap : h.allocOk h.nalloc = true → xs.length+(errnoCharacters EBADF).length+2 ≤ 2147483647) :
    let prepared := setS h i {s with again := 0}
    let after := failedFlushHeap h fs i s xs
    ReportMessageOutcome prepared after {fs with errno := EBADF} i {s with again := 0} xs ∧
    Space.get after (BRef.str (libcErrnoIndex (Zlib.GzFs.Proofs.nextErrorEpoch h) EBADF)) =
      some (strBytes (strerrorText EBADF)) ∧
    (∀ final, after.gzstates i = some final → final.msg ≠ errnoPointer h {fs with errno := EBADF}) ∧
    (∀ (nextFs : Fs) (p : BPtr) (fs' : Fs) (next : Heap),
      zstrerror nextFs after = .ok ((p,fs'),next) →
      Space.get next (BRef.str (libcErrnoIndex (Zlib.GzFs.Proofs.nextErrorEpoch h) EBADF)) = none ∧
      next.bytes = after.bytes ∧ next.gzstates = after.gzstates ∧ (∀ b, next.live b ↔ after.live b)) := by
  dsimp only
  have hs' : (setS h i {s with again := 0}).gzstates i = some {s with again := 0} := by simp
  have hf' := Shape.fresh (shape_setS hs {s with again := 0}) rfl hf
  have hp' : CString (setS h i {s with again := 0}) s.path xs :=
    cstring_of_same_malloc_bytes hp hpath rfl
  have complete := report_owned_complete (fs := {fs with errno := EBADF}) hs' hm hp' hpath hf' hcap
  exact ⟨complete.2.1,complete.2.2.2.2.1,complete.2.2.2.2.2.1,complete.2.2.2.2.2.2⟩

#print axioms report_failure_owned_run
#print axioms gzflush_direct_badfd_owned_run
#print axioms failed_flush_frame
#print axioms failed_flush_live
#print axioms failed_flush_content_lifetime
end Zlib.Gzwrite.DirectErrno
