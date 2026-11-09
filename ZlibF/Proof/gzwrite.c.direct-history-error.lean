import ZlibF.Proof.«gzwrite.c.direct-history-written»

/-! # Real public descriptor writer history reaches its owned error report

The same actual execution opens wT, selects buffer8, accepts an arbitrary short
caller slice and flushes against a descriptor absent from the modeled table.
The actual write reports EBADF. All flush memory and capacity premises are
produced from initialization and this same write. Original init uniqueness is
inherited, and the later message allocation may either succeed or refuse.
-/
namespace Zlib.Gzwrite.DirectHistory
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib Zlib.Gzwrite Zlib.Gzlib.Spec Zlib.Gzlib.Proofs
open ZlibF.Spec.Public ZlibF.Spec.Public.OffsetProof

def descriptorShortFlushHistory (fd : Int32) (mode source : BPtr) (n : UInt32) :
    G ((GzFilePtr × Int32 × Int32) × Int32) := do
  let result ← descriptorShortHistory fd mode source n
  let flushed ← gzflush result.1 Z_SYNC_FLUSH
  return (result,flushed)

/-- Complete actual four-public-call history, with its same final owned heap
and exact final flush Frame/live ledger. No symbolic formatter capacity or
private-path/no-alias condition is added to the caller. -/
theorem descriptor_short_flush_history {h : Heap} {fs : Fs} {fd : Int32} {mode : BPtr}
    {p off : Nat} {src : Array UInt8}
    (hf : Fresh h) (hu : Uniq h) (hg : LibraryGlobals h) (hnfd : 0 ≤ fd.toInt)
    (hm : CString h mode [119,84]) (hp : h.bytes p = some src)
    (n : UInt32) (hn : n ≠ 0) (hn8 : n.toNat < 8) (hsrc : off+n.toNat ≤ src.size)
    (ha : h.allocOk h.nalloc = true) (ha1 : h.allocOk (h.nalloc+1) = true)
    (ha2 : h.allocOk (h.nalloc+2) = true) (hinput : h.allocOk (h.nalloc+3) = true)
    (hfd : (fs.fds.size : Int) ≤ fd.toInt) :
    let entry := descriptorEntryHeap h fd
    let opened := descriptorReleased (writerOpenHeap entry true (descriptorPath fd) fd) h.nextBlk
    let state := writerOpenState entry true fd
    let written := firstWrittenHeap opened entry.nextBlk state src off n
    let writtenState := firstWrittenState opened state n
    let after := DirectErrno.failedFlushHeap written fs entry.nextBlk writtenState (descriptorPath fd)
    descriptorShortFlushHistory fd mode (.ref (.blk p) off) n fs h =
      .ok ((((some (.in_gzstate_x entry.nextBlk),0,n.toInt32),DirectErrno.failedFlushCode written),
        {fs with errno := EBADF}),after) ∧
    Frame written after (GzOwned written entry.nextBlk writtenState) ∧
    LiveChange written after (fun b => written.allocOk written.nalloc = true ∧ b = written.nextBlk)
      (fun _ => False) ∧
    Zlib.Gzlib.ErrnoOwned.ReportMessageOutcome (setS written entry.nextBlk {writtenState with again := 0})
      after {fs with errno := EBADF} entry.nextBlk {writtenState with again := 0} (descriptorPath fd) ∧
    Space.get after (BRef.str (libcErrnoIndex (Zlib.GzFs.Proofs.nextErrorEpoch written) EBADF)) =
      some (strBytes (strerrorText EBADF)) := by
  dsimp only
  have prefixed := descriptor_short_history (fs := fs) hf hu hg hnfd hm hp n hn hn8 hsrc ha ha1 ha2 hinput
  obtain ⟨_,ho,_,_⟩ := gzdopen_writer_accounted h fs fd mode true hf hu hg hnfd hm ha ha1 ha2
  have flushed := first_written_flush_badfd (src := src) (off := off) ho (descriptorPath_length fd hnfd) n hn hn8 fs (Or.inr hfd)
  have observations := first_written_observations
    (descriptorReleased (writerOpenHeap (descriptorEntryHeap h fd) true (descriptorPath fd) fd) h.nextBlk)
    (descriptorEntryHeap h fd).nextBlk (writerOpenState (descriptorEntryHeap h fd) true fd) src off n
  have fresh := first_written_fresh (src := src) ho.1.1 ho.1.2.2.1 off n
  have pathBuffer := Zlib.Gzlib.InitializedErrorPath.valid_observed_path_malloc ho.1 ho.2.2.2.1
  have privatePath := first_written_private_path (i := (descriptorEntryHeap h fd).nextBlk) (src := src) ho.2.2.2.1 pathBuffer ho.1.2.2.1 off n
  have content := DirectErrno.failed_flush_content_lifetime (fs := fs) observations.1
    (show (firstWrittenState _ _ n).msg = .null from rfl) privatePath.1 privatePath.2 fresh
    (fun _ => Zlib.Gzlib.InitializedErrorPath.descriptor_report_capacity fd EBADF hnfd)
  refine ⟨?_,DirectErrno.failed_flush_frame observations.1 fresh,
    DirectErrno.failed_flush_live observations.1 fresh,content.1,content.2.1⟩
  dsimp only [hnd] at flushed
  unfold descriptorShortFlushHistory
  offsetsimp [prefixed,flushed]

#print axioms descriptor_short_flush_history
end Zlib.Gzwrite.DirectHistory
