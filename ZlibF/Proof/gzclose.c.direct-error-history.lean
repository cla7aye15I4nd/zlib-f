import ZlibF.Zlib.«gzclose.c»
import ZlibF.Proof.«gzwrite.c.direct-history-close-accounting»

/-! # Public gzclose on the same descriptor error history

This uses actual mode dispatch and the entire real writer-close execution.
All memory conditions are supplied by earlier calls in the same history.
-/
namespace Zlib.Gzwrite.DirectHistory
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib Zlib.Gzwrite Zlib.Gzclose Zlib.Gzlib.Spec Zlib.Gzlib.Proofs
open ZlibF.Spec.Public ZlibF.Spec.Public.OffsetProof Zlib.Gzwrite.Proofs Zlib.Gzlib.MessageHistory

theorem gzclose_write_dispatch {h : Heap} {i : Nat} {s : GzState}
    (hs : h.gzstates i = some s) (hm : s.mode=GZ_WRITE) (fs : Fs) :
    gzclose (hnd i) fs h = gzclose_w (hnd i) fs h := by
  unfold gzclose
  offsetsimp [hs,hm,GZ_WRITE,GZ_READ,hnd,castState,ldS_eq]

def descriptorPublicCloseHistory (fd : Int32) (mode source : BPtr) (n : UInt32) :
    G (((GzFilePtr × Int32 × Int32) × Int32) × Int32) := do
  let result ← descriptorShortFlushHistory fd mode source n
  let closed ← gzclose result.1.1
  return (result,closed)

/-- Same five real public calls, including final public close. Both later
message allocations may succeed or refuse; fd close itself reports EBADF.
The original init uniqueness premise and short-input scope are explicit. -/
theorem descriptor_public_close_history {h : Heap} {fs : Fs} {fd : Int32} {mode : BPtr}
    {p off : Nat} {src : Array UInt8}
    (hf : Fresh h) (hu : Uniq h) (hg : LibraryGlobals h) (hnfd : 0 ≤ fd.toInt)
    (hm : CString h mode [119,84]) (hp : h.bytes p = some src)
    (n : UInt32) (hn : n ≠ 0) (hn8 : n.toNat < 8) (hsrc : off+n.toNat ≤ src.size)
    (ha : h.allocOk h.nalloc = true) (ha1 : h.allocOk (h.nalloc+1) = true)
    (ha2 : h.allocOk (h.nalloc+2) = true) (hinput : h.allocOk (h.nalloc+3) = true)
    (hfd : (fs.fds.size : Int) ≤ fd.toInt) :
    descriptorPublicCloseHistory fd mode (.ref (.blk p) off) n fs h =
      .ok (((((hnd (descriptorEntryHeap h fd).nextBlk,0,n.toInt32),
        DirectErrno.failedFlushCode (descriptorWrittenHeap h fd src off n)),Z_ERRNO),
        {fs with errno := EBADF}),descriptorClosedHeap h fs fd src off n) := by
  have full := descriptor_short_flush_history (fs := fs) hf hu hg hnfd hm hp n hn hn8 hsrc ha ha1 ha2 hinput hfd
  have writer := descriptor_short_flush_close_history (fs := fs) hf hu hg hnfd hm hp n hn hn8 hsrc ha ha1 ha2 hinput hfd
  have accounting := descriptor_error_caller_accounting (fs := fs) hf hu hg hnfd hm hp n hn hn8 hsrc ha ha1 ha2 hinput hfd
  have modeWrite : (descriptorErrorState h fd src off n).mode=GZ_WRITE := by
    change (reportedState (descriptorWrittenHeap h fd src off n) (descriptorWrittenState h fd n)).mode=GZ_WRITE
    rw [(reported_state_fields _ _).1]
    rfl
  have dispatch := gzclose_write_dispatch accounting.1 modeWrite {fs with errno := EBADF}
  dsimp only [hnd,descriptorErrorHeap,descriptorWrittenHeap,descriptorWrittenState,descriptorOpenedHeap,descriptorOpenedState] at dispatch
  have same : descriptorPublicCloseHistory fd mode (.ref (.blk p) off) n fs h =
      descriptorShortFlushCloseHistory fd mode (.ref (.blk p) off) n fs h := by
    unfold descriptorPublicCloseHistory descriptorShortFlushCloseHistory
    offsetsimp [full.1,dispatch]
  exact same.trans writer

#print axioms gzclose_write_dispatch
#print axioms descriptor_public_close_history
end Zlib.Gzwrite.DirectHistory
