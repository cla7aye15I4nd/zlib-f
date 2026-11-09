import ZlibF.Proof.«gzwrite.c.direct-error-retry»

/-! # Actual close after the complete descriptor error history

The earlier owned message may exist or be NULL. The close retry's allocation
may independently succeed or refuse. Every input/path/message premise below
comes from actual initialization and the same earlier short write and report.
-/
namespace Zlib.Gzwrite.DirectHistory
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib Zlib.Gzwrite Zlib.Gzlib.Spec Zlib.Gzlib.Proofs
open ZlibF.Spec.Public ZlibF.Spec.Public.OffsetProof Zlib.Gzwrite.Proofs
open Zlib.Gzlib.ErrnoOwned Zlib.Gzlib.MessageHistory Zlib.Gzlib.MessagePrevious
open Zlib.Gzlib.MessageCopy Zlib.Gzlib.MessageRefusal Zlib.Gzwrite.DirectClose

private theorem open_state_error_close_run {h : Heap} {i path off : Nat} {s : GzState}
    {src : Array UInt8} {name : List UInt8} {fd : Int32}
    (ho : OpenState h i s .write (-1) 0 1 fd name) (hptr : s.path = .ref (.blk path) 0)
    (n : UInt32) (hn : n ≠ 0) (hn8 : n.toNat < 8) (fs : Fs)
    (hfd : fd < 0 ∨ (fs.fds.size : Int) ≤ fd.toInt)
    (cap : name.length+(errnoCharacters EBADF).length+2 ≤ 2147483647) :
    let written := firstWrittenHeap h i s src off n
    let state := firstWrittenState h s n
    let first := DirectErrno.failedFlushHeap written fs i state name
    let firstState := reportedState written state
    let prepared := setS first i {firstState with again := 0}
    let retried := replacementHeap prepared {fs with errno := EBADF} i {firstState with again := 0} name
    let retryState := replacementState prepared {firstState with again := 0}
    gzclose_w (hnd i) {fs with errno := EBADF} first =
      .ok ((Z_ERRNO,{fs with errno := EBADF}),closedDirectHeap retried i retryState h.nextBlk path) := by
  dsimp only
  let written := firstWrittenHeap h i s src off n
  let state := firstWrittenState h s n
  let first := DirectErrno.failedFlushHeap written fs i state name
  let firstState := reportedState written state
  have observations := first_written_observations h i s src off n
  have hsW : written.gzstates i = some state := observations.1
  have hfW : Fresh written := first_written_fresh (src := src) ho.1.1 ho.1.2.2.1 off n
  have buffer : written.bytes h.nextBlk =
      some (copyRange (initBufferBytes h (configuredState s)) src 0 off n.toNat) := observations.2.1
  have roBuffer : written.ro h.nextBlk = false := by
    simp [written,firstWrittenHeap,writeEmptyHeap,directInitHeap,directInitAlloc,configuredHeap,setS]
  have hsFirst : first.gzstates i = some firstState := reported_message_record hsW hfW
  have freshFirst : Fresh first := reported_message_fresh hsW hfW
  have clearableFirst : ClearableMessage first firstState := reported_message_clearable hsW hfW
  have pathBuffer := Zlib.Gzlib.InitializedErrorPath.valid_observed_path_malloc ho.1 ho.2.2.2.1
  have pathWritten := first_written_private_path (i := i) (src := src) ho.2.2.2.1 pathBuffer ho.1.2.2.1 off n
  have pathFirst := reported_path_preserved (fs := fs) hsW hfW pathWritten.1 pathWritten.2
  obtain ⟨pb,pathBytes,pathPointer,pathData,pathRo,_⟩ := pathWritten.2
  have pointerWritten : state.path = .ref (.blk path) 0 := hptr
  have pbEq : pb = path := (BRef.blk.inj (Ptr.ref.inj (pathPointer.symm.trans pointerWritten)).1)
  subst pb
  have pathKeep := reported_preserves_old_block (fs := fs) (xs := name) hsW hfW pathData
  have inputKeep := reported_preserves_old_block (fs := fs) (xs := name) hsW hfW buffer
  have fields := reported_state_fields written state
  have inFirst : firstState.«in» = .ref (.blk h.nextBlk) 0 := fields.2.2.2.2.2.1
  have pathPointerFirst : firstState.path = .ref (.blk path) 0 := fields.2.2.2.2.1.trans hptr
  have msgSame : (reportedState written state).msg = (replacementState written state).msg := by
    cases accept : written.allocOk written.nalloc <;>
      simp [reportedState,replacementState,accept,copiedMessageState,refusedMessageState,clearedMessageState]
  have inputMsgNe : firstState.«in» ≠ firstState.msg := by
    have ne := replacement_message_ne_old_block (s := state) hfW buffer
    rw [←msgSame] at ne
    intro eq
    exact ne (inFirst.symm.trans eq)
  have inputsDifferent : h.nextBlk ≠ path := by
    obtain ⟨pathName,pathC,pathBuf⟩ := ho.1.2.2.2.2.2.1
    obtain ⟨b,a,ptr,bytes,_,_⟩ := pathBuf
    have eq : b = path := BRef.blk.inj (Ptr.ref.inj (ptr.symm.trans hptr)).1
    subst b
    intro equal
    rw [←equal] at bytes
    exact ho.1.2.2.1 h.nextBlk (Nat.le_refl _) (Or.inl (by rw [bytes]; simp))
  have modeFirst : firstState.mode = GZ_WRITE := fields.1.trans ho.2.1
  have skipFirst : firstState.skip = 0 := fields.2.2.2.1.trans ho.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have sizeFirst : firstState.size ≠ 0 := by rw [fields.2.2.1]; change (8 : UInt32) ≠ 0; decide
  have dirFirst : firstState.direct ≠ 0 := by
    rw [fields.2.1]
    have eq : s.direct.toInt = 1 := by simpa using ho.2.2.2.2.2.2.1
    intro zero
    change s.direct = 0 at zero
    rw [zero] at eq
    contradiction
  have availFirst : firstState.strm.avail_in = n := by rw [fields.2.2.2.2.2.2.2]; rfl
  have nextFirst : firstState.strm.next_in = .ref (.blk h.nextBlk) 0 := by rw [fields.2.2.2.2.2.2.2]; rfl
  have fdFirst : firstState.fd = fd := fields.2.2.2.2.2.2.1.trans ho.2.2.1
  have fdBad : firstState.fd < 0 ∨ (({fs with errno := EBADF} : Fs).fds.size : Int) ≤ firstState.fd.toInt := by
    rw [fdFirst]
    exact hfd
  have chunk : n ≤ 1073741824 := by apply UInt32.le_iff_toNat_le.mpr; change n.toNat ≤ 1073741824; omega
  have fit : n.toNat ≤ (copyRange (initBufferBytes h (configuredState s)) src 0 off n.toNat).size := by
    have size : (initBufferBytes h (configuredState s)).size = 16 := by
      simp only [initBufferBytes,Array.size_ofFn]
      rfl
    rw [size_copyRange,size]
    omega
  exact gzclose_w_retry_badfd_run hsFirst modeFirst skipFirst sizeFirst dirFirst
    n availFirst hn chunk inFirst nextFirst inputKeep.1 (inputKeep.2.trans roBuffer) fit
    pathPointerFirst pathKeep.1 (pathKeep.2.trans pathRo) inputsDifferent
    {fs with errno := EBADF} fdBad clearableFirst pathFirst.1 pathFirst.2.1 pathFirst.2.2 inputMsgNe
    freshFirst (fun _ => cap)

def descriptorRetriedHeap (h : Heap) (fs : Fs) (fd : Int32) (src : Array UInt8) (off : Nat) (n : UInt32) : Heap :=
  let first := descriptorErrorHeap h fs fd src off n
  let state := descriptorErrorState h fd src off n
  replacementHeap (setS first (descriptorEntryHeap h fd).nextBlk {state with again := 0})
    {fs with errno := EBADF} (descriptorEntryHeap h fd).nextBlk {state with again := 0} (descriptorPath fd)

def descriptorRetryState (h : Heap) (fs : Fs) (fd : Int32) (src : Array UInt8) (off : Nat) (n : UInt32) : GzState :=
  let first := descriptorErrorHeap h fs fd src off n
  let state := descriptorErrorState h fd src off n
  replacementState (setS first (descriptorEntryHeap h fd).nextBlk {state with again := 0}) {state with again := 0}

def descriptorClosedHeap (h : Heap) (fs : Fs) (fd : Int32) (src : Array UInt8) (off : Nat) (n : UInt32) : Heap :=
  closedDirectHeap (descriptorRetriedHeap h fs fd src off n) (descriptorEntryHeap h fd).nextBlk
    (descriptorRetryState h fs fd src off n) (descriptorOpenedHeap h fd).nextBlk
    ((descriptorEntryHeap h fd).nextBlk+1)

def descriptorShortFlushCloseHistory (fd : Int32) (mode source : BPtr) (n : UInt32) :
    G (((GzFilePtr × Int32 × Int32) × Int32) × Int32) := do
  let result ← descriptorShortFlushHistory fd mode source n
  let closed ← gzclose_w result.1.1
  return (result,closed)

/-- All close representation facts come from the same actual public init,
buffer choice, short write and failed flush. The two message allocation
oracles are unrestricted. This retains the original init Uniq premise. -/
theorem descriptor_short_flush_close_history {h : Heap} {fs : Fs} {fd : Int32} {mode : BPtr}
    {p off : Nat} {src : Array UInt8}
    (hf : Fresh h) (hu : Uniq h) (hg : LibraryGlobals h) (hnfd : 0 ≤ fd.toInt)
    (hm : CString h mode [119,84]) (hp : h.bytes p = some src)
    (n : UInt32) (hn : n ≠ 0) (hn8 : n.toNat < 8) (hsrc : off+n.toNat ≤ src.size)
    (ha : h.allocOk h.nalloc = true) (ha1 : h.allocOk (h.nalloc+1) = true)
    (ha2 : h.allocOk (h.nalloc+2) = true) (hinput : h.allocOk (h.nalloc+3) = true)
    (hfd : (fs.fds.size : Int) ≤ fd.toInt) :
    descriptorShortFlushCloseHistory fd mode (.ref (.blk p) off) n fs h =
      .ok (((((hnd (descriptorEntryHeap h fd).nextBlk,0,n.toInt32),
        DirectErrno.failedFlushCode (descriptorWrittenHeap h fd src off n)),Z_ERRNO),
        {fs with errno := EBADF}),descriptorClosedHeap h fs fd src off n) := by
  obtain ⟨_,ho,_,_⟩ := gzdopen_writer_accounted h fs fd mode true hf hu hg hnfd hm ha ha1 ha2
  have full := descriptor_short_flush_history (fs := fs) hf hu hg hnfd hm hp n hn hn8 hsrc ha ha1 ha2 hinput hfd
  have close := open_state_error_close_run (src := src) (off := off) ho rfl n hn hn8 fs (Or.inr hfd)
    (Zlib.Gzlib.InitializedErrorPath.descriptor_report_capacity fd EBADF hnfd)
  change gzclose_w (hnd (descriptorEntryHeap h fd).nextBlk) {fs with errno := EBADF}
    (descriptorErrorHeap h fs fd src off n) =
    .ok ((Z_ERRNO,{fs with errno := EBADF}),descriptorClosedHeap h fs fd src off n) at close
  dsimp only [hnd,descriptorErrorHeap,descriptorWrittenHeap,descriptorWrittenState,
    descriptorOpenedHeap,descriptorOpenedState] at close
  unfold descriptorShortFlushCloseHistory
  offsetsimp [full.1,close,descriptorErrorHeap,descriptorWrittenHeap,descriptorWrittenState,
    descriptorOpenedHeap,descriptorOpenedState,hnd]

#print axioms open_state_error_close_run
#print axioms descriptor_short_flush_close_history
end Zlib.Gzwrite.DirectHistory
