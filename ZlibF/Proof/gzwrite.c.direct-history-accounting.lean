import ZlibF.Proof.«gzwrite.c.direct-history-error»

/-! # Aggregate descriptor-writer resource accounting

The actual history retains its handle, private path and copied input before
End. A successful error-message allocation adds exactly its owned message.
This file composes those real heap changes with the original caller heap.
-/
namespace Zlib.Gzwrite.DirectHistory
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib Zlib.Gzwrite Zlib.Gzlib.Spec Zlib.Gzlib.Proofs
open ZlibF.Spec.Public Zlib.Gzwrite.Proofs Zlib.Gzlib.ErrnoOwned
open Zlib.Gzlib.MessageCopy Zlib.Gzlib.MessageRefusal Zlib.Gzlib.ErrnoLifetime

def descriptorOpenedHeap (h : Heap) (fd : Int32) : Heap :=
  descriptorReleased (writerOpenHeap (descriptorEntryHeap h fd) true (descriptorPath fd) fd) h.nextBlk

def descriptorOpenedState (h : Heap) (fd : Int32) : GzState :=
  writerOpenState (descriptorEntryHeap h fd) true fd

def descriptorWrittenHeap (h : Heap) (fd : Int32) (src : Array UInt8) (off : Nat) (n : UInt32) : Heap :=
  firstWrittenHeap (descriptorOpenedHeap h fd) (descriptorEntryHeap h fd).nextBlk
    (descriptorOpenedState h fd) src off n

def descriptorWrittenState (h : Heap) (fd : Int32) (n : UInt32) : GzState :=
  firstWrittenState (descriptorOpenedHeap h fd) (descriptorOpenedState h fd) n

def descriptorErrorHeap (h : Heap) (fs : Fs) (fd : Int32) (src : Array UInt8) (off : Nat) (n : UInt32) : Heap :=
  DirectErrno.failedFlushHeap (descriptorWrittenHeap h fd src off n) fs (descriptorEntryHeap h fd).nextBlk
    (descriptorWrittenState h fd n) (descriptorPath fd)

def descriptorErrorState (h : Heap) (fd : Int32) (src : Array UInt8) (off : Nat) (n : UInt32) : GzState :=
  let written := descriptorWrittenHeap h fd src off n
  let state := {descriptorWrittenState h fd n with again := 0}
  if written.allocOk written.nalloc then copiedMessageState written state else refusedMessageState state

/-- The descriptor temporary and both format temporaries have gone; only
actual allocator calls contribute to nalloc. -/
theorem descriptor_open_counts (h : Heap) (fd : Int32) (hn : 0 ≤ fd.toInt) :
    (descriptorOpenedHeap h fd).nextBlk = h.nextBlk+5 ∧
    (descriptorOpenedHeap h fd).nalloc = h.nalloc+3 ∧
    (descriptorOpenedHeap h fd).allocOk = h.allocOk ∧
    (descriptorOpenedHeap h fd).libcErrorBorrow = h.libcErrorBorrow := by
  have hfd : fd ≠ -1 := by intro eq; rw [eq] at hn; contradiction
  have hnonempty : (descriptorPath fd).toArray.isEmpty = false := by simp [descriptorPath]
  simp [descriptorOpenedHeap,descriptorReleased,writerOpenHeap,writerFinishedHeap,writerEntryHeap,
    writerFormattedHeap,pathFormattedHeap,pathBytesHeap,pathAllocatedHeap,writerIoHeap,
    descriptorEntryHeap,descriptorFormattedHeap,descriptorAllocatedHeap,openFrontHeap,setS,
    hfd,hnonempty,Nat.add_assoc]

theorem first_written_frame (h : Heap) (i : Nat) (s : GzState) (src : Array UInt8) (off : Nat) (n : UInt32) :
    Frame h (firstWrittenHeap h i s src off n) (fun j => j=i ∨ j=h.nextBlk) := by
  obtain ⟨_,_,hnext,halloc⟩ := first_written_observations h i s src off n
  refine ⟨rfl,rfl,rfl,by rw [hnext]; omega,by rw [halloc]; omega,?_⟩
  intro j _ hj
  have hi : j ≠ i := fun eq => hj (Or.inl eq)
  have hb : j ≠ h.nextBlk := fun eq => hj (Or.inr eq)
  simp [firstWrittenHeap,writeEmptyHeap,directInitHeap,directInitAlloc,configuredHeap,setS,hi,hb]

/-- The public buffer choice and byte copy retain every preexisting live
object. The sole newly live identity is the real input allocation. -/
theorem first_written_live {h : Heap} {i : Nat} {s : GzState} {src : Array UInt8}
    (hs : h.gzstates i = some s) (off : Nat) (n : UInt32) :
    LiveChange h (firstWrittenHeap h i s src off n) (fun j => j=h.nextBlk) (fun _ => False) := by
  intro j
  by_cases hi : j=i
  · subst j
    simp [Heap.live,firstWrittenHeap,writeEmptyHeap,directInitHeap,directInitAlloc,
      configuredHeap,setS,hs]
  · by_cases hb : j=h.nextBlk
    · subst j
      simp [Heap.live,firstWrittenHeap,writeEmptyHeap,directInitHeap,directInitAlloc,
        configuredHeap,setS,hi]
    · simp [Heap.live,firstWrittenHeap,writeEmptyHeap,directInitHeap,directInitAlloc,
        configuredHeap,setS,hi,hb]

/-- Real written-state ownership consists of its actual handle, path and
input buffer. Transparent mode excludes unused compressor/output pointers. -/
theorem descriptor_written_owned (h : Heap) (fd : Int32) (src : Array UInt8) (off : Nat) (n : UInt32) (j : Nat) :
    GzOwned (descriptorWrittenHeap h fd src off n) (descriptorEntryHeap h fd).nextBlk
      (descriptorWrittenState h fd n) j ↔
      j=(descriptorEntryHeap h fd).nextBlk ∨ j=(descriptorEntryHeap h fd).nextBlk+1 ∨
        j=(descriptorOpenedHeap h fd).nextBlk := by
  simp [GzOwned,descriptorWrittenState,firstWrittenState,directInitRec,configuredState,
    descriptorOpenedState,writerOpenState,writerEntryRecord,openFrontRecord,resetRec,
    GZ_WRITE,GZ_READ,eq_comm]

theorem descriptor_open_owned (h : Heap) (fd : Int32) (j : Nat) :
    GzOwned (descriptorOpenedHeap h fd) (descriptorEntryHeap h fd).nextBlk (descriptorOpenedState h fd) j ↔
      j=(descriptorEntryHeap h fd).nextBlk ∨ j=(descriptorEntryHeap h fd).nextBlk+1 := by
  exact (descriptorOwned_zero_heap (descriptorOpenedHeap h fd)
    (writerOpenHeap (descriptorEntryHeap h fd) true (descriptorPath fd) fd)
    (descriptorEntryHeap h fd).nextBlk (descriptorOpenedState h fd) rfl j).trans
      (writerOpen_owned (descriptorEntryHeap h fd) true (descriptorPath fd) fd j)

/-- The post-error ownership is read from the actual returned state graph. -/
theorem descriptor_error_owned (h : Heap) (fs : Fs) (fd : Int32) (src : Array UInt8)
    (off : Nat) (n : UInt32) (j : Nat) :
    GzOwned (descriptorErrorHeap h fs fd src off n) (descriptorEntryHeap h fd).nextBlk
      (descriptorErrorState h fd src off n) j ↔
      j=(descriptorEntryHeap h fd).nextBlk ∨ j=(descriptorEntryHeap h fd).nextBlk+1 ∨
      ((descriptorWrittenHeap h fd src off n).allocOk (descriptorWrittenHeap h fd src off n).nalloc = true ∧
        j=(descriptorWrittenHeap h fd src off n).nextBlk) ∨ j=(descriptorOpenedHeap h fd).nextBlk := by
  cases ha : (descriptorWrittenHeap h fd src off n).allocOk (descriptorWrittenHeap h fd src off n).nalloc <;>
    simp [GzOwned,descriptorErrorState,ha,copiedMessageState,refusedMessageState,
      descriptorWrittenState,firstWrittenState,directInitRec,configuredState,descriptorOpenedState,
      writerOpenState,writerEntryRecord,openFrontRecord,resetRec,GZ_WRITE,GZ_READ,eq_comm]

private theorem frame_caller_compose {caller middle after : Heap} {changed : Nat → Prop}
    (before : Frame caller middle (fun _ => False)) (tail : Frame middle after changed)
    (survives : ∀ j, caller.live j → middle.live j)
    (separate : ∀ j, caller.live j → ¬changed j) : Frame caller after (fun _ => False) := by
  obtain ⟨a1,a2,a3,a4,a5,af⟩ := before
  obtain ⟨b1,b2,b3,b4,b5,bf⟩ := tail
  refine ⟨a1.trans b1,a2.trans b2,a3.trans b3,Nat.le_trans a4 b4,Nat.le_trans a5 b5,?_⟩
  intro j hl _
  obtain ⟨x1,x2,x3,x4,x5,x6,x7,x8⟩ := af j hl (by simp)
  obtain ⟨y1,y2,y3,y4,y5,y6,y7,y8⟩ := bf j (survives j hl) (separate j hl)
  exact ⟨y1.trans x1,y2.trans x2,y3.trans x3,y4.trans x4,y5.trans x5,y6.trans x6,y7.trans x7,y8.trans x8⟩

private theorem outcome_state_counts {w after : Heap} {fs : Fs} {i : Nat} {s : GzState} {xs : List UInt8}
    (ho : ReportMessageOutcome w after fs i s xs) :
    after.gzstates i = some (if w.allocOk w.nalloc then copiedMessageState w s else refusedMessageState s) ∧
    after.nalloc = w.nalloc+1 ∧
    after.nextBlk = w.nextBlk + (if w.allocOk w.nalloc then 2 else 0) := by
  cases ha : w.allocOk w.nalloc with
  | false =>
    simp only [ReportMessageOutcome,ha,Bool.false_eq_true,ite_false] at ho
    simpa only [ha,Bool.false_eq_true,ite_false,Nat.add_zero] using
      And.intro ho.1 (And.intro ho.2.2.2 ho.2.2.1)
  | true =>
    simp only [ReportMessageOutcome,ha,ite_true] at ho
    simpa only [ha,ite_true] using And.intro ho.1 (And.intro ho.2.2.2.2 ho.2.2.2.1)

private theorem prepared_outcome_state_counts {w after : Heap} {fs : Fs} {i : Nat} {s : GzState} {xs : List UInt8}
    (ho : ReportMessageOutcome (setS w i {s with again := 0}) after fs i {s with again := 0} xs) :
    after.gzstates i = some (if w.allocOk w.nalloc then copiedMessageState w {s with again := 0}
      else refusedMessageState {s with again := 0}) ∧
    after.nalloc = w.nalloc+1 ∧
    after.nextBlk = w.nextBlk + (if w.allocOk w.nalloc then 2 else 0) := by
  exact outcome_state_counts ho

/-- Original caller objects are untouched by all four real public calls. The
retained live additions are exactly the same returned handle's actual owned
graph, including the input and optional copied message. Counters count calls
and all allocated identities, including the already-freed format temporaries. -/
theorem descriptor_error_caller_accounting {h : Heap} {fs : Fs} {fd : Int32} {mode : BPtr}
    {p off : Nat} {src : Array UInt8}
    (hf : Fresh h) (hu : Uniq h) (hg : LibraryGlobals h) (hnfd : 0 ≤ fd.toInt)
    (hm : CString h mode [119,84]) (hp : h.bytes p = some src)
    (n : UInt32) (hn : n ≠ 0) (hn8 : n.toNat < 8) (hsrc : off+n.toNat ≤ src.size)
    (ha : h.allocOk h.nalloc = true) (ha1 : h.allocOk (h.nalloc+1) = true)
    (ha2 : h.allocOk (h.nalloc+2) = true) (hinput : h.allocOk (h.nalloc+3) = true)
    (hfd : (fs.fds.size : Int) ≤ fd.toInt) :
    let after := descriptorErrorHeap h fs fd src off n
    let state := descriptorErrorState h fd src off n
    after.gzstates (descriptorEntryHeap h fd).nextBlk = some state ∧
    Frame h after (fun _ => False) ∧
    LiveChange h after (GzOwned after (descriptorEntryHeap h fd).nextBlk state) (fun _ => False) ∧
    after.nalloc = h.nalloc+5 ∧
    after.nextBlk = h.nextBlk + (if h.allocOk (h.nalloc+4) then 8 else 6) := by
  dsimp only
  obtain ⟨_,ho,openFrame,openLive⟩ := gzdopen_writer_accounted h fs fd mode true hf hu hg hnfd hm ha ha1 ha2
  have full := descriptor_short_flush_history (fs := fs) hf hu hg hnfd hm hp n hn hn8 hsrc ha ha1 ha2 hinput hfd
  have writtenFrame := first_written_frame (descriptorOpenedHeap h fd) (descriptorEntryHeap h fd).nextBlk
    (descriptorOpenedState h fd) src off n
  have writtenLive := first_written_live (src := src) ho.1.1 off n
  have openedCounts := descriptor_open_counts h fd hnfd
  have entryNext := (descriptorEntry_counts h fd).1
  have writtenCounts := first_written_observations (descriptorOpenedHeap h fd) (descriptorEntryHeap h fd).nextBlk
    (descriptorOpenedState h fd) src off n
  have inputSeparate : ∀ j, h.live j → ¬(j=(descriptorEntryHeap h fd).nextBlk ∨ j=(descriptorOpenedHeap h fd).nextBlk) := by
    intro j hl own
    rcases own with eq | eq
    · exact hf j (by rw [eq,entryNext]; omega) hl
    · exact hf j (by rw [eq,openedCounts.1]; omega) hl
  have oldOpened : ∀ j, h.live j → (descriptorOpenedHeap h fd).live j := by
    intro j hl
    exact (openLive j).2 (Or.inl ⟨hl,by simp⟩)
  have toWritten := frame_caller_compose openFrame writtenFrame oldOpened inputSeparate
  have oldWritten : ∀ j, h.live j → (descriptorWrittenHeap h fd src off n).live j := by
    intro j hl
    exact (writtenLive j).2 (Or.inl ⟨oldOpened j hl,by simp⟩)
  have ownedSeparate : ∀ j, h.live j →
      ¬GzOwned (descriptorWrittenHeap h fd src off n) (descriptorEntryHeap h fd).nextBlk
        (descriptorWrittenState h fd n) j := by
    intro j hl own
    rw [descriptor_written_owned] at own
    rcases own with eq | eq | eq
    · exact inputSeparate j hl (Or.inl eq)
    · exact hf j (by rw [eq,entryNext]; omega) hl
    · exact inputSeparate j hl (Or.inr eq)
  have finalFrame := frame_caller_compose toWritten full.2.1 oldWritten ownedSeparate
  have finalLive : LiveChange h (descriptorErrorHeap h fs fd src off n)
      (GzOwned (descriptorErrorHeap h fs fd src off n) (descriptorEntryHeap h fd).nextBlk
        (descriptorErrorState h fd src off n)) (fun _ => False) := by
    intro j
    have openedLedger := openLive j
    have writtenLedger := writtenLive j
    have errorLedger := full.2.2.1 j
    have openOwned := descriptor_open_owned h fd j
    have finalOwned := descriptor_error_owned h fs fd src off n j
    dsimp only [descriptorOpenedHeap,descriptorOpenedState] at openOwned
    dsimp only [LiveChange] at openedLedger writtenLedger errorLedger ⊢
    rw [openOwned] at openedLedger
    rw [writtenLedger,openedLedger] at errorLedger
    rw [finalOwned]
    simpa only [descriptorErrorHeap,descriptorWrittenHeap,descriptorWrittenState,descriptorOpenedHeap,descriptorOpenedState,
      not_false_eq_true,and_true,or_assoc,or_left_comm,or_comm] using errorLedger
  have outcome : ReportMessageOutcome
      (setS (descriptorWrittenHeap h fd src off n) (descriptorEntryHeap h fd).nextBlk
        {descriptorWrittenState h fd n with again := 0})
      (descriptorErrorHeap h fs fd src off n) {fs with errno := EBADF} (descriptorEntryHeap h fd).nextBlk
      {descriptorWrittenState h fd n with again := 0} (descriptorPath fd) := full.2.2.2.1
  have writtenAlloc : (descriptorWrittenHeap h fd src off n).allocOk = h.allocOk := by
    change (firstWrittenHeap _ _ _ _ _ _).allocOk = h.allocOk
    exact openedCounts.2.2.1
  have writtenNalloc : (descriptorWrittenHeap h fd src off n).nalloc = h.nalloc+4 := by
    change (firstWrittenHeap _ _ _ _ _ _).nalloc = h.nalloc+4
    rw [writtenCounts.2.2.2,openedCounts.2.1]
  have writtenNext : (descriptorWrittenHeap h fd src off n).nextBlk = h.nextBlk+6 := by
    change (firstWrittenHeap _ _ _ _ _ _).nextBlk = h.nextBlk+6
    rw [writtenCounts.2.2.1,openedCounts.1]
  have facts := prepared_outcome_state_counts outcome
  refine ⟨?_,finalFrame,finalLive,?_,?_⟩
  · exact facts.1
  · calc
      (descriptorErrorHeap h fs fd src off n).nalloc = (descriptorWrittenHeap h fd src off n).nalloc+1 := facts.2.1
      _ = h.nalloc+5 := by rw [writtenNalloc]
  · calc
      (descriptorErrorHeap h fs fd src off n).nextBlk =
        (descriptorWrittenHeap h fd src off n).nextBlk +
          (if (descriptorWrittenHeap h fd src off n).allocOk (descriptorWrittenHeap h fd src off n).nalloc then 2 else 0) := facts.2.2
      _ = h.nextBlk + (if h.allocOk (h.nalloc+4) then 8 else 6) := by
        rw [writtenNext,writtenAlloc,writtenNalloc]
        cases accept : h.allocOk (h.nalloc+4) <;> simp [Nat.add_assoc]

#print axioms descriptor_open_counts
#print axioms first_written_frame
#print axioms first_written_live
#print axioms descriptor_written_owned
#print axioms descriptor_open_owned
#print axioms descriptor_error_owned
#print axioms descriptor_error_caller_accounting
end Zlib.Gzwrite.DirectHistory
