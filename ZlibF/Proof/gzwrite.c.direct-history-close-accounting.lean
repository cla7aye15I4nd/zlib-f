import ZlibF.Proof.«gzwrite.c.direct-close-ledger»

/-! # Original caller resources after the actual complete error close

The original init Uniq premise is inherited. The two later message allocation
outcomes are unrestricted. No object created by this writer remains live.
-/
namespace Zlib.Gzwrite.DirectHistory
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib Zlib.Gzwrite Zlib.Gzlib.Spec Zlib.Gzlib.Proofs
open ZlibF.Spec.Public Zlib.Gzwrite.Proofs Zlib.Gzlib.ErrnoOwned
open Zlib.Gzlib.MessageCopy Zlib.Gzlib.MessageRefusal Zlib.Gzlib.MessagePrevious
open Zlib.Gzlib.MessageHistory Zlib.Gzwrite.DirectClose

theorem first_written_uniq {h : Heap} {i : Nat} {s : GzState} (hs : h.gzstates i = some s)
    (hf : Fresh h) (hu : Uniq h) (src : Array UInt8) (off : Nat) (n : UInt32) :
    Uniq (firstWrittenHeap h i s src off n) := by
  have hi : i ≠ h.nextBlk := by
    intro eq; subst i
    exact hf h.nextBlk (Nat.le_refl _) (by simp [Heap.live,hs])
  have hn := Heap.not_live.mp (hf h.nextBlk (Nat.le_refl _))
  intro j
  by_cases hb : j=h.nextBlk
  · subst j
    simp [firstWrittenHeap,writeEmptyHeap,directInitHeap,directInitAlloc,configuredHeap,setS,
      Ne.symm hi,hn.2.1,hn.2.2.1,hn.2.2.2.1,hn.2.2.2.2.1,hn.2.2.2.2.2.1,hn.2.2.2.2.2.2]
  · by_cases hji : j=i
    · subst j
      simpa [firstWrittenHeap,writeEmptyHeap,directInitHeap,directInitAlloc,configuredHeap,setS,hi,hs] using hu i
    · simpa [firstWrittenHeap,writeEmptyHeap,directInitHeap,directInitAlloc,configuredHeap,setS,hb,hji] using hu j

theorem descriptor_closed_as_cycle (h : Heap) (fs : Fs) (fd : Int32) (src : Array UInt8) (off : Nat) (n : UInt32) :
    descriptorClosedHeap h fs fd src off n =
      errorCycleHeap (descriptorWrittenHeap h fd src off n) fs (descriptorEntryHeap h fd).nextBlk
        (descriptorWrittenState h fd n) (descriptorPath fd) (descriptorOpenedHeap h fd).nextBlk
        ((descriptorEntryHeap h fd).nextBlk+1) := rfl

private theorem caller_frame_compose {caller middle after : Heap} {changed : Nat → Prop}
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

/-- Exact original-caller ledger for the returned heap of the complete error
close. All roots come from actual descriptor initialization and lazy input
allocation. The caller domain is not strengthened. -/
theorem descriptor_closed_accounting {h : Heap} {fs : Fs} {fd : Int32} {mode : BPtr}
    (hf : Fresh h) (hu : Uniq h) (hg : LibraryGlobals h) (hnfd : 0 ≤ fd.toInt)
    (hm : CString h mode [119,84])
    (ha : h.allocOk h.nalloc = true) (ha1 : h.allocOk (h.nalloc+1) = true)
    (ha2 : h.allocOk (h.nalloc+2) = true) (src : Array UInt8) (off : Nat) (n : UInt32) :
    let after := descriptorClosedHeap h fs fd src off n
    Frame h after (fun _ => False) ∧ LiveChange h after (fun _ => False) (fun _ => False) ∧
    after.gzstates (descriptorEntryHeap h fd).nextBlk = none ∧ after.nalloc=h.nalloc+6 ∧
    after.nextBlk=h.nextBlk+6+(if h.allocOk (h.nalloc+4) then 2 else 0)+
      (if h.allocOk (h.nalloc+5) then 2 else 0) := by
  dsimp only
  obtain ⟨_,ho,openFrame,openLive⟩ := gzdopen_writer_accounted h fs fd mode true hf hu hg hnfd hm ha ha1 ha2
  have openedCounts := descriptor_open_counts h fd hnfd
  have entryNext := (descriptorEntry_counts h fd).1
  have facts := first_written_observations (descriptorOpenedHeap h fd) (descriptorEntryHeap h fd).nextBlk
    (descriptorOpenedState h fd) src off n
  have fresh := first_written_fresh (src := src) ho.1.1 ho.1.2.2.1 off n
  have unique := first_written_uniq ho.1.1 ho.1.2.2.1 ho.1.2.2.2.1 src off n
  have privatePath := first_written_private_path (i := (descriptorEntryHeap h fd).nextBlk) (src := src)
    ho.2.2.2.1 (Zlib.Gzlib.InitializedErrorPath.valid_observed_path_malloc ho.1 ho.2.2.2.1) ho.1.2.2.1 off n
  obtain ⟨pb,pbytes,ptr,bytes,_,_⟩ := privatePath.2
  have pbEq : pb=(descriptorEntryHeap h fd).nextBlk+1 := (BRef.blk.inj (Ptr.ref.inj ptr).1).symm
  subst pb
  have tailFrame := error_cycle_frame facts.1 fresh fs (descriptorPath fd)
    (descriptorOpenedHeap h fd).nextBlk ((descriptorEntryHeap h fd).nextBlk+1)
  have tailLive := error_cycle_live facts.1 fresh unique fs (descriptorPath fd)
    (descriptorOpenedHeap h fd).nextBlk ((descriptorEntryHeap h fd).nextBlk+1) facts.2.1 bytes
  have plain := error_cycle_plain (descriptorWrittenHeap h fd src off n) fs (descriptorEntryHeap h fd).nextBlk
    (descriptorWrittenState h fd n) (descriptorPath fd) (descriptorOpenedHeap h fd).nextBlk
    ((descriptorEntryHeap h fd).nextBlk+1)
  have counts := error_cycle_counts (descriptorWrittenHeap h fd src off n) fs (descriptorEntryHeap h fd).nextBlk
    (descriptorWrittenState h fd n) (descriptorPath fd) (descriptorOpenedHeap h fd).nextBlk
    ((descriptorEntryHeap h fd).nextBlk+1)
  have states := error_cycle_gzstates (descriptorWrittenHeap h fd src off n) fs (descriptorEntryHeap h fd).nextBlk
    (descriptorWrittenState h fd n) (descriptorPath fd) (descriptorOpenedHeap h fd).nextBlk
    ((descriptorEntryHeap h fd).nextBlk+1)
  change Frame (descriptorWrittenHeap h fd src off n) (descriptorClosedHeap h fs fd src off n) _ at tailFrame
  change LiveChange (descriptorWrittenHeap h fd src off n) (descriptorClosedHeap h fs fd src off n) _ _ at tailLive
  have writtenFrame := first_written_frame (descriptorOpenedHeap h fd) (descriptorEntryHeap h fd).nextBlk
    (descriptorOpenedState h fd) src off n
  have writtenLive := first_written_live (src := src) ho.1.1 off n
  have rootSeparate : ∀j, h.live j → ¬(j=(descriptorEntryHeap h fd).nextBlk ∨
      j=(descriptorOpenedHeap h fd).nextBlk ∨ j=(descriptorEntryHeap h fd).nextBlk+1) := by
    intro j hl roots
    rcases roots with eq | eq | eq
    · exact hf j (by rw [eq,entryNext]; omega) hl
    · exact hf j (by rw [eq,openedCounts.1]; omega) hl
    · exact hf j (by rw [eq,entryNext]; omega) hl
  have oldOpened : ∀j, h.live j → (descriptorOpenedHeap h fd).live j := by
    intro j hl
    exact (openLive j).2 (Or.inl ⟨hl,by simp⟩)
  have oldWritten : ∀j, h.live j → (descriptorWrittenHeap h fd src off n).live j := by
    intro j hl
    exact (writtenLive j).2 (Or.inl ⟨oldOpened j hl,by simp⟩)
  have prefixFrame := caller_frame_compose openFrame writtenFrame oldOpened (by
    intro j hl roots
    rcases roots with eq | eq
    · exact rootSeparate j hl (Or.inl eq)
    · exact rootSeparate j hl (Or.inr (Or.inl eq)))
  have finalFrame := caller_frame_compose prefixFrame tailFrame oldWritten rootSeparate
  have finalLive : LiveChange h (descriptorClosedHeap h fs fd src off n) (fun _ => False) (fun _ => False) := by
    intro j
    constructor
    · intro hl
      rcases (tailLive j).1 hl with survives | impossible
      · rcases (writtenLive j).1 survives.1 with opened | input
        · rcases (openLive j).1 opened.1 with original | owns
          · exact Or.inl original
          · have roots := (descriptor_open_owned h fd j).1 owns
            rcases roots with handle | path
            · exact False.elim (survives.2 (Or.inl handle))
            · exact False.elim (survives.2 (Or.inr (Or.inr path)))
        · exact False.elim (survives.2 (Or.inr (Or.inl input)))
      · contradiction
    · intro hl
      rcases hl with old | impossible
      · exact (tailLive j).2 (Or.inl ⟨oldWritten j old.1,rootSeparate j old.1⟩)
      · contradiction
  have writtenAlloc : (descriptorWrittenHeap h fd src off n).allocOk = h.allocOk := openedCounts.2.2.1
  have writtenNalloc : (descriptorWrittenHeap h fd src off n).nalloc = h.nalloc+4 := by
    change (firstWrittenHeap _ _ _ _ _ _).nalloc = _
    rw [facts.2.2.2,openedCounts.2.1]
  have writtenNext : (descriptorWrittenHeap h fd src off n).nextBlk = h.nextBlk+6 := by
    change (firstWrittenHeap _ _ _ _ _ _).nextBlk = _
    rw [facts.2.2.1,openedCounts.1]
  refine ⟨finalFrame,finalLive,?_,?_,?_⟩
  · change (errorCycleHeap _ _ _ _ _ _ _).gzstates (descriptorEntryHeap h fd).nextBlk=none
    rw [states,upd_same]
  · change (errorCycleHeap _ _ _ _ _ _ _).nalloc=h.nalloc+6
    rw [counts.1,writtenNalloc]
  · change (errorCycleHeap _ _ _ _ _ _ _).nextBlk=_
    rw [counts.2,writtenAlloc,writtenNalloc,writtenNext]

#print axioms first_written_uniq
#print axioms descriptor_closed_as_cycle
#print axioms descriptor_closed_accounting
end Zlib.Gzwrite.DirectHistory
