import ZlibF.Proof.«gzlib.c.error-message-previous»
import ZlibF.Proof.«gzwrite.c.direct-errno-owned»

/-! # Actual copied-message preservation for a later close

A copied message is writable owned storage. Its allocation and formatting keep
all old byte objects and their readonly flags. The final cursor is fresh. These
facts supply later real previous-message cleanup instead of assuming GzValid.
-/
namespace Zlib.Gzlib.MessageCopy
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib Zlib.Gzlib.Spec Zlib.Gzlib.Proofs
open ZlibF.Spec.Public Zlib.GzFs.MessageStore Zlib.Gzlib.MessageRefusal

/-- The destination allocated by the actual message malloc remains writable
through the separate formatter temporary allocation and free. -/
theorem copied_message_writable (h : Heap) (i : Nat) (s : GzState) (xs es : List UInt8) :
    (copiedMessageHeap h i s xs es).ro h.nextBlk = false := by
  change (upd (upd h.ro h.nextBlk false) (h.nextBlk+1) false) h.nextBlk = false
  simp

/-- Existing byte storage, including the private path and pending input,
is preserved by the real message allocation/copy/temporary cleanup. -/
theorem copied_message_preserves_old_block {h : Heap} {i b : Nat} {s : GzState} {xs es : List UInt8}
    {a : Array UInt8} (hs : h.gzstates i = some s) (hf : Fresh h) (hb : h.bytes b = some a) :
    (copiedMessageHeap h i s xs es).bytes b = some a ∧
    (copiedMessageHeap h i s xs es).ro b = h.ro b := by
  have hn : b ≠ h.nextBlk := by
    intro eq
    subst b
    exact hf h.nextBlk (Nat.le_refl _) (Or.inl (by rw [hb]; simp))
  let ready := messageReadyHeap h i s xs es
  have bytes : ready.bytes b = some a := by
    simpa [ready,messageReadyHeap,mallocMessageHeap,preMessageHeap,setS,hn] using hb
  have readonly : ready.ro b = h.ro b := by
    simp [ready,messageReadyHeap,mallocMessageHeap,preMessageHeap,setS,hn]
  have frame := stored_message_frame (h := ready) (b := h.nextBlk)
    (a := messageGarbage h xs es) (out := messageChars xs es)
    (Fresh.slotUsed_next (ready_fresh hs hf))
  obtain ⟨same,_,_,_,_,_,_,sameRo⟩ := frame.2.2.2.2.2 b (Or.inl (by rw [bytes]; simp)) hn
  exact ⟨same.trans bytes,sameRo.trans readonly⟩

theorem copied_message_fresh {h : Heap} {i : Nat} {s : GzState} {xs es : List UInt8}
    (hs : h.gzstates i = some s) (hf : Fresh h) : Fresh (copiedMessageHeap h i s xs es) := by
  have live := copied_message_live (xs := xs) (es := es) hs hf
  have next := (copied_message_observations (xs := xs) (es := es) hs hf).2.2.2.1
  intro b hb hl
  rw [next] at hb
  rcases (live b).1 hl with old | new
  · exact hf b (by omega) old.1
  · omega

theorem refused_message_fresh {h : Heap} {i : Nat} {s : GzState}
    (hs : h.gzstates i = some s) (hf : Fresh h) : Fresh (refusedMessageHeap h i s) := by
  intro b hb hl
  have old := (refused_message_live h i s hs b).1 hl
  apply hf b hb
  simpa using old

end Zlib.Gzlib.MessageCopy

namespace Zlib.Gzlib.MessageHistory
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib Zlib.Gzlib.Spec Zlib.Gzlib.Proofs
open ZlibF.Spec.Public Zlib.Gzlib.MessageCopy Zlib.Gzlib.MessageRefusal Zlib.Gzlib.MessagePrevious
open Zlib.Gzlib.ErrnoOwned Zlib.Gzlib.ErrnoLifetime

def reportedState (h : Heap) (s : GzState) : GzState :=
  if h.allocOk h.nalloc then copiedMessageState h {s with again := 0}
  else refusedMessageState {s with again := 0}

/-- The exact record follows from the same actual report result; this small
abstract projection keeps large initialized heap expressions opaque. -/
theorem reported_message_record {h : Heap} {fs : Fs} {i : Nat} {s : GzState} {xs : List UInt8}
    (hs : h.gzstates i = some s) (hf : Fresh h) :
    (Zlib.Gzwrite.DirectErrno.failedFlushHeap h fs i s xs).gzstates i = some (reportedState h s) := by
  have hs' : (setS h i {s with again := 0}).gzstates i = some {s with again := 0} := by simp
  have hf' := Shape.fresh (shape_setS hs {s with again := 0}) rfl hf
  have outcome := report_owned_message_outcome (fs := {fs with errno := EBADF}) (xs := xs) hs' hf'
  cases accept : h.allocOk h.nalloc with
  | false =>
    have flag : (setS h i {s with again := 0}).allocOk (setS h i {s with again := 0}).nalloc = false := accept
    simp only [ReportMessageOutcome,flag,Bool.false_eq_true,ite_false] at outcome
    simpa only [Zlib.Gzwrite.DirectErrno.failedFlushHeap,reportedState,accept,Bool.false_eq_true,ite_false] using outcome.1
  | true =>
    have flag : (setS h i {s with again := 0}).allocOk (setS h i {s with again := 0}).nalloc = true := accept
    simp only [ReportMessageOutcome,flag,ite_true] at outcome
    simpa only [Zlib.Gzwrite.DirectErrno.failedFlushHeap,reportedState,accept,ite_true,copiedMessageState,setS] using outcome.1

/-- The first real report leaves a clearable malloc message or NULL, for both
allocator outcomes. This condition is produced from actual bytes and flags. -/
theorem reported_message_clearable {h : Heap} {fs : Fs} {i : Nat} {s : GzState} {xs : List UInt8}
    (hs : h.gzstates i = some s) (hf : Fresh h) :
    ClearableMessage (Zlib.Gzwrite.DirectErrno.failedFlushHeap h fs i s xs) (reportedState h s) := by
  have hs' : (setS h i {s with again := 0}).gzstates i = some {s with again := 0} := by simp
  have hf' := Shape.fresh (shape_setS hs {s with again := 0}) rfl hf
  have facts := report_owned_message_outcome (fs := {fs with errno := EBADF}) (xs := xs) hs' hf'
  cases accept : h.allocOk h.nalloc with
  | false =>
    left
    simp [reportedState,accept,refusedMessageState]
  | true =>
    have flag : (setS h i {s with again := 0}).allocOk (setS h i {s with again := 0}).nalloc = true := accept
    simp only [ReportMessageOutcome,flag,ite_true] at facts
    have heapEq : Zlib.Gzwrite.DirectErrno.failedFlushHeap h fs i s xs =
        copiedMessageHeap (errnoHeap (setS h i {s with again := 0}) {fs with errno := EBADF})
          i {s with again := 0} xs (errnoCharacters EBADF) := by
      unfold Zlib.Gzwrite.DirectErrno.failedFlushHeap ownedReportHeap
      change (if h.allocOk h.nalloc then _ else _) = _
      rw [accept]
      rfl
    unfold reportedState
    rw [accept]
    refine Or.inr ⟨h.nextBlk,(messageChars xs (errnoCharacters EBADF)).push 0,rfl,?_,?_,?_⟩
    · exact facts.2.1
    · rw [heapEq]
      exact copied_message_writable _ _ _ _ _
    · change Z_ERRNO ≠ Z_MEM_ERROR
      decide

theorem reported_message_fresh {h : Heap} {fs : Fs} {i : Nat} {s : GzState} {xs : List UInt8}
    (hs : h.gzstates i = some s) (hf : Fresh h) :
    Fresh (Zlib.Gzwrite.DirectErrno.failedFlushHeap h fs i s xs) := by
  have hs' : (setS h i {s with again := 0}).gzstates i = some {s with again := 0} := by simp
  have hf' := Shape.fresh (shape_setS hs {s with again := 0}) rfl hf
  have hsB : (errnoHeap (setS h i {s with again := 0}) {fs with errno := EBADF}).gzstates i =
      some {s with again := 0} := hs'
  have hfB : Fresh (errnoHeap (setS h i {s with again := 0}) {fs with errno := EBADF}) := hf'
  unfold Zlib.Gzwrite.DirectErrno.failedFlushHeap ownedReportHeap
  change Fresh (if h.allocOk h.nalloc then _ else _)
  cases accept : h.allocOk h.nalloc with
  | false =>
    simpa only [Bool.false_eq_true,ite_false] using refused_message_fresh hsB hfB
  | true =>
    simpa only [ite_true] using copied_message_fresh hsB hfB

/-- The same actual first-report heap preserves each live old byte block and
its readonly flag, including pending input and the private path. -/
theorem reported_preserves_old_block {h : Heap} {fs : Fs} {i b : Nat} {s : GzState} {xs : List UInt8}
    {a : Array UInt8} (hs : h.gzstates i = some s) (hf : Fresh h) (hb : h.bytes b = some a) :
    (Zlib.Gzwrite.DirectErrno.failedFlushHeap h fs i s xs).bytes b = some a ∧
    (Zlib.Gzwrite.DirectErrno.failedFlushHeap h fs i s xs).ro b = h.ro b := by
  have hs' : (setS h i {s with again := 0}).gzstates i = some {s with again := 0} := by simp
  have hf' := Shape.fresh (shape_setS hs {s with again := 0}) rfl hf
  have hsB : (errnoHeap (setS h i {s with again := 0}) {fs with errno := EBADF}).gzstates i =
      some {s with again := 0} := hs'
  have hfB : Fresh (errnoHeap (setS h i {s with again := 0}) {fs with errno := EBADF}) := hf'
  unfold Zlib.Gzwrite.DirectErrno.failedFlushHeap ownedReportHeap
  change (if h.allocOk h.nalloc then _ else _ : Heap).bytes b = some a ∧
    (if h.allocOk h.nalloc then _ else _ : Heap).ro b = h.ro b
  cases accept : h.allocOk h.nalloc with
  | false =>
    simp only [Bool.false_eq_true,ite_false]
    exact ⟨hb,rfl⟩
  | true =>
    simp only [ite_true]
    exact copied_message_preserves_old_block hsB hfB hb

private theorem CString_block_transport {h after : Heap} {p : BPtr} {xs : List UInt8} {b : Nat}
    (hp : p = .ref (.blk b) 0) (hc : CString h p xs) (hb : after.bytes b = h.bytes b) :
    CString after p xs := by
  subst p
  refine ⟨?_,hc.2⟩
  rcases hc.1 with hn | ⟨r,off,a,hptr,ha,hfit,htext⟩
  · cases hn.1
  · cases hptr
    exact Or.inr ⟨.blk b,0,a,rfl,hb.trans ha,hfit,htext⟩

theorem reported_path_preserved {h : Heap} {fs : Fs} {i : Nat} {s : GzState} {xs : List UInt8}
    (hs : h.gzstates i = some s) (hf : Fresh h) (hp : CString h s.path xs)
    (hpath : MallocBuffer h s.path (xs.length+1)) :
    CString (Zlib.Gzwrite.DirectErrno.failedFlushHeap h fs i s xs) (reportedState h s).path xs ∧
    MallocBuffer (Zlib.Gzwrite.DirectErrno.failedFlushHeap h fs i s xs) (reportedState h s).path (xs.length+1) ∧
    (reportedState h s).path ≠ (reportedState h s).msg := by
  obtain ⟨b,a,hptr,hbytes,hro,hfit⟩ := hpath
  have keep := reported_preserves_old_block (fs := fs) (xs := xs) hs hf hbytes
  have pathEq : (reportedState h s).path = s.path := by unfold reportedState; split <;> rfl
  refine ⟨?_,?_,?_⟩
  · rw [pathEq]
    exact CString_block_transport hptr hp (keep.1.trans hbytes.symm)
  · rw [pathEq]
    exact ⟨b,a,hptr,keep.1,keep.2.trans hro,hfit⟩
  · rw [pathEq]
    cases accept : h.allocOk h.nalloc with
    | false => simp [reportedState,accept,refusedMessageState,hptr]
    | true =>
      have sep : b ≠ h.nextBlk := by
        intro eq
        subst b
        exact hf h.nextBlk (Nat.le_refl _) (Or.inl (by rw [hbytes]; simp))
      simp [reportedState,accept,copiedMessageState,hptr,sep]

/-- Previous-message cleanup retains this actual separate malloc path. The
separation premise here is produced by the first report above. -/
theorem clear_previous_keeps_path {h : Heap} {i : Nat} {s : GzState} {xs : List UInt8}
    (hc : ClearableMessage h s) (hp : CString h s.path xs)
    (hpath : MallocBuffer h s.path (xs.length+1)) (sep : s.path ≠ s.msg) :
    CString (clearedMessageHeap h i s) s.path xs ∧
    MallocBuffer (clearedMessageHeap h i s) s.path (xs.length+1) := by
  obtain ⟨b,a,hptr,hbytes,hro,hfit⟩ := hpath
  have bytes : (clearedMessageHeap h i s).bytes b = h.bytes b := by
    rcases hc with hm | ⟨mb,ma,hm,_,_,_⟩
    · simp [clearedMessageHeap,freeStr,setS,hm]
    · have ne : b ≠ mb := by intro eq; subst mb; exact sep (hptr.trans hm.symm)
      simp [clearedMessageHeap,freeStr,setS,hm,ne]
  have readonly : (clearedMessageHeap h i s).ro b = h.ro b := by
    cases hm : s.msg with
    | null => simp [clearedMessageHeap,freeStr,setS,hm]
    | ref r off => cases r <;> simp [clearedMessageHeap,freeStr,setS,hm]
  refine ⟨CString_block_transport hptr hp bytes,?_⟩
  exact ⟨b,a,hptr,bytes.trans hbytes,readonly.trans hro,hfit⟩

#print axioms reported_message_record
#print axioms reported_message_clearable
#print axioms reported_message_fresh
#print axioms reported_preserves_old_block
#print axioms reported_path_preserved
#print axioms clear_previous_keeps_path
end Zlib.Gzlib.MessageHistory
