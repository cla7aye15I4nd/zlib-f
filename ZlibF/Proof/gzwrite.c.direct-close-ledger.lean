import ZlibF.Proof.«gzwrite.c.direct-history-close»

/-! # Exact final allocation ledger of direct error close -/
namespace Zlib.Gzwrite.DirectHistory
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib Zlib.Gzwrite Zlib.Gzlib.Spec Zlib.Gzlib.Proofs
open ZlibF.Spec.Public Zlib.Gzwrite.Proofs Zlib.Gzlib.ErrnoOwned
open Zlib.Gzlib.MessageCopy Zlib.Gzlib.MessageRefusal Zlib.Gzlib.MessagePrevious
open Zlib.Gzlib.MessageHistory Zlib.Gzwrite.DirectClose

theorem stored_bytes (h : Heap) (b j : Nat) (a out : Array UInt8) :
    (Zlib.GzFs.MessageStore.storedMessageHeap h b a out).bytes j =
      if j=b then some (out.push 0) else if j=h.nextBlk then none else h.bytes j := by
  change (upd (upd (upd (upd h.bytes h.nextBlk (some out)) b
    (some (copyRange a out 0 0 out.size))) h.nextBlk none) b (some (out.push 0))) j = _
  by_cases hb : j=b
  · subst j; simp
  · by_cases ht : j=h.nextBlk
    · subst j; simp [hb]
    · simp [hb,ht]

theorem copied_bytes (h : Heap) (i j : Nat) (s : GzState) (xs es : List UInt8) :
    (copiedMessageHeap h i s xs es).bytes j =
      if j=h.nextBlk then some ((messageChars xs es).push 0)
      else if j=h.nextBlk+1 then none else h.bytes j := by
  rw [copiedMessageHeap,stored_bytes]
  dsimp only [messageReadyHeap,mallocMessageHeap,preMessageHeap,setS]
  by_cases hj : j=h.nextBlk <;> simp [hj]

theorem fresh_bytes_none {h : Heap} (hf : Fresh h) {j : Nat} (hj : h.nextBlk ≤ j) : h.bytes j = none := by
  cases hb : h.bytes j with
  | none => rfl
  | some a => exact False.elim (hf j hj (Or.inl (by rw [hb]; simp)))

theorem free_block_bytes (h : Heap) (b j : Nat) :
    (freeStr h (.ref (.blk b) 0)).bytes j = if j=b then none else h.bytes j := by
  simp [freeStr,upd_apply]

/-- Allocate, format with a temporary, and free the copied message: the
original byte table is restored pointwise, including both fresh identities. -/
theorem free_copied_bytes {h : Heap} (hf : Fresh h) (i j : Nat) (s : GzState) (xs es : List UInt8) :
    (freeStr (copiedMessageHeap h i s xs es) (copiedMessageState h s).msg).bytes j = h.bytes j := by
  rw [show (copiedMessageState h s).msg = .ref (.blk h.nextBlk) 0 from rfl,free_block_bytes]
  by_cases hj : j=h.nextBlk
  · subst j
    simp [fresh_bytes_none hf (Nat.le_refl _)]
  · rw [ite_eq_right hj,copied_bytes]
    by_cases ht : j=h.nextBlk+1
    · subst j
      simp [fresh_bytes_none hf (by omega : h.nextBlk ≤ h.nextBlk+1)]
    · simp [hj,ht]

/-- Final direct cleanup removes input and path, plus exactly the current
owned message pointer. This byte projection does not need global uniqueness. -/
theorem closed_bytes (h : Heap) (i b path j : Nat) (s : GzState) :
    (closedDirectHeap h i s b path).bytes j =
      if j=b ∨ j=path then none else (freeStr h s.msg).bytes j := by
  by_cases hb : j=b <;> by_cases hp : j=path
  all_goals cases hm : s.msg with
  | null => simp [closedDirectHeap,messageFreedHeap,clearMessageHeap,inputFreedHeap,freeStr,setS,hm,upd_apply,hb,hp]
  | ref r off => cases r <;> simp [closedDirectHeap,messageFreedHeap,clearMessageHeap,inputFreedHeap,freeStr,setS,hm,upd_apply,hb,hp]


theorem free_reported_bytes {h : Heap} {i : Nat} {s : GzState} {fs : Fs} {xs : List UInt8}
    (hs : h.gzstates i = some s) (hf : Fresh h) (j : Nat) :
    (freeStr (DirectErrno.failedFlushHeap h fs i s xs) (reportedState h s).msg).bytes j = h.bytes j := by
  let prepared := setS h i {s with again := 0}
  let borrowed := Zlib.Gzlib.ErrnoLifetime.errnoHeap prepared {fs with errno := EBADF}
  have hfP : Fresh prepared := Shape.fresh (shape_setS hs {s with again := 0}) rfl hf
  have hfB : Fresh borrowed := hfP
  unfold DirectErrno.failedFlushHeap ownedReportHeap reportedState
  change (freeStr (if h.allocOk h.nalloc then _ else _) ((if h.allocOk h.nalloc then _ else _) : GzState).msg).bytes j = _
  cases accept : h.allocOk h.nalloc with
  | false => simp only [Bool.false_eq_true,ite_false,refusedMessageState,freeStr]; rfl
  | true =>
    simp only [ite_true]
    exact free_copied_bytes hfB i j {s with again := 0} xs (errnoCharacters EBADF)

theorem free_replacement_bytes {h : Heap} {i : Nat} {s : GzState} {fs : Fs} {xs : List UInt8}
    (hs : h.gzstates i = some s) (hc : ClearableMessage h s) (hf : Fresh h) (j : Nat) :
    (freeStr (replacementHeap h fs i s xs) (replacementState h s).msg).bytes j = (freeStr h s.msg).bytes j := by
  let borrowed := Zlib.Gzlib.ErrnoLifetime.errnoHeap h fs
  let cleared := clearedMessageHeap borrowed i s
  have hsB : borrowed.gzstates i = some s := hs
  have hcB : ClearableMessage borrowed s := hc
  have hfB : Fresh borrowed := hf
  have hfC : Fresh cleared := cleared_message_fresh hsB hcB hfB
  have nextC : cleared.nextBlk = h.nextBlk := (cleared_message_metadata borrowed i s).2.1
  have bytesC : cleared.bytes j = (freeStr h s.msg).bytes j := by
    cases hm : s.msg with
    | null => simp [cleared,borrowed,clearedMessageHeap,Zlib.Gzlib.ErrnoLifetime.errnoHeap,freeStr,setS,hm]
    | ref r off => cases r <;> simp [cleared,borrowed,clearedMessageHeap,Zlib.Gzlib.ErrnoLifetime.errnoHeap,freeStr,setS,hm]
  unfold replacementHeap replacementState
  change (freeStr (if h.allocOk h.nalloc then _ else _) ((if h.allocOk h.nalloc then _ else _) : GzState).msg).bytes j = _
  cases accept : h.allocOk h.nalloc with
  | false => simp only [Bool.false_eq_true,ite_false,refusedMessageState,freeStr]; exact bytesC
  | true =>
    simp only [ite_true]
    have run := free_copied_bytes hfC i j (clearedMessageState s) xs (errnoCharacters fs.errno)
    rw [bytesC] at run
    simpa only [copiedMessageState,nextC] using run

def errorCycleHeap (h : Heap) (fs : Fs) (i : Nat) (s : GzState) (xs : List UInt8) (b path : Nat) : Heap :=
  let first := DirectErrno.failedFlushHeap h fs i s xs
  let state := reportedState h s
  let prepared := setS first i {state with again := 0}
  closedDirectHeap (replacementHeap prepared {fs with errno := EBADF} i {state with again := 0} xs)
    i (replacementState prepared {state with again := 0}) b path

theorem error_cycle_bytes {h : Heap} {i : Nat} {s : GzState} (hs : h.gzstates i = some s)
    (hf : Fresh h) (fs : Fs) (xs : List UInt8) (b path j : Nat) :
    (errorCycleHeap h fs i s xs b path).bytes j = if j=b ∨ j=path then none else h.bytes j := by
  let first := DirectErrno.failedFlushHeap h fs i s xs
  let state := reportedState h s
  let prepared := setS first i {state with again := 0}
  have hsFirst : first.gzstates i = some state := reported_message_record hs hf
  have hfFirst : Fresh first := reported_message_fresh hs hf
  have hcFirst : ClearableMessage first state := reported_message_clearable hs hf
  have hsP : prepared.gzstates i = some {state with again := 0} := by simp [prepared]
  have hfP : Fresh prepared := Shape.fresh (shape_setS hsFirst {state with again := 0}) rfl hfFirst
  have hcP : ClearableMessage prepared {state with again := 0} := hcFirst
  rw [errorCycleHeap,closed_bytes]
  split
  · rfl
  · have final := free_replacement_bytes (fs := {fs with errno := EBADF}) (xs := xs) hsP hcP hfP j
    have same : (freeStr prepared {state with again := 0}.msg).bytes j = (freeStr first state.msg).bytes j := by
      cases hm : state.msg with
      | null => rfl
      | ref r off => cases r <;> rfl
    rw [same] at final
    exact final.trans (free_reported_bytes hs hf j)

theorem freeStr_gzstates (h : Heap) (p : BPtr) : (freeStr h p).gzstates = h.gzstates := by
  cases p with
  | null => rfl
  | ref r off => cases r <;> rfl

theorem copied_gzstates (h : Heap) (i : Nat) (s : GzState) (xs es : List UInt8) :
    (copiedMessageHeap h i s xs es).gzstates = upd h.gzstates i (some (copiedMessageState h s)) := by
  change upd (upd h.gzstates i (some {s with err := Z_ERRNO})) i (some (copiedMessageState h s)) = _
  exact upd_upd _ _ _ _

theorem replacement_erase_record (h : Heap) (fs : Fs) (i : Nat) (s : GzState) (xs : List UInt8) :
    upd (replacementHeap h fs i s xs).gzstates i none = upd h.gzstates i none := by
  unfold replacementHeap
  split
  · rw [copied_gzstates,upd_upd]
    simp only [clearedMessageHeap,setS,freeStr_gzstates,upd_upd]
    rfl
  · simp only [refusedMessageHeap,setS,clearedMessageHeap,freeStr_gzstates,upd_upd]
    rfl

theorem report_erase_record (h : Heap) (fs : Fs) (i : Nat) (s : GzState) (xs : List UInt8) :
    upd (DirectErrno.failedFlushHeap h fs i s xs).gzstates i none = upd h.gzstates i none := by
  unfold DirectErrno.failedFlushHeap ownedReportHeap
  split
  · rw [copied_gzstates,upd_upd]
    simp only [Zlib.Gzlib.ErrnoLifetime.errnoHeap,setS,upd_upd]
  · simp only [refusedMessageHeap,Zlib.Gzlib.ErrnoLifetime.errnoHeap,setS,upd_upd]

theorem closed_gzstates (h : Heap) (i b path : Nat) (s : GzState) :
    (closedDirectHeap h i s b path).gzstates = upd h.gzstates i none := by
  simp only [closedDirectHeap,messageFreedHeap,clearMessageHeap,setS,freeStr_gzstates,upd_upd,inputFreedHeap]

theorem error_cycle_gzstates (h : Heap) (fs : Fs) (i : Nat) (s : GzState) (xs : List UInt8) (b path : Nat) :
    (errorCycleHeap h fs i s xs b path).gzstates = upd h.gzstates i none := by
  rw [errorCycleHeap,closed_gzstates,replacement_erase_record]
  simp only [setS,upd_upd]
  exact report_erase_record h fs i s xs

def PlainTables (h after : Heap) : Prop :=
  after.words=h.words ∧ after.streams=h.streams ∧ after.gzheaders=h.gzheaders ∧
  after.dstates=h.dstates ∧ after.istates=h.istates ∧ after.static=h.static ∧
  after.allocOk=h.allocOk ∧ after.garbage=h.garbage

theorem PlainTables.trans {h a z : Heap} (x : PlainTables h a) (y : PlainTables a z) : PlainTables h z :=
  ⟨y.1.trans x.1,y.2.1.trans x.2.1,y.2.2.1.trans x.2.2.1,
   y.2.2.2.1.trans x.2.2.2.1,y.2.2.2.2.1.trans x.2.2.2.2.1,
   y.2.2.2.2.2.1.trans x.2.2.2.2.2.1,y.2.2.2.2.2.2.1.trans x.2.2.2.2.2.2.1,
   y.2.2.2.2.2.2.2.trans x.2.2.2.2.2.2.2⟩

theorem setS_plain (h : Heap) (i : Nat) (s : GzState) : PlainTables h (setS h i s) :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
theorem errno_plain (h : Heap) (fs : Fs) : PlainTables h (Zlib.Gzlib.ErrnoLifetime.errnoHeap h fs) :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
theorem stored_plain (h : Heap) (b : Nat) (a out : Array UInt8) :
    PlainTables h (Zlib.GzFs.MessageStore.storedMessageHeap h b a out) :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
theorem copied_plain (h : Heap) (i : Nat) (s : GzState) (xs es : List UInt8) : PlainTables h (copiedMessageHeap h i s xs es) := by
  have ready : PlainTables h (messageReadyHeap h i s xs es) := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  exact ready.trans (stored_plain _ h.nextBlk _ _)
theorem refused_plain (h : Heap) (i : Nat) (s : GzState) : PlainTables h (refusedMessageHeap h i s) :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
theorem freeStr_plain (h : Heap) (p : BPtr) : PlainTables h (freeStr h p) := by
  cases p with
  | null => exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  | ref r off => cases r <;> exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
theorem cleared_plain (h : Heap) (i : Nat) (s : GzState) : PlainTables h (clearedMessageHeap h i s) :=
  (freeStr_plain h s.msg).trans (setS_plain _ i _)

theorem replacement_plain (h : Heap) (fs : Fs) (i : Nat) (s : GzState) (xs : List UInt8) :
    PlainTables h (replacementHeap h fs i s xs) := by
  have pre := (errno_plain h fs).trans (cleared_plain _ i s)
  unfold replacementHeap
  split
  · exact pre.trans (copied_plain _ i _ xs _)
  · exact pre.trans (refused_plain _ i _)

theorem report_plain (h : Heap) (fs : Fs) (i : Nat) (s : GzState) (xs : List UInt8) :
    PlainTables h (DirectErrno.failedFlushHeap h fs i s xs) := by
  have pre := (setS_plain h i {s with again := 0}).trans (errno_plain _ {fs with errno := EBADF})
  unfold DirectErrno.failedFlushHeap ownedReportHeap
  split
  · exact pre.trans (copied_plain _ i _ xs _)
  · exact pre.trans (refused_plain _ i _)

theorem closed_plain (h : Heap) (i b path : Nat) (s : GzState) :
    PlainTables h (closedDirectHeap h i s b path) := by
  have same := freeStr_plain (inputFreedHeap h b) s.msg
  exact same

theorem error_cycle_plain (h : Heap) (fs : Fs) (i : Nat) (s : GzState) (xs : List UInt8) (b path : Nat) :
    PlainTables h (errorCycleHeap h fs i s xs b path) := by
  exact (report_plain h fs i s xs).trans ((setS_plain _ i _).trans
    ((replacement_plain _ _ i _ xs).trans (closed_plain _ i b path _)))

theorem freeStr_ro (h : Heap) (p : BPtr) : (freeStr h p).ro = h.ro := by
  cases p with
  | null => rfl
  | ref r off => cases r <;> rfl

theorem copied_ro (h : Heap) (i j : Nat) (s : GzState) (xs es : List UInt8) (hj : j<h.nextBlk) :
    (copiedMessageHeap h i s xs es).ro j = h.ro j := by
  change (upd (upd h.ro h.nextBlk false) (h.nextBlk+1) false) j = h.ro j
  simp [show j ≠ h.nextBlk by omega,show j ≠ h.nextBlk+1 by omega]

theorem report_counts (h : Heap) (fs : Fs) (i : Nat) (s : GzState) (xs : List UInt8) :
    (DirectErrno.failedFlushHeap h fs i s xs).nextBlk = h.nextBlk+(if h.allocOk h.nalloc then 2 else 0) ∧
    (DirectErrno.failedFlushHeap h fs i s xs).nalloc = h.nalloc+1 := by
  unfold DirectErrno.failedFlushHeap ownedReportHeap
  change ((if h.allocOk h.nalloc then _ else _) : Heap).nextBlk = _ ∧ ((if h.allocOk h.nalloc then _ else _) : Heap).nalloc = _
  cases accept : h.allocOk h.nalloc <;> simp only [Bool.false_eq_true,ite_false,ite_true,Nat.add_zero] <;> exact ⟨rfl,rfl⟩

theorem report_ro (h : Heap) (fs : Fs) (i j : Nat) (s : GzState) (xs : List UInt8) (hj : j<h.nextBlk) :
    (DirectErrno.failedFlushHeap h fs i s xs).ro j = h.ro j := by
  unfold DirectErrno.failedFlushHeap ownedReportHeap
  split
  · exact copied_ro _ i j _ xs _ hj
  · rfl

theorem replacement_counts (h : Heap) (fs : Fs) (i : Nat) (s : GzState) (xs : List UInt8) :
    (replacementHeap h fs i s xs).nextBlk = h.nextBlk+(if h.allocOk h.nalloc then 2 else 0) ∧
    (replacementHeap h fs i s xs).nalloc = h.nalloc+1 := by
  have facts := cleared_message_metadata (Zlib.Gzlib.ErrnoLifetime.errnoHeap h fs) i s
  have next : (clearedMessageHeap (Zlib.Gzlib.ErrnoLifetime.errnoHeap h fs) i s).nextBlk = h.nextBlk := facts.2.1
  have count : (clearedMessageHeap (Zlib.Gzlib.ErrnoLifetime.errnoHeap h fs) i s).nalloc = h.nalloc := facts.2.2
  unfold replacementHeap
  cases accept : h.allocOk h.nalloc
  · simp only [Bool.false_eq_true,ite_false]
    exact ⟨next,by change (clearedMessageHeap _ i s).nalloc+1=_; rw [count]⟩
  · simp only [ite_true]
    constructor
    · change (clearedMessageHeap _ i s).nextBlk+1+1=h.nextBlk+2
      rw [next]
    · change (clearedMessageHeap _ i s).nalloc+1=h.nalloc+1
      rw [count]

theorem replacement_ro (h : Heap) (fs : Fs) (i j : Nat) (s : GzState) (xs : List UInt8) (hj : j<h.nextBlk) :
    (replacementHeap h fs i s xs).ro j = h.ro j := by
  let cleared := clearedMessageHeap (Zlib.Gzlib.ErrnoLifetime.errnoHeap h fs) i s
  have next : cleared.nextBlk = h.nextBlk := (cleared_message_metadata _ i s).2.1
  have readonly : cleared.ro = h.ro := freeStr_ro _ s.msg
  unfold replacementHeap
  split
  · exact (copied_ro cleared i j _ xs _ (by rw [next]; exact hj)).trans (congrArg (fun r => r j) readonly)
  · exact congrArg (fun r => r j) readonly

theorem closed_counts (h : Heap) (i b path : Nat) (s : GzState) :
    (closedDirectHeap h i s b path).nextBlk=h.nextBlk ∧
    (closedDirectHeap h i s b path).nalloc=h.nalloc := by
  cases hm : s.msg with
  | null => simp [closedDirectHeap,messageFreedHeap,clearMessageHeap,freeStr,setS,inputFreedHeap,hm]
  | ref r off => cases r <;> simp [closedDirectHeap,messageFreedHeap,clearMessageHeap,freeStr,setS,inputFreedHeap,hm]

theorem error_cycle_counts (h : Heap) (fs : Fs) (i : Nat) (s : GzState) (xs : List UInt8) (b path : Nat) :
    let first := DirectErrno.failedFlushHeap h fs i s xs
    (errorCycleHeap h fs i s xs b path).nalloc=h.nalloc+2 ∧
    (errorCycleHeap h fs i s xs b path).nextBlk=h.nextBlk+(if h.allocOk h.nalloc then 2 else 0)+
      (if h.allocOk (h.nalloc+1) then 2 else 0) := by
  dsimp only
  have first := report_counts h fs i s xs
  have middle := replacement_counts (setS (DirectErrno.failedFlushHeap h fs i s xs) i {(reportedState h s) with again := 0})
    {fs with errno := EBADF} i {(reportedState h s) with again := 0} xs
  have fixed := report_plain h fs i s xs
  have final := closed_counts (replacementHeap (setS (DirectErrno.failedFlushHeap h fs i s xs) i {(reportedState h s) with again := 0})
    {fs with errno := EBADF} i {(reportedState h s) with again := 0} xs) i b path
    (replacementState (setS (DirectErrno.failedFlushHeap h fs i s xs) i {(reportedState h s) with again := 0}) {(reportedState h s) with again := 0})
  dsimp only [errorCycleHeap]
  constructor
  · rw [final.2,middle.2]
    change (DirectErrno.failedFlushHeap h fs i s xs).nalloc+1=h.nalloc+2
    rw [first.2]
  · rw [final.1,middle.1]
    change (DirectErrno.failedFlushHeap h fs i s xs).nextBlk+
      (if (DirectErrno.failedFlushHeap h fs i s xs).allocOk (DirectErrno.failedFlushHeap h fs i s xs).nalloc then 2 else 0)=_
    rw [fixed.2.2.2.2.2.2.1,first.2,first.1]

theorem error_cycle_ro (h : Heap) (fs : Fs) (i j : Nat) (s : GzState) (xs : List UInt8) (b path : Nat)
    (hj : j<h.nextBlk) : (errorCycleHeap h fs i s xs b path).ro j = h.ro j := by
  have first := report_counts h fs i s xs
  have middle := replacement_ro (setS (DirectErrno.failedFlushHeap h fs i s xs) i {(reportedState h s) with again := 0})
    {fs with errno := EBADF} i j {(reportedState h s) with again := 0} xs (by change j<(DirectErrno.failedFlushHeap h fs i s xs).nextBlk; rw [first.1]; omega)
  have final : (errorCycleHeap h fs i s xs b path).ro =
      (replacementHeap (setS (DirectErrno.failedFlushHeap h fs i s xs) i {(reportedState h s) with again := 0})
        {fs with errno := EBADF} i {(reportedState h s) with again := 0} xs).ro := by
    exact freeStr_ro _ _
  rw [final,middle]
  exact report_ro h fs i j s xs hj

theorem error_cycle_frame {h : Heap} {i : Nat} {s : GzState} (hs : h.gzstates i = some s)
    (hf : Fresh h) (fs : Fs) (xs : List UInt8) (b path : Nat) :
    Frame h (errorCycleHeap h fs i s xs b path) (fun j => j=i ∨ j=b ∨ j=path) := by
  have fixed := error_cycle_plain h fs i s xs b path
  have counts := error_cycle_counts h fs i s xs b path
  refine ⟨fixed.2.2.2.2.2.1.symm,fixed.2.2.2.2.2.2.1.symm,fixed.2.2.2.2.2.2.2.symm,
    by rw [counts.2]; omega,by rw [counts.1]; omega,?_⟩
  intro j hl notChanged
  have hi : j ≠ i := fun eq => notChanged (Or.inl eq)
  have hb : j ≠ b := fun eq => notChanged (Or.inr (Or.inl eq))
  have hp : j ≠ path := fun eq => notChanged (Or.inr (Or.inr eq))
  have hj : j<h.nextBlk := by
    by_cases right : j<h.nextBlk
    · exact right
    · exact False.elim (hf j (by omega) hl)
  refine ⟨?_,congrArg (fun t => t j) fixed.1,congrArg (fun t => t j) fixed.2.1,
    congrArg (fun t => t j) fixed.2.2.1,congrArg (fun t => t j) fixed.2.2.2.1,
    congrArg (fun t => t j) fixed.2.2.2.2.1,?_,error_cycle_ro h fs i j s xs b path hj⟩
  · simp only [error_cycle_bytes hs hf,show ¬(j=b ∨ j=path) by simp [hb,hp],ite_false]
  · rw [error_cycle_gzstates,upd_ne _ _ _ _ hi]

theorem error_cycle_live {h : Heap} {i : Nat} {s : GzState} {input pathBytes : Array UInt8}
    (hs : h.gzstates i = some s) (hf : Fresh h) (hu : Uniq h) (fs : Fs) (xs : List UInt8)
    (b path : Nat) (hb : h.bytes b = some input) (hp : h.bytes path = some pathBytes) :
    LiveChange h (errorCycleHeap h fs i s xs b path) (fun _ => False) (fun j => j=i ∨ j=b ∨ j=path) := by
  have fixed := error_cycle_plain h fs i s xs b path
  have ih := writerHandle_only h i s hu hs
  have ib := writerPath_only h b input hu hb
  have ip := writerPath_only h path pathBytes hu hp
  intro j
  have bytes := error_cycle_bytes hs hf fs xs b path j
  have states := error_cycle_gzstates h fs i s xs b path
  dsimp only [LiveChange]
  simp only [or_false]
  by_cases hi : j=i
  · subst j
    simp [Heap.live,bytes,states,fixed.1,fixed.2.1,fixed.2.2.1,fixed.2.2.2.1,fixed.2.2.2.2.1,ih]
  · by_cases hbj : j=b
    · subst j
      simp [Heap.live,bytes,states,fixed.1,fixed.2.1,fixed.2.2.1,fixed.2.2.2.1,fixed.2.2.2.2.1,ib,upd_apply]
    · by_cases hpj : j=path
      · subst j
        simp [Heap.live,bytes,states,fixed.1,fixed.2.1,fixed.2.2.1,fixed.2.2.2.1,fixed.2.2.2.2.1,ip,upd_apply]
      · simp [Heap.live,bytes,states,fixed.1,fixed.2.1,fixed.2.2.1,fixed.2.2.2.1,fixed.2.2.2.2.1,hi,hbj,hpj]

#print axioms error_cycle_bytes
#print axioms error_cycle_gzstates
#print axioms error_cycle_plain
#print axioms error_cycle_counts
#print axioms error_cycle_ro
#print axioms error_cycle_frame
#print axioms error_cycle_live
end Zlib.Gzwrite.DirectHistory
