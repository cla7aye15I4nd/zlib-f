import ZlibF.Proof.«gzlib.c.error-message-preservation»

/-! # Same actual strerror report with a previous owned message

Cleanup of the old message precedes the real new strlen/malloc/copy. The path
and its separation are memory observations supplied by the previous real report.
The new errno CString comes from this actual borrow after cleanup. Both new
message allocation outcomes remain explicit and no callee contract is assumed.
-/
namespace Zlib.Gzlib.MessageHistory
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib Zlib.Gzlib.Spec Zlib.Gzlib.Proofs
open ZlibF.Spec.Public ZlibF.Spec.Public.OffsetProof Zlib.Gzlib.MessageCopy
open Zlib.Gzlib.MessageRefusal Zlib.Gzlib.MessagePrevious Zlib.Gzlib.ErrnoOwned Zlib.Gzlib.ErrnoLifetime

def replacementHeap (h : Heap) (fs : Fs) (i : Nat) (s : GzState) (xs : List UInt8) : Heap :=
  let cleared := clearedMessageHeap (errnoHeap h fs) i s
  if h.allocOk h.nalloc then
    copiedMessageHeap cleared i (clearedMessageState s) xs (errnoCharacters fs.errno)
  else refusedMessageHeap cleared i (clearedMessageState s)

def replacementState (h : Heap) (s : GzState) : GzState :=
  if h.allocOk h.nalloc then copiedMessageState h (clearedMessageState s)
  else refusedMessageState (clearedMessageState s)

/-- Actual full handler run with old-message cleanup and either new allocation
outcome. The external error text is produced on this same actual cleared heap. -/
theorem replacement_handler_run {h : Heap} {fs : Fs} {i : Nat} {s : GzState} {xs : List UInt8}
    (hs : h.gzstates i = some s) (hc : ClearableMessage h s)
    (hp : CString h s.path xs) (hpath : MallocBuffer h s.path (xs.length+1))
    (sep : s.path ≠ s.msg) (hf : Fresh h)
    (hcap : h.allocOk h.nalloc = true → xs.length+(errnoCharacters fs.errno).length+2 ≤ 2147483647) :
    gz_error (some (.tab i)) Z_ERRNO (errnoPointer h fs) (errnoHeap h fs) =
      .ok ((),replacementHeap h fs i s xs) := by
  have hsB : (errnoHeap h fs).gzstates i = some s := hs
  have hfB : Fresh (errnoHeap h fs) := hf
  have hcB : ClearableMessage (errnoHeap h fs) s := by
    simpa only [ClearableMessage,errnoHeap] using hc
  have hpB := path_cstring_after_errno hp hpath fs
  have hpathB : MallocBuffer (errnoHeap h fs) s.path (xs.length+1) := hpath
  have hpClear := (clear_previous_keeps_path (i := i) hcB hpB hpathB sep).1
  have heClear : CString (clearedMessageHeap (errnoHeap h fs) i s) (errnoPointer h fs)
      (errnoCharacters fs.errno) := by
    apply C.LibcBorrow.current_cstring
    exact (cleared_message_metadata (errnoHeap h fs) i s).1
  cases accept : h.allocOk h.nalloc with
  | false =>
    have run := gz_error_replace_refusal_run hsB hcB hpClear heClear accept
    simpa only [replacementHeap,accept,Bool.false_eq_true,ite_false] using run
  | true =>
    have run := gz_error_replace_copy_run hsB hcB hpClear heClear hfB accept (hcap accept)
    simpa only [replacementHeap,accept,ite_true] using run

/-- The translated caller's actual adjacent strerror report and -1 return.
All old-message cleanup and new temporary cleanup are included in its result. -/
theorem replacement_report_failure_run {h : Heap} {fs : Fs} {i : Nat} {s : GzState} {xs : List UInt8}
    (hs : h.gzstates i = some s) (hc : ClearableMessage h s)
    (hp : CString h s.path xs) (hpath : MallocBuffer h s.path (xs.length+1))
    (sep : s.path ≠ s.msg) (hf : Fresh h)
    (hcap : h.allocOk h.nalloc = true → xs.length+(errnoCharacters fs.errno).length+2 ≤ 2147483647) :
    Zlib.Gzwrite.DirectErrno.reportFailure i fs h = .ok ((-1,fs),replacementHeap h fs i s xs) := by
  have handler := replacement_handler_run hs hc hp hpath sep hf hcap
  dsimp only [errnoPointer,errnoHeap] at handler
  unfold Zlib.Gzwrite.DirectErrno.reportFailure
  offsetsimp [Zlib.GzFs.Proofs.zstrerror_run,handler]

/-- New-message storage is fresh even after old owned storage was released. -/
theorem replacement_fresh {h : Heap} {fs : Fs} {i : Nat} {s : GzState} {xs : List UInt8}
    (hs : h.gzstates i = some s) (hc : ClearableMessage h s) (hf : Fresh h) :
    Fresh (replacementHeap h fs i s xs) := by
  have hsB : (errnoHeap h fs).gzstates i = some s := hs
  have hfB : Fresh (errnoHeap h fs) := hf
  have hcB : ClearableMessage (errnoHeap h fs) s := by simpa only [ClearableMessage,errnoHeap] using hc
  have hsClear : (clearedMessageHeap (errnoHeap h fs) i s).gzstates i = some (clearedMessageState s) := by
    simp [clearedMessageHeap]
  have hfClear := cleared_message_fresh hsB hcB hfB
  unfold replacementHeap
  cases accept : h.allocOk h.nalloc with
  | false => simpa only [Bool.false_eq_true,ite_false] using refused_message_fresh hsClear hfClear
  | true => simpa only [ite_true] using copied_message_fresh hsClear hfClear

/-- Exact state and counters of the same real replacement report. -/
theorem replacement_observations {h : Heap} {fs : Fs} {i : Nat} {s : GzState} {xs : List UInt8}
    (hs : h.gzstates i = some s) (hc : ClearableMessage h s) (hf : Fresh h) :
    (replacementHeap h fs i s xs).gzstates i = some (replacementState h s) ∧
    (replacementHeap h fs i s xs).nalloc = h.nalloc+1 ∧
    (replacementHeap h fs i s xs).nextBlk = h.nextBlk+(if h.allocOk h.nalloc then 2 else 0) ∧
    (replacementHeap h fs i s xs).libcErrorBorrow = some (Zlib.GzFs.Proofs.nextErrorEpoch h,fs.errno) := by
  let cleared := clearedMessageHeap (errnoHeap h fs) i s
  have hsB : (errnoHeap h fs).gzstates i = some s := hs
  have hfB : Fresh (errnoHeap h fs) := hf
  have hcB : ClearableMessage (errnoHeap h fs) s := by simpa only [ClearableMessage,errnoHeap] using hc
  have hsClear : cleared.gzstates i = some (clearedMessageState s) := by simp [cleared,clearedMessageHeap]
  have hfClear : Fresh cleared := cleared_message_fresh hsB hcB hfB
  have metadataFacts := cleared_message_metadata (errnoHeap h fs) i s
  have nextEq : cleared.nextBlk = h.nextBlk := metadataFacts.2.1
  have nallocEq : cleared.nalloc = h.nalloc := metadataFacts.2.2
  have borrowEq : cleared.libcErrorBorrow = some (Zlib.GzFs.Proofs.nextErrorEpoch h,fs.errno) := metadataFacts.1
  have stateEq : copiedMessageState cleared (clearedMessageState s) = copiedMessageState h (clearedMessageState s) := by
    dsimp only [copiedMessageState]
    rw [nextEq]
  cases accept : h.allocOk h.nalloc with
  | false =>
    have record : (refusedMessageHeap cleared i (clearedMessageState s)).gzstates i =
        some (refusedMessageState (clearedMessageState s)) := by simp [refusedMessageHeap,setS]
    have alloc : (refusedMessageHeap cleared i (clearedMessageState s)).nalloc = h.nalloc+1 := by
      change cleared.nalloc+1=h.nalloc+1
      rw [nallocEq]
    have afterNext : (refusedMessageHeap cleared i (clearedMessageState s)).nextBlk = h.nextBlk := by
      change cleared.nextBlk = h.nextBlk
      exact nextEq
    have afterBorrow : (refusedMessageHeap cleared i (clearedMessageState s)).libcErrorBorrow =
        some (Zlib.GzFs.Proofs.nextErrorEpoch h,fs.errno) := by
      change cleared.libcErrorBorrow = _
      exact borrowEq
    simpa only [replacementHeap,replacementState,accept,Bool.false_eq_true,ite_false,Nat.add_zero]
      using And.intro record (And.intro alloc (And.intro afterNext afterBorrow))
  | true =>
    have facts := copied_message_observations (xs := xs) (es := errnoCharacters fs.errno) hsClear hfClear
    have alloc : (copiedMessageHeap cleared i (clearedMessageState s) xs (errnoCharacters fs.errno)).nalloc = h.nalloc+1 :=
      facts.2.2.2.2.1.trans (congrArg (·+1) nallocEq)
    have next : (copiedMessageHeap cleared i (clearedMessageState s) xs (errnoCharacters fs.errno)).nextBlk = h.nextBlk+2 :=
      facts.2.2.2.1.trans (congrArg (·+2) nextEq)
    have borrowed := facts.2.2.2.2.2.trans borrowEq
    simpa only [replacementHeap,replacementState,accept,ite_true,stateEq]
      using And.intro facts.1 (And.intro alloc (And.intro next borrowed))

/-- Clearing a previous message cannot touch a distinct old byte block. -/
theorem clear_previous_keeps_block {h : Heap} {i b : Nat} {s : GzState} {a : Array UInt8}
    (hc : ClearableMessage h s) (hb : h.bytes b = some a) (sep : .ref (.blk b) 0 ≠ s.msg) :
    (clearedMessageHeap h i s).bytes b = some a ∧ (clearedMessageHeap h i s).ro b = h.ro b := by
  rcases hc with hm | ⟨mb,ma,hm,_,_,_⟩
  · simpa [clearedMessageHeap,freeStr,setS,hm] using And.intro hb (rfl : h.ro b = h.ro b)
  · have ne : b ≠ mb := by intro eq; subst mb; exact sep hm.symm
    simpa [clearedMessageHeap,freeStr,setS,hm,ne] using And.intro hb (rfl : h.ro b = h.ro b)

/-- Pending input and private path bytes survive both old-message cleanup
and any new copied-message allocation. -/
theorem replacement_preserves_old_block {h : Heap} {fs : Fs} {i b : Nat} {s : GzState} {xs : List UInt8}
    {a : Array UInt8} (hs : h.gzstates i = some s) (hc : ClearableMessage h s) (hf : Fresh h)
    (hb : h.bytes b = some a) (sep : .ref (.blk b) 0 ≠ s.msg) :
    (replacementHeap h fs i s xs).bytes b = some a ∧ (replacementHeap h fs i s xs).ro b = h.ro b := by
  have hsB : (errnoHeap h fs).gzstates i = some s := hs
  have hfB : Fresh (errnoHeap h fs) := hf
  have hcB : ClearableMessage (errnoHeap h fs) s := by simpa only [ClearableMessage,errnoHeap] using hc
  have keep : (clearedMessageHeap (errnoHeap h fs) i s).bytes b = some a ∧
      (clearedMessageHeap (errnoHeap h fs) i s).ro b = h.ro b :=
    clear_previous_keeps_block (i := i) hcB hb sep
  have hsClear : (clearedMessageHeap (errnoHeap h fs) i s).gzstates i = some (clearedMessageState s) := by
    simp [clearedMessageHeap]
  have hfClear := cleared_message_fresh hsB hcB hfB
  unfold replacementHeap
  cases accept : h.allocOk h.nalloc with
  | false => simpa only [Bool.false_eq_true,ite_false,refusedMessageHeap,setS] using keep
  | true =>
    have copied := copied_message_preserves_old_block (xs := xs) (es := errnoCharacters fs.errno) hsClear hfClear keep.1
    simpa only [ite_true,errnoHeap] using And.intro copied.1 (copied.2.trans keep.2)

/-- The replacement itself again supplies the close clear's real writable
message-or-NULL premise. No assumed public representation contract is used. -/
theorem replacement_clearable {h : Heap} {fs : Fs} {i : Nat} {s : GzState} {xs : List UInt8}
    (hs : h.gzstates i = some s) (hc : ClearableMessage h s) (hf : Fresh h) :
    ClearableMessage (replacementHeap h fs i s xs) (replacementState h s) := by
  let cleared := clearedMessageHeap (errnoHeap h fs) i s
  have hsB : (errnoHeap h fs).gzstates i = some s := hs
  have hfB : Fresh (errnoHeap h fs) := hf
  have hcB : ClearableMessage (errnoHeap h fs) s := by simpa only [ClearableMessage,errnoHeap] using hc
  have hsClear : cleared.gzstates i = some (clearedMessageState s) := by simp [cleared,clearedMessageHeap]
  have hfClear : Fresh cleared := cleared_message_fresh hsB hcB hfB
  have nextEq : cleared.nextBlk = h.nextBlk := (cleared_message_metadata (errnoHeap h fs) i s).2.1
  cases accept : h.allocOk h.nalloc with
  | false =>
    left
    simp [replacementState,accept,refusedMessageState]
  | true =>
    have facts := copied_message_observations (xs := xs) (es := errnoCharacters fs.errno) hsClear hfClear
    have heapEq : replacementHeap h fs i s xs =
        copiedMessageHeap cleared i (clearedMessageState s) xs (errnoCharacters fs.errno) := by
      simp only [replacementHeap,accept,ite_true,cleared]
    unfold replacementState
    rw [accept]
    refine Or.inr ⟨h.nextBlk,(messageChars xs (errnoCharacters fs.errno)).push 0,rfl,?_,?_,?_⟩
    · rw [heapEq,←nextEq]
      exact facts.2.1
    · rw [heapEq,←nextEq]
      exact copied_message_writable _ _ _ _ _
    · change Z_ERRNO ≠ Z_MEM_ERROR
      decide

/-- Clearing metadata changes only again/err/msg; input, path and mode are
retained for the actual direct close continuation. -/
theorem replacement_state_fields (h : Heap) (s : GzState) :
    (replacementState h s).mode = s.mode ∧ (replacementState h s).direct = s.direct ∧
    (replacementState h s).size = s.size ∧ (replacementState h s).skip = s.skip ∧
    (replacementState h s).path = s.path ∧ (replacementState h s).«in» = s.«in» ∧
    (replacementState h s).fd = s.fd ∧ (replacementState h s).strm = s.strm := by
  unfold replacementState
  split <;> exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem reported_state_fields (h : Heap) (s : GzState) :
    (reportedState h s).mode = s.mode ∧ (reportedState h s).direct = s.direct ∧
    (reportedState h s).size = s.size ∧ (reportedState h s).skip = s.skip ∧
    (reportedState h s).path = s.path ∧ (reportedState h s).«in» = s.«in» ∧
    (reportedState h s).fd = s.fd ∧ (reportedState h s).strm = s.strm := by
  unfold reportedState
  split <;> exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Freshness separates a later actual message allocation from every retained
old malloc byte object, including pending input and the private path. -/
theorem replacement_message_ne_old_block {h : Heap} {s : GzState} {b : Nat} {a : Array UInt8}
    (hf : Fresh h) (hb : h.bytes b = some a) : .ref (.blk b) 0 ≠ (replacementState h s).msg := by
  cases accept : h.allocOk h.nalloc with
  | false => simp [replacementState,accept,refusedMessageState]
  | true =>
    have sep : b ≠ h.nextBlk := by
      intro eq
      subst b
      exact hf h.nextBlk (Nat.le_refl _) (Or.inl (by rw [hb]; simp))
    simp [replacementState,accept,copiedMessageState,sep]

/-- The real final NULL-message clear supports every requested error code.
In particular close passes Z_OK, freeing a prior malloc message exactly once. -/
def clearMessageHeap (h : Heap) (i : Nat) (s : GzState) (code : Int32) : Heap :=
  setS (freeStr h s.msg) i {s with msg := .null,err := code}

theorem gz_error_clear_code_run {h : Heap} {i : Nat} {s : GzState}
    (hs : h.gzstates i = some s) (hc : ClearableMessage h s) (code : Int32) :
    gz_error (some (.tab i)) code .null h = .ok ((),clearMessageHeap h i s code) := by
  unfold gz_error
  rcases hc with hm | ⟨b,a,hm,hb,hr,he⟩
  · gsimp [hs,hm,clearMessageHeap,setS,upd_upd]
  · have free := C.freeB_ok hb hr
    gsimp [hs,hm,he,free,clearMessageHeap,freeStr,setS,upd_upd]

#print axioms replacement_handler_run
#print axioms replacement_report_failure_run
#print axioms replacement_fresh
#print axioms replacement_observations
#print axioms replacement_preserves_old_block
#print axioms gz_error_clear_code_run
#print axioms replacement_clearable
#print axioms replacement_state_fields
#print axioms reported_state_fields
#print axioms replacement_message_ne_old_block
end Zlib.Gzlib.MessageHistory
