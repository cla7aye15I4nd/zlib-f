import ZlibF.Zlib.«gzwrite.c»
import ZlibF.Proof.«gzfs.borrowed-error»
import ZlibF.Spec.Public.GzClose
import ZlibF.Spec.Functional.Api.Compress

/-!
# gzwrite.c: complete borrowed-error close regression

The same legal zero-room history that exposed the old libc allocation residue
now closes without a new live object. Every gzip allocation is released. The
external borrow is metadata, with its own lifetime and no malloc identity.
-/

namespace Zlib.Gzwrite.BorrowRegression
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib Zlib.Gzwrite
open ZlibF.Spec.Public

def callerHeap (statics : Statics) : Heap :=
  { Heap.empty with bytes := ⟨#[some #[112, 0], some #[119, 84, 0]]⟩
                    nextBlk := 2, static := statics }

def initialFs : Fs := { fsizeLimit := 0 }

def openedFs : Fs :=
  { names := #[(#[112], 0)], nodes := #[{ data := #[], isDir := false }]
    fds := #[none, none, none, some { node := 0, pos := 0, rd := false, wr := true, append := false }]
    fsizeLimit := 0, nos := 1 }

def openedState : GzState :=
  { GzState.zeroed with
    mode := GZ_WRITE, fd := 3, path := .ref (.blk 3) 0
    want := 8192, direct := 1, level := Z_DEFAULT_COMPRESSION }

def openedHeap (statics : Statics) : Heap :=
  { Heap.empty with
    bytes := ⟨#[some #[112, 0], some #[119, 84, 0], none, some #[112, 0], none]⟩
    ro := ⟨#[false, false, false, false, false]⟩
    gzstates := ⟨#[none, none, some openedState]⟩
    static := statics, nextBlk := 5, nalloc := 2 }

def smallState : GzState := { openedState with want := 8 }
def smallHeap (statics : Statics) : Heap :=
  { openedHeap statics with gzstates := upd (openedHeap statics).gzstates 2 (some smallState) }

def writtenState : GzState :=
  { GzState.zeroed with
    mode := GZ_WRITE, fd := 3, path := .ref (.blk 3) 0
    want := 8, size := 8, «in» := .ref (.blk 5) 0, direct := 1
    level := Z_DEFAULT_COMPRESSION
    x := { GzState.zeroed.x with pos := 1 }
    strm := { GzState.zeroed.strm with next_in := .ref (.blk 5) 0, avail_in := 1 } }

def writtenHeap (statics : Statics) : Heap :=
  { Heap.empty with
    bytes := ⟨#[some #[112, 0], some #[119, 84, 0], none, some #[112, 0], none,
      some #[112, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]⟩
    ro := ⟨#[false, false, false, false, false, false]⟩
    gzstates := ⟨#[none, none, some writtenState]⟩
    static := statics, nextBlk := 6, nalloc := 3 }

def finalFs : Fs := { openedFs with fds := #[none, none, none, none], errno := EFBIG, nos := 3 }

def finalHeap (statics : Statics) : Heap :=
  { Heap.empty with
    bytes := ⟨#[some #[112, 0], some #[119, 84, 0], none, none, none, none, none, none]⟩
    ro := ⟨#[false, false, false, false, false, false, false, false]⟩
    gzstates := ⟨#[none, none, none]⟩
    static := statics, nextBlk := 8, nalloc := 4
    libcErrorBorrow := some (1, EFBIG) }

set_option maxRecDepth 20000 in
theorem actual_open (statics : Statics) :
    gzopen (.ref (.blk 0) 0) (.ref (.blk 1) 0) initialFs (callerHeap statics) =
      .ok ((some (.in_gzstate_x 2), openedFs), openedHeap statics) := by
  conv => lhs; cbv
  conv => rhs; cbv
  all_goals rfl

set_option maxRecDepth 20000 in
theorem actual_buffer (statics : Statics) :
    gzbuffer (some (.in_gzstate_x 2)) 8 (openedHeap statics) = .ok (0, smallHeap statics) := by
  conv => lhs; cbv
  conv => rhs; cbv
  all_goals rfl

set_option maxRecDepth 20000 in
theorem actual_write (statics : Statics) :
    gzwrite (some (.in_gzstate_x 2)) (.ref (.blk 0) 0) 1 openedFs (smallHeap statics) =
      .ok ((1, openedFs), writtenHeap statics) := by
  conv => lhs; cbv
  conv => rhs; cbv
  all_goals rfl

set_option maxRecDepth 20000 in
/-- Public open, buffer selection and write produce this exact small state.
The write accepts byte112 without growing the empty zero-limit file. -/
theorem actual_prefix (statics : Statics) :
    (do let file ← gzopen (.ref (.blk 0) 0) (.ref (.blk 1) 0)
        let buffered ← StateT.lift (gzbuffer file 8)
        let wrote ← gzwrite file (.ref (.blk 0) 0) 1
        return (file, buffered, wrote)) initialFs (callerHeap statics) =
      .ok (((some (.in_gzstate_x 2), 0, 1), openedFs), writtenHeap statics) := by
  conv => lhs; cbv
  conv => rhs; cbv
  all_goals rfl

set_option maxRecDepth 20000 in
/-- The complete real close still reaches EFBIG and releases its owned input,
path, formatted message, temporary and handle, then closes fd3. Borrowed error
text is not malloc storage and leaves no external block behind. -/
theorem actual_close (statics : Statics) :
    gzclose_w (some (.in_gzstate_x 2)) openedFs (writtenHeap statics) =
      .ok ((Z_ERRNO, finalFs), finalHeap statics) := by
  conv => lhs; cbv
  conv => rhs; cbv
  all_goals rfl

set_option maxRecDepth 20000 in
/-- The entire public history has one exact returned heap and file world. -/
theorem actual_full_history (statics : Statics) :
    (do let file ← gzopen (.ref (.blk 0) 0) (.ref (.blk 1) 0)
        let buffered ← StateT.lift (gzbuffer file 8)
        let wrote ← gzwrite file (.ref (.blk 0) 0) 1
        let closed ← gzclose_w file
        return (buffered, wrote, closed)) initialFs (callerHeap statics) =
      .ok (((0, 1, Z_ERRNO), finalFs), finalHeap statics) := by
  conv => lhs; cbv
  conv => rhs; cbv
  all_goals rfl

/-- The original empty zero-limit world is admitted by FileSystem. -/
theorem initial_world_valid : FileSystem initialFs := by
  refine ⟨by decide, ?_, ?_, ?_⟩
  · intro path node hm; simp [initialFs] at hm
  · intro i file hg; simp [initialFs] at hg
  · intro i node hg; simp [initialFs] at hg

/-- Ordinary caller storage, not fabricated initialized private buffers. -/
theorem caller_fresh_uniq (statics : Statics) : Fresh (callerHeap statics) ∧ Zlib.Gzlib.Spec.Uniq (callerHeap statics) := by
  constructor
  · intro b hb hl
    have hb2 : 2 ≤ b := hb
    simp (disch := omega) [Heap.live, callerHeap, Heap.empty, Tbl.get, Tbl.empty,
      Array.getD_eq_getD_getElem?, List.getElem?_eq_none, default] at hl
  · intro b
    simp [callerHeap, Heap.empty, Zlib.Gzlib.Spec.cnt, Tbl.get, Tbl.empty, default]
    split <;> omega

/-- Public argument legality and actual execution establish this same history. -/
theorem written_reachable (statics : Statics) (hg : LibraryGlobals (callerHeap statics)) :
    GzReachable (writtenHeap statics) openedFs 2 := by
  have hc := caller_fresh_uniq statics
  have hp : CString (callerHeap statics) (.ref (.blk 0) 0) [112] :=
    ⟨Or.inr ⟨.blk 0, 0, #[112, 0], rfl, rfl, by decide, rfl⟩, by decide, by decide⟩
  have hm : CString (callerHeap statics) (.ref (.blk 1) 0) [119, 84] :=
    ⟨Or.inr ⟨.blk 1, 0, #[119, 84, 0], rfl, rfl, by decide, rfl⟩, by decide, by decide⟩
  have ho := GzReachable.open hc.1 hc.2 hg initial_world_valid hp hm (actual_open statics)
  have hbexec : (Call.gzbuffer (some (.in_gzstate_x 2)) 8).execute openedFs (openedHeap statics) =
      .ok (((0 : Int32), openedFs), smallHeap statics) := by
    simp only [Call.execute, heapCall, actual_buffer]
  have hb := GzReachable.step ho (show (openedHeap statics).gzstates 2 = some openedState from rfl)
    (show GzOperation 2 (.gzbuffer (some (.in_gzstate_x 2)) 8) from rfl)
    (show GzArguments (openedHeap statics) 2 openedState (.gzbuffer (some (.in_gzstate_x 2)) 8) from True.intro) hbexec
  have ha : GzArguments (smallHeap statics) 2 smallState
      (.gzwrite (some (.in_gzstate_x 2)) (.ref (.blk 0) 0) 1) := by
    change GzRange _ _ _ _ _ false
    refine Or.inr ⟨⟨[112], Or.inr ⟨.blk 0, 0, #[112, 0], rfl, rfl, by decide, rfl⟩⟩, by simp, ?_⟩
    intro b hb
    have hb0 : b = 0 := by simpa [ByteRoot] using hb
    subst b
    have hsize : smallState.size = 0 := rfl
    have hmsg : smallState.msg = .null := rfl
    have hpath : smallState.path = .ref (.blk 3) 0 := rfl
    simp [GzOwned, hsize, hmsg, hpath]
  exact GzReachable.step hb (show (smallHeap statics).gzstates 2 = some smallState from rfl)
    (show GzOperation 2 (.gzwrite (some (.in_gzstate_x 2)) (.ref (.blk 0) 0) 1) from rfl)
    ha (actual_write statics)

/-- The actual pending-input state satisfies the original public memory
representation at close entry, on exactly the returned heap. -/
theorem written_valid (statics : Statics) (hg : LibraryGlobals (callerHeap statics)) :
    GzValid (writtenHeap statics) 2 writtenState := by
  have hf : Fresh (writtenHeap statics) := by
    intro b hb hl
    have hb6 : 6 ≤ b := hb
    simp (disch := omega) [Heap.live, writtenHeap, Heap.empty, Tbl.get, Tbl.empty,
      Array.getD_eq_getD_getElem?, List.getElem?_eq_none, default] at hl
    have hz : [none, none, some writtenState][b]? = none := List.getElem?_eq_none (by change 3 ≤ b; omega)
    simp [hz] at hl
  have hu : Zlib.Gzlib.Spec.Uniq (writtenHeap statics) := by
    intro b
    have hc : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨ 6 ≤ b := by omega
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | hb
    all_goals simp (disch := omega) [writtenHeap, Heap.empty, Tbl.get, Tbl.empty,
      Zlib.Gzlib.Spec.cnt, Array.getD_eq_getD_getElem?, List.getElem?_eq_none, default]
    all_goals first | decide | split <;> omega
  have hp : CString (writtenHeap statics) (.ref (.blk 3) 0) [112] :=
    ⟨Or.inr ⟨.blk 3, 0, #[112, 0], rfl, rfl, by decide, rfl⟩, by decide, by decide⟩
  have hpb : MallocBuffer (writtenHeap statics) (.ref (.blk 3) 0) 2 :=
    ⟨3, #[112, 0], rfl, rfl, rfl, by decide⟩
  have hib : MallocBuffer (writtenHeap statics) (.ref (.blk 5) 0) 16 :=
    ⟨5, #[112, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], rfl, rfl, rfl, by decide⟩
  refine ⟨rfl, Or.inr rfl, hf, hu, hg, ⟨[112], hp, hpb⟩, Or.inl rfl, ?_, by decide, by decide, ?_, ?_⟩
  · intro _; rfl
  · intro _
    refine ⟨rfl, hib, ?_⟩
    intro hc
    have hn : ¬ (writtenState.mode = GZ_READ ∨ writtenState.direct = 0) := by decide
    exact (hn hc).elim
  · intro hhave
    exact (hhave rfl).elim

/-- Exactly the original gzip handle, private path and input buffer are
owned; the active external borrow has no malloc identity. -/
theorem written_owned (b : Nat) :
    GzOwned (writtenHeap statics) 2 writtenState b ↔ b = 2 ∨ b = 3 ∨ b = 5 := by
  have hsize : writtenState.size = 8 := rfl
  have hdir : writtenState.direct = 1 := rfl
  have hmode : writtenState.mode = GZ_WRITE := rfl
  have hpath : writtenState.path = .ref (.blk 3) 0 := rfl
  have hin : writtenState.«in» = .ref (.blk 5) 0 := rfl
  have hmsg : writtenState.msg = .null := rfl
  simp [GzOwned, hsize, hdir, hmode, hpath, hin, hmsg, GZ_WRITE, GZ_READ, eq_comm]

/-- Only the two original caller byte objects remain live after close. -/
theorem final_live (statics : Statics) (b : Nat) :
    (finalHeap statics).live b ↔ b = 0 ∨ b = 1 := by
  by_cases h0 : b = 0
  · subst b; exact ⟨fun _ => Or.inl rfl, fun _ => Or.inl (by intro hz; cases hz)⟩
  by_cases h1 : b = 1
  · subst b; exact ⟨fun _ => Or.inr rfl, fun _ => Or.inl (by intro hz; cases hz)⟩
  simp only [h0, h1, or_self, iff_false]
  have hc : b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨ b = 6 ∨ b = 7 ∨ 8 ≤ b := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | hb
  all_goals first
    | exact Heap.slotUsed_eq_false.mp rfl
    | simp (disch := omega) [Heap.live, finalHeap, Heap.empty, Tbl.get, Tbl.empty,
        Array.getD_eq_getD_getElem?, List.getElem?_eq_none, default]
  have hz : ([none, none, none] : List (Option GzState))[b]? = none :=
    List.getElem?_eq_none (by change 3 ≤ b; omega)
  simp [hz]

/-- The complete final heap contains exactly the caller's original live set.
No fresh readonly object or message temporary survives this history. -/
theorem final_no_new_live (statics : Statics) :
    LiveChange (callerHeap statics) (finalHeap statics) (fun _ => False) (fun _ => False) := by
  intro b
  rw [final_live]
  simp only [not_false_eq_true, and_true, or_false]
  by_cases h0 : b = 0
  · subst b; exact ⟨fun _ => Or.inl (by intro hz; cases hz), fun _ => Or.inl rfl⟩
  by_cases h1 : b = 1
  · subst b; exact ⟨fun _ => Or.inl (by intro hz; cases hz), fun _ => Or.inr rfl⟩
  simp only [h0, h1, or_self, false_iff]
  have hf := (caller_fresh_uniq statics).1
  exact hf b (by change 2 ≤ b; omega)

/-- The close removes exactly the original owned objects and creates none.
The external error borrow is still valid metadata, never a leaked allocation. -/
theorem close_live_ledger (statics : Statics) (hg : LibraryGlobals (callerHeap statics)) :
    LiveChange (writtenHeap statics) (finalHeap statics) (fun _ => False)
      (GzOwned (writtenHeap statics) 2 writtenState) := by
  intro b
  rw [final_live, written_owned]
  simp only [not_or, or_false]
  by_cases hsmall : b < 6
  · have hc : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 := by omega
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [Heap.live, writtenHeap, Heap.empty, Tbl.get, Tbl.empty, default]
  · have hl := (written_valid statics hg).2.2.1 b (by change 6 ≤ b; omega)
    have h0 : b ≠ 0 := by omega
    have h1 : b ≠ 1 := by omega
    simp [hl, h0, h1]

/-- Allocation success, valid descriptor and writer mode are the same entry
conditions as the original finding. The empty file remains empty after EFBIG. -/
theorem entry_and_cleanup (statics : Statics) :
    NoAllocationFailure (writtenHeap statics) ∧ WriterReady writtenState ∧
    DescriptorPresent openedFs writtenState.fd ∧
    (finalHeap statics).gzstates 2 = none ∧ (finalHeap statics).bytes 3 = none ∧
    (finalHeap statics).bytes 5 = none ∧ (finalHeap statics).bytes 6 = none ∧
    (finalHeap statics).bytes 7 = none ∧ finalFs.fds[3]? = some none ∧
    finalFs.nodes[0]!.data = #[] ∧ (finalHeap statics).libcErrorBorrow = some (1, EFBIG) := by
  refine ⟨?_, ?_, ⟨by decide, ?_⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro n; rfl
  · unfold WriterReady; decide
  · exact ⟨{ node := 0, pos := 0, rd := false, wr := true, append := false }, rfl⟩

/-- Only the error handler's message allocation is refused. Open, private
path and input-buffer allocation still succeed before the failing close. -/
def refuseMessage (n : Nat) : Bool := !(n == 3)

def refusalCallerHeap (statics : Statics) : Heap := { callerHeap statics with allocOk := refuseMessage }
def refusalWrittenHeap (statics : Statics) : Heap := { writtenHeap statics with allocOk := refuseMessage }
def refusalFinalHeap (statics : Statics) : Heap :=
  { finalHeap statics with
    bytes := ⟨#[some #[112, 0], some #[119, 84, 0], none, none, none, none]⟩
    ro := ⟨#[false, false, false, false, false, false]⟩
    nextBlk := 6, allocOk := refuseMessage }

set_option maxRecDepth 20000 in
/-- The same public prefix remains real when only the later message malloc
will fail. Its input byte is accepted before that refusal. -/
theorem actual_refusal_prefix (statics : Statics) :
    (do let file ← gzopen (.ref (.blk 0) 0) (.ref (.blk 1) 0)
        let buffered ← StateT.lift (gzbuffer file 8)
        let wrote ← gzwrite file (.ref (.blk 0) 0) 1
        return (file, buffered, wrote)) initialFs (refusalCallerHeap statics) =
      .ok (((some (.in_gzstate_x 2), 0, 1), openedFs), refusalWrittenHeap statics) := by
  conv => lhs; cbv
  conv => rhs; cbv
  all_goals rfl

set_option maxRecDepth 20000 in
/-- The actual malloc-refusal error handler does not retain or free its
borrowed argument. Close still releases all gzip storage and closes fd3. -/
theorem actual_refusal_close (statics : Statics) :
    gzclose_w (some (.in_gzstate_x 2)) openedFs (refusalWrittenHeap statics) =
      .ok ((Z_MEM_ERROR, finalFs), refusalFinalHeap statics) := by
  conv => lhs; cbv
  conv => rhs; cbv
  all_goals rfl

set_option maxRecDepth 20000 in
/-- The complete public history also terminates without external malloc
storage when allocation of gzip's own copied error message is refused. -/
theorem actual_refusal_full_history (statics : Statics) :
    (do let file ← gzopen (.ref (.blk 0) 0) (.ref (.blk 1) 0)
        let buffered ← StateT.lift (gzbuffer file 8)
        let wrote ← gzwrite file (.ref (.blk 0) 0) 1
        let closed ← gzclose_w file
        return (buffered, wrote, closed)) initialFs (refusalCallerHeap statics) =
      .ok (((0, 1, Z_MEM_ERROR), finalFs), refusalFinalHeap statics) := by
  conv => lhs; cbv
  conv => rhs; cbv
  all_goals rfl

/-- Refusing the copied message leaves the same live table identities as the
successful-copy final heap; the unused table capacity is not an allocation. -/
theorem refusal_final_live (statics : Statics) (b : Nat) :
    (refusalFinalHeap statics).live b ↔ (finalHeap statics).live b := by
  by_cases hb : b < 8
  · have hc : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨ b = 6 ∨ b = 7 := by omega
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [Heap.live, refusalFinalHeap, finalHeap, Heap.empty, Tbl.get, Tbl.empty, default]
  · have hbytes : ([some #[112, 0], some #[119, 84, 0], none, none, none, none] : List (Option (Array UInt8)))[b]? = none :=
      List.getElem?_eq_none (by change 6 ≤ b; omega)
    have hstates : ([none, none, none] : List (Option GzState))[b]? = none :=
      List.getElem?_eq_none (by change 3 ≤ b; omega)
    have hbytesFinal : ([some #[112, 0], some #[119, 84, 0], none, none, none, none, none, none] : List (Option (Array UInt8)))[b]? = none :=
      List.getElem?_eq_none (by change 8 ≤ b; omega)
    simp [Heap.live, refusalFinalHeap, finalHeap, Heap.empty, Tbl.get, Tbl.empty,
      Array.getD_eq_getD_getElem?, hbytes, hbytesFinal, hstates, default]

/-- The refusal history also restores exactly the caller's original live set. -/
theorem refusal_final_no_new_live (statics : Statics) :
    LiveChange (refusalCallerHeap statics) (refusalFinalHeap statics) (fun _ => False) (fun _ => False) := by
  intro b
  rw [refusal_final_live]
  exact final_no_new_live statics b

#print axioms actual_prefix
#print axioms actual_close
#print axioms actual_full_history
#print axioms written_reachable
#print axioms written_valid
#print axioms final_no_new_live
#print axioms close_live_ledger
#print axioms actual_refusal_full_history
#print axioms refusal_final_no_new_live
end Zlib.Gzwrite.BorrowRegression
