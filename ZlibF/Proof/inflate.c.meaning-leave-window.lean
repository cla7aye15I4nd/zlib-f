import ZlibF.Proof.«inflate.c.meaning-dictionary»
import ZlibF.Proof.«inflate.c.window-public-ring»
import ZlibF.Proof.«inflate.c.input-cursor»

/-!
# inflate.c: the window after `inf_leave`

At `inf_leave` zlib calls `updatewindow(strm, strm->next_out, out - strm->avail_out)`:
the `copy` bytes before the output cursor, this call's output since the check
base, go into the window. `leave_window_meaning` says what this does to
`WindowMeaning`: from the window of the output before the call, a successful
update gives the window of that output followed by the copied bytes. This
covers a window that is not yet allocated (`updatewindow` allocates it; then
the history before the call is empty) and a window that is allocated but empty
(`wsize = 0` after a reset). An allocation failure (`rc = 1`, zlib then enters
`MEM`) changes only the allocation counter: the state is the old one, the
window is still not allocated, and the old `WindowMeaning` still holds.

The only hypotheses are the stream invariant `Good`, the default allocator,
the bytes at the output range, and that the output buffer is not the window
block (from the caller range, `callerRange_private_window`).
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- `WindowMeaning` depends only on dictionary followed by output. -/
theorem windowMeaning_regroup {h : Heap} {s : InflateState} {dict out dict' out' : List UInt8}
    (same : dict ++ out = dict' ++ out') (window : WindowMeaning h s dict out) :
    WindowMeaning h s dict' out' := by
  unfold WindowMeaning at *
  rw [← same]
  exact window

/-- `WindowMeaning` does not see the heap when the window is empty and unset. -/
theorem windowMeaning_of_unset {h h' : Heap} {s : InflateState} {dict out : List UInt8}
    (unset : s.wsize = 0) (window : WindowMeaning h s dict out) : WindowMeaning h' s dict out := by
  rcases window with ⟨nonzero, _⟩ | empty
  · exact absurd unset nonzero
  · exact Or.inr empty

/-- `local int updatewindow(z_streamp strm, const Bytef *end, unsigned copy)` at
`inf_leave`: the `copy` bytes `bytes` before `end = .ref source (off + copy)`
are appended to the history of the window.

Outcomes: success (`rc = 0`) with the window of `out0 ++ bytes`; or allocation
failure (`rc = 1`) when no window was allocated, with the state unchanged, the
heap changed only in its allocation counter, and the old window meaning kept.
In both cases the state changes only in its window fields, the code tables and
the output bytes are kept. -/
theorem leave_window_meaning {h after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} {dict out0 bytes : List UInt8} {source : BRef} {off : Nat}
    {copy : UInt32} {rc : Int32}
    (good : Good h r zs z s) (allocator : z.zalloc = .fn "zcalloc")
    (window : WindowMeaning h s dict out0)
    (written : Bytes h (.ref source off) copy.toNat bytes)
    (unowned : ∀ w, s.window = .ref (.blk w) 0 → source ≠ .blk w)
    (run : C.run (updatewindow (some r) (.ref source (off + copy.toNat)) copy) h = .ok (rc, after)) :
    ∃ state, Good after r zs z state ∧ WindowStateFrame s state ∧
      (∀ ref : CodeRef, (Space.get after ref : Option (Array Code)) = Space.get h ref) ∧
      Bytes after (.ref source off) copy.toNat bytes ∧
      ((rc = 0 ∧ WindowMeaning after state dict (out0 ++ bytes)) ∨
       (rc = 1 ∧ state = s ∧ s.window = .null ∧
         after = setI { h with nalloc := h.nalloc + 1 } zs s ∧
         WindowMeaning after state dict out0)) := by
  obtain null | ⟨ref, i, a, ptr, get, fit, values⟩ := written
  · exact absurd null.1 (by simp)
  cases ptr
  obtain ⟨wr, heap1, state1, windowRun, good1, frame, sourceView, codeViews, outcome⟩ :=
    updatewindow_decoder_boundary (copy := copy) (eo := off + copy.toNat) good allocator get
      (by omega) fit unowned
  have same : (wr, heap1) = (rc, after) := by
    have := run.symm.trans windowRun
    cases this
    rfl
  cases same
  have view : Bytes after (.ref source off) copy.toNat bytes :=
    Or.inr ⟨source, off, a, rfl, sourceView, fit, values⟩
  refine ⟨state1, good1, frame, codeViews, view, ?_⟩
  rcases outcome with success | ⟨failure, null, stateEq, heapEq⟩
  · subst success
    left
    refine ⟨rfl, ?_⟩
    have separate : Separate (.ref source off) copy.toNat s.window (2 ^ s.wbits.toNat) := by
      rcases good.inv.win.block with isNull | ⟨w, _, isWindow, _⟩
      · simp [Separate, isNull]
      · simp [Separate, isWindow, unowned w isWindow]
    have install : ∀ o, InflateDictionary h s o →
        InflateDictionary after state1
          ((o ++ bytes).drop ((o ++ bytes).length - 2 ^ s.wbits.toNat)) := by
      intro o old
      obtain ⟨v, after', state', run', good', result⟩ :=
        updatewindow_dictionary_public good allocator get fit values old separate
      have same' : (v, after') = ((0 : Int32), after) := by
        have := run'.symm.trans windowRun
        cases this
        rfl
      cases same'
      have states : state' = state1 :=
        Option.some.inj (good'.live.hs.symm.trans good1.live.hs)
      subst states
      rcases result with ⟨_, dictionary⟩ | ⟨one, _⟩
      · exact dictionary
      · exact absurd one (by decide)
    have wbitsEq : state1.wbits = s.wbits := by rw [frame]
    have old : WindowMeaning h s (dict ++ out0) [] :=
      windowMeaning_regroup (by simp) window
    have next : WindowMeaning after state1 ((dict ++ out0) ++ bytes) [] :=
      window_after_dictionary old good.inv.win good1.inv.win wbitsEq install
    exact windowMeaning_regroup (by simp) next
  · right
    subst stateEq
    refine ⟨failure, rfl, null, heapEq, ?_⟩
    exact windowMeaning_of_unset (good.inv.win.nullws null) window

/-- The same with the output start as a pointer and the cursor advanced over
the copied bytes, as `LoopMatches` holds them (`put = inputAdvance start n`). -/
theorem leave_window_meaning_cursor {h after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} {dict out0 bytes : List UInt8} {start : BPtr} {copy : UInt32} {rc : Int32}
    (good : Good h r zs z s) (allocator : z.zalloc = .fn "zcalloc")
    (window : WindowMeaning h s dict out0)
    (nonnull : start ≠ .null)
    (written : Bytes h start copy.toNat bytes)
    (unowned : ∀ w source off, start = .ref source off → s.window = .ref (.blk w) 0 →
      source ≠ .blk w)
    (run : C.run (updatewindow (some r) (inputAdvance start copy.toNat) copy) h = .ok (rc, after)) :
    ∃ state, Good after r zs z state ∧ WindowStateFrame s state ∧
      (∀ ref : CodeRef, (Space.get after ref : Option (Array Code)) = Space.get h ref) ∧
      Bytes after start copy.toNat bytes ∧
      ((rc = 0 ∧ WindowMeaning after state dict (out0 ++ bytes)) ∨
       (rc = 1 ∧ state = s ∧ s.window = .null ∧
         after = setI { h with nalloc := h.nalloc + 1 } zs s ∧
         WindowMeaning after state dict out0)) := by
  cases start with
  | null => exact absurd rfl nonnull
  | ref source off =>
    exact leave_window_meaning good allocator window written
      (fun w => unowned w source off rfl) run

#print axioms leave_window_meaning
#print axioms leave_window_meaning_cursor

end Zlib.Inflate.Proofs
