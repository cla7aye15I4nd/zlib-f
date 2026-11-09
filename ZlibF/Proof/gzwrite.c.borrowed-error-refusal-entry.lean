import ZlibF.Proof.«gzwrite.c.borrowed-error-regression»

/-! # Public entry and full closing effects for the refusal regression -/
namespace Zlib.Gzwrite.BorrowRegression
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib Zlib.Gzwrite
open ZlibF.Spec.Public

def refusalOpenedHeap (st : Statics) : Heap := { openedHeap st with allocOk := refuseMessage }
def refusalSmallHeap (st : Statics) : Heap := { smallHeap st with allocOk := refuseMessage }
set_option maxRecDepth 20000 in
theorem actual_refusal_open (statics : Statics) :
    gzopen (.ref (.blk 0) 0) (.ref (.blk 1) 0) initialFs (refusalCallerHeap statics) =
      .ok ((some (.in_gzstate_x 2), openedFs), refusalOpenedHeap statics) := by
  conv => lhs; cbv
  conv => rhs; cbv
  all_goals rfl

set_option maxRecDepth 20000 in
theorem actual_refusal_buffer (statics : Statics) :
    gzbuffer (some (.in_gzstate_x 2)) 8 (refusalOpenedHeap statics) = .ok (0, refusalSmallHeap statics) := by
  conv => lhs; cbv
  conv => rhs; cbv
  all_goals rfl

set_option maxRecDepth 20000 in
theorem actual_refusal_write (statics : Statics) :
    gzwrite (some (.in_gzstate_x 2)) (.ref (.blk 0) 0) 1 openedFs (refusalSmallHeap statics) =
      .ok ((1, openedFs), refusalWrittenHeap statics) := by
  conv => lhs; cbv
  conv => rhs; cbv
  all_goals rfl

/-- Ordinary caller storage, not fabricated initialized private buffers. -/
theorem refusal_caller_fresh_uniq (statics : Statics) : Fresh (refusalCallerHeap statics) ∧ Zlib.Gzlib.Spec.Uniq (refusalCallerHeap statics) := by
  constructor
  · intro b hb hl
    have hb2 : 2 ≤ b := hb
    simp (disch := omega) [Heap.live, refusalCallerHeap, callerHeap, Heap.empty, Tbl.get, Tbl.empty,
      Array.getD_eq_getD_getElem?, List.getElem?_eq_none, default] at hl
  · intro b
    simp [refusalCallerHeap, callerHeap, Heap.empty, Zlib.Gzlib.Spec.cnt, Tbl.get, Tbl.empty, default]
    split <;> omega

/-- Public argument legality and actual execution establish this same history. -/
theorem refusal_written_reachable (statics : Statics) (hg : LibraryGlobals (refusalCallerHeap statics)) :
    GzReachable (refusalWrittenHeap statics) openedFs 2 := by
  have hc := refusal_caller_fresh_uniq statics
  have hp : CString (refusalCallerHeap statics) (.ref (.blk 0) 0) [112] :=
    ⟨Or.inr ⟨.blk 0, 0, #[112, 0], rfl, rfl, by decide, rfl⟩, by decide, by decide⟩
  have hm : CString (refusalCallerHeap statics) (.ref (.blk 1) 0) [119, 84] :=
    ⟨Or.inr ⟨.blk 1, 0, #[119, 84, 0], rfl, rfl, by decide, rfl⟩, by decide, by decide⟩
  have ho := GzReachable.open hc.1 hc.2 hg initial_world_valid hp hm (actual_refusal_open statics)
  have hbexec : (Call.gzbuffer (some (.in_gzstate_x 2)) 8).execute openedFs (refusalOpenedHeap statics) =
      .ok (((0 : Int32), openedFs), refusalSmallHeap statics) := by
    simp only [Call.execute, heapCall, actual_refusal_buffer]
  have hb := GzReachable.step ho (show (refusalOpenedHeap statics).gzstates 2 = some openedState from rfl)
    (show GzOperation 2 (.gzbuffer (some (.in_gzstate_x 2)) 8) from rfl)
    (show GzArguments (refusalOpenedHeap statics) 2 openedState (.gzbuffer (some (.in_gzstate_x 2)) 8) from True.intro) hbexec
  have ha : GzArguments (refusalSmallHeap statics) 2 smallState
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
  exact GzReachable.step hb (show (refusalSmallHeap statics).gzstates 2 = some smallState from rfl)
    (show GzOperation 2 (.gzwrite (some (.in_gzstate_x 2)) (.ref (.blk 0) 0) 1) from rfl)
    ha (actual_refusal_write statics)


/-- Allocation outcomes do not alter the same public memory invariant. -/
theorem refusal_written_valid (st : Statics) (hg : LibraryGlobals (callerHeap st)) :
    GzValid (refusalWrittenHeap st) 2 writtenState := by
  exact written_valid st hg

/-- The failing message allocation does not change the exact initial ownership. -/
theorem refusal_written_owned (st : Statics) (b : Nat) :
    GzOwned (refusalWrittenHeap st) 2 writtenState b ↔ b = 2 ∨ b = 3 ∨ b = 5 := by
  exact written_owned (statics := st) b

/-- Both close outcomes remove precisely the original owned objects. -/
theorem refusal_close_live_ledger (st : Statics) (hg : LibraryGlobals (callerHeap st)) :
    LiveChange (refusalWrittenHeap st) (refusalFinalHeap st) (fun _ => False)
      (GzOwned (refusalWrittenHeap st) 2 writtenState) := by
  intro b
  rw [refusal_final_live]
  exact close_live_ledger st hg b

#print axioms refusal_written_reachable
#print axioms refusal_written_valid
#print axioms refusal_close_live_ledger
end Zlib.Gzwrite.BorrowRegression
