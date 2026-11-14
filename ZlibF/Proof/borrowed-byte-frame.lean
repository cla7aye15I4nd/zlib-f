import ZlibF.Spec.Public.History
import ZlibF.Proof.LibcBorrow
import ZlibF.Spec.Functional.Api.Basic

/-!
# Allocation frames and volatile external byte views

The original allocation frame does not constrain libc's external borrow.
Transport of an external view additionally uses a stability observation
proved from the actual computation. No public frame or caller domain changes.
-/

namespace ZlibF.Spec.Public.BorrowedViews
open C C.LibcBorrow
set_option autoImplicit false

/-- Replacing a byte view writes malloc or embedded storage, never libc's
borrow metadata. This includes ignored writes to readonly static views. -/
theorem put_borrow (h : Heap) (ref : BRef) (a : Array UInt8) :
    (Space.put h ref a).libcErrorBorrow = h.libcErrorBorrow := by
  cases ref <;> first | rfl | (simp only [Space.put]; split <;> rfl)

/-- Updating one byte-reference family retains every distinct byte view,
including volatile strings whose borrow is untouched by the actual store. -/
theorem get_put_other (h : Heap) {dest source : BRef}
    (different : source ≠ dest) (a : Array UInt8) :
    (Space.get (Space.put h dest a) source : Option (Array UInt8)) = Space.get h source := by
  cases source with
  | str i => exact str_view_stable (Or.inr (put_borrow h dest a))
  | _ =>
    cases dest <;> simp_all [Space.get, Space.put, upd_ne]
    all_goals split <;> simp_all [Space.get, Space.put, upd_ne]

/-- Restoring output arrays for the allocation-frame check retains the
actual returned heap's external-borrow observation. -/
theorem restore_borrow (before after : Heap) (regions : List Region) :
    (restoreRegions before after regions).libcErrorBorrow = after.libcErrorBorrow := by
  induction regions generalizing after with
  | nil => rfl
  | cons region rest ih =>
    change (restoreRegions before
      (match region.pointer with
      | .null => after
      | .ref ref _ => match Space.get before ref with
        | none => after
        | some a => Space.put after ref a) rest).libcErrorBorrow = _
    rw [ih]
    cases pointer : region.pointer with
    | null => rfl
    | ref ref off =>
      cases get : (Space.get before ref : Option (Array UInt8)) with
      | none => simp only [get]
      | some a => simpa only [get] using put_borrow after ref a

/-- A real borrow-stability observation survives output restoration.
It is not inferred merely from the allocation frame. -/
theorem restore_stable {before after : Heap} {ref : BRef}
    (stable : BorrowStable before after ref) (regions : List Region) :
    BorrowStable before (restoreRegions before after regions) ref := by
  cases ref <;> simp only [BorrowStable] at stable ⊢
  rcases stable with source | same
  · exact Or.inl source
  · exact Or.inr ((restore_borrow before after regions).trans same)

/-- A frame transports byte contents outside its permitted allocations
when volatile external storage is stable on this same transition.
Ordinary source literals discharge stability through PersistentView.stable. -/
theorem frame_get {before after : Heap} {changed : Nat → Prop}
    {ref : BRef} {a : Array UInt8} {off : Nat}
    (frame : Frame before after changed)
    (get : Space.get before ref = some a)
    (outside : ∀ b, ByteRoot (.ref ref off) b → ¬ changed b)
    (stable : BorrowStable before after ref) :
    Space.get after ref = some a := by
  have slots := frame.2.2.2.2.2
  cases ref with
  | blk b =>
    have live : before.live b := by simp [Heap.live, show before.bytes b = some a from get]
    exact (slots b live (outside b rfl)).1.trans get
  | dstate_depth b =>
    cases state : before.dstates b with
    | none => simp [Space.get, state] at get
    | some value =>
      have live : before.live b := by simp [Heap.live, state]
      have same := slots b live (outside b rfl)
      change (after.dstates b).map (·.depth) = some a
      rw [same.2.2.2.2.1]
      exact get
  | str i => exact (str_view_stable stable).trans get
  | st_dist_code => change some after.static.dist_code = some a; rw [← frame.1]; exact get
  | st_length_code => change some after.static.length_code = some a; rw [← frame.1]; exact get

/-- Persistent view transport needs no external-state premise. Actual
volatile views instead use frame_get with their proved execution fact. -/
theorem frame_get_persistent {before after : Heap} {changed : Nat → Prop}
    {ref : BRef} {a : Array UInt8} {off : Nat}
    (frame : Frame before after changed)
    (get : Space.get before ref = some a)
    (outside : ∀ b, ByteRoot (.ref ref off) b → ¬ changed b)
    (persistent : PersistentView ref) : Space.get after ref = some a :=
  frame_get frame get outside persistent.stable

/-- The restored-output frame transports an input view distinct from the
output view, using stability from that same actual returned transition. -/
theorem buffer_other_get {before after : Heap} {changed : Nat → Prop}
    {source dest : BRef} {input output : Array UInt8} {readOff writeOff count : Nat}
    (frame : BufferFrame before after changed [⟨.ref dest writeOff, count⟩])
    (get : Space.get before source = some input)
    (getOutput : Space.get before dest = some output)
    (outside : ∀ b, ByteRoot (.ref source readOff) b → ¬ changed b)
    (different : source ≠ dest) (stable : BorrowStable before after source) :
    Space.get after source = some input := by
  have same := frame_get frame.1 get outside (restore_stable stable _)
  have restored : restoreRegions before after [⟨.ref dest writeOff, count⟩] =
      Space.put after dest output := by simp [restoreRegions, getOutput]
  rw [restored, get_put_other after different output] at same
  exact same

/-- The allocation frame intentionally permits a change in borrowed libc
storage. This is a model boundary, not a malloc leak or a C counterexample. -/
theorem frame_borrow_update (h : Heap) (borrow : Option (Nat × Int32)) :
    Frame h { h with libcErrorBorrow := borrow } (fun _ => False) := by
  simp [Frame]

/-- An explicit counterexample to transporting every static-index view
using an allocation frame alone. The new stable-view rule is necessary. -/
theorem frame_alone_can_invalidate_view :
    let before := { Heap.empty with libcErrorBorrow := some (1, (27 : Int32)) }
    let after := { before with libcErrorBorrow := some (2, (9 : Int32)) }
    let ref := BRef.str (libcErrnoIndex 1 27)
    Frame before after (fun _ => False) ∧
      Space.get before ref = some (strBytes (libcErrnoText 27)) ∧
      Space.get after ref = none := by
  refine ⟨frame_borrow_update _ _, (current_view _ 1 27 rfl).1, ?_⟩
  exact old_view_invalid _ 1 2 27 9 rfl (by decide)

#print axioms restore_borrow
#print axioms restore_stable
#print axioms get_put_other
#print axioms frame_get
#print axioms frame_get_persistent
#print axioms buffer_other_get
#print axioms frame_alone_can_invalidate_view
end ZlibF.Spec.Public.BorrowedViews
