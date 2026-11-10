import ZlibF.Spec.Public.Sequences

namespace ZlibF.Spec.Public.CausalAllocationOracle
open C
set_option autoImplicit false

private theorem bytes_put {h : Heap} {ref : BRef} {array : Array UInt8} :
    (Space.put h ref array).allocOk = h.allocOk := by
  cases ref <;> simp only [Space.put]
  split <;> rfl

/-- Restoring caller byte views cannot alter the allocator's oracle. -/
theorem restore_regions (before after : Heap) (regions : List Region) :
    (restoreRegions before after regions).allocOk = after.allocOk := by
  induction regions generalizing after with
  | nil => rfl
  | cons region regions ih =>
    change (restoreRegions before
      (match region.pointer with
        | .null => after
        | .ref ref _ => match Space.get before ref with
          | none => after
          | some array => Space.put after ref array) regions).allocOk = after.allocOk
    rw [ih]
    cases region.pointer with
    | null => rfl
    | ref ref off =>
      cases get : (Space.get before ref : Option (Array UInt8)) with
      | none => simp only [get]
      | some array => simpa only [get] using (bytes_put (h := after) (ref := ref) (array := array))

/-- A proved actual frame transports the original allocation premise;
no successful allocation choice is added at an internal cut. -/
theorem frame_no_failure {before after : Heap} {changed : Nat → Prop}
    (frame : Frame before after changed) (noFailure : NoAllocationFailure before) :
    NoAllocationFailure after := by
  intro n
  rw [← frame.2.1]
  exact noFailure n

theorem buffer_frame_no_failure {before after : Heap} {changed : Nat → Prop}
    {regions : List Region} (frame : BufferFrame before after changed regions)
    (noFailure : NoAllocationFailure before) : NoAllocationFailure after := by
  have same : before.allocOk = after.allocOk := frame.1.2.1.trans (restore_regions before after regions)
  intro n
  rw [← same]
  exact noFailure n

theorem rebuffer_no_failure {before after : Heap} {r : ZStreamRef}
    (edit : Rebuffer before after r) (noFailure : NoAllocationFailure before) :
    NoAllocationFailure after :=
  frame_no_failure edit.2.2.2.1 noFailure

#print axioms restore_regions
#print axioms frame_no_failure
#print axioms buffer_frame_no_failure
#print axioms rebuffer_no_failure
end ZlibF.Spec.Public.CausalAllocationOracle
