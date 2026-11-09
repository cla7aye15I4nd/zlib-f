import ZlibF.Proof.«uncompr.c.local-wrapper-memory»

namespace Zlib.Uncompr.Proof.LocalWrapperShape
open C ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inflate.Local
set_option autoImplicit false

def SlotShape (before after : Heap) (b : Nat) : Prop :=
  (after.bytes b).isSome = (before.bytes b).isSome ∧
  (after.words b).isSome = (before.words b).isSome ∧
  (after.streams b).isSome = (before.streams b).isSome ∧
  (after.gzheaders b).isSome = (before.gzheaders b).isSome ∧
  (after.dstates b).isSome = (before.dstates b).isSome ∧
  (after.istates b).isSome = (before.istates b).isSome ∧
  (after.gzstates b).isSome = (before.gzstates b).isSome

def ShapeBelow (before after : Heap) (cutoff : Nat) : Prop :=
  ∀ b, b < cutoff → SlotShape before after b

theorem SlotShape.trans {a b c : Heap} {x : Nat} (first : SlotShape a b x) (second : SlotShape b c x) :
    SlotShape a c x := by
  obtain ⟨a0,a1,a2,a3,a4,a5,a6⟩ := first
  obtain ⟨b0,b1,b2,b3,b4,b5,b6⟩ := second
  exact ⟨b0.trans a0,b1.trans a1,b2.trans a2,b3.trans a3,b4.trans a4,b5.trans a5,b6.trans a6⟩

theorem ShapeBelow.trans {a b c : Heap} {cutoff : Nat}
    (first : ShapeBelow a b cutoff) (second : ShapeBelow b c cutoff) : ShapeBelow a c cutoff :=
  fun x below => (first x below).trans (second x below)

/-- Replacing an existing byte view cannot change its allocation type,
including embedded depth arrays. No read-only premise is needed for shape. -/
theorem byte_view_put_shape_unchecked {h : Heap} {ref : BRef} {old : Array UInt8}
    (get : Space.get h ref = some old) (array : Array UInt8) : Shape h (Space.put h ref array) := by
  cases ref with
  | blk i =>
    intro b
    by_cases same : b = i
    · subst b
      simp [Space.put, show h.bytes i = some old from get]
    · simp [Space.put, upd_ne _ _ _ _ same]
  | dstate_depth i =>
    cases stored : h.dstates i with
    | none => simp [Space.get, stored] at get
    | some state =>
      intro b
      by_cases same : b = i
      · subst b
        simp [Space.put, stored]
      · simp [Space.put, stored, upd_ne _ _ _ _ same]
  | str _ | st_dist_code | st_length_code => exact Shape.refl h

theorem slotShape_of_dead {h after : Heap} {b : Nat} (before : ¬ h.live b) (final : ¬ after.live b) :
    SlotShape h after b := by
  obtain ⟨a0,a1,a2,a3,a4,a5,a6⟩ := Heap.not_live.mp before
  obtain ⟨b0,b1,b2,b3,b4,b5,b6⟩ := Heap.not_live.mp final
  simp [SlotShape,a0,a1,a2,a3,a4,a5,a6,b0,b1,b2,b3,b4,b5,b6]

/-- A real framed output replacement retains the type of every older slot.
New live allocations are kept separate by the explicit cutoff discipline. -/
theorem shapeBelow_of_bufferFrame {h after : Heap} {cutoff : Nat} {changed : Nat → Prop}
    {dest : BRef} {off made : Nat} {array : Array UInt8}
    (get : Space.get h dest = some array)
    (frame : BufferFrame h after changed [⟨.ref dest off, made⟩])
    (privateAge : ∀ b, changed b → cutoff ≤ b)
    (noNewOld : ∀ b, b < cutoff → after.live b → h.live b) : ShapeBelow h after cutoff := by
  obtain ⟨next, nextGet, _, _⟩ := frame.2 ⟨.ref dest off, made⟩ (by simp) dest off array rfl get
  have typed := byte_view_put_shape_unchecked nextGet array
  have masked : Frame h (Space.put after dest array) changed := by
    simpa only [restoreRegions, List.foldl_cons, List.foldl_nil, get] using frame.1
  intro b below
  by_cases live : h.live b
  · have fields := masked.2.2.2.2.2 b live (fun owns => by have := privateAge b owns; omega)
    obtain ⟨p0,p1,p2,p3,p4,p5,p6⟩ := typed b
    exact ⟨p0.symm.trans (congrArg Option.isSome fields.1),
      p1.symm.trans (congrArg Option.isSome fields.2.1),
      p2.symm.trans (congrArg Option.isSome fields.2.2.1),
      p3.symm.trans (congrArg Option.isSome fields.2.2.2.1),
      p4.symm.trans (congrArg Option.isSome fields.2.2.2.2.1),
      p5.symm.trans (congrArg Option.isSome fields.2.2.2.2.2.1),
      p6.symm.trans (congrArg Option.isSome fields.2.2.2.2.2.2.1)⟩
  · exact slotShape_of_dead live (fun alive => live (noNewOld b below alive))

#print axioms byte_view_put_shape_unchecked
#print axioms shapeBelow_of_bufferFrame
end Zlib.Uncompr.Proof.LocalWrapperShape
