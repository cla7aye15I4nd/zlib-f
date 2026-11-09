import ZlibF.Proof.«uncompr.c.local-wrapper-shape-loop»

namespace Zlib.Uncompr.Proof.LocalWrapperShape
open C ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inflate.Local
open Zlib.Uncompr.Proof.Finish Zlib.Uncompr.Proof.Wrapper
set_option autoImplicit false

theorem store_shape {h after : Heap} {p : BPtr} {xs : List UInt8} (store : Store h p xs after) :
    Shape h after := by
  rcases store with ⟨_, same⟩ | ⟨ref, off, array, _, get, _, _, same⟩
  · subst after; exact Shape.refl h
  · subst after; exact byte_view_put_shape_unchecked get _

theorem freeWin_shapeBelow (h : Heap) (window : BPtr) (cutoff : Nat)
    (age : ∀ w, window = .ref (.blk w) 0 → cutoff ≤ w) : ShapeBelow h (freeWin h window) cutoff := by
  intro b below
  unfold freeWin
  split
  · rename_i oldPointer w
    have different : b ≠ w := by have := age w rfl; omega
    simp [SlotShape, upd_ne _ _ _ _ different]
  · exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem end_shapeBelow (h : Heap) (cutoff b zs : Nat) (z : ZStream) (s : InflateState)
    (streamAge : cutoff ≤ b) (stateAge : cutoff ≤ zs)
    (windowAge : ∀ w, s.window = .ref (.blk w) 0 → cutoff ≤ w) :
    ShapeBelow h ((.tab b : ZStreamRef).put (endHeap h zs s) {z with state := none}) cutoff := by
  have first := freeWin_shapeBelow h s.window cutoff windowAge
  have second : ShapeBelow (freeWin h s.window) (endHeap h zs s) cutoff := by
    intro x below
    have different : x ≠ zs := by omega
    simp [SlotShape,endHeap,freeIst,upd_ne _ _ _ _ different]
  have third : ShapeBelow (endHeap h zs s)
      ((.tab b : ZStreamRef).put (endHeap h zs s) {z with state := none}) cutoff := by
    intro x below
    have different : x ≠ b := by omega
    cases stored : (endHeap h zs s).streams b <;>
      simp [SlotShape, ZStreamRef.put, stored, upd_ne _ _ _ _ different]
  exact first.trans (second.trans third)

theorem released_shapeBelow (h : Heap) (cutoff stream reserved : Nat)
    (streamAge : cutoff ≤ stream) (reservedAge : cutoff ≤ reserved) :
    ShapeBelow h (releasedHeap h stream reserved) cutoff := by
  intro x below
  have a : x ≠ stream := by omega
  have b : x ≠ reserved := by omega
  simp [SlotShape,releasedHeap,upd_ne _ _ _ _ a,upd_ne _ _ _ _ b]

/-- Initialization changes only the newly allocated private identities. -/
theorem core_shapeBelow (h : Heap) (source dest : BPtr) (capacity : UInt64) :
    ShapeBelow h (coreHeap h source dest capacity) h.nextBlk := by
  intro b below
  have a : b ≠ h.nextBlk := by omega
  have c : b ≠ h.nextBlk + 1 := by omega
  have d : b ≠ h.nextBlk + 2 := by omega
  simp [SlotShape,coreHeap_eq,upd_ne _ _ _ _ a,upd_ne _ _ _ _ c,upd_ne _ _ _ _ d]

/-- Typed shape, rather than mere live-set equality, transports any caller
allocation cutoff. It need not be the decoder's later initialization cutoff. -/
theorem Shape.uniqueFrom {h after : Heap} (shape : Shape h after) (callerCutoff : Nat)
    (unique : UniqueFrom h callerCutoff) : UniqueFrom after callerCutoff := by
  intro b old
  have bound := unique b old
  obtain ⟨e0,e1,e2,e3,e4,e5,e6⟩ := shape b
  simpa only [cnt,e0,e1,e2,e3,e4,e5,e6] using bound

#print axioms store_shape
#print axioms freeWin_shapeBelow
#print axioms end_shapeBelow
#print axioms released_shapeBelow
#print axioms core_shapeBelow
#print axioms Shape.uniqueFrom
end Zlib.Uncompr.Proof.LocalWrapperShape
