import ZlibF.Proof.«deflate.c.engine.generic-wrapper-foreign-view»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-caller-publication»
import ZlibF.Proof.«deflate.c.init.frame»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Proofs.DefaultInit
set_option autoImplicit false

theorem generic_wrapper_frame_trans {h g j : Heap} {changed : Nat → Prop}
    (first : Frame h g changed) (second : Frame g j changed) : Frame h j changed := by
  obtain ⟨staticA, allocA, garbageA, frontierA, countA, slotsA⟩ := first
  obtain ⟨staticB, allocB, garbageB, frontierB, countB, slotsB⟩ := second
  refine ⟨staticA.trans staticB, allocA.trans allocB, garbageA.trans garbageB,
    Nat.le_trans frontierA frontierB, Nat.le_trans countA countB, ?_⟩
  intro x live outside
  have same := slotsA x live outside
  exact SlotSame.trans same (slotsB x ((SlotSame.live same).mpr live) outside)

/-- Private prefix stores which leave the foreign caller view exact compose
with its actual publication frame without a fresh caller precondition. -/
theorem generic_wrapper_foreign_private_prefix {h ready after : Heap} {owner off n : Nat}
    {changed : Nat → Prop}
    (privateFrame : Frame h ready changed)
    (view : Space.get ready (BRef.dstate_depth owner) = (Space.get h (BRef.dstate_depth owner) : Option (Array UInt8)))
    (precise : BufferFrame ready after changed [⟨.ref (.dstate_depth owner) off, n⟩]) :
    BufferFrame h after changed [⟨.ref (.dstate_depth owner) off, n⟩] := by
  have restored : restoreRegions h after [⟨.ref (.dstate_depth owner) off, n⟩] =
      restoreRegions ready after [⟨.ref (.dstate_depth owner) off, n⟩] := by
    simp only [restoreRegions, List.foldl_cons, List.foldl_nil, view]
  refine ⟨?_, ?_⟩
  · rw [restored]
    exact generic_wrapper_frame_trans privateFrame precise.1
  · intro region member ref offset array pointer get
    have only := List.mem_singleton.mp member
    subst region
    obtain ⟨sameRef,sameOff⟩ := Ptr.ref.inj pointer
    subst ref offset
    exact precise.2 ⟨.ref (.dstate_depth owner) off,n⟩ (by simp) (BRef.dstate_depth owner) off array rfl (view.trans get)

/-- A subsequent scalar store in the current private record leaves the
foreign region frame intact. The caller owner is distinct from that record. -/
theorem generic_wrapper_foreign_setD_frame {before middle : Heap} {ds owner off n : Nat}
    {current result foreignBefore foreignMiddle : DeflateState} {changed : Nat → Prop}
    (state : middle.dstates ds = some current)
    (beforeGet : before.dstates owner = some foreignBefore)
    (middleGet : middle.dstates owner = some foreignMiddle)
    (different : owner ≠ ds) (privateFrame : changed ds) (depth : result.depth = current.depth)
    (precise : BufferFrame before middle changed [⟨.ref (.dstate_depth owner) off, n⟩]) :
    BufferFrame before (setD middle ds result) changed [⟨.ref (.dstate_depth owner) off, n⟩] := by
  let restoredMiddle := setD middle owner {foreignMiddle with depth := foreignBefore.depth}
  let restoredAfter := setD (setD middle ds result) owner {foreignMiddle with depth := foreignBefore.depth}
  have middleRestore : restoreRegions before middle [⟨.ref (.dstate_depth owner) off,n⟩] = restoredMiddle := by
    simp only [restoreRegions,List.foldl_cons,List.foldl_nil,BRef.get_dstate_depth beforeGet]
    exact foreign_depth_put_exact middleGet _
  have afterGet : (setD middle ds result).dstates owner = some foreignMiddle := by
    simpa only [setD_dstates_ne _ _ _ _ different] using middleGet
  have afterRestore : restoreRegions before (setD middle ds result) [⟨.ref (.dstate_depth owner) off,n⟩] = restoredAfter := by
    simp only [restoreRegions,List.foldl_cons,List.foldl_nil,BRef.get_dstate_depth beforeGet]
    exact foreign_depth_put_exact afterGet _
  have scalarFrame : Frame restoredMiddle restoredAfter changed := by
    refine ⟨rfl,rfl,rfl,Nat.le_refl _,Nat.le_refl _,?_⟩
    intro x _live outside
    have other : x ≠ ds := fun same => outside (same ▸ privateFrame)
    by_cases own : x = owner
    · subst x
      simp [SlotSame,restoredMiddle,restoredAfter,setD,upd_apply,different]
    · simp [SlotSame,restoredMiddle,restoredAfter,setD,upd_apply,own,other]
  refine ⟨?_,?_⟩
  · rw [afterRestore]
    have first := precise.1
    rw [middleRestore] at first
    exact generic_wrapper_frame_trans first scalarFrame
  · intro region member ref offset array pointer get
    obtain ⟨next,getNext,sizeNext,outside⟩ := precise.2 region member ref offset array pointer get
    exact ⟨next,(byte_view_setD_depth state depth ref).trans getNext,sizeNext,outside⟩

end Zlib.Deflate.Engine.Proofs
#print axioms Zlib.Deflate.Engine.Proofs.generic_wrapper_frame_trans
#print axioms Zlib.Deflate.Engine.Proofs.generic_wrapper_foreign_private_prefix
#print axioms Zlib.Deflate.Engine.Proofs.generic_wrapper_foreign_setD_frame
