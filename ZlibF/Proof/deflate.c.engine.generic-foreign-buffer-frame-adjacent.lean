import ZlibF.Proof.«deflate.c.engine.generic-foreign-buffer-frame-restore»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Proofs.DefaultInit
set_option autoImplicit false

/-- A genuine foreign-depth byte frame supplies owner field retention, its table flag,
and the corresponding coarse old-object frame. No array interval alone implies these facts. -/
theorem foreign_buffer_frame_owner_facts {h after : Heap} {owner offset produced : Nat}
    {foreign : DeflateState} {changed : Nat → Prop}
    (get : h.dstates owner=some foreign) (outside : ¬ changed owner)
    (frame : BufferFrame h after changed [⟨.ref (.dstate_depth owner) offset,produced⟩]) :
    ForeignOwnerFields h after owner ∧ ForeignOwnerReadonly h after owner ∧
      Frame h after (fun b => changed b ∨ b=owner) := by
  have fields : ForeignOwnerFields h after owner := by
    intro old oldGet
    exact buffer_frame_foreign_owner_fields oldGet outside frame
  obtain ⟨next,getNext,nonDepth⟩ := fields foreign get
  have restored : restoreRegions h after [⟨.ref (.dstate_depth owner) offset,produced⟩] = setD after owner foreign := by
    simp only [restoreRegions,List.foldl_cons,List.foldl_nil,BRef.get_dstate_depth get]
    rw [foreign_depth_put_exact getNext,nonDepth]
  have kept := frame.1
  rw [restored] at kept
  have live : h.live owner := by simp [Heap.live,get]
  have readonly : ForeignOwnerReadonly h after owner := (kept.2.2.2.2.2 owner live outside).2.2.2.2.2.2.2
  refine ⟨fields,readonly,?_⟩
  obtain ⟨static,alloc,garbage,nextBlk,nalloc,slots⟩ := kept
  refine ⟨static,alloc,garbage,nextBlk,nalloc,?_⟩
  intro b live outside
  have different : b≠owner := fun eq => outside (Or.inr eq)
  have original := slots b live (fun yes => outside (Or.inl yes))
  obtain ⟨a,bw,c,d,e,f,g,hr⟩ := slot_setD_except after owner foreign b different
  exact ⟨a.symm.trans original.1,bw.symm.trans original.2.1,c.symm.trans original.2.2.1,
    d.symm.trans original.2.2.2.1,e.symm.trans original.2.2.2.2.1,
    f.symm.trans original.2.2.2.2.2.1,g.symm.trans original.2.2.2.2.2.2.1,
    hr.symm.trans original.2.2.2.2.2.2.2⟩

/-- Adjacent actual byte frames compose on one foreign depth view. The initial owner
is outside the private footprint; shape and uniqueness retain its other object slots. -/
theorem foreign_buffer_frame_adjacent {h middle after : Heap} {owner offset first second : Nat}
    {foreign : DeflateState} {changed : Nat → Prop}
    (one : BufferFrame h middle changed [⟨.ref (.dstate_depth owner) offset,first⟩])
    (two : BufferFrame middle after changed [⟨.ref (.dstate_depth owner) (offset+first),second⟩])
    (shapeOne : Shape h middle) (shapeTwo : Shape middle after) (unique : Uniq h)
    (get : h.dstates owner=some foreign) (outside : ¬ changed owner) :
    BufferFrame h after changed [⟨.ref (.dstate_depth owner) offset,first+second⟩] := by
  obtain ⟨fieldsOne,readonlyOne,frameOne⟩ := foreign_buffer_frame_owner_facts get outside one
  obtain ⟨mid,getMid,_⟩ := fieldsOne foreign get
  obtain ⟨fieldsTwo,readonlyTwo,frameTwo⟩ := foreign_buffer_frame_owner_facts getMid outside two
  exact foreign_buffer_frame_of_fields
    (full_frame_trans_shape frameOne frameTwo shapeOne) (shapeOne.trans shapeTwo) unique get
    (fieldsOne.trans fieldsTwo) (readonlyOne.trans readonlyTwo)
    ((ByteOutputInterval.of_buffer_frame one).trans (ByteOutputInterval.of_buffer_frame two))

end Zlib.Deflate.Engine.Proofs
