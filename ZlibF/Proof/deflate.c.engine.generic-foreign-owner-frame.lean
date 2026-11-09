import ZlibF.Proof.«deflate.c.engine.generic-foreign-public-pending»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- An existing foreign depth owner cannot alias any allocation created at or beyond init's birth frontier. -/
theorem foreign_depth_old_owner_disjoint {h : Heap} {owner created : Nat} {foreign : DeflateState}
    (fresh : Fresh h) (get : h.dstates owner = some foreign) (new : h.nextBlk ≤ created) : owner ≠ created := by
  have before := foreign_depth_owner_before_frontier fresh get
  omega

/-- A foreign-output BufferFrame preserves all owner fields except the depth bytes.
The equality obtained by restoring depth records every remaining field at once. -/
theorem buffer_frame_foreign_owner_fields {h after : Heap} {owner off n : Nat}
    {foreign : DeflateState} {changed : Nat → Prop}
    (get : h.dstates owner = some foreign) (outside : ¬ changed owner)
    (frame : BufferFrame h after changed [⟨.ref (.dstate_depth owner) off,n⟩]) :
    ∃ next, after.dstates owner = some next ∧ {next with depth := foreign.depth} = foreign := by
  have live : h.live owner := by simp [Heap.live,get]
  have state := (frame.1.2.2.2.2.2 owner live outside).2.2.2.2.1
  change (restoreRegions h after [⟨.ref (.dstate_depth owner) off,n⟩]).dstates owner = h.dstates owner at state
  simp only [restoreRegions,List.foldl_cons,List.foldl_nil,BRef.get_dstate_depth get] at state
  cases nextGet : after.dstates owner with
  | none =>
    simp only [Space.put,nextGet] at state
    rw [get] at state
    contradiction
  | some next =>
    rw [foreign_depth_put_exact nextGet,setD_dstates_same,get] at state
    exact ⟨next,rfl,Option.some.inj state⟩

end Zlib.Deflate.Engine.Proofs
