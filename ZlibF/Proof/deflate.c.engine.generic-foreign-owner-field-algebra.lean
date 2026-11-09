import ZlibF.Proof.«deflate.c.engine.generic-foreign-macro-physical»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-owner-frame»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- All foreign owner fields are unchanged except its explicitly writable depth byte array. -/
def ForeignOwnerFields (h after : Heap) (owner : Nat) : Prop :=
  ∀ foreign, h.dstates owner=some foreign →
    ∃ next, after.dstates owner=some next ∧ {next with depth:=foreign.depth}=foreign

theorem ForeignOwnerFields.refl (h : Heap) (owner : Nat) : ForeignOwnerFields h h owner := by
  intro foreign get
  exact ⟨foreign,get,rfl⟩

theorem ForeignOwnerFields.of_same {h after : Heap} {owner : Nat}
    (same : after.dstates owner=h.dstates owner) : ForeignOwnerFields h after owner := by
  intro foreign get
  exact ⟨foreign,same.trans get,rfl⟩

theorem ForeignOwnerFields.trans {h middle after : Heap} {owner : Nat}
    (one : ForeignOwnerFields h middle owner) (two : ForeignOwnerFields middle after owner) :
    ForeignOwnerFields h after owner := by
  intro foreign get
  obtain ⟨mid,getM,fieldsM⟩ := one foreign get
  obtain ⟨next,getA,fieldsA⟩ := two mid getM
  refine ⟨next,getA,?_⟩
  have kept := congrArg (fun d : DeflateState => {d with depth:=foreign.depth}) fieldsA
  exact kept.trans fieldsM

/-- Public caller ownership excludes the foreign owner from every private object and stream root. -/
theorem caller_foreign_owner_outside {h : Heap} {r : ZStreamRef} {ds owner oo : Nat}
    {z : ZStream} {d : DeflateState} (good : DGood h r ds z d) (buffers : StreamBuffers h r)
    (pointer : z.next_out=.ref (.dstate_depth owner) oo) :
    ¬ (StreamRoot r owner ∨ DeflateOwned ds d owner) := by
  obtain ⟨_foreign,_get,_bound,_different,_frontier,noRoot⟩ := caller_foreign_output good buffers pointer
  obtain ⟨z0,getZ,_,output,_⟩ := buffers
  have same : z0=z := Option.some.inj (getZ.symm.trans good.live.hz)
  subst z0
  rw [pointer] at output
  rcases output with impossible | ⟨_,_,unowned⟩
  · cases impossible
  · intro inside
    rcases inside with root | owned
    · exact noRoot root
    · exact unowned owner rfl ((stream_owned_deflate good owner).mpr owned)

/-- Genuine private writes preserve the foreign owner's complete record. -/
theorem ForeignOwnerFields.of_private_frame {h after : Heap} {r : ZStreamRef} {ds owner oo : Nat}
    {z : ZStream} {d : DeflateState} (good : DGood h r ds z d) (buffers : StreamBuffers h r)
    (pointer : z.next_out=.ref (.dstate_depth owner) oo)
    (frame : Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b)) :
    ForeignOwnerFields h after owner := by
  apply ForeignOwnerFields.of_same
  obtain ⟨foreign,get,_⟩ := caller_foreign_output good buffers pointer
  have live : h.live owner := by simp [Heap.live,get]
  exact (frame.2.2.2.2.2 owner live (caller_foreign_owner_outside good buffers pointer)).2.2.2.2.1

/-- The full actual byte frame checks every non-depth foreign owner field after restoration. -/
theorem ForeignOwnerFields.of_buffer_frame {h after : Heap} {r : ZStreamRef} {ds owner oo n : Nat}
    {z : ZStream} {d : DeflateState} (good : DGood h r ds z d) (buffers : StreamBuffers h r)
    (pointer : z.next_out=.ref (.dstate_depth owner) oo)
    (frame : BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,n⟩]) :
    ForeignOwnerFields h after owner := by
  intro foreign get
  rw [pointer] at frame
  exact buffer_frame_foreign_owner_fields get (caller_foreign_owner_outside good buffers pointer) frame

end Zlib.Deflate.Engine.Proofs
