import ZlibF.Proof.«deflate.c.engine.generic-foreign-owner-field-algebra»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- The foreign owner's table-level read-only flag is unchanged. -/
def ForeignOwnerReadonly (h after : Heap) (owner : Nat) : Prop := after.ro owner=h.ro owner

theorem ForeignOwnerReadonly.refl (h : Heap) (owner : Nat) : ForeignOwnerReadonly h h owner := rfl

theorem ForeignOwnerReadonly.of_same {h after : Heap} {owner : Nat}
    (same : after.ro owner=h.ro owner) : ForeignOwnerReadonly h after owner := same

theorem ForeignOwnerReadonly.trans {h middle after : Heap} {owner : Nat}
    (one : ForeignOwnerReadonly h middle owner) (two : ForeignOwnerReadonly middle after owner) :
    ForeignOwnerReadonly h after owner := Eq.trans two one

/-- Genuine private writes preserve every slot at the caller owner, including its table flag. -/
theorem ForeignOwnerReadonly.of_private_frame {h after : Heap} {r : ZStreamRef} {ds owner oo : Nat}
    {z : ZStream} {d : DeflateState} (good : DGood h r ds z d) (buffers : StreamBuffers h r)
    (pointer : z.next_out=.ref (.dstate_depth owner) oo)
    (frame : Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b)) :
    ForeignOwnerReadonly h after owner := by
  obtain ⟨foreign,get,_⟩ := caller_foreign_output good buffers pointer
  have live : h.live owner := by simp [Heap.live,get]
  exact (frame.2.2.2.2.2 owner live (caller_foreign_owner_outside good buffers pointer)).2.2.2.2.2.2.2

/-- Restoring depth changes no read-only table entry; the fine frame therefore checks the owner flag. -/
theorem ForeignOwnerReadonly.of_buffer_frame {h after : Heap} {r : ZStreamRef} {ds owner oo n : Nat}
    {z : ZStream} {d : DeflateState} (good : DGood h r ds z d) (buffers : StreamBuffers h r)
    (pointer : z.next_out=.ref (.dstate_depth owner) oo)
    (frame : BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,n⟩]) :
    ForeignOwnerReadonly h after owner := by
  obtain ⟨foreign,get,_⟩ := caller_foreign_output good buffers pointer
  have live : h.live owner := by simp [Heap.live,get]
  have same := (frame.1.2.2.2.2.2 owner live (caller_foreign_owner_outside good buffers pointer)).2.2.2.2.2.2.2
  have restored : (restoreRegions h after [⟨z.next_out,n⟩]).ro owner=after.ro owner := by
    simp only [restoreRegions,List.foldl_cons,List.foldl_nil,pointer,BRef.get_dstate_depth get]
    simp only [Space.put]
    split <;> rfl
  exact restored.symm.trans same

end Zlib.Deflate.Engine.Proofs
