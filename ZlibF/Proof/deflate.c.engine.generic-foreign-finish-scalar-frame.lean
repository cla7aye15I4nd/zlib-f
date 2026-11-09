import ZlibF.Proof.«deflate.c.engine.generic-foreign-buffer-frame-restore»
import ZlibF.Proof.«deflate.c.engine.generic-wrapper-frames»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- A private scalar record store retains an already proved full foreign byte frame. -/
theorem foreign_finish_scalar_buffer_frame {h middle : Heap} {r : ZStreamRef} {ds owner oo produced : Nat}
    {z : ZStream} {d current result : DeflateState}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r)
    (pointer : z.next_out=.ref (.dstate_depth owner) oo)
    (get : middle.dstates ds=some current) (depth : result.depth=current.depth)
    (precise : BufferFrame h middle (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,produced⟩]) :
    BufferFrame h (setD middle ds result) (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,produced⟩] := by
  obtain ⟨foreign,beforeGet,_bound,different,_old,_notRoot⟩ := caller_foreign_output good buffers pointer
  rw [pointer] at precise ⊢
  obtain ⟨middleForeign,middleGet,_fields⟩ := buffer_frame_foreign_owner_fields beforeGet
    (caller_foreign_owner_outside good buffers pointer) precise
  exact generic_wrapper_foreign_setD_frame get beforeGet middleGet different (Or.inr (Or.inl rfl)) depth precise

end Zlib.Deflate.Engine.Proofs
