import ZlibF.Proof.«deflate.c.engine.generic-foreign-pending-semantics»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Proofs.DefaultInit
set_option autoImplicit false

/-- The private stream updates and the caller depth interval form the public buffer frame.
The foreign record is restored field-for-field except for its permitted depth interval. -/
theorem foreign_output_private_buffer_frame {h : Heap} {r : ZStreamRef} {ds po owner oo : Nat}
    {stream : ZStream} {result foreign : DeflateState} {pending : Array UInt8} (n : UInt32)
    (get : h.dstates owner = some foreign) (different : owner ≠ ds)
    (bound : oo + n.toNat ≤ foreign.depth.size) :
    BufferFrame h (setD (r.put (setD h owner { foreign with depth := copyRange foreign.depth pending oo po n.toNat }) stream) ds result)
      (fun x => StreamRoot r x ∨ x = ds) [⟨.ref (.dstate_depth owner) oo, n.toNat⟩] := by
  let next := copyRange foreign.depth pending oo po n.toNat
  let copied := setD h owner { foreign with depth := next }
  let after := setD (r.put copied stream) ds result
  have afterGet : after.dstates owner = some { foreign with depth := next } := by
    simp [after,copied,next,different]
  have restored : restoreRegions h after [⟨.ref (.dstate_depth owner) oo, n.toNat⟩] = setD after owner foreign := by
    simp only [restoreRegions,List.foldl_cons,List.foldl_nil,BRef.get_dstate_depth get]
    rw [foreign_depth_put_exact afterGet]
  refine ⟨?_, ?_⟩
  · rw [restored]
    refine ⟨by simp [after,copied],by simp [after,copied],
      by simp [after,copied],by simp [after,copied],
      by simp [after,copied],?_⟩
    intro x _ outside
    have noRoot : ¬ StreamRoot r x := fun same => outside (Or.inl same)
    have noPrivate : x ≠ ds := fun same => outside (Or.inr same)
    have privateSlots : SlotSame copied after x :=
      (slot_put_except copied r stream x noRoot).trans
        (slot_setD_except (r.put copied stream) ds result x noPrivate)
    by_cases same : x = owner
    · subst x
      obtain ⟨bytes,words,streams,headers,_,istates,gzstates,ro⟩ := privateSlots
      exact ⟨bytes,words,streams,headers,by simpa only [setD_dstates_same] using get.symm,istates,gzstates,ro⟩
    · exact ((slot_setD_except h owner { foreign with depth := next } x same).trans privateSlots).trans
        (slot_setD_except after owner foreign x same)
  · intro region member ref off a pointer old
    simp only [List.mem_singleton] at member
    subst region
    obtain ⟨sameRef,sameOff⟩ := Ptr.ref.inj pointer
    subst ref off
    have equal : a = foreign.depth := Option.some.inj (old.symm.trans (BRef.get_dstate_depth get))
    subst a
    refine ⟨next,BRef.get_dstate_depth afterGet,size_copyRange _ _ _ _ _,?_⟩
    intro j _ outside
    rw [getElem?_copyRange _ _ _ _ _ _ bound]
    have apart : ¬ (oo ≤ j ∧ j < oo + n.toNat) := by
      intro inside
      exact outside ⟨⟨.ref (.dstate_depth owner) oo,n.toNat⟩,by simp,oo,rfl,inside⟩
    simp only [apart,ite_false]

end Zlib.Deflate.Engine.Proofs
