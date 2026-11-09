import ZlibF.Proof.«inflate.c.fast-writeback-frame»
import ZlibF.Proof.«inflate.c.buffer-frame-compose»

namespace Zlib.Uncompr.Proof.StoredSliceFrame
open C Zlib.Inflate Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- An exact byte-array patch has the standard interval frame. The frame
checks all typed tables and metadata after restoring only this byte view;
the pointwise condition retains both sides of the actual written interval. -/
theorem write_buffer_frame {h : Heap} {db off count : Nat} {before written : Array UInt8}
    (get : h.bytes db=some before) (size : written.size=before.size)
    (outside : ∀i,i<off ∨ off+count≤i → written[i]?=before[i]?) (changed : Nat→Prop) :
    BufferFrame h (Space.put h (BRef.blk db) written) changed [⟨.ref (.blk db) off,count⟩] := by
  refine ⟨?_,?_⟩
  · have restore : restoreRegions h (Space.put h (BRef.blk db) written) [⟨.ref (.blk db) off,count⟩]=h := by
      simp only [restoreRegions,List.foldl_cons,List.foldl_nil,get,Space.get,Space.put,upd_upd]
      exact congrArg (fun b => {h with bytes:=b}) (upd_self h.bytes db before get)
    rw [restore]
    exact ⟨rfl,rfl,rfl,Nat.le_refl _,Nat.le_refl _,by intro b live allowed;exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩⟩
  · intro region member ref pos old ptr oldGet
    have same : region=(⟨.ref (.blk db) off,count⟩:Region) := by simpa only [List.mem_singleton] using member
    subst region
    cases ptr
    have oldEq : old=before := Option.some.inj (oldGet.symm.trans get)
    subst old
    refine ⟨written,by simp only [Space.get,Space.put,upd_same],size,?_⟩
    intro i bound notCovered
    apply outside i
    by_cases lower : i<off
    · exact Or.inl lower
    · right
      apply Decidable.byContradiction
      intro upper
      apply notCovered
      exact ⟨⟨.ref (.blk db) off,count⟩,by simp,off,rfl,by omega,by change i<off+count;omega⟩

#print axioms write_buffer_frame
end Zlib.Uncompr.Proof.StoredSliceFrame
