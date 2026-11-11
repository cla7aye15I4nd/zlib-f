import ZlibF.Proof.«inflate.c.table-invariant»

/-!
# inflate.c: caller rebuffering preserves the guarded table clause

The proof uses the actual public Rebuffer frame. It does not retain caller
input/output bytes or assume that every code array in the heap is unchanged.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The representation invariant restricts both table pointers to this
decoder's codes or the fixed statics. Those exact views are unchanged. -/
theorem dataTablesSafe_of_state_static {before after : Heap} {zs : Nat} {s : InflateState}
    (pointers : PtrInv zs s) (state : after.istates zs = before.istates zs)
    (statics : after.static = before.static) (tables : DataTablesSafe before s) :
    DataTablesSafe after s := by
  have views : ∀ (ref : CodeRef) (offset : Nat),
      (s.lencode = .ref ref offset ∨ s.distcode = .ref ref offset) →
      (Space.get after ref : Option (Array Code)) = Space.get before ref := by
    intro ref offset pointer
    rcases pointers.2 with ⟨i, j, lens, dists, _, _⟩ | ⟨lens, dists⟩
    · rcases pointer with pointer | pointer
      · rw [lens] at pointer
        cases pointer
        change (after.istates zs).map (·.codes) = (before.istates zs).map (·.codes)
        rw [state]
      · rw [dists] at pointer
        cases pointer
        change (after.istates zs).map (·.codes) = (before.istates zs).map (·.codes)
        rw [state]
    · rcases pointer with pointer | pointer
      · rw [lens] at pointer
        cases pointer
        change some after.static.lenfix = some before.static.lenfix
        rw [statics]
      · rw [dists] at pointer
        cases pointer
        change some after.static.distfix = some before.static.distfix
        rw [statics]
  constructor
  · obtain ⟨ref, offset, ca, pointer, get, safe⟩ := tables.lengthTable
    exact ⟨ref, offset, ca, pointer, by rw [views ref offset (Or.inl pointer)]; exact get, safe⟩
  · obtain ⟨ref, offset, ca, pointer, get, safe⟩ := tables.distanceTable
    exact ⟨ref, offset, ca, pointer, by rw [views ref offset (Or.inr pointer)]; exact get, safe⟩
  · exact tables.lengthLeaves_frame rfl rfl (fun ref offset pointer => views ref offset (Or.inl pointer))

/-- Actual caller edits preserve the decoder's state and both possible
sources of installed table data. No restriction on the new caller buffer
contents is needed for this clause. This proves one history constructor's
table obligation, not the entire stronger invariant. -/
theorem rebuffer_dataTableInvariant {before after : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState}
    (good : Good before r zs z s) (rebuffer : Rebuffer before after r)
    (tables : DataTableInvariant before s) :
    after.istates zs = some s ∧ DataTableInvariant after s := by
  obtain ⟨_, _, _, frame, _⟩ := rebuffer
  obtain ⟨statics, _, _, _, _, objects⟩ := frame
  have owned : StreamOwned before r zs := by
    refine ⟨z, good.live.hz, Or.inl ⟨zs, s, good.live.zst, good.live.hs, ?_⟩⟩
    exact Or.inl rfl
  have live : before.live zs := by
    simp [Heap.live, good.live.hs]
  have preserved := objects zs live (by intro notOwned; exact notOwned owned)
  have state : after.istates zs = before.istates zs := preserved.2.2.2.2.2.1
  refine ⟨state.trans good.live.hs, ?_⟩
  intro mode
  exact dataTablesSafe_of_state_static good.inv.ptr state statics.symm (tables mode)

end Zlib.Inflate.Proofs
