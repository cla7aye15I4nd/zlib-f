import ZlibF.Proof.«public-inflate-init2»

open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public ZlibF.Spec
open ZlibF.Spec.Public.Proofs.InflateInit

/-! The heap and the invalid window argument are those of the former counterexample.
The call allocates and frees a state, and the state table grows from zero entries to
four. The contract now compares tables entry by entry, so the public goal holds here. -/
namespace Init2Regression

def r : ZStreamRef := .tab 0
def v : BPtr := .ref (.blk 1) 0

theorem domain : InitDomain witnessHeap r v := public_witness_domain

theorem default_get : r.get witnessHeap = some default := by
  rfl

theorem defaults : DefaultOrNull (default : ZStream) := by
  exact ⟨Or.inl rfl, Or.inl rfl⟩

/-- The table still grows: the physical shapes differ, as before. -/
theorem actual_table_size : (initBadHeap witnessHeap r default).istates.arr.size = 4 := by
  rfl

/-- The public goal now gives the clean refusal on this heap. -/
theorem refused : ∃ after,
    C.run (inflateInit2_ (some r) 1 v 112) witnessHeap = .ok (Z_STREAM_ERROR, after) ∧
    SameObjectsUpToTableShape
      (r.put witnessHeap { preparedStream default with state := none }) after := by
  obtain ⟨hf, hu, hg, hv, _, _, _, _⟩ := domain
  obtain ⟨rc, after, hr, _, post⟩ :=
    (inflate_init2_public 1).2.2 witnessHeap r default v hf hu hg default_get defaults hv
  have alloc_ok : witnessHeap.allocOk witnessHeap.nalloc = true := by rfl
  have post' : rc = Z_STREAM_ERROR ∧ SameObjectsUpToTableShape
      (r.put witnessHeap { preparedStream default with state := none }) after := by
    simpa [alloc_ok, Api.inflWbits] using post
  exact ⟨after, by rw [hr, post'.1], post'.2⟩

#print axioms refused
end Init2Regression
