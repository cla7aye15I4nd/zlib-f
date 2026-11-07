import ZlibF.Proof.«public-inflate-init»

open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public ZlibF.Spec
open ZlibF.Spec.Public.Proofs.InflateInit

/-! The invalid-window path allocates and frees a state. The finite table backing
`istates` grows from zero entries to four. `SameObjects` requires structural
equality, so the current public goal does not hold for this valid initial heap. -/
namespace Init2Counterexample

def r : ZStreamRef := .tab 0
def v : BPtr := .ref (.blk 1) 0

theorem domain : InitDomain witnessHeap r v := public_witness_domain

theorem default_get : r.get witnessHeap = some default := by
  rfl

theorem defaults : DefaultOrNull (default : ZStream) := by
  exact ⟨Or.inl rfl, Or.inl rfl⟩

theorem alloc_ok : witnessHeap.allocOk witnessHeap.nalloc = true := by rfl

theorem bad_params : reset2Params (1 : Int32) = none := by decide

theorem actual : C.run (inflateInit2_ (some r) 1 v 112) witnessHeap =
    .ok (Z_STREAM_ERROR, initBadHeap witnessHeap r default) := by
  obtain ⟨hn, hv⟩ := version_value_read domain.2.2.2.1
  exact inflateInit2_badbits default_get domain.1 alloc_ok defaults.1 defaults.2 hn hv bad_params

theorem actual_table_size : (initBadHeap witnessHeap r default).istates.arr.size = 4 := by
  rfl

theorem expected_table_size :
    (r.put witnessHeap { preparedStream default with state := none }).istates.arr.size = 0 := by
  rfl

theorem shapes_differ :
    (initBadHeap witnessHeap r default).istates.arr.size ≠
      (r.put witnessHeap { preparedStream default with state := none }).istates.arr.size := by
  rw [actual_table_size, expected_table_size]
  decide

theorem goal_false : ¬ Goal.inflateInit2_ := by
  intro goal
  obtain ⟨hf, hu, hg, hv, _, _, _, _⟩ := domain
  obtain ⟨rc, after, hr, _, post⟩ := (goal 1).2.2 witnessHeap r default v hf hu hg default_get defaults hv
  rw [actual] at hr
  cases hr
  have same : SameObjects (r.put witnessHeap { preparedStream default with state := none })
      (initBadHeap witnessHeap r default) := by
    simpa [alloc_ok, Api.inflWbits] using post
  have e := congrArg (fun table => table.arr.size) same.2.2.2.2.2.2.1
  exact shapes_differ e

#print axioms goal_false
end Init2Counterexample
