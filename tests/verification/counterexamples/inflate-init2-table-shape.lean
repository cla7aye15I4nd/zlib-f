import ZlibF.Proof.«public-inflate-init»

open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public ZlibF.Spec
open ZlibF.Spec.Public.Proofs.InflateInit

/-! The invalid-window path allocates and frees a state. Its backing `istates`
table keeps empty padding. The archived structural predicate rejects this shape;
the current pointwise predicate accepts the same actual objects and cleanup.
This fixture does not negate or prove the complete current public goal. -/
namespace Init2Counterexample

/-- Snapshot of SameObjects before the pointwise object-lookup correction. -/
def LegacySameObjects (expected after : Heap) : Prop :=
  after.bytes = expected.bytes ∧ after.words = expected.words ∧
  (∀ b, expected.live b → after.ro b = expected.ro b) ∧
  after.streams = expected.streams ∧ after.gzheaders = expected.gzheaders ∧
  after.dstates = expected.dstates ∧ after.istates = expected.istates ∧
  after.gzstates = expected.gzstates ∧ after.static = expected.static ∧
  after.allocOk = expected.allocOk ∧ after.garbage = expected.garbage ∧
  expected.nextBlk ≤ after.nextBlk ∧ expected.nalloc ≤ after.nalloc

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

/-- The old structural predicate still observes empty backing-table padding. -/
theorem legacy_same_objects_false :
    ¬ LegacySameObjects (r.put witnessHeap { preparedStream default with state := none })
      (initBadHeap witnessHeap r default) := by
  intro same
  have e := congrArg (fun table => table.arr.size) same.2.2.2.2.2.2.1
  exact shapes_differ e

/-- On exactly the same actual result, every current object lookup is correct.
The freed temporary state leaves no represented object at its old identity. -/
theorem pointwise_objects :
    SameObjects (r.put witnessHeap { preparedStream default with state := none })
      (initBadHeap witnessHeap r default) := by
  simp [SameObjects, initBadHeap, freeIst, allocIstHeap, r, ZStreamRef.put,
    initStream2, initStream, preparedStream, upd_upd, witnessHeap, Heap.empty, upd_apply]

theorem pointwise_istate_lookups (b : Nat) :
    (initBadHeap witnessHeap r default).istates b =
      (r.put witnessHeap { preparedStream default with state := none }).istates b := by
  exact pointwise_objects.2.2.2.2.2.2.1 b

/-- No object appears or disappears in this complete allocate/free execution. -/
theorem no_new_live (b : Nat) :
    (initBadHeap witnessHeap r default).live b ↔ witnessHeap.live b := by
  exact (initBad_good default_get domain.2.1 domain.1).2.2 b

theorem live_change :
    LiveChange witnessHeap (initBadHeap witnessHeap r default)
      (fun _ => False) (fun _ => False) := by
  intro b
  change (initBadHeap witnessHeap r default).live b ↔
    (witnessHeap.live b ∧ ¬False) ∨ False
  simpa using no_new_live b

/-- The unchanged actual C run has the corrected object/cleanup observation.
This is one invalid-window execution, not a proof of all public init cases. -/
theorem actual_pointwise_observation :
    C.run (inflateInit2_ (some r) 1 v 112) witnessHeap =
      .ok (Z_STREAM_ERROR, initBadHeap witnessHeap r default) ∧
    SameObjects (r.put witnessHeap { preparedStream default with state := none })
      (initBadHeap witnessHeap r default) ∧
    LiveChange witnessHeap (initBadHeap witnessHeap r default)
      (fun _ => False) (fun _ => False) ∧
    (initBadHeap witnessHeap r default).nextBlk = witnessHeap.nextBlk+1 ∧
    (initBadHeap witnessHeap r default).nalloc = witnessHeap.nalloc+1 := by
  exact ⟨actual, pointwise_objects, live_change, rfl, rfl⟩

#print axioms legacy_same_objects_false
#print axioms pointwise_objects
#print axioms no_new_live
#print axioms actual_pointwise_observation
end Init2Counterexample
