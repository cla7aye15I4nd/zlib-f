import ZlibF.Proof.«inflate.c.borrow-stable-dispatch»

/-! Successful-return borrow preservation of the complete actual public inflate
entry, including its local allocation/free and every early return. -/
namespace Zlib.Inflate.BorrowProofs
open C C.LibcBorrow Zlib.Inflate

/-- Validation reads only represented stream and state objects. -/
theorem stable_inflateStateCheck (p : ZStreamPtr) : StableM (inflateStateCheck p) := by
  unfold inflateStateCheck
  inflate_borrow_m

theorem stable_inflate_run_result (c : Ctx) (l : IL) :
    StableM (StateT.run (ExceptT.run (inflate_run c)) l) := stable_x_inflate_run c l

/-- The complete actual public call retains external borrow metadata on all
returning paths. No Good, Frame, allocator, mode or input restrictions are assumed.
Fault exclusion, leak freedom and termination are separate obligations. -/
theorem stable_inflate (p : ZStreamPtr) (flush : Int32) : StableM (inflate p flush) := by
  unfold inflate
  repeat' first
    | with_reducible exact stable_allocLocalB _
    | with_reducible exact stable_inflateStateCheck _
    | with_reducible exact stable_inflate_run_result _ _
    | with_reducible exact stable_inflate_leave _ _
    | with_reducible exact stable_freeB _
    | with_reducible exact StableM.pure _
    | with_reducible exact stable_ldZStream _
    | with_reducible exact stable_castInflateState _
    | with_reducible apply StableM.ite
    | with_reducible apply StableM.bind
    | split
    | intro x
    | dsimp only

/-- The observation belongs to this very public execution, including early
validation errors and modeled error results. -/
theorem inflate_borrow_eq (p : ZStreamPtr) (flush : Int32) (h after : Heap) (rc : Int32)
    (run : inflate p flush h = .ok (rc, after)) :
    after.libcErrorBorrow = h.libcErrorBorrow := stable_inflate p flush h rc after run

theorem inflate_borrow_stable (p : ZStreamPtr) (flush : Int32) (h after : Heap) (rc : Int32)
    (run : inflate p flush h = .ok (rc, after)) (ref : BRef) : BorrowStable h after ref :=
  (stable_inflate p flush).view run ref

#print axioms stable_inflateStateCheck
#print axioms stable_inflate
#print axioms inflate_borrow_eq
#print axioms inflate_borrow_stable
end Zlib.Inflate.BorrowProofs
