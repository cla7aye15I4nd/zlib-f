import ZlibF.Proof.LibcBorrow

namespace C.LibcBorrow

/-- Pure reads can fault, but a successful read does not invalidate a borrow. -/
theorem stable_strlenB (p : BPtr) : StableM (strlenB p) := by
  intro h value after hr
  unfold strlenB at hr
  split at hr
  · contradiction
  · split at hr
    · contradiction
    · split at hr
      · cases hr; rfl
      · contradiction

theorem stable_strLitRef (s : String) : StableM (strLitRef s) := by
  intro h value after hr
  unfold strLitRef at hr
  split at hr
  · cases hr; rfl
  · contradiction

/-- Heap updates to ordinary byte views leave the separate external borrow
metadata unchanged. Even a non-owning static view cannot reset it. -/
theorem space_modify_borrow (h : Heap) (r : BRef) (f : Array UInt8 → Array UInt8) :
    (Space.modify h r f).libcErrorBorrow = h.libcErrorBorrow := by
  cases r <;> rfl

theorem space_put_borrow (h : Heap) (r : BRef) (a : Array UInt8) :
    (Space.put h r a).libcErrorBorrow = h.libcErrorBorrow := by
  cases r <;> simp only [Space.put]
  split <;> rfl

/-- The actual block-copy primitive does not invoke strerror, on every
returning branch and every supported byte-reference kind. -/
theorem stable_memcpyB (dst src : BPtr) (n : Nat) : StableM (memcpyB dst src n) := by
  intro h value after hr
  unfold memcpyB Ptr.memcpy at hr
  split at hr
  · split at hr
    · split at hr
      · contradiction
      · split at hr
        · split at hr
          · cases hr; exact space_modify_borrow _ _ _
          · contradiction
        · contradiction
    · contradiction
  · contradiction

/-- The actual byte store preserves borrow metadata even when its target is
an embedded byte array. Borrowed readonly views still fail the existing check. -/
theorem stable_store8 (p : BPtr) (v : UInt8) : StableM (store8 p v) := by
  intro h value after hr
  unfold store8 Ptr.store at hr
  split at hr
  · contradiction
  · split at hr
    · contradiction
    · split at hr
      · contradiction
      · split at hr
        · cases hr; exact space_modify_borrow _ _ _
        · contradiction

theorem stable_allocBytes (a : Array UInt8) : StableM (allocBytes a) := by
  intro h value after hr
  unfold allocBytes at hr
  split at hr
  · contradiction
  · cases hr; rfl

/-- Actual for-in iterations preserve an observation by composition. This is
a theorem about the loop primitive, not a callee contract given by callers. -/
theorem StableM.list_forIn {α β : Type} (values : List α)
    (body : (value : α) → value ∈ values → β → M (ForInStep β))
    (stable : ∀ value member state, StableM (body value member state))
    (initial : β) : StableM (List.forIn' values initial body) := by
  induction values generalizing initial with
  | nil =>
    simp only [List.forIn'_eq_forIn', List.forIn'_nil]
    exact StableM.pure _
  | cons head tail ih =>
    simp only [List.forIn'_eq_forIn', List.forIn'_cons]
    apply StableM.bind (stable head (by simp) initial)
    intro decision
    cases decision with
    | done value => exact StableM.pure _
    | yield next =>
      exact ih (fun value member state => body value (by simp [member]) state)
        (fun value member state => stable value (by simp [member]) state) next

#print axioms stable_strlenB
#print axioms stable_memcpyB
#print axioms stable_store8
#print axioms StableM.list_forIn
end C.LibcBorrow
