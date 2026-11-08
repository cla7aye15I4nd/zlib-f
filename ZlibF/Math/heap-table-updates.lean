import ZlibF.Runtime.Space

namespace C.Tbl
set_option autoImplicit false
variable {α : Type} [Inhabited α]

/-- Table equality needs both extensional values and the stored extent. -/
theorem eq_of_size_get {left right : Tbl α}
    (size : left.arr.size = right.arr.size) (values : ∀ index, left index = right index) : left = right := by
  obtain ⟨first⟩ := left
  obtain ⟨second⟩ := right
  congr 1
  apply Array.ext_getElem?
  intro index
  by_cases inside : index < first.size
  · have other : index < second.size := by change first.size = second.size at size; omega
    have value := values index
    simp only [get_eq, Array.getElem?_eq_getElem inside, Array.getElem?_eq_getElem other, Option.getD_some] at value
    simp only [Array.getElem?_eq_getElem inside, Array.getElem?_eq_getElem other, value]
  · have other : second.size ≤ index := by change first.size = second.size at size; omega
    rw [Array.getElem?_eq_none (by omega), Array.getElem?_eq_none other]

theorem size_set (table : Tbl α) (index : Nat) (value : α) :
    (table.set index value).arr.size = max table.arr.size (index + 1) := by
  unfold set
  split <;> simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, Array.size_push,
    Array.size_append, Array.size_replicate]
  all_goals omega

/-- Distinct updates commute, including growth and default padding. -/
theorem set_comm (table : Tbl α) {first second : Nat} (different : first ≠ second) (a b : α) :
    (table.set first a).set second b = (table.set second b).set first a := by
  apply eq_of_size_get
  · simp only [size_set]
    omega
  · intro index
    simp only [get_set]
    by_cases one : index = first <;> by_cases two : index = second <;> simp_all

end C.Tbl
