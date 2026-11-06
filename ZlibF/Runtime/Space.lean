/-!
# Runtime: the parts that do not mention the heap

Trusted base of every translation; see `docs/trusted-base.md`. The heap itself is generated
(`Schema.lean`, from the C headers). This file holds what the generated file builds on:

* `upd`, the update of a table (a function from block numbers);
* `Ptr R`, a pointer into an array: null, or the array (`R` says where it lives) and an index;
* `Space`, which says how the heap stores the arrays of a reference type `R`;
* `FnPtr`, a function pointer as a name;
* `Junk`, the value of an uninitialised integer.
-/

namespace C

/-- A table of the heap: the objects of one kind by block number, as an `Array`, so that code which uses the heap
linearly updates it in place (`Tbl.modify`). Proofs see it as the function `Tbl.get t : Nat → α` (a coercion): entry
`k` is `t.arr[k]` if that exists and `default` otherwise (`none` for a table of objects, `false` for the read-only
flags). `upd` is the update; `upd_same`, `upd_ne`, `upd_upd`, `upd_self` are its rules. -/
structure Tbl (α : Type) [Inhabited α] where
  arr : Array α

namespace Tbl
variable {α : Type} [Inhabited α]

/-- The entry `k`: `t.arr[k]`, or `default` beyond the end. -/
def get (t : Tbl α) (k : Nat) : α := t.arr.getD k default
instance : CoeFun (Tbl α) (fun _ => Nat → α) := ⟨Tbl.get⟩

/-- The table with every entry `default`. -/
def empty : Tbl α := ⟨#[]⟩

instance : Inhabited (Tbl α) := ⟨empty⟩
/-- `t` with the entry `k` replaced by `v` (the table grows when `k` is beyond its end). -/
def set (t : Tbl α) (k : Nat) (v : α) : Tbl α :=
  if k < t.arr.size then ⟨t.arr.set! k v⟩ else ⟨(t.arr ++ Array.replicate (k - t.arr.size) default).push v⟩
/-- `t` with the entry `k` changed by `f`. The entry is taken out of the array, changed and put back, so it is
updated in place when `t` and the entry are not shared. No change when `k` is beyond the end. -/
def modify (t : Tbl α) (k : Nat) (f : α → α) : Tbl α := ⟨t.arr.modify k f⟩

theorem get_eq (t : Tbl α) (k : Nat) : t.get k = (t.arr[k]?).getD default := by
  simp [get, Array.getD_eq_getD_getElem?]

theorem get_set (t : Tbl α) (k : Nat) (v : α) (x : Nat) :
    (t.set k v).get x = if x = k then v else t.get x := by
  unfold set
  split
  · rename_i h
    simp [get_eq, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    split <;> simp_all [eq_comm]
  · rename_i h
    simp only [get_eq]
    simp [Array.getElem?_push, Array.getElem?_append, Array.getElem?_replicate]
    by_cases h1 : x < t.arr.size
    · have : x ≠ k := by omega
      simp [h1, this]
    · by_cases h2 : x = k
      · subst h2; simp [h1]
      · simp [h1, h2]
        have h3 : x - t.arr.size ≠ k - t.arr.size := by omega
        simp [h3]
        split <;> simp

theorem get_empty (k : Nat) : (empty : Tbl α).get k = default := by
  simp [get_eq, empty]

@[simp] theorem get_empty_opt {β : Type} (k : Nat) : (empty : Tbl (Option β)).get k = none := by
  simp [get_eq, empty]
  rfl

@[simp] theorem get_empty_bool (k : Nat) : (empty : Tbl Bool).get k = false := by
  simp [get_eq, empty]

theorem lt_size_of_get_ne (t : Tbl α) (k : Nat) (h : t.get k ≠ default) : k < t.arr.size := by
  by_cases hc : k < t.arr.size
  · exact hc
  · exfalso
    apply h
    simp [get_eq, Array.getElem?_eq_none (by omega : t.arr.size ≤ k)]

theorem modify_eq (t : Tbl α) (k : Nat) (f : α → α) (hk : k < t.arr.size) :
    t.modify k f = t.set k (f (t.get k)) := by
  unfold modify set
  simp only [hk, ite_true]
  congr 1
  apply Array.ext_getElem?
  intro i
  simp [Array.getElem?_modify, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, get_eq, hk]
  split
  · rename_i hki
    subst hki
    simp [Array.getElem?_eq_getElem hk]
  · simp_all

theorem set_self (t : Tbl α) (k : Nat) (hk : k < t.arr.size) : t.set k (t.get k) = t := by
  obtain ⟨arr⟩ := t
  have hk' : k < arr.size := hk
  unfold set
  simp only [hk', ite_true]
  simp only [Tbl.mk.injEq]
  apply Array.ext_getElem?
  intro i
  simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, get_eq]
  intro hki
  subst hki
  simp [hk', Array.getElem?_eq_getElem hk']

theorem set_set (t : Tbl α) (k : Nat) (v v' : α) : (t.set k v).set k v' = t.set k v' := by
  unfold set
  split
  · rename_i h
    simp only [h, ite_true, Array.size_setIfInBounds, Array.set!_eq_setIfInBounds]
    congr 1
    apply Array.ext_getElem?
    intro i
    simp [Array.getElem?_setIfInBounds]
  · rename_i h
    have h2 : k < ((t.arr ++ Array.replicate (k - t.arr.size) default).push v).size := by simp; omega
    simp only [h2, ite_true, Array.set!_eq_setIfInBounds]
    congr 1
    apply Array.ext_getElem?
    intro i
    simp [Array.getElem?_setIfInBounds, Array.getElem?_push, Array.getElem?_append]
    by_cases hki : k = i
    · subst hki
      have h4 : k < t.arr.size + (k - t.arr.size + 1) := by omega
      simp [h4, h]
    · simp only [hki, ite_false]
      by_cases h1 : i < t.arr.size
      · simp [h1]
      · have h3 : i - t.arr.size ≠ k - t.arr.size := by omega
        simp [h1, h3]

end Tbl
/-- `t` with the entry `k` replaced by `v`: the update of a table of the heap. -/
def upd {α : Type} [Inhabited α] (t : Tbl α) (k : Nat) (v : α) : Tbl α := t.set k v

@[simp] theorem upd_same {α : Type} [Inhabited α] (t : Tbl α) (k : Nat) (v : α) : upd t k v k = v := by
  have := Tbl.get_set t k v k
  simpa [upd] using this
@[simp] theorem upd_ne {α : Type} [Inhabited α] (t : Tbl α) (k : Nat) (v : α) (x : Nat) (h : x ≠ k) :
    upd t k v x = t x := by
  have := Tbl.get_set t k v x
  simpa [upd, h] using this
/-- The update as a function: the new value at `k`, the old table elsewhere. -/
theorem upd_apply {α : Type} [Inhabited α] (t : Tbl α) (k : Nat) (v : α) (x : Nat) :
    upd t k v x = if x = k then v else t x := by
  have := Tbl.get_set t k v x
  simpa [upd] using this

theorem upd_upd {α : Type} [Inhabited α] (t : Tbl α) (k : Nat) (v v' : α) : upd (upd t k v) k v' = upd t k v' :=
  Tbl.set_set t k v v'
theorem upd_self {α : Type} (t : Tbl (Option α)) (k : Nat) (a : α) (hf : t k = some a) :
    upd t k (some a) = t := by
  have hk : k < t.arr.size := Tbl.lt_size_of_get_ne t k (by simp [Tbl.get] at hf ⊢; simp [hf])
  have := Tbl.set_self t k hk
  rw [show t.get k = some a from hf] at this
  exact this

/-- Changing an entry that holds `a` in place is the same as replacing it. -/
theorem Tbl.modify_opt {β : Type} (t : Tbl (Option β)) (k : Nat) (g : β → β) (a : β) (hg : t k = some a) :
    t.modify k (Option.map g) = upd t k (some (g a)) := by
  have hk : k < t.arr.size := Tbl.lt_size_of_get_ne t k (by simp [Tbl.get] at hg ⊢; simp [hg])
  rw [Tbl.modify_eq t k _ hk]
  simp [upd, show t.get k = some a from hg]


/-- A pointer into an array: null, or the array (`R` says where it lives: a heap block, an array inside a
struct, a static table) and an index. There is no address. One past the end is a valid pointer. -/
inductive Ptr (R : Type) where
  | null
  | ref (r : R) (off : Nat)
  deriving DecidableEq

instance {R : Type} : Inhabited (Ptr R) := ⟨.null⟩

/-- How the heap stores the arrays that the reference type `R` denotes. `get h r` is the array (if it is live),
`put h r a` the heap with that array replaced, `ro h r` says that the array is read-only. `modify h r f` is the heap
with the array changed by `f`: the same as `put h r (f a)` (`modify_eq`) for a live array `a`, and it is what the
primitives that write (`Ptr.store`, `Ptr.memcpy`, `Ptr.fill`) use, because it takes the array out of its table, so
that `f` updates it in place when the heap is not shared. -/
class Space (H : Type) (R : Type) (T : outParam Type) where
  get : H → R → Option (Array T)
  put : H → R → Array T → H
  ro : H → R → Bool
  modify : H → R → (Array T → Array T) → H
  modify_eq : ∀ h r a f, get h r = some a → modify h r f = put h r (f a)

/-- A function pointer: null, or the name of the function. -/
inductive FnPtr where
  | null
  | fn (name : String)
  deriving DecidableEq, Inhabited

/-- The value of an uninitialised integer of type `T`, given an arbitrary 64-bit pattern. -/
class Junk (T : Type) where
  of : UInt64 → T

instance : Junk UInt8 := ⟨UInt64.toUInt8⟩
instance : Junk UInt16 := ⟨UInt64.toUInt16⟩
instance : Junk UInt32 := ⟨UInt64.toUInt32⟩
instance : Junk UInt64 := ⟨id⟩
instance : Junk Int8 := ⟨fun x => x.toUInt8.toInt8⟩
instance : Junk Int16 := ⟨fun x => x.toUInt16.toInt16⟩
instance : Junk Int32 := ⟨fun x => x.toUInt32.toInt32⟩
instance : Junk Int64 := ⟨UInt64.toInt64⟩

end C
