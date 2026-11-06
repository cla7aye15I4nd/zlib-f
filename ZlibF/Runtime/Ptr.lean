import ZlibF.Runtime.Monad

/-!
# Runtime: pointers into arrays

Trusted base of every translation; see `docs/trusted-base.md`.

A pointer is `Ptr R`: null, or an array (where it lives is the reference `R`: a heap block, an array inside a struct,
a static table) and an index. Every primitive is written once, for every `R`, through the class `Space`. Each one
says which C operation it models and when it faults. Byte pointers are `BPtr = Ptr BRef` (see `Schema.lean`), and
`load8`, `index8` and `store8` are their names in the translation. The functions of the C library (`memcpy`,
`memset`, `strlen`, `malloc`, `free`) are in `Libc.lean`.
-/

namespace C

section generic
variable {R T : Type} [Space Heap R T]

/-- `p + k`. Faults unless the result is an index of the array or one past its end. `NULL + 0` is `NULL` (allowed
by decision, although C17 leaves it undefined; see `docs/trusted-base.md`); the pointer must point to a live array.
It checks the result only: a pointer built by hand outside its array (`Ptr.ref r off` with `off` beyond the end) is
not caught here. The translations obtain pointers from `Ptr.add` and from the schema, which never form one. -/
def Ptr.add (p : Ptr R) (k : Int) : M (Ptr R) := fun h =>
  match p with
  | .null => if k = 0 then .ok (.null, h) else .error (.ub "arithmetic on a null pointer")
  | .ref r off =>
    match Space.get h r with
    | none => .error (.ub "arithmetic on a dangling pointer")
    | some a =>
      if 0 ≤ (off : Int) + k ∧ (off : Int) + k ≤ (a.size : Int) then .ok (.ref r ((off : Int) + k).toNat, h)
      else .error (.ub "pointer arithmetic outside its object")

/-- `*p`. Faults if `p` is null, dangling, or outside its array (one past the end is not readable). -/
def Ptr.load (p : Ptr R) : M T := fun h =>
  match p with
  | .null => .error (.ub "null dereference")
  | .ref r off =>
    match Space.get h r with
    | none => .error (.ub "read through a dangling pointer")
    | some a => if hk : off < a.size then .ok (a[off], h) else .error (.ub "read outside its object")

/-- `p[i]`, that is `*(p + i)`. -/
def Ptr.index (p : Ptr R) (i : Int) : M T := do
  Ptr.load (← p.add i)

/-- `*p = v`. Faults if `p` is null, dangling, outside its array, or the array is read-only. -/
def Ptr.store (p : Ptr R) (v : T) : M Unit := fun h =>
  match p with
  | .null => .error (.ub "null store")
  | .ref r off =>
    match Space.get h r with
    | none => .error (.ub "store through a dangling pointer")
    | some a =>
      if Space.ro h r then .error (.ub "store into a read-only object")
      else if off < a.size then .ok ((), Space.modify h r (fun a => a.set! off v))
      else .error (.ub "store outside its object")

/-- `p - q` (a `ptrdiff_t`). Faults unless both point into the same live array and the difference is a `ptrdiff_t`
(`NULL - NULL` is a fault although C23 defines it as 0). -/
def Ptr.diff [DecidableEq R] (p q : Ptr R) : M Int64 := fun h =>
  match p, q with
  | .ref r1 o1, .ref r2 o2 =>
    if r1 = r2 then
      match Space.get h r1 with
      | some a =>
        if o1 ≤ a.size ∧ o2 ≤ a.size then
          if -(2 ^ 63 : Int) ≤ (o1 : Int) - (o2 : Int) ∧ (o1 : Int) - (o2 : Int) < 2 ^ 63 then
            .ok (Int64.ofInt ((o1 : Int) - (o2 : Int)), h)
          else .error (.ub "pointer difference is not a ptrdiff_t")
        else .error (.ub "pointer outside its object")
      | none => .error (.ub "difference of dangling pointers")
    else .error (.ub "difference of pointers into different objects")
  | _, _ => .error (.ub "difference of null pointers")

/-- `p < q`. Faults unless both point into the same live array (relational comparison of unrelated pointers is
undefined). -/
def Ptr.lt [DecidableEq R] (p q : Ptr R) : M Bool := fun h =>
  match p, q with
  | .ref r1 o1, .ref r2 o2 =>
    if r1 = r2 then
      match Space.get h r1 with
      | some a =>
        if o1 ≤ a.size ∧ o2 ≤ a.size then .ok (decide (o1 < o2), h)
        else .error (.ub "pointer outside its object")
      | none => .error (.ub "comparison of dangling pointers")
    else .error (.ub "comparison of pointers into different objects")
  | _, _ => .error (.ub "comparison of null pointers")

/-- `p <= q`; the same faults as `Ptr.lt`. -/
def Ptr.le [DecidableEq R] (p q : Ptr R) : M Bool := do
  return !(← Ptr.lt q p)

/-! ### Rules -/

theorem Ptr.add_ok {h : Heap} {r : R} {a : Array T} {off : Nat} {k : Int}
    (hg : Space.get h r = some a) (h0 : 0 ≤ (off : Int) + k) (h1 : (off : Int) + k ≤ (a.size : Int)) :
    OkOn h (Ptr.add (Ptr.ref r off) k) (Ptr.ref r ((off : Int) + k).toNat) := by
  unfold OkOn Ptr.add; simp [hg, h0, h1]

theorem Ptr.add_nat_ok {h : Heap} {r : R} {a : Array T} {off n : Nat}
    (hg : Space.get h r = some a) (h1 : off + n ≤ a.size) :
    OkOn h (Ptr.add (Ptr.ref r off) (n : Int)) (Ptr.ref r (off + n)) := by
  have := Ptr.add_ok (a := a) (off := off) (k := (n : Int)) hg (by omega) (by omega)
  have e : ((off : Int) + (n : Int)).toNat = off + n := by omega
  rwa [e] at this

theorem Ptr.sub_nat_ok {h : Heap} {r : R} {a : Array T} {off n : Nat}
    (hg : Space.get h r = some a) (hn : n ≤ off) (h1 : off ≤ a.size) :
    OkOn h (Ptr.add (Ptr.ref r off) (-(n : Int))) (Ptr.ref r (off - n)) := by
  have := Ptr.add_ok (a := a) (off := off) (k := -(n : Int)) hg (by omega) (by omega)
  have e : ((off : Int) + -(n : Int)).toNat = off - n := by omega
  rwa [e] at this

theorem Ptr.add_null_zero {h : Heap} : OkOn h (Ptr.add (Ptr.null : Ptr R) 0) Ptr.null := by
  unfold OkOn Ptr.add; simp

theorem Ptr.load_ok {h : Heap} {r : R} {a : Array T} {off : Nat}
    (hg : Space.get h r = some a) (hlt : off < a.size) :
    OkOn h (Ptr.load (Ptr.ref r off)) a[off] := by
  unfold OkOn Ptr.load; simp [hg, hlt]

theorem Ptr.index_ok {h : Heap} {r : R} {a : Array T} {off i : Nat}
    (hg : Space.get h r = some a) (hlt : off + i < a.size) :
    OkOn h (Ptr.index (Ptr.ref r off) (i : Int)) a[off + i] := by
  unfold Ptr.index
  refine OkOn.bind (Ptr.add_nat_ok hg (by omega)) ?_
  exact Ptr.load_ok hg hlt

theorem Ptr.store_ok {h : Heap} {r : R} {a : Array T} {off : Nat} {v : T}
    (hg : Space.get h r = some a) (hro : Space.ro h r = false) (hlt : off < a.size) :
    Ptr.store (Ptr.ref r off) v h = .ok ((), Space.put h r (a.set! off v)) := by
  simp [Ptr.store, hg, hro, hlt, Space.modify_eq _ _ _ _ hg]

theorem Ptr.diff_ok [DecidableEq R] {h : Heap} {r : R} {a : Array T} {o1 o2 : Nat}
    (hg : Space.get h r = some a) (h1 : o1 ≤ a.size) (h2 : o2 ≤ a.size)
    (hr : -(2 ^ 63 : Int) ≤ (o1 : Int) - (o2 : Int) ∧ (o1 : Int) - (o2 : Int) < 2 ^ 63) :
    OkOn h (Ptr.diff (Ptr.ref r o1) (Ptr.ref r o2)) (Int64.ofInt ((o1 : Int) - (o2 : Int))) := by
  unfold OkOn Ptr.diff; simp [hg, h1, h2]; omega

theorem Ptr.lt_ok [DecidableEq R] {h : Heap} {r : R} {a : Array T} {o1 o2 : Nat}
    (hg : Space.get h r = some a) (h1 : o1 ≤ a.size) (h2 : o2 ≤ a.size) :
    OkOn h (Ptr.lt (Ptr.ref r o1) (Ptr.ref r o2)) (decide (o1 < o2)) := by
  unfold OkOn Ptr.lt; simp [hg, h1, h2]
end generic

/-! ## Byte pointers -/

/-- `*p` for an `unsigned char *`. -/
abbrev load8 (p : BPtr) : M UInt8 := Ptr.load p
/-- `p[i]` for an `unsigned char *`. -/
abbrev index8 (p : BPtr) (i : Int) : M UInt8 := Ptr.index p i
/-- `*p = v` for an `unsigned char *`. -/
abbrev store8 (p : BPtr) (v : UInt8) : M Unit := Ptr.store p v
theorem load8_ok {h : Heap} {blk off : Nat} {bytes : Array UInt8} (hb : h.bytes blk = some bytes)
    (hlt : off < bytes.size) : OkOn h (load8 (.ref (.blk blk) off)) bytes[off] :=
  Ptr.load_ok hb hlt

theorem index8_ok {h : Heap} {blk off i : Nat} {bytes : Array UInt8} (hb : h.bytes blk = some bytes)
    (hlt : off + i < bytes.size) : OkOn h (index8 (.ref (.blk blk) off) i) bytes[off + i] :=
  Ptr.index_ok hb hlt

/-- A store into a read-only block is a fault. -/
theorem store_readonly {h : Heap} {b off : Nat} {a : Array UInt8} {v : UInt8} (hb : h.bytes b = some a) (hro : h.ro b = true) :
    store8 (.ref (.blk b) off) v h = .error (.ub "store into a read-only object") := by
  simp [store8, Ptr.store, hb, hro]

end C
