import ZlibF.Runtime.Monad

/-!
# Runtime: pointers into arrays

Trusted base of every translation; see `docs/trusted-base.md`.

A pointer is `Ptr R`: null, or an array (where it lives is the reference `R`: a heap block, an array inside a struct,
a static table) and an index. Every primitive is written once, for every `R`, through the class `Space`. Each one
says which C operation it models and when it faults. Byte pointers are `BPtr = Ptr BRef` (see `Schema.lean`), and
`load8`, `store8`, `memcpyB`, `memsetB`, `strlenB` are their names in the translation.
-/

namespace C

/-- The value of an element of type `T` whose every byte is `c`: what `memset(p, c, n * sizeof(T))` stores in each
element. -/
class ByteRepeat (T : Type) where
  ofByte : UInt8 → T

instance : ByteRepeat UInt8 := ⟨id⟩
instance : ByteRepeat UInt16 := ⟨fun c => (c.toUInt16 <<< 8) ||| c.toUInt16⟩
instance : ByteRepeat UInt32 := ⟨fun c => let x := c.toUInt32; (x <<< 24) ||| (x <<< 16) ||| (x <<< 8) ||| x⟩
instance : ByteRepeat UInt64 :=
  ⟨fun c => let x := c.toUInt64; (x <<< 56) ||| (x <<< 48) ||| (x <<< 40) ||| (x <<< 32) ||| (x <<< 24) ||| (x <<< 16) ||| (x <<< 8) ||| x⟩
instance : ByteRepeat Int8 := ⟨UInt8.toInt8⟩
instance : ByteRepeat Int16 := ⟨fun c => ((c.toUInt16 <<< 8) ||| c.toUInt16).toInt16⟩
instance : ByteRepeat Int32 := ⟨fun c => let x := c.toUInt32; ((x <<< 24) ||| (x <<< 16) ||| (x <<< 8) ||| x).toInt32⟩
instance : ByteRepeat Int64 :=
  ⟨fun c => let x := c.toUInt64; ((x <<< 56) ||| (x <<< 48) ||| (x <<< 40) ||| (x <<< 32) ||| (x <<< 24) ||| (x <<< 16) ||| (x <<< 8) ||| x).toInt64⟩

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

/-- `d` with `n` elements from `s` copied to it: element `doff + i` becomes element `soff + i` of `s`
(read before any write, so it is also the result of `memmove`). -/
def copyRange [Inhabited T] (d s : Array T) (doff soff n : Nat) : Array T :=
  (List.range n).foldl (fun a i => a.set! (doff + i) s[soff + i]!) d

/-- `d` with `n` elements from `off` on set to `v`. -/
def fillRange (d : Array T) (off n : Nat) (v : T) : Array T :=
  (List.range n).foldl (fun a i => a.set! (off + i) v) d

/-- `memcpy(dst, src, n)` for `n` elements. Faults if either pointer is null (even for `n = 0`) or dangling, if a
range leaves its array, if the destination is read-only and `n > 0`, or if the ranges overlap. -/
def Ptr.memcpy [DecidableEq R] [Inhabited T] (dst src : Ptr R) (n : Nat) : M Unit := fun h =>
  match dst, src with
  | .ref rd od, .ref rs os =>
    match Space.get h rd, Space.get h rs with
    | some da, some sa =>
      if Space.ro h rd && decide (n ≠ 0) then .error (.ub "memcpy into a read-only object")
      else if od + n ≤ da.size ∧ os + n ≤ sa.size then
        if rd ≠ rs ∨ od + n ≤ os ∨ os + n ≤ od then .ok ((), Space.modify h rd (fun da => copyRange da sa od os n))
        else .error (.ub "memcpy with overlapping ranges")
      else .error (.ub "memcpy outside its objects")
    | _, _ => .error (.ub "memcpy through a dangling pointer")
  | _, _ => .error (.ub "memcpy through a null pointer")

/-- `memmove(dst, src, n)` for `n` elements: as `memcpy`, and the ranges may overlap (a read-only destination is a
fault only when `n > 0`). -/
def Ptr.memmove [DecidableEq R] [Inhabited T] (dst src : Ptr R) (n : Nat) : M Unit := fun h =>
  match dst, src with
  | .ref rd od, .ref rs os =>
    match Space.get h rd, Space.get h rs with
    | some da, some sa =>
      if Space.ro h rd && decide (n ≠ 0) then .error (.ub "memmove into a read-only object")
      else if od + n ≤ da.size ∧ os + n ≤ sa.size then .ok ((), Space.modify h rd (fun da => copyRange da sa od os n))
      else .error (.ub "memmove outside its objects")
    | _, _ => .error (.ub "memmove through a dangling pointer")
  | _, _ => .error (.ub "memmove through a null pointer")

/-- Set `n` elements to the value `v`. This is `memset(dst, c, n * sizeof(T))` only for a byte array, and for any
element type when the value is zero (`zmemzero`). For a wider element type and another byte, use `Ptr.memset`, which
stores the element whose every byte is `c`. Faults if `dst` is null or dangling, the range leaves the array, or the
array is read-only and `n > 0`. -/
def Ptr.fill (dst : Ptr R) (v : T) (n : Nat) : M Unit := fun h =>
  match dst with
  | .ref r off =>
    match Space.get h r with
    | none => .error (.ub "memset through a dangling pointer")
    | some a =>
      if Space.ro h r && decide (n ≠ 0) then .error (.ub "memset of a read-only object")
      else if off + n ≤ a.size then .ok ((), Space.modify h r (fun a => fillRange a off n v))
      else .error (.ub "memset outside its object")
  | .null => .error (.ub "memset through a null pointer")

/-- `memset(dst, c, n * sizeof(T))`: `n` elements, each with every byte equal to `c`. For a byte array it is `Ptr.fill`
with `c`. The faults are those of `Ptr.fill`. -/
def Ptr.memset [ByteRepeat T] (dst : Ptr R) (c : UInt8) (n : Nat) : M Unit :=
  Ptr.fill dst (ByteRepeat.ofByte c) n

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

theorem size_copyRange [Inhabited T] (d s : Array T) (doff soff n : Nat) :
    (copyRange d s doff soff n).size = d.size := by
  unfold copyRange
  suffices ∀ (l : List Nat) (a : Array T), (l.foldl (fun a i => a.set! (doff + i) s[soff + i]!) a).size = a.size by
    exact this _ _
  intro l
  induction l with
  | nil => intro a; rfl
  | cons i l ih => intro a; simp only [List.foldl]; rw [ih]; simp

theorem size_fillRange (d : Array T) (off n : Nat) (v : T) : (fillRange d off n v).size = d.size := by
  unfold fillRange
  suffices ∀ (l : List Nat) (a : Array T), (l.foldl (fun a i => a.set! (off + i) v) a).size = a.size by
    exact this _ _
  intro l
  induction l with
  | nil => intro a; rfl
  | cons i l ih => intro a; simp only [List.foldl]; rw [ih]; simp

theorem Ptr.memcpy_ok [DecidableEq R] [Inhabited T] {h : Heap} {rd rs : R} {od os n : Nat} {da sa : Array T}
    (hd : Space.get h rd = some da) (hs : Space.get h rs = some sa) (hro : Space.ro h rd = false)
    (h1 : od + n ≤ da.size) (h2 : os + n ≤ sa.size) (hdis : rd ≠ rs ∨ od + n ≤ os ∨ os + n ≤ od) :
    Ptr.memcpy (Ptr.ref rd od) (Ptr.ref rs os) n h = .ok ((), Space.put h rd (copyRange da sa od os n)) := by
  simp [Ptr.memcpy, hd, hs, hro, h1, h2, hdis, Space.modify_eq _ _ _ _ hd]

theorem Ptr.memmove_ok [DecidableEq R] [Inhabited T] {h : Heap} {rd rs : R} {od os n : Nat} {da sa : Array T}
    (hd : Space.get h rd = some da) (hs : Space.get h rs = some sa) (hro : Space.ro h rd = false)
    (h1 : od + n ≤ da.size) (h2 : os + n ≤ sa.size) :
    Ptr.memmove (Ptr.ref rd od) (Ptr.ref rs os) n h = .ok ((), Space.put h rd (copyRange da sa od os n)) := by
  simp [Ptr.memmove, hd, hs, hro, h1, h2, Space.modify_eq _ _ _ _ hd]

theorem Ptr.fill_ok {h : Heap} {r : R} {a : Array T} {off n : Nat} {v : T}
    (hg : Space.get h r = some a) (hro : Space.ro h r = false) (h1 : off + n ≤ a.size) :
    Ptr.fill (Ptr.ref r off) v n h = .ok ((), Space.put h r (fillRange a off n v)) := by
  simp [Ptr.fill, hg, hro, h1, Space.modify_eq _ _ _ _ hg]

end generic

/-! ## Byte pointers -/

/-- `*p` for an `unsigned char *`. -/
abbrev load8 (p : BPtr) : M UInt8 := Ptr.load p
/-- `p[i]` for an `unsigned char *`. -/
abbrev index8 (p : BPtr) (i : Int) : M UInt8 := Ptr.index p i
/-- `*p = v` for an `unsigned char *`. -/
abbrev store8 (p : BPtr) (v : UInt8) : M Unit := Ptr.store p v
/-- `memcpy(dst, src, n)` for byte pointers (`zmemcpy`). -/
abbrev memcpyB (dst src : BPtr) (n : Nat) : M Unit := Ptr.memcpy dst src n
/-- `memmove(dst, src, n)` for byte pointers. -/
abbrev memmoveB (dst src : BPtr) (n : Nat) : M Unit := Ptr.memmove dst src n
/-- `memset(dst, c, n)` for a byte pointer. -/
abbrev memsetB (dst : BPtr) (c : UInt8) (n : Nat) : M Unit := Ptr.fill dst c n

theorem load8_ok {h : Heap} {blk off : Nat} {bytes : Array UInt8} (hb : h.bytes blk = some bytes)
    (hlt : off < bytes.size) : OkOn h (load8 (.ref (.blk blk) off)) bytes[off] :=
  Ptr.load_ok hb hlt

theorem index8_ok {h : Heap} {blk off i : Nat} {bytes : Array UInt8} (hb : h.bytes blk = some bytes)
    (hlt : off + i < bytes.size) : OkOn h (index8 (.ref (.blk blk) off) i) bytes[off + i] :=
  Ptr.index_ok hb hlt

/-- `memcpy` between two different byte blocks, both writable-or-readable as needed: the destination block `nb` is
writable, the ranges are inside the blocks. The result is the heap with the block `nb` replaced. -/
theorem memcpyB_blk_ok {h : Heap} {nb no pb po n : Nat} {ob pbuf : Array UInt8}
    (e1 : h.bytes nb = some ob) (e2 : h.bytes pb = some pbuf) (hro : h.ro nb = false) (hne : nb ≠ pb)
    (h1 : no + n ≤ ob.size) (h2 : po + n ≤ pbuf.size) :
    memcpyB (.ref (.blk nb) no) (.ref (.blk pb) po) n h =
      .ok ((), { h with bytes := upd h.bytes nb (some (copyRange ob pbuf no po n)) }) :=
  Ptr.memcpy_ok (rd := BRef.blk nb) (rs := BRef.blk pb) e1 e2 hro h1 h2 (Or.inl (fun hh => hne (BRef.blk.inj hh)))

/-- The index of the first NUL byte of `a` at or after `i`. -/
def strlenFrom (a : Array UInt8) (i : Nat) : Option Nat :=
  if h : i < a.size then (if a[i] == 0 then some i else strlenFrom a (i + 1)) else none
termination_by a.size - i

/-- `strlen(p)`. Faults if `p` is null or dangling, or if no NUL byte follows inside the block (the C reads outside
the object). -/
def strlenB (p : BPtr) : M UInt64 := fun h =>
  match p with
  | .null => .error (.ub "strlen of a null pointer")
  | .ref r off =>
    match Space.get h r with
    | none => .error (.ub "strlen through a dangling pointer")
    | some a =>
      match strlenFrom a off with
      | some j => .ok (UInt64.ofNat (j - off), h)
      | none => .error (.ub "strlen: no terminating NUL inside the object")

theorem strlenFrom_eq (a : Array UInt8) (k : Nat) (hz : a[k]? = some 0) :
    ∀ d i, i + d = k → (∀ j, i ≤ j → j < k → a[j]? ≠ some 0) → strlenFrom a i = some k := by
  intro d
  induction d with
  | zero =>
    intro i hi _
    subst hi
    have hlt : i < a.size := by
      rcases Nat.lt_or_ge i a.size with hh | hh
      · exact hh
      · simp [Array.getElem?_eq_none hh] at hz
    rw [strlenFrom]
    simp [hlt]
    have : a[i] = 0 := by simpa [hlt] using hz
    simp [this]
  | succ d ih =>
    intro i hi hn
    have hlt : i < a.size := by
      rcases Nat.lt_or_ge i a.size with hh | hh
      · exact hh
      · simp [Array.getElem?_eq_none (by omega : a.size ≤ k)] at hz
    have hne : a[i] ≠ 0 := by
      intro h0
      exact hn i (Nat.le_refl _) (by omega) (by simp [hlt, h0])
    rw [strlenFrom]
    simp only [hlt, dite_true]
    have : (a[i] == 0) = false := by simpa using hne
    simp only [this, Bool.false_eq_true, ite_false]
    exact ih (i + 1) (by omega) (fun j hj hjk => hn j (by omega) hjk)

theorem strlenB_ok {h : Heap} {r : BRef} {a : Array UInt8} {off k : Nat}
    (hg : Space.get h r = some a) (hk : off ≤ k) (hz : a[k]? = some 0)
    (hn : ∀ j, off ≤ j → j < k → a[j]? ≠ some 0) :
    OkOn h (strlenB (Ptr.ref r off)) (UInt64.ofNat (k - off)) := by
  unfold OkOn strlenB
  simp [hg, strlenFrom_eq a k hz (k - off) off (by omega) hn]

end C
