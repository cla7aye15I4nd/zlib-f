import ZlibF.Runtime.Ptr
import ZlibF.Runtime.LibcTables

/-!
# Runtime: the C library

Trusted base of every translation; see `docs/trusted-base.md`. Everything here models a function of the C library
(or of the compiler's literal handling), not the C language: the language level (pointers, arithmetic, loops, the
heap tables) is in `Space.lean`, `Monad.lean` and `Ptr.lean`. Each function says how it differs from the real one.

| C library | Lean | Differs from the real function |
| --- | --- | --- |
| `memcpy`, `zmemcpy` | `Ptr.memcpy`, `memcpyB` (and `copyK` for a whole record, `LibcTables.lean`) | faults on NULL even for `n = 0`; on a read-only destination (for `n > 0`); on overlap; counts elements, not bytes |
| `memmove` | `Ptr.memmove`, `memmoveB` | the same without the overlap fault |
| `memset`, `zmemzero` | `Ptr.fill` (set `n` elements to a value), `Ptr.memset` (every byte of each element is `c`), `memsetB` | counts elements; `Ptr.fill` is `memset` only for bytes or the value 0 |
| `strlen` | `strlenB` | faults when no NUL lies inside the block (the C reads past the object) |
| `malloc` (through `ZALLOC`) | `allocB`, `allocW`, `allocK` per struct kind | the content is arbitrary integers and NULL pointers; success is decided by the oracle `Heap.allocOk`; faults if the heap is not `Fresh`; the size is a count of elements |
| `free` | `freeB`, `freeW`, `freeK` | faults on a pointer that is not the start of a live block, on a freed block (double free), on a read-only block; NULL is a no-op |
| string literal | `strLitRef` (the table `strTable`) | a static read-only array, the same pointer every time; a text outside the sources is a fault |
| (test harness, not a C function) | `allocBytes`, `allocBytesRO` | put given bytes in a fresh block; take no allocation call |

Not modelled: `calloc`, `realloc`, `printf` and the `gz` file calls other than through `GzFs` (the file system model of
the translations, in `ZlibF/Zlib/gzfs.lean`), `errno`, `abs`, `strerror` (the translations write them themselves).
-/

namespace C

/-! ## `memcpy`, `memmove`, `memset`, `strlen` on arrays -/

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

/-- `memcpy(dst, src, n)` for byte pointers (`zmemcpy`). -/
abbrev memcpyB (dst src : BPtr) (n : Nat) : M Unit := Ptr.memcpy dst src n
/-- `memmove(dst, src, n)` for byte pointers. -/
abbrev memmoveB (dst src : BPtr) (n : Nat) : M Unit := Ptr.memmove dst src n
/-- `memset(dst, c, n)` for a byte pointer. -/
abbrev memsetB (dst : BPtr) (c : UInt8) (n : Nat) : M Unit := Ptr.fill dst c n

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

/-! ## `malloc`, `free` and string literals

`malloc` and `free` through the default allocator, for byte blocks and for blocks of 16-bit words (the struct kinds
have their own in `LibcTables.lean`). All kinds share one counter of block numbers: a new object takes `nextBlk`, which
only grows, so a freed block number is never reused and a use after free is always detected. Whether the call succeeds
is decided by the oracle `allocOk`; the content of the new memory is arbitrary (`garbage`), so a theorem holds for every
content.

**Block numbers.** `allocB`, `allocW`, `allocBytes`, `allocBytesRO` (and `allocK` for each struct kind) fault if the
block number `nextBlk` is already in use (`Heap.slotUsed`). The fault is not a C behaviour: it says that the heap is not
`Fresh`. A theorem about code that allocates carries `Fresh`; the rules (`allocB_some`, ...) take the hypothesis
`h.slotUsed h.nextBlk = false`, which the tactic `fresh_slot` finds from `Fresh h` in the context. The names with the
suffix `Chk` are aliases of the plain ones. -/


/-- `malloc(n)` for `n` bytes: a fresh writable block with arbitrary content, or `NULL` when the failure oracle
says so. -/
def allocB (n : Nat) : M BPtr := fun h =>
  if h.allocOk h.nalloc then
    if h.slotUsed h.nextBlk then .error (.ub "allocation: the block number is in use (the heap is not Fresh)")
    else
      .ok (.ref (.blk h.nextBlk) 0,
        { h with bytes := upd h.bytes h.nextBlk (some (Array.ofFn (n := n) fun i => Junk.of (h.garbage h.nalloc i.val))),
                 ro := upd h.ro h.nextBlk false, nextBlk := h.nextBlk + 1, nalloc := h.nalloc + 1 })
  else .ok (.null, { h with nalloc := h.nalloc + 1 })

/-- For harnesses and tests, not a C operation: put the bytes `a` into a fresh writable block. It takes no allocation
call of the oracle. -/
def allocBytes (a : Array UInt8) : M BPtr := fun h =>
  if h.slotUsed h.nextBlk then .error (.ub "allocation: the block number is in use (the heap is not Fresh)")
  else
    .ok (.ref (.blk h.nextBlk) 0,
      { h with bytes := upd h.bytes h.nextBlk (some a), ro := upd h.ro h.nextBlk false, nextBlk := h.nextBlk + 1 })

/-- For harnesses and tests, not a C operation: put the bytes `a` into a fresh read-only block (a string literal, a
`const` buffer). -/
def allocBytesRO (a : Array UInt8) : M BPtr := fun h =>
  if h.slotUsed h.nextBlk then .error (.ub "allocation: the block number is in use (the heap is not Fresh)")
  else
    .ok (.ref (.blk h.nextBlk) 0,
      { h with bytes := upd h.bytes h.nextBlk (some a), ro := upd h.ro h.nextBlk true, nextBlk := h.nextBlk + 1 })

/-- `malloc(2 * n)` for `n` 16-bit words, as `allocB`. -/
def allocW (n : Nat) : M WPtr := fun h =>
  if h.allocOk h.nalloc then
    if h.slotUsed h.nextBlk then .error (.ub "allocation: the block number is in use (the heap is not Fresh)")
    else
      .ok (.ref (.blk h.nextBlk) 0,
        { h with words := upd h.words h.nextBlk (some (Array.ofFn (n := n) fun i => Junk.of (h.garbage h.nalloc i.val))),
                 nextBlk := h.nextBlk + 1, nalloc := h.nalloc + 1 })
  else .ok (.null, { h with nalloc := h.nalloc + 1 })

/-- `free(p)` for a byte block: a no-op for `NULL`. Faults for a block that was freed already (double free), for a
read-only block, and for a pointer that is not the start of an allocated block. -/
def freeB (p : BPtr) : M Unit := fun h =>
  match p with
  | .null => .ok ((), h)
  | .ref (.blk b) 0 =>
    match h.bytes b with
    | some _ => if h.ro b then .error (.ub "free of a read-only block") else .ok ((), { h with bytes := upd h.bytes b none })
    | none => .error (.ub "free of a freed or invalid pointer")
  | _ => .error (.ub "free of a pointer that is not the start of an allocated block")

/-- `free(p)` for a block of 16-bit words, as `freeB`. -/
def freeW (p : WPtr) : M Unit := fun h =>
  match p with
  | .null => .ok ((), h)
  | .ref (.blk b) 0 =>
    match h.words b with
    | some _ => .ok ((), { h with words := upd h.words b none })
    | none => .error (.ub "free of a freed or invalid pointer")
  | _ => .error (.ub "free of a pointer that is not the start of an allocated block")

/-- Alias of `allocB`. -/
abbrev allocBChk := allocB
/-- Alias of `allocW`. -/
abbrev allocWChk := allocW
/-- Alias of `allocBytes`. -/
abbrev allocBytesChk := allocBytes
/-- Alias of `allocBytesRO`. -/
abbrev allocBytesROChk := allocBytesRO

/-! ### String literals

A literal is a static, read-only object that is never freed and never consumes an allocation (`BRef.str`, `strTable`
in `Schema.lean`). `strLitRef s` is the pointer to the literal `s`: the same pointer every time, no change to the heap.
The set of literals is closed (the string literals of the library sources); any other text is a fault. -/

/-- The number of the literal `s` in `strTable`, if it is one. -/
def strIndex (s : String) : Option Nat := strTable.findIdx? (fun t => t == s)

/-- A string literal of the C sources: a pointer to its first byte. It reads the heap and does not change it; it
faults if `s` is not a literal of the sources (`strTable`). -/
def strLitRef (s : String) : M BPtr := fun h =>
  match strIndex s with
  | some i => .ok (.ref (.str i) 0, h)
  | none => .error (.ub "string literal not in the table of literals of the sources")

theorem strLitRef_of_index {h : Heap} {s : String} {i : Nat} (hi : strIndex s = some i) :
    strLitRef s h = .ok (.ref (.str i) 0, h) := by
  simp [strLitRef, hi]

theorem strIndex_get {s : String} {i : Nat} (hi : strIndex s = some i) : strTable[i]? = some s := by
  unfold strIndex at hi
  rw [Array.findIdx?_eq_some_iff_getElem] at hi
  obtain ⟨h1, h2, -⟩ := hi
  rw [Array.getElem?_eq_getElem h1]
  simpa using h2

/-- Every text of `strTable` is found. -/
theorem strIndex_of_mem {s : String} (hs : s ∈ strTable) : ∃ i, strIndex s = some i := by
  cases hx : strIndex s with
  | some i => exact ⟨i, rfl⟩
  | none =>
    exfalso
    unfold strIndex at hx
    rw [Array.findIdx?_eq_none_iff] at hx
    have := hx s hs
    simp at this

/-- A literal of the sources: the pointer is the start of the read-only static array of its text and a NUL, and the
heap is unchanged (no block is allocated). -/
theorem strLitRef_of_mem {h : Heap} {s : String} (hs : s ∈ strTable) :
    ∃ i, strLitRef s h = .ok (.ref (.str i) 0, h) ∧ strTable[i]? = some s := by
  obtain ⟨i, hi⟩ := strIndex_of_mem hs
  exact ⟨i, strLitRef_of_index hi, strIndex_get hi⟩

/-- The bytes behind the pointer of a literal: the text and a NUL. -/
theorem strLitRef_get {h : Heap} {s : String} {i : Nat} (hi : strIndex s = some i) :
    Space.get h (BRef.str i) = some (strBytes s) := by
  have hlt : i < strTable.size := (Array.getElem?_eq_some_iff.mp (strIndex_get hi)).1
  rw [BRef.get_str]
  simp only [staticStringBytes, hlt, ite_true, strIndex_get hi, Option.map_some]

/-- A literal is read-only. -/
theorem strLitRef_ro (h : Heap) (i : Nat) : Space.ro h (BRef.str i) = true := rfl

/-! ### Rules -/

theorem allocB_some {h : Heap} (n : Nat) (hok : h.allocOk h.nalloc = true)
    (hs : h.slotUsed h.nextBlk = false := by fresh_slot) :
    allocB n h = .ok (.ref (.blk h.nextBlk) 0,
      { h with bytes := upd h.bytes h.nextBlk (some (Array.ofFn (n := n) fun i => Junk.of (h.garbage h.nalloc i.val))),
               ro := upd h.ro h.nextBlk false, nextBlk := h.nextBlk + 1, nalloc := h.nalloc + 1 }) := by
  simp [allocB, hok, hs]

theorem allocBytesRO_ok {h : Heap} (a : Array UInt8) (hs : h.slotUsed h.nextBlk = false := by fresh_slot) :
    allocBytesRO a h = .ok (.ref (.blk h.nextBlk) 0,
      { h with bytes := upd h.bytes h.nextBlk (some a), ro := upd h.ro h.nextBlk true, nextBlk := h.nextBlk + 1 }) := by
  simp [allocBytesRO, hs]

theorem allocB_none {h : Heap} (n : Nat) (hok : ¬ h.allocOk h.nalloc = true) :
    allocB n h = .ok (.null, { h with nalloc := h.nalloc + 1 }) := by
  simp [allocB, hok]

theorem allocW_some {h : Heap} (n : Nat) (hok : h.allocOk h.nalloc = true)
    (hs : h.slotUsed h.nextBlk = false := by fresh_slot) :
    allocW n h = .ok (.ref (.blk h.nextBlk) 0,
      { h with words := upd h.words h.nextBlk (some (Array.ofFn (n := n) fun i => Junk.of (h.garbage h.nalloc i.val))),
               nextBlk := h.nextBlk + 1, nalloc := h.nalloc + 1 }) := by
  simp [allocW, hok, hs]

theorem allocW_none {h : Heap} (n : Nat) (hok : ¬ h.allocOk h.nalloc = true) :
    allocW n h = .ok (.null, { h with nalloc := h.nalloc + 1 }) := by
  simp [allocW, hok]

theorem freeB_null {h : Heap} : freeB .null h = .ok ((), h) := rfl

theorem freeB_ok {h : Heap} {b : Nat} {a : Array UInt8} (hb : h.bytes b = some a) (hro : h.ro b = false) :
    freeB (.ref (.blk b) 0) h = .ok ((), { h with bytes := upd h.bytes b none }) := by
  simp [freeB, hb, hro]

theorem freeB_freed {h : Heap} {b : Nat} (hb : h.bytes b = none) :
    freeB (.ref (.blk b) 0) h = .error (.ub "free of a freed or invalid pointer") := by
  simp [freeB, hb]

theorem freeW_ok {h : Heap} {b : Nat} {a : Array UInt16} (hb : h.words b = some a) :
    freeW (.ref (.blk b) 0) h = .ok ((), { h with words := upd h.words b none }) := by
  simp [freeW, hb]

/-! ### Faults and ownership

A freed block is never reused, so a use after free and a double free are faults. `Owns` (see `Schema.lean`) says which
blocks are live: the two lemmas below show how `allocB` and `freeB` change it, which is what a leak statement is built
from. -/

/-- A use after free is a fault: a read through a pointer into a block that was freed. -/
theorem load_after_free {h : Heap} {b off : Nat} {a : Array UInt8} (hb : h.bytes b = some a) (hro : h.ro b = false) :
    (freeB (.ref (.blk b) 0) >>= fun _ => load8 (.ref (.blk b) off)) h = .error (.ub "read through a dangling pointer") := by
  rw [bind_app, freeB_ok hb hro]
  simp [load8, Ptr.load]

/-- A double free is a fault. -/
theorem free_twice {h : Heap} {b : Nat} {a : Array UInt8} (hb : h.bytes b = some a) (hro : h.ro b = false) :
    (freeB (.ref (.blk b) 0) >>= fun _ => freeB (.ref (.blk b) 0)) h = .error (.ub "free of a freed or invalid pointer") := by
  rw [bind_app, freeB_ok hb hro]
  simp [freeB]

/-- A successful `allocB` adds exactly the new block to the live blocks. -/
theorem allocB_owns {h : Heap} (n : Nat) {S : Nat → Prop} (hok : h.allocOk h.nalloc = true) (hO : h.Owns S)
    (hs : h.slotUsed h.nextBlk = false := by fresh_slot) :
    ∃ h', allocB n h = .ok (.ref (.blk h.nextBlk) 0, h') ∧ h'.Owns (fun b => S b ∨ b = h.nextBlk) := by
  refine ⟨_, allocB_some n hok hs, ?_⟩
  intro b
  by_cases hb : b = h.nextBlk
  · subst hb; simp [Heap.live]
  · have := hO b
    simp only [Heap.live] at this ⊢
    simp [upd_ne _ _ _ _ hb, hb, this]

/-- `free` of a byte block that no other table holds removes exactly that block from the live blocks. -/
theorem freeB_owns {h : Heap} {b : Nat} {a : Array UInt8} {S : Nat → Prop} (hb : h.bytes b = some a)
    (hro : h.ro b = false)
    (hother : h.words b = none ∧ h.streams b = none ∧ h.gzheaders b = none ∧ h.dstates b = none ∧
      h.istates b = none ∧ h.gzstates b = none)
    (hO : h.Owns S) :
    ∃ h', freeB (.ref (.blk b) 0) h = .ok ((), h') ∧ h'.Owns (fun x => S x ∧ x ≠ b) := by
  refine ⟨_, freeB_ok hb hro, ?_⟩
  intro x
  by_cases hx : x = b
  · subst hx
    obtain ⟨e1, e2, e3, e4, e5, e6⟩ := hother
    simp [Heap.live, e1, e2, e3, e4, e5, e6]
  · have := hO x
    simp only [Heap.live] at this ⊢
    simp [upd_ne _ _ _ _ hx, hx, this]

end C
