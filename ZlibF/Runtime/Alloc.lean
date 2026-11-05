import ZlibF.Runtime.Ptr

/-!
# Runtime: allocation of blocks

Trusted base of every translation; see `docs/trusted-base.md`.

`malloc` and `free` through the default allocator, for byte blocks and for blocks of 16-bit words. (Struct kinds
have their own, generated in `Tables.lean`.) All kinds share one counter of block numbers: a new object takes
`nextBlk`, which only grows, so a freed block number is never reused and a use after free is always detected.
Whether the call succeeds is decided by the oracle `allocOk`; the content of the new memory is arbitrary (`garbage`),
so a theorem holds for every content.

**Block numbers.** `allocB`, `allocW`, `allocBytes`, `allocBytesRO` (and `allocK` for each struct kind in
`Tables.lean`) fault if the block number `nextBlk` is already in use (`Heap.slotUsed`). The fault is not a C
behaviour: it says that the heap is not `Fresh`. A theorem about code that allocates carries `Fresh`; the rules
(`allocB_some`, ...) take the hypothesis `h.slotUsed h.nextBlk = false`, which the tactic `fresh_slot` finds from
`Fresh h` in the context. The names with the suffix `Chk` are aliases of the plain ones.
-/

namespace C

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
  simp [strIndex_get hi]

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

/-- A store into a read-only block is a fault. -/
theorem store_readonly {h : Heap} {b off : Nat} {a : Array UInt8} {v : UInt8} (hb : h.bytes b = some a) (hro : h.ro b = true) :
    store8 (.ref (.blk b) off) v h = .error (.ub "store into a read-only object") := by
  simp [store8, Ptr.store, hb, hro]

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
