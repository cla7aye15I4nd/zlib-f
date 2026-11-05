import ZlibF.Runtime.Monad

/-!
# Load and store for every struct kind (GENERATED, do not edit)

`ldK p` is `*p` for a pointer to a struct of kind `K`, `stK p v` is `*p = v` (a whole-record store; a field
write is a load, a record update and a store). Every primitive faults on a null, dangling or read-only target, as
the C is undefined there. `malloc`, `free` and the whole-record `memcpy` of each kind are in `LibcTables.lean`.
-/

namespace C

/-- `*p` for a `z_stream *`: faults if `p` is null or does not point to a live object. -/
def ldZStream (p : ZStreamPtr) : M ZStream := fun h =>
  match p with
  | none => .error (.ub "null dereference (z_stream)")
  | some r => match r.get h with
    | some v => .ok (v, h)
    | none => .error (.ub "access through a dangling pointer (z_stream)")

/-- `*p = v` for a `z_stream *`: faults if `p` is null, dangling or read-only. -/
def stZStream (p : ZStreamPtr) (v : ZStream) : M Unit := fun h =>
  match p with
  | none => .error (.ub "null dereference (z_stream)")
  | some r => match r.get h with
    | some _ => if r.isRo then .error (.ub "store into a read-only object (z_stream)") else .ok ((), r.put h v)
    | none => .error (.ub "access through a dangling pointer (z_stream)")

theorem ldZStream_ok {h : Heap} {r : ZStreamRef} {v : ZStream} (e : r.get h = some v) :
    ldZStream (some r) h = .ok (v, h) := by simp [ldZStream, e]

theorem stZStream_ok {h : Heap} {r : ZStreamRef} {v v' : ZStream} (e : r.get h = some v) (hro : r.isRo = false) :
    stZStream (some r) v' h = .ok ((), r.put h v') := by simp [stZStream, e, hro]

theorem ldZStream_tab {h : Heap} {i : Nat} {v : ZStream} (e : h.streams i = some v) :
    ldZStream (some (.tab i)) h = .ok (v, h) := ldZStream_ok e

theorem stZStream_tab {h : Heap} {i : Nat} {v v' : ZStream} (e : h.streams i = some v) :
    stZStream (some (.tab i)) v' h = .ok ((), { h with streams := upd h.streams i (some v') }) := by
  rw [stZStream_ok (r := .tab i) e rfl]
  rw [ZStreamRef.put_tab e v']

/-- `*p` for a `gz_header *`: faults if `p` is null or does not point to a live object. -/
def ldGzHeader (p : GzHeaderPtr) : M GzHeader := fun h =>
  match p with
  | none => .error (.ub "null dereference (gz_header)")
  | some r => match r.get h with
    | some v => .ok (v, h)
    | none => .error (.ub "access through a dangling pointer (gz_header)")

/-- `*p = v` for a `gz_header *`: faults if `p` is null, dangling or read-only. -/
def stGzHeader (p : GzHeaderPtr) (v : GzHeader) : M Unit := fun h =>
  match p with
  | none => .error (.ub "null dereference (gz_header)")
  | some r => match r.get h with
    | some _ => if r.isRo then .error (.ub "store into a read-only object (gz_header)") else .ok ((), r.put h v)
    | none => .error (.ub "access through a dangling pointer (gz_header)")

theorem ldGzHeader_ok {h : Heap} {r : GzHeaderRef} {v : GzHeader} (e : r.get h = some v) :
    ldGzHeader (some r) h = .ok (v, h) := by simp [ldGzHeader, e]

theorem stGzHeader_ok {h : Heap} {r : GzHeaderRef} {v v' : GzHeader} (e : r.get h = some v) (hro : r.isRo = false) :
    stGzHeader (some r) v' h = .ok ((), r.put h v') := by simp [stGzHeader, e, hro]

theorem ldGzHeader_tab {h : Heap} {i : Nat} {v : GzHeader} (e : h.gzheaders i = some v) :
    ldGzHeader (some (.tab i)) h = .ok (v, h) := ldGzHeader_ok e

theorem stGzHeader_tab {h : Heap} {i : Nat} {v v' : GzHeader} (e : h.gzheaders i = some v) :
    stGzHeader (some (.tab i)) v' h = .ok ((), { h with gzheaders := upd h.gzheaders i (some v') }) := by
  rw [stGzHeader_ok (r := .tab i) e rfl]
  rw [GzHeaderRef.put_tab e v']

/-- `*p` for a `deflate_state *`: faults if `p` is null or does not point to a live object. -/
def ldDeflateState (p : DeflateStatePtr) : M DeflateState := fun h =>
  match p with
  | none => .error (.ub "null dereference (deflate_state)")
  | some r => match r.get h with
    | some v => .ok (v, h)
    | none => .error (.ub "access through a dangling pointer (deflate_state)")

/-- `*p = v` for a `deflate_state *`: faults if `p` is null, dangling or read-only. -/
def stDeflateState (p : DeflateStatePtr) (v : DeflateState) : M Unit := fun h =>
  match p with
  | none => .error (.ub "null dereference (deflate_state)")
  | some r => match r.get h with
    | some _ => if r.isRo then .error (.ub "store into a read-only object (deflate_state)") else .ok ((), r.put h v)
    | none => .error (.ub "access through a dangling pointer (deflate_state)")

theorem ldDeflateState_ok {h : Heap} {r : DeflateStateRef} {v : DeflateState} (e : r.get h = some v) :
    ldDeflateState (some r) h = .ok (v, h) := by simp [ldDeflateState, e]

theorem stDeflateState_ok {h : Heap} {r : DeflateStateRef} {v v' : DeflateState} (e : r.get h = some v) (hro : r.isRo = false) :
    stDeflateState (some r) v' h = .ok ((), r.put h v') := by simp [stDeflateState, e, hro]

theorem ldDeflateState_tab {h : Heap} {i : Nat} {v : DeflateState} (e : h.dstates i = some v) :
    ldDeflateState (some (.tab i)) h = .ok (v, h) := ldDeflateState_ok e

theorem stDeflateState_tab {h : Heap} {i : Nat} {v v' : DeflateState} (e : h.dstates i = some v) :
    stDeflateState (some (.tab i)) v' h = .ok ((), { h with dstates := upd h.dstates i (some v') }) := by
  rw [stDeflateState_ok (r := .tab i) e rfl]
  rw [DeflateStateRef.put_tab e v']

/-- `*p` for a `inflate_state *`: faults if `p` is null or does not point to a live object. -/
def ldInflateState (p : InflateStatePtr) : M InflateState := fun h =>
  match p with
  | none => .error (.ub "null dereference (inflate_state)")
  | some r => match r.get h with
    | some v => .ok (v, h)
    | none => .error (.ub "access through a dangling pointer (inflate_state)")

/-- `*p = v` for a `inflate_state *`: faults if `p` is null, dangling or read-only. -/
def stInflateState (p : InflateStatePtr) (v : InflateState) : M Unit := fun h =>
  match p with
  | none => .error (.ub "null dereference (inflate_state)")
  | some r => match r.get h with
    | some _ => if r.isRo then .error (.ub "store into a read-only object (inflate_state)") else .ok ((), r.put h v)
    | none => .error (.ub "access through a dangling pointer (inflate_state)")

theorem ldInflateState_ok {h : Heap} {r : InflateStateRef} {v : InflateState} (e : r.get h = some v) :
    ldInflateState (some r) h = .ok (v, h) := by simp [ldInflateState, e]

theorem stInflateState_ok {h : Heap} {r : InflateStateRef} {v v' : InflateState} (e : r.get h = some v) (hro : r.isRo = false) :
    stInflateState (some r) v' h = .ok ((), r.put h v') := by simp [stInflateState, e, hro]

theorem ldInflateState_tab {h : Heap} {i : Nat} {v : InflateState} (e : h.istates i = some v) :
    ldInflateState (some (.tab i)) h = .ok (v, h) := ldInflateState_ok e

theorem stInflateState_tab {h : Heap} {i : Nat} {v v' : InflateState} (e : h.istates i = some v) :
    stInflateState (some (.tab i)) v' h = .ok ((), { h with istates := upd h.istates i (some v') }) := by
  rw [stInflateState_ok (r := .tab i) e rfl]
  rw [InflateStateRef.put_tab e v']

/-- `*p` for a `gz_state *`: faults if `p` is null or does not point to a live object. -/
def ldGzState (p : GzStatePtr) : M GzState := fun h =>
  match p with
  | none => .error (.ub "null dereference (gz_state)")
  | some r => match r.get h with
    | some v => .ok (v, h)
    | none => .error (.ub "access through a dangling pointer (gz_state)")

/-- `*p = v` for a `gz_state *`: faults if `p` is null, dangling or read-only. -/
def stGzState (p : GzStatePtr) (v : GzState) : M Unit := fun h =>
  match p with
  | none => .error (.ub "null dereference (gz_state)")
  | some r => match r.get h with
    | some _ => if r.isRo then .error (.ub "store into a read-only object (gz_state)") else .ok ((), r.put h v)
    | none => .error (.ub "access through a dangling pointer (gz_state)")

theorem ldGzState_ok {h : Heap} {r : GzStateRef} {v : GzState} (e : r.get h = some v) :
    ldGzState (some r) h = .ok (v, h) := by simp [ldGzState, e]

theorem stGzState_ok {h : Heap} {r : GzStateRef} {v v' : GzState} (e : r.get h = some v) (hro : r.isRo = false) :
    stGzState (some r) v' h = .ok ((), r.put h v') := by simp [stGzState, e, hro]

theorem ldGzState_tab {h : Heap} {i : Nat} {v : GzState} (e : h.gzstates i = some v) :
    ldGzState (some (.tab i)) h = .ok (v, h) := ldGzState_ok e

theorem stGzState_tab {h : Heap} {i : Nat} {v v' : GzState} (e : h.gzstates i = some v) :
    stGzState (some (.tab i)) v' h = .ok ((), { h with gzstates := upd h.gzstates i (some v') }) := by
  rw [stGzState_ok (r := .tab i) e rfl]
  rw [GzStateRef.put_tab e v']

/-- `*p` for a `gzFile_s *`: faults if `p` is null or does not point to a live object. -/
def ldGzFile (p : GzFilePtr) : M GzFile := fun h =>
  match p with
  | none => .error (.ub "null dereference (gzFile_s)")
  | some r => match r.get h with
    | some v => .ok (v, h)
    | none => .error (.ub "access through a dangling pointer (gzFile_s)")

/-- `*p = v` for a `gzFile_s *`: faults if `p` is null, dangling or read-only. -/
def stGzFile (p : GzFilePtr) (v : GzFile) : M Unit := fun h =>
  match p with
  | none => .error (.ub "null dereference (gzFile_s)")
  | some r => match r.get h with
    | some _ => if r.isRo then .error (.ub "store into a read-only object (gzFile_s)") else .ok ((), r.put h v)
    | none => .error (.ub "access through a dangling pointer (gzFile_s)")

theorem ldGzFile_ok {h : Heap} {r : GzFileRef} {v : GzFile} (e : r.get h = some v) :
    ldGzFile (some r) h = .ok (v, h) := by simp [ldGzFile, e]

theorem stGzFile_ok {h : Heap} {r : GzFileRef} {v v' : GzFile} (e : r.get h = some v) (hro : r.isRo = false) :
    stGzFile (some r) v' h = .ok ((), r.put h v') := by simp [stGzFile, e, hro]

/-- `*p` for a `tree_desc *`: faults if `p` is null or does not point to a live object. -/
def ldTreeDesc (p : TreeDescPtr) : M TreeDesc := fun h =>
  match p with
  | none => .error (.ub "null dereference (tree_desc)")
  | some r => match r.get h with
    | some v => .ok (v, h)
    | none => .error (.ub "access through a dangling pointer (tree_desc)")

/-- `*p = v` for a `tree_desc *`: faults if `p` is null, dangling or read-only. -/
def stTreeDesc (p : TreeDescPtr) (v : TreeDesc) : M Unit := fun h =>
  match p with
  | none => .error (.ub "null dereference (tree_desc)")
  | some r => match r.get h with
    | some _ => if r.isRo then .error (.ub "store into a read-only object (tree_desc)") else .ok ((), r.put h v)
    | none => .error (.ub "access through a dangling pointer (tree_desc)")

theorem ldTreeDesc_ok {h : Heap} {r : TreeDescRef} {v : TreeDesc} (e : r.get h = some v) :
    ldTreeDesc (some r) h = .ok (v, h) := by simp [ldTreeDesc, e]

theorem stTreeDesc_ok {h : Heap} {r : TreeDescRef} {v v' : TreeDesc} (e : r.get h = some v) (hro : r.isRo = false) :
    stTreeDesc (some r) v' h = .ok ((), r.put h v') := by simp [stTreeDesc, e, hro]

/-- `*p` for a `static_tree_desc *`: faults if `p` is null or does not point to a live object. -/
def ldStaticTreeDesc (p : StaticTreeDescPtr) : M StaticTreeDesc := fun h =>
  match p with
  | none => .error (.ub "null dereference (static_tree_desc)")
  | some r => match r.get h with
    | some v => .ok (v, h)
    | none => .error (.ub "access through a dangling pointer (static_tree_desc)")

/-- `*p = v` for a `static_tree_desc *`: faults if `p` is null, dangling or read-only. -/
def stStaticTreeDesc (p : StaticTreeDescPtr) (v : StaticTreeDesc) : M Unit := fun h =>
  match p with
  | none => .error (.ub "null dereference (static_tree_desc)")
  | some r => match r.get h with
    | some _ => if r.isRo then .error (.ub "store into a read-only object (static_tree_desc)") else .ok ((), r.put h v)
    | none => .error (.ub "access through a dangling pointer (static_tree_desc)")

theorem ldStaticTreeDesc_ok {h : Heap} {r : StaticTreeDescRef} {v : StaticTreeDesc} (e : r.get h = some v) :
    ldStaticTreeDesc (some r) h = .ok (v, h) := by simp [ldStaticTreeDesc, e]

theorem stStaticTreeDesc_ok {h : Heap} {r : StaticTreeDescRef} {v v' : StaticTreeDesc} (e : r.get h = some v) (hro : r.isRo = false) :
    stStaticTreeDesc (some r) v' h = .ok ((), r.put h v') := by simp [stStaticTreeDesc, e, hro]

/-! ## `struct internal_state *` and its casts -/

/-- `(deflate_state *) p` for `p` of type `struct internal_state *`: faults if `p` points to the other kind of state. -/
def castDeflateState (p : Option StateRef) : M DeflateStatePtr := fun h =>
  match p with
  | none => .ok (none, h)
  | some (.deflate i) => .ok (some (.tab i), h)
  | some (.inflate _) => .error (.ub "a inflate_state is used as a deflate_state")

theorem castDeflateState_ok {h : Heap} {i : Nat} : castDeflateState (some (.deflate i)) h = .ok (some (.tab i), h) := rfl

/-- `(struct internal_state *) p` for `p` of type `deflate_state *`. -/
def StateRef.ofDeflateState : DeflateStatePtr → Option StateRef
  | none => none
  | some (.tab i) => some (.deflate i)

/-- `(inflate_state *) p` for `p` of type `struct internal_state *`: faults if `p` points to the other kind of state. -/
def castInflateState (p : Option StateRef) : M InflateStatePtr := fun h =>
  match p with
  | none => .ok (none, h)
  | some (.inflate i) => .ok (some (.tab i), h)
  | some (.deflate _) => .error (.ub "a deflate_state is used as a inflate_state")

theorem castInflateState_ok {h : Heap} {i : Nat} : castInflateState (some (.inflate i)) h = .ok (some (.tab i), h) := rfl

/-- `(struct internal_state *) p` for `p` of type `inflate_state *`. -/
def StateRef.ofInflateState : InflateStatePtr → Option StateRef
  | none => none
  | some (.tab i) => some (.inflate i)

end C
