import ZlibF.Runtime.Monad

/-!
# Load, store, allocate and free for every struct kind (GENERATED, do not edit)

`ldK p` is `*p` for a pointer to a struct of kind `K`, `stK p v` is `*p = v` (a whole-record store; a field
write is a load, a record update and a store), `allocK` and `freeK` are `malloc` and `free` through the
default allocator. Every primitive faults on a null, dangling or read-only target, as the C is undefined there.
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

/-- `malloc(sizeof(z_stream))` through the default allocator: a fresh live record with arbitrary integers and
null pointers (a documented gap: C leaves them indeterminate, see `docs/trusted-base.md`), or null when the
failure oracle says so. It is a fault (not a C behaviour) if the block number `nextBlk` is already in use:
the heap is then not `Fresh`, and a theorem about allocation carries `Fresh`. -/
def allocZStream : M ZStreamPtr := fun h =>
  if h.allocOk h.nalloc then
    if h.slotUsed h.nextBlk then .error (.ub "allocation: the block number is in use (the heap is not Fresh)")
    else .ok (some (.tab h.nextBlk), { h with streams := upd h.streams h.nextBlk (some (ZStream.garbage (h.garbage h.nalloc))), nextBlk := h.nextBlk + 1, nalloc := h.nalloc + 1 })
  else .ok (none, { h with nalloc := h.nalloc + 1 })

/-- Alias of `allocZStream`. -/
abbrev allocZStreamChk := allocZStream

theorem allocZStream_some {h : Heap} (hok : h.allocOk h.nalloc = true)
    (hs : h.slotUsed h.nextBlk = false := by fresh_slot) :
    allocZStream h = .ok (some (.tab h.nextBlk), { h with streams := upd h.streams h.nextBlk (some (ZStream.garbage (h.garbage h.nalloc))), nextBlk := h.nextBlk + 1, nalloc := h.nalloc + 1 }) := by simp [allocZStream, hok, hs]

theorem allocZStream_none {h : Heap} (hok : ¬ h.allocOk h.nalloc = true) :
    allocZStream h = .ok (none, { h with nalloc := h.nalloc + 1 }) := by simp [allocZStream, hok]

/-- `free(p)` for a `z_stream *`: a no-op for null; faults for a block that is not live (double free) and for a
pointer that was not returned by the allocator. -/
def freeZStream (p : ZStreamPtr) : M Unit := fun h =>
  match p with
  | none => .ok ((), h)
  | some (.tab i) => match h.streams i with
    | some _ => .ok ((), { h with streams := upd h.streams i none })
    | none => .error (.ub "free of a freed or invalid pointer (z_stream)")
  | some _ => .error (.ub "free of a pointer that was not allocated (z_stream)")

theorem freeZStream_null {h : Heap} : freeZStream none h = .ok ((), h) := rfl

/-- `*dst = *src` for two `z_stream *` (`zmemcpy(dst, src, sizeof *dst)`): a whole-record copy. Faults if either pointer
is null, dangling or the destination read-only, and if both denote the same object (`memcpy` with overlapping
ranges is undefined; the `z_stream` objects of the heap do not contain one another). -/
def copyZStream (dst src : ZStreamPtr) : M Unit := fun h =>
  match dst, src with
  | some d, some s =>
    if d = s then .error (.ub "memcpy of a z_stream onto itself (overlapping ranges)")
    else (ldZStream (some s) >>= fun v => stZStream (some d) v) h
  | _, _ => .error (.ub "null dereference (z_stream)")

theorem freeZStream_tab {h : Heap} {i : Nat} {v : ZStream} (e : h.streams i = some v) :
    freeZStream (some (.tab i)) h = .ok ((), { h with streams := upd h.streams i none }) := by simp [freeZStream, e]

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

/-- `malloc(sizeof(gz_header))` through the default allocator: a fresh live record with arbitrary integers and
null pointers (a documented gap: C leaves them indeterminate, see `docs/trusted-base.md`), or null when the
failure oracle says so. It is a fault (not a C behaviour) if the block number `nextBlk` is already in use:
the heap is then not `Fresh`, and a theorem about allocation carries `Fresh`. -/
def allocGzHeader : M GzHeaderPtr := fun h =>
  if h.allocOk h.nalloc then
    if h.slotUsed h.nextBlk then .error (.ub "allocation: the block number is in use (the heap is not Fresh)")
    else .ok (some (.tab h.nextBlk), { h with gzheaders := upd h.gzheaders h.nextBlk (some (GzHeader.garbage (h.garbage h.nalloc))), nextBlk := h.nextBlk + 1, nalloc := h.nalloc + 1 })
  else .ok (none, { h with nalloc := h.nalloc + 1 })

/-- Alias of `allocGzHeader`. -/
abbrev allocGzHeaderChk := allocGzHeader

theorem allocGzHeader_some {h : Heap} (hok : h.allocOk h.nalloc = true)
    (hs : h.slotUsed h.nextBlk = false := by fresh_slot) :
    allocGzHeader h = .ok (some (.tab h.nextBlk), { h with gzheaders := upd h.gzheaders h.nextBlk (some (GzHeader.garbage (h.garbage h.nalloc))), nextBlk := h.nextBlk + 1, nalloc := h.nalloc + 1 }) := by simp [allocGzHeader, hok, hs]

theorem allocGzHeader_none {h : Heap} (hok : ¬ h.allocOk h.nalloc = true) :
    allocGzHeader h = .ok (none, { h with nalloc := h.nalloc + 1 }) := by simp [allocGzHeader, hok]

/-- `free(p)` for a `gz_header *`: a no-op for null; faults for a block that is not live (double free) and for a
pointer that was not returned by the allocator. -/
def freeGzHeader (p : GzHeaderPtr) : M Unit := fun h =>
  match p with
  | none => .ok ((), h)
  | some (.tab i) => match h.gzheaders i with
    | some _ => .ok ((), { h with gzheaders := upd h.gzheaders i none })
    | none => .error (.ub "free of a freed or invalid pointer (gz_header)")

theorem freeGzHeader_null {h : Heap} : freeGzHeader none h = .ok ((), h) := rfl

/-- `*dst = *src` for two `gz_header *` (`zmemcpy(dst, src, sizeof *dst)`): a whole-record copy. Faults if either pointer
is null, dangling or the destination read-only, and if both denote the same object (`memcpy` with overlapping
ranges is undefined; the `gz_header` objects of the heap do not contain one another). -/
def copyGzHeader (dst src : GzHeaderPtr) : M Unit := fun h =>
  match dst, src with
  | some d, some s =>
    if d = s then .error (.ub "memcpy of a gz_header onto itself (overlapping ranges)")
    else (ldGzHeader (some s) >>= fun v => stGzHeader (some d) v) h
  | _, _ => .error (.ub "null dereference (gz_header)")

theorem freeGzHeader_tab {h : Heap} {i : Nat} {v : GzHeader} (e : h.gzheaders i = some v) :
    freeGzHeader (some (.tab i)) h = .ok ((), { h with gzheaders := upd h.gzheaders i none }) := by simp [freeGzHeader, e]

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

/-- `malloc(sizeof(deflate_state))` through the default allocator: a fresh live record with arbitrary integers and
null pointers (a documented gap: C leaves them indeterminate, see `docs/trusted-base.md`), or null when the
failure oracle says so. It is a fault (not a C behaviour) if the block number `nextBlk` is already in use:
the heap is then not `Fresh`, and a theorem about allocation carries `Fresh`. -/
def allocDeflateState : M DeflateStatePtr := fun h =>
  if h.allocOk h.nalloc then
    if h.slotUsed h.nextBlk then .error (.ub "allocation: the block number is in use (the heap is not Fresh)")
    else .ok (some (.tab h.nextBlk), { h with dstates := upd h.dstates h.nextBlk (some (DeflateState.garbage (h.garbage h.nalloc))), nextBlk := h.nextBlk + 1, nalloc := h.nalloc + 1 })
  else .ok (none, { h with nalloc := h.nalloc + 1 })

/-- Alias of `allocDeflateState`. -/
abbrev allocDeflateStateChk := allocDeflateState

theorem allocDeflateState_some {h : Heap} (hok : h.allocOk h.nalloc = true)
    (hs : h.slotUsed h.nextBlk = false := by fresh_slot) :
    allocDeflateState h = .ok (some (.tab h.nextBlk), { h with dstates := upd h.dstates h.nextBlk (some (DeflateState.garbage (h.garbage h.nalloc))), nextBlk := h.nextBlk + 1, nalloc := h.nalloc + 1 }) := by simp [allocDeflateState, hok, hs]

theorem allocDeflateState_none {h : Heap} (hok : ¬ h.allocOk h.nalloc = true) :
    allocDeflateState h = .ok (none, { h with nalloc := h.nalloc + 1 }) := by simp [allocDeflateState, hok]

/-- `free(p)` for a `deflate_state *`: a no-op for null; faults for a block that is not live (double free) and for a
pointer that was not returned by the allocator. -/
def freeDeflateState (p : DeflateStatePtr) : M Unit := fun h =>
  match p with
  | none => .ok ((), h)
  | some (.tab i) => match h.dstates i with
    | some _ => .ok ((), { h with dstates := upd h.dstates i none })
    | none => .error (.ub "free of a freed or invalid pointer (deflate_state)")

theorem freeDeflateState_null {h : Heap} : freeDeflateState none h = .ok ((), h) := rfl

/-- `*dst = *src` for two `deflate_state *` (`zmemcpy(dst, src, sizeof *dst)`): a whole-record copy. Faults if either pointer
is null, dangling or the destination read-only, and if both denote the same object (`memcpy` with overlapping
ranges is undefined; the `deflate_state` objects of the heap do not contain one another). -/
def copyDeflateState (dst src : DeflateStatePtr) : M Unit := fun h =>
  match dst, src with
  | some d, some s =>
    if d = s then .error (.ub "memcpy of a deflate_state onto itself (overlapping ranges)")
    else (ldDeflateState (some s) >>= fun v => stDeflateState (some d) v) h
  | _, _ => .error (.ub "null dereference (deflate_state)")

theorem freeDeflateState_tab {h : Heap} {i : Nat} {v : DeflateState} (e : h.dstates i = some v) :
    freeDeflateState (some (.tab i)) h = .ok ((), { h with dstates := upd h.dstates i none }) := by simp [freeDeflateState, e]

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

/-- `malloc(sizeof(inflate_state))` through the default allocator: a fresh live record with arbitrary integers and
null pointers (a documented gap: C leaves them indeterminate, see `docs/trusted-base.md`), or null when the
failure oracle says so. It is a fault (not a C behaviour) if the block number `nextBlk` is already in use:
the heap is then not `Fresh`, and a theorem about allocation carries `Fresh`. -/
def allocInflateState : M InflateStatePtr := fun h =>
  if h.allocOk h.nalloc then
    if h.slotUsed h.nextBlk then .error (.ub "allocation: the block number is in use (the heap is not Fresh)")
    else .ok (some (.tab h.nextBlk), { h with istates := upd h.istates h.nextBlk (some (InflateState.garbage (h.garbage h.nalloc))), nextBlk := h.nextBlk + 1, nalloc := h.nalloc + 1 })
  else .ok (none, { h with nalloc := h.nalloc + 1 })

/-- Alias of `allocInflateState`. -/
abbrev allocInflateStateChk := allocInflateState

theorem allocInflateState_some {h : Heap} (hok : h.allocOk h.nalloc = true)
    (hs : h.slotUsed h.nextBlk = false := by fresh_slot) :
    allocInflateState h = .ok (some (.tab h.nextBlk), { h with istates := upd h.istates h.nextBlk (some (InflateState.garbage (h.garbage h.nalloc))), nextBlk := h.nextBlk + 1, nalloc := h.nalloc + 1 }) := by simp [allocInflateState, hok, hs]

theorem allocInflateState_none {h : Heap} (hok : ¬ h.allocOk h.nalloc = true) :
    allocInflateState h = .ok (none, { h with nalloc := h.nalloc + 1 }) := by simp [allocInflateState, hok]

/-- `free(p)` for a `inflate_state *`: a no-op for null; faults for a block that is not live (double free) and for a
pointer that was not returned by the allocator. -/
def freeInflateState (p : InflateStatePtr) : M Unit := fun h =>
  match p with
  | none => .ok ((), h)
  | some (.tab i) => match h.istates i with
    | some _ => .ok ((), { h with istates := upd h.istates i none })
    | none => .error (.ub "free of a freed or invalid pointer (inflate_state)")

theorem freeInflateState_null {h : Heap} : freeInflateState none h = .ok ((), h) := rfl

/-- `*dst = *src` for two `inflate_state *` (`zmemcpy(dst, src, sizeof *dst)`): a whole-record copy. Faults if either pointer
is null, dangling or the destination read-only, and if both denote the same object (`memcpy` with overlapping
ranges is undefined; the `inflate_state` objects of the heap do not contain one another). -/
def copyInflateState (dst src : InflateStatePtr) : M Unit := fun h =>
  match dst, src with
  | some d, some s =>
    if d = s then .error (.ub "memcpy of a inflate_state onto itself (overlapping ranges)")
    else (ldInflateState (some s) >>= fun v => stInflateState (some d) v) h
  | _, _ => .error (.ub "null dereference (inflate_state)")

theorem freeInflateState_tab {h : Heap} {i : Nat} {v : InflateState} (e : h.istates i = some v) :
    freeInflateState (some (.tab i)) h = .ok ((), { h with istates := upd h.istates i none }) := by simp [freeInflateState, e]

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

/-- `malloc(sizeof(gz_state))` through the default allocator: a fresh live record with arbitrary integers and
null pointers (a documented gap: C leaves them indeterminate, see `docs/trusted-base.md`), or null when the
failure oracle says so. It is a fault (not a C behaviour) if the block number `nextBlk` is already in use:
the heap is then not `Fresh`, and a theorem about allocation carries `Fresh`. -/
def allocGzState : M GzStatePtr := fun h =>
  if h.allocOk h.nalloc then
    if h.slotUsed h.nextBlk then .error (.ub "allocation: the block number is in use (the heap is not Fresh)")
    else .ok (some (.tab h.nextBlk), { h with gzstates := upd h.gzstates h.nextBlk (some (GzState.garbage (h.garbage h.nalloc))), nextBlk := h.nextBlk + 1, nalloc := h.nalloc + 1 })
  else .ok (none, { h with nalloc := h.nalloc + 1 })

/-- Alias of `allocGzState`. -/
abbrev allocGzStateChk := allocGzState

theorem allocGzState_some {h : Heap} (hok : h.allocOk h.nalloc = true)
    (hs : h.slotUsed h.nextBlk = false := by fresh_slot) :
    allocGzState h = .ok (some (.tab h.nextBlk), { h with gzstates := upd h.gzstates h.nextBlk (some (GzState.garbage (h.garbage h.nalloc))), nextBlk := h.nextBlk + 1, nalloc := h.nalloc + 1 }) := by simp [allocGzState, hok, hs]

theorem allocGzState_none {h : Heap} (hok : ¬ h.allocOk h.nalloc = true) :
    allocGzState h = .ok (none, { h with nalloc := h.nalloc + 1 }) := by simp [allocGzState, hok]

/-- `free(p)` for a `gz_state *`: a no-op for null; faults for a block that is not live (double free) and for a
pointer that was not returned by the allocator. -/
def freeGzState (p : GzStatePtr) : M Unit := fun h =>
  match p with
  | none => .ok ((), h)
  | some (.tab i) => match h.gzstates i with
    | some _ => .ok ((), { h with gzstates := upd h.gzstates i none })
    | none => .error (.ub "free of a freed or invalid pointer (gz_state)")

theorem freeGzState_null {h : Heap} : freeGzState none h = .ok ((), h) := rfl

/-- `*dst = *src` for two `gz_state *` (`zmemcpy(dst, src, sizeof *dst)`): a whole-record copy. Faults if either pointer
is null, dangling or the destination read-only, and if both denote the same object (`memcpy` with overlapping
ranges is undefined; the `gz_state` objects of the heap do not contain one another). -/
def copyGzState (dst src : GzStatePtr) : M Unit := fun h =>
  match dst, src with
  | some d, some s =>
    if d = s then .error (.ub "memcpy of a gz_state onto itself (overlapping ranges)")
    else (ldGzState (some s) >>= fun v => stGzState (some d) v) h
  | _, _ => .error (.ub "null dereference (gz_state)")

theorem freeGzState_tab {h : Heap} {i : Nat} {v : GzState} (e : h.gzstates i = some v) :
    freeGzState (some (.tab i)) h = .ok ((), { h with gzstates := upd h.gzstates i none }) := by simp [freeGzState, e]

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
