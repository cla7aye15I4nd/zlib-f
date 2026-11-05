import ZlibF.Runtime.Tables

/-!
# `malloc`, `free` and `memcpy` of every struct kind (GENERATED, do not edit)

`allocK` and `freeK` are `malloc(sizeof(K))` and `free` through the default allocator, `copyK dst src` is the
`memcpy` of a whole record. They model the C library (see `Libc.lean` and `docs/trusted-base.md`); the loads and
stores of the records are in `Tables.lean`.
-/

namespace C

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

end C
