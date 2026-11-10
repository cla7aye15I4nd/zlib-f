import ZlibF.Proof.«uncompr.c.loop-safe»
import ZlibF.Proof.«uncompr.c.loop-resources»
import ZlibF.Proof.«uncompr.c.cells»
import ZlibF.Proof.«inflate.c.default-byte-view»
import ZlibF.Proof.«public-inflate-end»

/-!
# The actual uncompress wrapper entry and continuations

The full source equation preserves the original order: init, core loop, input
length writeback, output length writeback, inflateEnd, reserved cleanup, stream
cleanup. Successful actual initialization establishes the default decoder relation
on the same exact heap. These are internal support results with explicit Uniq and
ByteObjectsFit premises. The unchanged public utility goal has a broader heap
premise; this module does not claim that goal or silently narrow it.
-/

set_option maxRecDepth 8192

namespace Zlib.Uncompr.Proof.Wrapper
open C Zlib.Gzguts ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs
open Zlib.Uncompr.Proof.Loop Zlib.Uncompr.Proof.Buffers
open Zlib.Uncompr.Proof.PostRanges Zlib.Uncompr.Proof.Resources Zlib.Uncompr.Proof.Cells
open Zlib.Inflate (inflateInit_ inflateEnd)

def freeLocals (stream : ZStreamPtr) (reserved : BPtr) : M Unit := do
  freeB reserved
  freeZStream stream

def finish (stream : ZStreamPtr) (reserved destLen sourceLen : BPtr) (l : UncLoop) : M Int32 := do
  -- len += stream.avail_in; left += stream.avail_out; *sourceLen -= len; *destLen -= left;
  let z ← ldZ stream
  let len := l.len + z.avail_in.toUInt64
  let left := l.left + z.avail_out.toUInt64
  store64 sourceLen ((← load64 sourceLen) - len)
  store64 destLen ((← load64 destLen) - left)
  -- inflateEnd(&stream);
  let _ ← inflateEnd stream
  -- return err == Z_STREAM_END ? Z_OK : err == Z_NEED_DICT ? Z_DATA_ERROR : err == Z_BUF_ERROR && len == 0 ? Z_DATA_ERROR : err;
  let err := l.err
  let r : Int32 :=
    if err == Z_STREAM_END then Z_OK
    else if err == Z_NEED_DICT then Z_DATA_ERROR
    else if err == Z_BUF_ERROR && len == 0 then Z_DATA_ERROR
    else err
  freeLocals stream reserved
  return r


def entered (stream : ZStreamPtr) (reserved dest destLen source sourceLen : BPtr)
    (len left : UInt64) : M Int32 := do
  -- if (left == 0 && dest == Z_NULL) dest = (Bytef *)&stream.reserved;
  let dest := if left == 0 && dest == .null then reserved else dest
  -- stream.next_in = (z_const Bytef *)source; stream.avail_in = 0; zalloc, zfree, opaque = 0;
  updZ stream fun z => { z with next_in := source, avail_in := 0, zalloc := .null, zfree := .null, «opaque» := .null }
  -- err = inflateInit(&stream); if (err != Z_OK) return err;
  let ver ← Zlib.GzFs.strLit ZLIB_VERSION
  let err ← inflateInit_ stream ver 112
  if err != Z_OK then
    freeLocals stream reserved
    return err
  -- stream.next_out = dest; stream.avail_out = 0;
  updZ stream fun z => { z with next_out := dest, avail_out := 0 }
  -- do { ... } while (err == Z_OK);
  let l ← cdoWhile (loopBody stream) loopCondition { err, len, left }
  finish stream reserved destLen sourceLen l

def decomposed (dest : BPtr) (destLen : BPtr) (source : BPtr) (sourceLen : BPtr) : M Int32 := do
  -- z_stream stream; int err; const uInt max = (uInt)-1; z_size_t len, left;
  let stream ← allocLocalZ
  let reserved ← allocLocal 8
  -- if (sourceLen == Z_NULL || (*sourceLen > 0 && source == Z_NULL) || destLen == Z_NULL || (*destLen > 0 && dest == Z_NULL))
  --   return Z_STREAM_ERROR;
  let mut bad := false
  if sourceLen == .null then bad := true
  else if (← load64 sourceLen) > 0 && source == .null then bad := true
  else if destLen == .null then bad := true
  else if (← load64 destLen) > 0 && dest == .null then bad := true
  if bad then
    freeLocals stream reserved
    return Z_STREAM_ERROR
  -- len = *sourceLen; left = *destLen;
  let len ← load64 sourceLen
  let left ← load64 destLen
  entered stream reserved dest destLen source sourceLen len left

/-- The complete source uses exactly these init, core, scalar-store, end and local
cleanup continuations, in their original order. -/
theorem uncompress2_z_wrapper_source : uncompress2_z = decomposed := by
  unfold uncompress2_z decomposed entered finish freeLocals loopBody loopCondition
  with_reducible rfl

def junkBytes (h : Heap) : Array UInt8 :=
  Array.ofFn (n := 8) fun i => Junk.of (h.garbage h.nalloc i.val)

def streamHeap (h : Heap) : Heap :=
  { h with
    streams := upd h.streams h.nextBlk (some (ZStream.garbage (h.garbage h.nalloc)))
    nextBlk := h.nextBlk + 1 }

def localHeap (h : Heap) : Heap :=
  { h with
    bytes := upd h.bytes (h.nextBlk + 1) (some (junkBytes h))
    streams := upd h.streams h.nextBlk (some (ZStream.garbage (h.garbage h.nalloc)))
    ro := upd h.ro (h.nextBlk + 1) false
    nextBlk := h.nextBlk + 2 }

def preparedStream (h : Heap) (source : BPtr) : ZStream :=
  { ZStream.garbage (h.garbage h.nalloc) with
    next_in := source, avail_in := 0, zalloc := .null, zfree := .null, «opaque» := .null }

def preparedHeap (h : Heap) (source : BPtr) : Heap :=
  { localHeap h with streams := upd h.streams h.nextBlk (some (preparedStream h source)) }

theorem allocLocalZ_run (h : Heap) (fresh : Fresh h) :
    allocLocalZ h = .ok (some (.tab h.nextBlk), streamHeap h) := by
  have slot : ({ h with allocOk := fun _ => true } : Heap).slotUsed h.nextBlk = false := fresh.slotUsed_next
  simp [allocLocalZ, allocZStream, slot, streamHeap]

theorem allocReserved_run (h : Heap) (fresh : Fresh h) :
    allocLocal 8 (streamHeap h) = .ok (.ref (.blk (h.nextBlk + 1)) 0, localHeap h) := by
  have slot : (streamHeap h).slotUsed (h.nextBlk + 1) = false := by
    have old := Heap.slotUsed_eq_false.mpr (fresh (h.nextBlk + 1) (by omega))
    simpa [streamHeap, Heap.slotUsed, upd_apply] using old
  simp only [streamHeap] at slot
  simp [allocLocal, allocBytes, streamHeap, slot, localHeap, junkBytes, Nat.add_assoc]

theorem prepare_run (h : Heap) (source : BPtr) :
    updZ (some (.tab h.nextBlk))
      (fun z => { z with next_in := source, avail_in := 0, zalloc := .null, zfree := .null, «opaque» := .null })
      (localHeap h) = .ok ((), preparedHeap h source) := by
  simp [updZ, ldZStream, stZStream, ZStreamRef.get, ZStreamRef.put,
    ZStreamRef.isRo, localHeap, preparedHeap, preparedStream, upd_upd]

theorem prepared_fresh (h : Heap) (fresh : Fresh h) (source : BPtr) : Fresh (preparedHeap h source) := by
  apply fresh.mono (by simp [preparedHeap, localHeap])
  intro x hx
  have notStream : x ≠ h.nextBlk := by simp only [preparedHeap, localHeap] at hx; omega
  have notBytes : x ≠ h.nextBlk + 1 := by simp only [preparedHeap, localHeap] at hx; omega
  simp [preparedHeap, localHeap, notStream, notBytes]

theorem prepared_uniq (h : Heap) (fresh : Fresh h) (uniq : Uniq h) (source : BPtr) :
    Uniq (preparedHeap h source) := by
  intro x
  by_cases stream : x = h.nextBlk
  · subst x
    have dead := Heap.not_live.mp (fresh h.nextBlk (by omega))
    simp [cnt, preparedHeap, localHeap, dead.1, dead.2.1,
      dead.2.2.2.1, dead.2.2.2.2.1, dead.2.2.2.2.2.1, dead.2.2.2.2.2.2]
  · by_cases bytes : x = h.nextBlk + 1
    · subst x
      have dead := Heap.not_live.mp (fresh (h.nextBlk + 1) (by omega))
      simp [cnt, preparedHeap, localHeap, dead.2.1, dead.2.2.1,
        dead.2.2.2.1, dead.2.2.2.2.1, dead.2.2.2.2.2.1, dead.2.2.2.2.2.2]
    · simpa [preparedHeap, localHeap, stream, bytes] using uniq x

theorem prepared_platform (h : Heap) (fit : ZlibF.PlatformMemory.ByteObjectsFit h) (source : BPtr) :
    ZlibF.PlatformMemory.ByteObjectsFit (preparedHeap h source) := by
  have bounded : (junkBytes h).size < ZlibF.PlatformMemory.byteObjectLimit := by
    simp only [junkBytes, Array.size_ofFn, ZlibF.PlatformMemory.byteObjectLimit]
    decide
  exact (fit.with_bytes (block := h.nextBlk + 1) bounded).of_storage_eq rfl rfl rfl

private theorem versionIndex : strIndex ZLIB_VERSION = some 57 := by decide +kernel

theorem version_run (h : Heap) : Zlib.GzFs.strLit ZLIB_VERSION h = .ok (.ref (.str 57) 0, h) := by
  simp [Zlib.GzFs.strLit, strLitRef, versionIndex]

theorem version_value (h : Heap) : VersionValue h (.ref (.str 57) 0) (some 49) := by
  refine Or.inr ⟨49, rfl, Or.inr ⟨.str 57, 0, strBytes ZLIB_VERSION, rfl, ?_, ?_, ?_⟩⟩
  · rw [BRef.get_str]
    rfl
  · decide
  · decide

theorem prepared_domain (h : Heap) (fresh : Fresh h) (uniq : Uniq h)
    (globals : LibraryGlobals h) (source : BPtr) :
    InitDomain (preparedHeap h source) (.tab h.nextBlk) (.ref (.str 57) 0) := by
  exact ⟨prepared_fresh h fresh source, prepared_uniq h fresh uniq source,
    globals, version_value _, preparedStream h source,
    by simp [preparedHeap, ZStreamRef.get], ⟨Or.inl rfl, Or.inl rfl⟩, rfl⟩

def initializedStream (h : Heap) (source : BPtr) : ZStream :=
  resetKeepStream (initStream2 (preparedStream h source) (h.nextBlk + 2))
    (resetPre (reset2Pre 5 15 (initState (.tab h.nextBlk))))

def initializedState (h : Heap) : InflateState :=
  resetKeepState (h.nextBlk + 2) (resetPre (reset2Pre 5 15 (initState (.tab h.nextBlk))))

def initHeap (h : Heap) (source : BPtr) : Heap :=
  initOkHeap (preparedHeap h source) (.tab h.nextBlk) (preparedStream h source) 5 15

theorem initHeap_eq (h : Heap) (source : BPtr) :
    initHeap h source =
      { h with
        bytes := upd h.bytes (h.nextBlk + 1) (some (junkBytes h))
        streams := upd h.streams h.nextBlk (some (initializedStream h source))
        istates := upd h.istates (h.nextBlk + 2) (some (initializedState h))
        ro := upd h.ro (h.nextBlk + 1) false
        nextBlk := h.nextBlk + 3
        nalloc := h.nalloc + 1 } := by
  unfold initHeap initOkHeap
  dsimp only
  rw [reset2Heap_null _ _ _ rfl]
  simp [preparedHeap, localHeap, allocIstHeap, ZStreamRef.put, setI,
    initializedStream, initializedState, upd_upd, Nat.add_assoc]

theorem initHeap_stream (h : Heap) (source : BPtr) :
    ZStreamRef.get (initHeap h source) (.tab h.nextBlk) = some (initializedStream h source) := by
  simp [initHeap_eq, ZStreamRef.get]

theorem initHeap_state (h : Heap) (source : BPtr) :
    (initHeap h source).istates (h.nextBlk + 2) = some (initializedState h) := by
  simp [initHeap_eq]

/-- Successful real initialization, under an explicit internal Uniq/platform domain.
No caller supplies the initialized decoder relation. -/
theorem initialized_boundary (h : Heap) (source : BPtr)
    (fresh : Fresh h) (uniq : Uniq h) (globals : LibraryGlobals h)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit h) (allocation : h.allocOk h.nalloc = true) :
    C.run (inflateInit_ (some (.tab h.nextBlk)) (.ref (.str 57) 0) 112) (preparedHeap h source) =
      .ok (Z_OK, initHeap h source) ∧
    DefaultStateJ (initHeap h source) (.tab h.nextBlk) (h.nextBlk + 2)
      (initializedStream h source) (initializedState h) ∧
    DefAlloc (initializedStream h source) := by
  have domain := prepared_domain h fresh uniq globals source
  have fit := prepared_platform h platform source
  have alloc : (preparedHeap h source).allocOk (preparedHeap h source).nalloc = true := allocation
  have get : ZStreamRef.get (preparedHeap h source) (.tab h.nextBlk) = some (preparedStream h source) := by
    simp [preparedHeap, ZStreamRef.get]
  have byte : OkOn (preparedHeap h source) (index8 (.ref (.str 57) 0) 0) 49 := by
    have hg : Space.get (preparedHeap h source) (.str 57 : BRef) = some (strBytes ZLIB_VERSION) := by
      rw [BRef.get_str]
      rfl
    exact Ptr.index_ok hg (by decide)
  have actual : C.run (inflateInit_ (some (.tab h.nextBlk)) (.ref (.str 57) 0) 112) (preparedHeap h source) =
      .ok (Z_OK, initHeap h source) := by
    exact inflateInit2_success get (prepared_fresh h fresh source) alloc
      (Or.inl rfl) (Or.inl rfl) (by simp) byte params15
  obtain ⟨after, stream, state, run, _initial, current, _reachable⟩ :=
    inflate_default_state_initial (preparedHeap h source) (.tab h.nextBlk) (.ref (.str 57) 0) domain fit alloc
  have heaps : after = initHeap h source := congrArg Prod.snd (Except.ok.inj (run.symm.trans actual))
  subst after
  have streams : stream = initializedStream h source :=
    Option.some.inj (current.good.live.hz.symm.trans (initHeap_stream h source))
  have states : state = initializedState h :=
    Option.some.inj (current.good.live.hs.symm.trans (initHeap_state h source))
  subst stream state
  exact ⟨actual, current, ⟨rfl, rfl⟩⟩

def outputStream (z : ZStream) (dest : BPtr) : ZStream := { z with next_out := dest, avail_out := 0 }
def outputHeap (h : Heap) (b : Nat) (z : ZStream) (dest : BPtr) : Heap :=
  { h with streams := upd h.streams b (some (outputStream z dest)) }

theorem output_default_state (h : Heap) (b zs : Nat) (z : ZStream) (state : InflateState) (dest : BPtr)
    (invariant : DefaultStateJ h (.tab b) zs z state) :
    DefaultStateJ (outputHeap h b z dest) (.tab b) zs (outputStream z dest) state := by
  have get : h.streams b = some z := invariant.good.live.hz
  have shape := shape_put invariant.good.live.hz (outputStream z dest)
  have put : ZStreamRef.put h (.tab b) (outputStream z dest) = outputHeap h b z dest := by
    simp [ZStreamRef.put, get, outputHeap]
  rw [put] at shape
  have win : WinInv (outputHeap h b z dest) state := by
    refine { invariant.good.inv.win with block := ?_ }
    simpa only [outputHeap] using invariant.good.inv.win.block
  have inv : StInv (outputHeap h b z dest) zs state := { invariant.good.inv with win := win }
  have good : Good (outputHeap h b z dest) (.tab b) zs (outputStream z dest) state := by
    refine ⟨?_, inv, shape.uniq invariant.good.uniq, shape.fresh rfl invariant.good.fresh⟩
    exact ⟨by simp [outputHeap, ZStreamRef.get], invariant.good.live.hs,
      invariant.good.live.zst, invariant.good.live.back, invariant.good.live.mode,
      invariant.good.live.zalloc, invariant.good.live.zfree⟩
  have tables : DataTableInvariant (outputHeap h b z dest) state := by
    intro mode
    exact dataTablesSafe_of_state_static (before := h) (after := outputHeap h b z dest)
      invariant.good.inv.ptr rfl rfl (invariant.tables mode)
  have platform : ZlibF.PlatformMemory.ByteObjectsFit (outputHeap h b z dest) := by
    intro ref a read
    apply invariant.platform ref a
    cases ref <;> simpa only [Space.get, outputHeap, staticStringBytes] using read
  exact ⟨⟨good, tables, invariant.pending, invariant.lengths, invariant.headerLengths,
    invariant.held, invariant.window, invariant.wrapper, invariant.header,
    invariant.modes, invariant.trailer, invariant.globals, platform⟩,
    invariant.requestedBits, invariant.requestedWrap, invariant.phase⟩

def normalizedDest (h : Heap) (dest : BPtr) (capacity : UInt64) : BPtr :=
  if capacity == 0 && dest == .null then .ref (.blk (h.nextBlk + 1)) 0 else dest

def coreStream (h : Heap) (source dest : BPtr) (capacity : UInt64) : ZStream :=
  outputStream (initializedStream h source) (normalizedDest h dest capacity)

def coreHeap (h : Heap) (source dest : BPtr) (capacity : UInt64) : Heap :=
  outputHeap (initHeap h source) h.nextBlk (initializedStream h source) (normalizedDest h dest capacity)

theorem coreHeap_eq (h : Heap) (source dest : BPtr) (capacity : UInt64) :
    coreHeap h source dest capacity =
      { h with
        bytes := upd h.bytes (h.nextBlk + 1) (some (junkBytes h))
        streams := upd h.streams h.nextBlk (some (coreStream h source dest capacity))
        istates := upd h.istates (h.nextBlk + 2) (some (initializedState h))
        ro := upd h.ro (h.nextBlk + 1) false
        nextBlk := h.nextBlk + 3
        nalloc := h.nalloc + 1 } := by
  simp [coreHeap, outputHeap, initHeap_eq, coreStream, upd_upd]

theorem core_boundary (h : Heap) (source dest : BPtr) (capacity : UInt64)
    (fresh : Fresh h) (uniq : Uniq h) (globals : LibraryGlobals h)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit h) (allocation : h.allocOk h.nalloc = true) :
    DefaultStateJ (coreHeap h source dest capacity) (.tab h.nextBlk) (h.nextBlk + 2)
      (coreStream h source dest capacity) (initializedState h) ∧
    DefAlloc (coreStream h source dest capacity) := by
  have initialized := initialized_boundary h source fresh uniq globals platform allocation
  exact ⟨output_default_state _ _ _ _ _ _ initialized.2.1, initialized.2.2⟩

theorem normalizedDest_nonnull (h : Heap) (dest : BPtr) (capacity : UInt64)
    (valid : dest = .null → capacity = 0) : normalizedDest h dest capacity ≠ .null := by
  by_cases null : dest = .null
  · simp [normalizedDest, null, valid null]
  · simp [normalizedDest, null]

private theorem original_get (h after : Heap) (fresh : Fresh h)
    (bytes : after.bytes = upd h.bytes (h.nextBlk + 1) (some (junkBytes h)))
    (dstates : after.dstates = h.dstates) (statics : after.static = h.static)
    (borrow : after.libcErrorBorrow = h.libcErrorBorrow)
    (ref : BRef) (a : Array UInt8) (get : Space.get h ref = some a) : Space.get after ref = some a := by
  cases ref with
  | blk b =>
    have oldGet : h.bytes b = some a := get
    have below : b < h.nextBlk := fresh.lt (Or.inl (by simp [oldGet]))
    change after.bytes b = some a
    rw [bytes, upd_ne _ _ _ _ (by omega), oldGet]
  | dstate_depth b => simpa only [Space.get, dstates] using get
  | str i => exact (C.LibcBorrow.str_view_stable (Or.inr borrow)).trans get
  | st_dist_code => simpa only [Space.get, statics] using get
  | st_length_code => simpa only [Space.get, statics] using get

private theorem original_ro (h after : Heap) (fresh : Fresh h)
    (readonly : after.ro = upd h.ro (h.nextBlk + 1) false)
    (ref : BRef) (a : Array UInt8) (get : Space.get h ref = some a) : Space.ro after ref = Space.ro h ref := by
  cases ref with
  | blk b =>
    have oldGet : h.bytes b = some a := get
    have below : b < h.nextBlk := fresh.lt (Or.inl (by simp [oldGet]))
    change after.ro b = h.ro b
    rw [readonly, upd_ne _ _ _ _ (by omega)]
  | dstate_depth b => rfl
  | str i => rfl
  | st_dist_code => rfl
  | st_length_code => rfl

private theorem cell_from_views (h after : Heap) (p : BPtr) (v : UInt64)
    (views : ∀ (ref : BRef) (a : Array UInt8), Space.get h ref = some a → Space.get after ref = some a)
    (readonly : ∀ (ref : BRef) (a : Array UInt8), Space.get h ref = some a → Space.ro after ref = Space.ro h ref)
    (cell : LengthCell h p v) : LengthCell after p v := by
  rcases cell with ⟨readable, writable⟩
  constructor
  · rcases readable with null | ⟨r, off, a, ptr, get, fit, content⟩
    · exact Or.inl null
    · exact Or.inr ⟨r, off, a, ptr, views r a get, fit, content⟩
  · rcases writable with null | ⟨r, off, a, ptr, get, ro, fit⟩
    · exact Or.inl null
    · exact Or.inr ⟨r, off, a, ptr, views r a get, (readonly r a get).trans ro, fit⟩

theorem local_cell (h : Heap) (fresh : Fresh h) (p : BPtr) (v : UInt64) (cell : LengthCell h p v) :
    LengthCell (localHeap h) p v :=
  cell_from_views h (localHeap h) p v (original_get h _ fresh rfl rfl rfl rfl)
    (original_ro h _ fresh rfl) cell

theorem core_cell (h : Heap) (fresh : Fresh h) (source dest p : BPtr) (capacity v : UInt64)
    (cell : LengthCell h p v) : LengthCell (coreHeap h source dest capacity) p v := by
  apply cell_from_views h _ p v ?_ ?_ cell
  · exact original_get h _ fresh (by simp [coreHeap_eq]) (by simp [coreHeap_eq]) (by simp [coreHeap_eq])
      (by simp [coreHeap_eq])
  · exact original_ro h _ fresh (by simp [coreHeap_eq])

theorem cell_nonnull (h : Heap) (p : BPtr) (v : UInt64) (cell : LengthCell h p v) : p ≠ .null := by
  intro null
  subst p
  rcases cell.1 with bad | ⟨ref, off, array, ptr, _⟩
  · simp at bad
  · cases ptr

theorem output_run (h : Heap) (b : Nat) (z : ZStream) (dest : BPtr) (get : h.streams b = some z) :
    updZ (some (.tab b)) (fun z => { z with next_out := dest, avail_out := 0 }) h =
      .ok ((), outputHeap h b z dest) := by
  simp [updZ, ldZStream, stZStream, ZStreamRef.get, ZStreamRef.put,
    ZStreamRef.isRo, get, outputHeap, outputStream]

/-- The real valid-entry wrapper reaches the exact initialized core heap.
The equation retains the original order of both scalar stores and all cleanup. -/
theorem uncompress2_z_to_core (h : Heap) (source dest sourceLen destLen : BPtr) (n capacity : UInt64)
    (fresh : Fresh h) (uniq : Uniq h) (globals : LibraryGlobals h)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit h) (allocation : h.allocOk h.nalloc = true)
    (inputCell : LengthCell h sourceLen n) (outputCell : LengthCell h destLen capacity)
    (validInput : source = .null → n = 0) (validOutput : dest = .null → capacity = 0) :
    C.run (uncompress2_z dest destLen source sourceLen) h =
      (do
        let last ← cdoWhile (loopBody (some (.tab h.nextBlk))) loopCondition
          { err := Z_OK, len := n, left := capacity }
        finish (some (.tab h.nextBlk)) (.ref (.blk (h.nextBlk + 1)) 0) destLen sourceLen last)
        (coreHeap h source dest capacity) := by
  have srcNotNull := cell_nonnull h sourceLen n inputCell
  have dstNotNull := cell_nonnull h destLen capacity outputCell
  have input := load64_lengthCell (localHeap h) sourceLen n (local_cell h fresh sourceLen n inputCell)
  have output := load64_lengthCell (localHeap h) destLen capacity (local_cell h fresh destLen capacity outputCell)
  simp only [C.run] at input output
  have initialized := (initialized_boundary h source fresh uniq globals platform allocation).1
  simp only [C.run] at initialized
  have outGet : (initHeap h source).streams h.nextBlk = some (initializedStream h source) :=
    initHeap_stream h source
  have outputSet := output_run (initHeap h source) h.nextBlk (initializedStream h source)
    (normalizedDest h dest capacity) outGet
  have sourceValid : ¬ (0 < n ∧ source = .null) := by
    rintro ⟨positive, null⟩
    simp [validInput null] at positive
  have destValid : ¬ (0 < capacity ∧ dest = .null) := by
    rintro ⟨positive, null⟩
    simp [validOutput null] at positive
  simp only [normalizedDest, Bool.and_eq_true, beq_iff_eq] at outputSet
  rw [uncompress2_z_wrapper_source]
  simp [C.run, decomposed, entered, allocLocalZ_run h fresh, allocReserved_run h fresh,
    srcNotNull, dstNotNull, input, output, sourceValid, destValid, prepare_run,
    version_run, initialized, normalizedDest, outputSet, coreHeap]

#print axioms initialized_boundary
#print axioms core_boundary
#print axioms core_cell
#print axioms uncompress2_z_to_core

end Zlib.Uncompr.Proof.Wrapper
