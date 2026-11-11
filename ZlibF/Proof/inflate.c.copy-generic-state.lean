import ZlibF.Proof.«inflate.c.copy-relocation»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The record installed by a successful copy after the C pointer repairs.
The offsets are obtained from the source `Good` pointer invariant; they are
not additional restrictions on the public caller. -/
def copiedGeneric (dest : ZStreamRef) (old fresh nextOff distOff : Nat)
    (window : BPtr) (s : InflateState) : InflateState :=
  { s with
    strm := some dest,
    lencode := if s.lencode = .ref (.istate_codes old) 0 then
      .ref (.istate_codes fresh) 0 else s.lencode,
    distcode := if s.lencode = .ref (.istate_codes old) 0 then
      .ref (.istate_codes fresh) distOff else s.distcode,
    next := .ref (.istate_codes fresh) nextOff,
    window := window }

theorem copy_codes_off_diff
    {h : Heap} {i off : Nat} {s : InflateState}
    (get : h.istates i = some s) (size : s.codes.size = 1444)
    (bound : off ≤ 1444) :
    (Ptr.diff (.ref (CodeRef.istate_codes i) off)
      (.ref (CodeRef.istate_codes i) 0)) h =
      .ok (Int64.ofInt (off : Int), h) := by
  have table : Space.get h (CodeRef.istate_codes i) = some s.codes :=
    CodeRef.get_istate_codes get
  have run := Ptr.diff_ok (r := CodeRef.istate_codes i)
    (a := s.codes) (o1 := off) (o2 := 0) table
    (by omega) (by omega)
    (by omega : -(2 ^ 63 : Int) ≤ (off : Int) - 0 ∧
      (off : Int) - 0 < 2 ^ 63)
  simpa [C.run, OkOn, size] using run

theorem copy_codes_off_add
    {h : Heap} {i off : Nat} {s : InflateState}
    (get : h.istates i = some s) (size : s.codes.size = 1444)
    (bound : off ≤ 1444) :
    (Ptr.add (.ref (CodeRef.istate_codes i) 0) (off : Int)) h =
      .ok (.ref (CodeRef.istate_codes i) off, h) := by
  have table : Space.get h (CodeRef.istate_codes i) = some s.codes :=
    CodeRef.get_istate_codes get
  have run := Ptr.add_nat_ok (r := CodeRef.istate_codes i)
    (a := s.codes) (off := 0) (n := off) table (by omega)
  simpa [C.run, OkOn, size] using run

/-- Both source table origins are repaired into a valid destination pointer
shape. The dynamic distance offset may be nonzero, and `next` may be one past
the array. -/
theorem copiedGeneric_ptr
    {old fresh nextOff distOff : Nat} {dest : ZStreamRef}
    {window : BPtr} {s : InflateState}
    (origin : CopyTableOrigin old s)
    (nextBound : nextOff ≤ 1444)
    (distBound : distOff ≤ 1443) :
    PtrInv fresh (copiedGeneric dest old fresh nextOff distOff window s) := by
  refine ⟨⟨nextOff, rfl, nextBound⟩, ?_⟩
  rcases origin with dynamic | fixed
  · left
    refine ⟨0, distOff, ?_, ?_, by decide, distBound⟩
    · simp [copiedGeneric, dynamic]
    · simp [copiedGeneric, dynamic]
  · right
    constructor
    · simp [copiedGeneric, fixed.1]
    · simp [copiedGeneric, fixed.1, fixed.2]

/-- CODELENS retains the actual source code array, but its pointer is
rebound to the copied state record. -/
theorem copiedGeneric_code_lengths
    {old fresh nextOff distOff : Nat} {dest : ZStreamRef}
    {window : BPtr} {s : InflateState}
    (lengths : CodeLengthInvariant old s) :
    CodeLengthInvariant fresh
      (copiedGeneric dest old fresh nextOff distOff window s) := by
  intro active
  have sourceActive : s.mode = CODELENS := by
    simpa [copiedGeneric] using active
  obtain ⟨dynamic, safe, nlen, ndist, haveBound, lens⟩ := lengths sourceActive
  simp only [CodeLengthInvariant] at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [copiedGeneric, dynamic]
  · simpa [copiedGeneric] using safe
  · simpa [copiedGeneric] using nlen
  · simpa [copiedGeneric] using ndist
  · simpa [copiedGeneric] using haveBound
  · simpa [copiedGeneric] using lens

/-- The guarded decoder tables survive copying because the fresh dynamic
array contains the same code entries and fixed tables remain static. -/
theorem copiedGeneric_data_tables
    {h after : Heap} {old fresh nextOff distOff : Nat}
    {dest : ZStreamRef} {window : BPtr} {s : InflateState}
    (tables : DataTableInvariant h s)
    (origin : CopyTableOrigin old s)
    (dynamicDist : s.lencode = .ref (.istate_codes old) 0 →
      s.distcode = .ref (.istate_codes old) distOff)
    (sourceCodes : Space.get h (CodeRef.istate_codes old) = some s.codes)
    (freshCodes : Space.get after (CodeRef.istate_codes fresh) = some s.codes)
    (fixedLen : Space.get after CodeRef.st_lenfix = Space.get h CodeRef.st_lenfix)
    (fixedDist : Space.get after CodeRef.st_distfix = Space.get h CodeRef.st_distfix) :
    DataTableInvariant after
      (copiedGeneric dest old fresh nextOff distOff window s) := by
  intro active
  have sourceActive : DataTableMode s.mode := by
    simpa [copiedGeneric] using active
  obtain ⟨⟨lenRef, lenOff, lenArray, lenPtr, lenGet, lenSafe⟩,
    ⟨distRef, distOffset, distArray, distPtr, distGet, distSafe⟩⟩ :=
    tables sourceActive
  rcases origin with dynamic | fixed
  · have lenPair := Ptr.ref.inj (lenPtr.symm.trans dynamic)
    have lenArrayEq : lenArray = s.codes := by
      rcases lenPair with ⟨refEq, offEq⟩
      subst lenRef
      subst lenOff
      exact Option.some.inj (lenGet.symm.trans sourceCodes)
    have sourceDist := dynamicDist dynamic
    have distPair := Ptr.ref.inj (distPtr.symm.trans sourceDist)
    have distArrayEq : distArray = s.codes := by
      rcases distPair with ⟨refEq, offEq⟩
      subst distRef
      subst distOffset
      exact Option.some.inj (distGet.symm.trans sourceCodes)
    refine ⟨⟨.istate_codes fresh, 0, s.codes, ?_, freshCodes, ?_⟩,
      ⟨.istate_codes fresh, distOff, s.codes, ?_, freshCodes, ?_⟩⟩
    · simp [copiedGeneric, dynamic]
    · rcases lenPair with ⟨refEq, offEq⟩
      subst lenRef
      subst lenOff
      simpa [copiedGeneric, lenArrayEq] using lenSafe
    · simp [copiedGeneric, dynamic]
    · rcases distPair with ⟨refEq, offEq⟩
      subst distRef
      subst distOffset
      simpa [copiedGeneric, distArrayEq] using distSafe
  · have lenPair := Ptr.ref.inj (lenPtr.symm.trans fixed.1)
    have distPair := Ptr.ref.inj (distPtr.symm.trans fixed.2)
    refine ⟨⟨.st_lenfix, 0, lenArray, ?_, ?_, ?_⟩,
      ⟨.st_distfix, 0, distArray, ?_, ?_, ?_⟩⟩
    · simp [copiedGeneric, fixed.1]
    · rw [fixedLen]
      rcases lenPair with ⟨refEq, offEq⟩
      subst lenRef
      exact lenGet
    · rcases lenPair with ⟨refEq, offEq⟩
      subst lenRef
      subst lenOff
      exact lenSafe
    · simp [copiedGeneric, fixed.1, fixed.2]
    · rw [fixedDist]
      rcases distPair with ⟨refEq, offEq⟩
      subst distRef
      exact distGet
    · rcases distPair with ⟨refEq, offEq⟩
      subst distRef
      subst distOffset
      exact distSafe

/-- Transport all decoder and default-history clauses through pointer
relocation. The heap facts here are the concrete effects still to be supplied
by the actual `inflateCopy` execution proof. -/
theorem copiedGeneric_J_of_heap_facts
    {h after : Heap} {source dest : ZStreamRef}
    {old fresh nextOff distOff : Nat} {z : ZStream}
    {window : BPtr} {s : InflateState}
    (invariant : DefaultStateJ h source old z s)
    (windowNull : s.window = .null → window = .null)
    (origin : CopyTableOrigin old s)
    (dynamicDist : s.lencode = .ref (.istate_codes old) 0 →
      s.distcode = .ref (.istate_codes old) distOff)
    (freshCodes : Space.get after (CodeRef.istate_codes fresh) = some s.codes)
    (fixedLen : Space.get after CodeRef.st_lenfix = Space.get h CodeRef.st_lenfix)
    (fixedDist : Space.get after CodeRef.st_distfix = Space.get h CodeRef.st_distfix)
    (goodAfter : Good after dest fresh
      { z with state := some (.inflate fresh) }
      (copiedGeneric dest old fresh nextOff distOff window s))
    (globalsAfter : LibraryGlobals after)
    (platformAfter : ZlibF.PlatformMemory.ByteObjectsFit after) :
    DefaultStateJ after dest fresh
      { z with state := some (.inflate fresh) }
      (copiedGeneric dest old fresh nextOff distOff window s) := by
  let copied := copiedGeneric dest old fresh nextOff distOff window s
  have sourceCodes : Space.get h (CodeRef.istate_codes old) = some s.codes :=
    CodeRef.get_istate_codes invariant.good.live.hs
  have tables : DataTableInvariant after copied :=
    copiedGeneric_data_tables invariant.tables origin dynamicDist sourceCodes
      freshCodes fixedLen fixedDist
  have pending : DataPendingInvariant copied := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [copied, copiedGeneric] using invariant.pending.sane
    · simpa [copied, copiedGeneric, LengthExtraSafe, BackBound]
        using invariant.pending.lenext
    · simpa [copied, copiedGeneric, DistanceSafe, PendingLengthSafe, BackBound]
        using invariant.pending.dist
    · simpa [copied, copiedGeneric, DistanceExtraSafe, PendingLengthSafe, BackBound]
        using invariant.pending.distext
    · simpa [copied, copiedGeneric, MatchSafe]
        using invariant.pending.matching
  have lengths : CodeLengthInvariant fresh copied :=
    copiedGeneric_code_lengths invariant.lengths
  have headerLengths : LengthHeaderInvariant copied := by
    simpa [copied, copiedGeneric, LengthHeaderInvariant]
      using invariant.headerLengths
  refine ⟨⟨goodAfter, tables, pending, lengths, headerLengths,
    ?_, ?_, ?_, ?_, ?_, ?_, globalsAfter, platformAfter⟩,
    ?_, ?_, ?_⟩
  · simpa [copied, copiedGeneric] using invariant.held
  · rcases invariant.window with range | ⟨zero, null, unread, nonraw⟩
    · left
      simpa [copied, copiedGeneric] using range
    · right
      simp [copied, copiedGeneric, zero, windowNull null, unread, nonraw]
  · simpa [copied, copiedGeneric] using invariant.wrapper
  · simpa [copied, copiedGeneric] using invariant.header
  · simpa [copied, copiedGeneric] using invariant.modes
  · simpa [copied, copiedGeneric] using invariant.trailer
  · simpa [copied, copiedGeneric] using invariant.requestedBits
  · simpa [copied, copiedGeneric] using invariant.requestedWrap
  · simpa [copied, copiedGeneric] using invariant.phase

/-- Relocating a record onto its own state object is the identity. This
turns the destination transport theorem into a source-preservation theorem
once the actual heap frame has been established. -/
theorem copiedGeneric_self
    {source : ZStreamRef} {old nextOff distOff : Nat}
    {s : InflateState}
    (back : s.strm = some source)
    (origin : CopyTableOrigin old s)
    (nextPtr : s.next = .ref (.istate_codes old) nextOff)
    (dynamicDist : s.lencode = .ref (.istate_codes old) 0 →
      s.distcode = .ref (.istate_codes old) distOff) :
    copiedGeneric source old old nextOff distOff s.window s = s := by
  rcases origin with dynamic | fixed
  · cases s
    simp_all [copiedGeneric]
  · cases s
    simp_all [copiedGeneric]

theorem copiedSource_J_of_heap_facts
    {h after : Heap} {source : ZStreamRef}
    {old nextOff distOff : Nat} {z : ZStream}
    {s : InflateState}
    (invariant : DefaultStateJ h source old z s)
    (origin : CopyTableOrigin old s)
    (nextPtr : s.next = .ref (.istate_codes old) nextOff)
    (dynamicDist : s.lencode = .ref (.istate_codes old) 0 →
      s.distcode = .ref (.istate_codes old) distOff)
    (goodAfter : Good after source old z s)
    (freshCodes : Space.get after (CodeRef.istate_codes old) = some s.codes)
    (fixedLen : Space.get after CodeRef.st_lenfix = Space.get h CodeRef.st_lenfix)
    (fixedDist : Space.get after CodeRef.st_distfix = Space.get h CodeRef.st_distfix)
    (globalsAfter : LibraryGlobals after)
    (platformAfter : ZlibF.PlatformMemory.ByteObjectsFit after) :
    DefaultStateJ after source old z s := by
  have self := copiedGeneric_self invariant.good.live.back
    origin nextPtr dynamicDist
  have zState := invariant.good.live.zst
  have zNext : { z with state := some (.inflate old) } = z := by
    cases z
    simpa using zState.symm
  have goodTransport : Good after source old
      { z with state := some (.inflate old) }
      (copiedGeneric source old old nextOff distOff s.window s) := by
    rw [self, zNext]
    exact goodAfter
  have transported := copiedGeneric_J_of_heap_facts
    (h := h) (after := after) (source := source) (dest := source)
    (old := old) (fresh := old) (nextOff := nextOff) (distOff := distOff)
    (z := z) (window := s.window) (s := s)
    invariant id origin dynamicDist freshCodes fixedLen fixedDist
    goodTransport globalsAfter platformAfter
  simpa [self, zNext] using transported

theorem copiedSource_good_of_heap_facts
    {h after : Heap} {source : ZStreamRef} {old : Nat}
    {z : ZStream} {s : InflateState}
    (good : Good h source old z s)
    (streamGet : source.get after = some z)
    (stateGet : after.istates old = some s)
    (windowFrame : ∀ w, s.window = .ref (.blk w) 0 →
      after.bytes w = h.bytes w ∧ after.ro w = h.ro w)
    (fresh : Fresh after) (uniq : Uniq after) :
    Good after source old z s := by
  have live : Live after source old z s :=
    ⟨streamGet, stateGet, good.live.zst, good.live.back,
      good.live.mode, good.live.zalloc, good.live.zfree⟩
  have win : WinInv after s := by
    refine ⟨good.inv.win.wbits, ?_, good.inv.win.nullws,
      good.inv.win.ws, good.inv.win.hv, good.inv.win.wn,
      good.inv.win.eq⟩
    rcases good.inv.win.block with noWindow | ⟨w, a, ptr, get, ro, size⟩
    · exact Or.inl noWindow
    · obtain ⟨bytes, readonly⟩ := windowFrame w ptr
      exact Or.inr ⟨w, a, ptr, by rw [bytes]; exact get,
        by rw [readonly]; exact ro, size⟩
  have inv : StInv after old s :=
    ⟨good.inv.wf, win, good.inv.reqbits, good.inv.bits, good.inv.ptr⟩
  exact ⟨live, inv, uniq, fresh⟩

/-- The no-window heap produced by the actual C copy has a valid destination
representation for any bounded dynamic cursor or fixed table pair. -/
theorem copiedGeneric_no_window_good
    {h : Heap} {source dest : ZStreamRef}
    {old nextOff distOff : Nat} {z oldDest : ZStream}
    {s : InflateState}
    (good : Good h source old z s)
    (destGet : dest.get h = some oldDest)
    (origin : CopyTableOrigin old s)
    (nextBound : nextOff ≤ 1444)
    (distBound : distOff ≤ 1443)
    (noWindow : s.window = .null) :
    let fresh := h.nextBlk
    let copied := copiedGeneric dest old fresh nextOff distOff .null s
    let zNext : ZStream := { z with state := some (.inflate fresh) }
    Good (allocIstHeap (dest.put h zNext) copied) dest fresh zNext copied := by
  dsimp only
  let fresh := h.nextBlk
  let copied := copiedGeneric dest old fresh nextOff distOff .null s
  let zNext : ZStream := { z with state := some (.inflate fresh) }
  let put := dest.put h zNext
  let after := allocIstHeap put copied
  have putShape : Shape h put := shape_put destGet zNext
  have putFresh : Fresh put := putShape.fresh (by simp [put]) good.fresh
  have putUniq : Uniq put := putShape.uniq good.uniq
  have freshAfter : Fresh after := fresh_allocIst putFresh copied
  have uniqAfter : Uniq after := uniq_allocIst putUniq putFresh copied
  have live : Live after dest fresh zNext copied := by
    refine ⟨?_, ?_, rfl, ?_, ?_, ?_, ?_⟩
    · rw [ZStreamRef.get_allocIst]
      simp [put, ZStreamRef.get_put, destGet]
    · simp [after, fresh, put]
    · rfl
    · simpa [copied, copiedGeneric] using good.live.mode
    · exact good.live.zalloc
    · exact good.live.zfree
  have win : WinInv after copied := by
    refine ⟨good.inv.win.wbits, Or.inl rfl, ?_,
      good.inv.win.ws, good.inv.win.hv, good.inv.win.wn, good.inv.win.eq⟩
    intro _
    exact good.inv.win.nullws noWindow
  have inv : StInv after fresh copied := by
    refine ⟨?_, win, ?_, ?_, copiedGeneric_ptr origin nextBound distBound⟩
    · simpa [InflateState.WellFormed, copied, copiedGeneric] using good.inv.wf
    · simpa [copied, copiedGeneric] using good.inv.reqbits
    · simpa [copied, copiedGeneric] using good.inv.bits
  exact ⟨live, inv, uniqAfter, freshAfter⟩

/-- The windowed destination representation needs the fresh block's exact
extent, writability, and the ordinary heap freshness facts. These facts are
produced by the two actual allocations and the bounded byte copy. -/
theorem copiedGeneric_window_good_of_heap_facts
    {h after : Heap} {source dest : ZStreamRef}
    {old fresh freshWindow nextOff distOff : Nat}
    {z : ZStream} {s : InflateState} {a : Array UInt8}
    (sourceGood : Good h source old z s)
    (origin : CopyTableOrigin old s)
    (nextBound : nextOff ≤ 1444)
    (distBound : distOff ≤ 1443)
    (destGet : dest.get after = some { z with state := some (.inflate fresh) })
    (stateGet : after.istates fresh = some
      (copiedGeneric dest old fresh nextOff distOff
        (.ref (.blk freshWindow) 0) s))
    (windowGet : after.bytes freshWindow = some a)
    (windowWritable : after.ro freshWindow = false)
    (windowSize : a.size = 2 ^ s.wbits.toNat)
    (freshAfter : Fresh after) (uniqAfter : Uniq after) :
    Good after dest fresh { z with state := some (.inflate fresh) }
      (copiedGeneric dest old fresh nextOff distOff
        (.ref (.blk freshWindow) 0) s) := by
  let copied := copiedGeneric dest old fresh nextOff distOff
    (.ref (.blk freshWindow) 0) s
  have live : Live after dest fresh
      { z with state := some (.inflate fresh) } copied := by
    refine ⟨destGet, stateGet, rfl, ?_, ?_,
      sourceGood.live.zalloc, sourceGood.live.zfree⟩
    · rfl
    · simpa [copied, copiedGeneric] using sourceGood.live.mode
  have win : WinInv after copied := by
    refine ⟨sourceGood.inv.win.wbits,
      Or.inr ⟨freshWindow, a, rfl, windowGet, windowWritable, ?_⟩,
      ?_, sourceGood.inv.win.ws, sourceGood.inv.win.hv,
      sourceGood.inv.win.wn, sourceGood.inv.win.eq⟩
    · simpa [copied, copiedGeneric] using windowSize
    · intro impossible
      simp [copied, copiedGeneric] at impossible
  have inv : StInv after fresh copied := by
    refine ⟨?_, win, ?_, ?_, copiedGeneric_ptr origin nextBound distBound⟩
    · simpa [InflateState.WellFormed, copied, copiedGeneric]
        using sourceGood.inv.wf
    · simpa [copied, copiedGeneric] using sourceGood.inv.reqbits
    · simpa [copied, copiedGeneric] using sourceGood.inv.bits
  exact ⟨live, inv, uniqAfter, freshAfter⟩

/-- The exact no-window heap shape carries the complete default relation,
including tables in active decoding modes. -/
theorem copiedGeneric_no_window_J
    {h : Heap} {source dest : ZStreamRef}
    {old nextOff distOff : Nat} {z oldDest : ZStream}
    {s : InflateState}
    (invariant : DefaultStateJ h source old z s)
    (destGet : dest.get h = some oldDest)
    (origin : CopyTableOrigin old s)
    (nextBound : nextOff ≤ 1444)
    (distBound : distOff ≤ 1443)
    (dynamicDist : s.lencode = .ref (.istate_codes old) 0 →
      s.distcode = .ref (.istate_codes old) distOff)
    (noWindow : s.window = .null) :
    let fresh := h.nextBlk
    let copied := copiedGeneric dest old fresh nextOff distOff .null s
    let zNext : ZStream := { z with state := some (.inflate fresh) }
    DefaultStateJ (allocIstHeap (dest.put h zNext) copied)
      dest fresh zNext copied := by
  dsimp only
  let fresh := h.nextBlk
  let copied := copiedGeneric dest old fresh nextOff distOff .null s
  let zNext : ZStream := { z with state := some (.inflate fresh) }
  let after := allocIstHeap (dest.put h zNext) copied
  have goodAfter : Good after dest fresh zNext copied :=
    copiedGeneric_no_window_good invariant.good destGet origin
      nextBound distBound noWindow
  have copiedGet : after.istates fresh = some copied := by
    simp [after, fresh]
  have freshCodes : Space.get after (CodeRef.istate_codes fresh) = some s.codes := by
    simpa [copied, copiedGeneric] using
      (CodeRef.get_istate_codes copiedGet)
  have fixedLen : Space.get after CodeRef.st_lenfix =
      Space.get h CodeRef.st_lenfix := by
    simp [after, allocIstHeap, Space.get]
  have fixedDist : Space.get after CodeRef.st_distfix =
      Space.get h CodeRef.st_distfix := by
    simp [after, allocIstHeap, Space.get]
  have globalsAfter : LibraryGlobals after := by
    simpa [after, LibraryGlobals, allocIstHeap, ZStreamRef.put_static]
      using invariant.globals
  have sizes : ByteViewSizes h after :=
    (byte_view_sizes_stream_put h dest zNext).trans
      (copy_allocIst_byte_view_sizes (dest.put h zNext) copied)
  have platformAfter : ZlibF.PlatformMemory.ByteObjectsFit after :=
    sizes.platform invariant.platform
  exact copiedGeneric_J_of_heap_facts invariant (fun _ => rfl) origin dynamicDist
    freshCodes fixedLen fixedDist goodAfter globalsAfter platformAfter

/-- The source remains a valid default decoder in the exact no-window heap
installed for a distinct destination. -/
theorem copiedGeneric_no_window_source_J
    {h : Heap} {source dest : ZStreamRef}
    {old nextOff distOff : Nat} {z oldDest : ZStream}
    {s : InflateState}
    (invariant : DefaultStateJ h source old z s)
    (destGet : dest.get h = some oldDest)
    (different : source ≠ dest)
    (origin : CopyTableOrigin old s)
    (nextPtr : s.next = .ref (.istate_codes old) nextOff)
    (nextBound : nextOff ≤ 1444)
    (distBound : distOff ≤ 1443)
    (dynamicDist : s.lencode = .ref (.istate_codes old) 0 →
      s.distcode = .ref (.istate_codes old) distOff)
    (noWindow : s.window = .null) :
    let fresh := h.nextBlk
    let copied := copiedGeneric dest old fresh nextOff distOff .null s
    let zNext : ZStream := { z with state := some (.inflate fresh) }
    DefaultStateJ (allocIstHeap (dest.put h zNext) copied)
      source old z s := by
  dsimp only
  let fresh := h.nextBlk
  let copied := copiedGeneric dest old fresh nextOff distOff .null s
  let zNext : ZStream := { z with state := some (.inflate fresh) }
  let after := allocIstHeap (dest.put h zNext) copied
  have destJ : DefaultStateJ after dest fresh zNext copied :=
    copiedGeneric_no_window_J invariant destGet origin
      nextBound distBound dynamicDist noWindow
  have sourceGet : source.get after = some z := by
    rw [ZStreamRef.get_allocIst]
    exact (copy_stream_get_put_other h different zNext).trans
      invariant.good.live.hz
  have distinct : old ≠ h.nextBlk := by
    intro equal
    have live : h.live old := by
      simp [Heap.live, invariant.good.live.hs]
    exact invariant.good.fresh old (by omega) live
  have stateGet : after.istates old = some s := by
    simpa [after, allocIstHeap, upd_ne _ _ _ _ distinct]
      using invariant.good.live.hs
  have windowFrame : ∀ w, s.window = .ref (.blk w) 0 →
      after.bytes w = h.bytes w ∧ after.ro w = h.ro w := by
    intro w ptr
    rw [noWindow] at ptr
    cases ptr
  have goodAfter : Good after source old z s :=
    copiedSource_good_of_heap_facts invariant.good sourceGet stateGet
      windowFrame destJ.good.fresh destJ.good.uniq
  have freshCodes : Space.get after (CodeRef.istate_codes old) = some s.codes :=
    CodeRef.get_istate_codes stateGet
  have fixedLen : Space.get after CodeRef.st_lenfix =
      Space.get h CodeRef.st_lenfix := by
    simp [after, allocIstHeap, Space.get]
  have fixedDist : Space.get after CodeRef.st_distfix =
      Space.get h CodeRef.st_distfix := by
    simp [after, allocIstHeap, Space.get]
  exact copiedSource_J_of_heap_facts invariant origin nextPtr dynamicDist
    goodAfter freshCodes fixedLen fixedDist destJ.globals destJ.platform

#print axioms copiedGeneric_no_window_J
#print axioms copiedGeneric_no_window_source_J
#print axioms copiedGeneric_window_good_of_heap_facts

end Zlib.Inflate.Proofs
