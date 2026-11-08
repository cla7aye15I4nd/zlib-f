import ZlibF.Proof.«inflate.c.default-foundation»
import ZlibF.Proof.«inflate.c.output-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The only two table origins installed by completed decoder calls. This is
an internal history fact; `Good` alone deliberately allows more pointer shapes. -/
def CopyTableOrigin (zs : Nat) (s : InflateState) : Prop :=
  s.lencode = .ref (.istate_codes zs) 0 ∨
    (s.lencode = .ref .st_lenfix 0 ∧ s.distcode = .ref .st_distfix 0)

def copiedNoWindow (dest : ZStreamRef) (fresh : Nat)
    (s : InflateState) : InflateState :=
  { s with
    strm := some dest,
    lencode := .ref (.istate_codes fresh) 0,
    distcode := .ref (.istate_codes fresh) 0,
    next := .ref (.istate_codes fresh) 0,
    window := .null }

/-- Copying a stream record into a distinct destination cannot change the
source record, including when one reference is embedded in a gzip state. -/
theorem copy_stream_get_put_other
    (h : Heap) {source dest : ZStreamRef}
    (different : source ≠ dest) (v : ZStream) :
    source.get (dest.put h v) = source.get h := by
  cases source with
  | tab si =>
    cases dest with
    | tab di =>
      have ne : si ≠ di := by
        intro eq
        cases eq
        exact different rfl
      cases hd : h.streams di <;>
        simp [ZStreamRef.get, ZStreamRef.put, hd, upd_ne _ _ _ _ ne]
    | in_gzstate_strm di =>
      cases hd : h.gzstates di <;>
        simp [ZStreamRef.get, ZStreamRef.put, hd]
  | in_gzstate_strm si =>
    cases dest with
    | tab di =>
      cases hd : h.streams di <;>
        simp [ZStreamRef.get, ZStreamRef.put, hd]
    | in_gzstate_strm di =>
      have ne : si ≠ di := by
        intro eq
        cases eq
        exact different rfl
      cases hd : h.gzstates di <;>
        simp [ZStreamRef.get, ZStreamRef.put, hd, upd_ne _ _ _ _ ne]

/-- A dynamic source selected by the patched equality test has its
distance pointer in the same bounded code array. The next pointer may be
one past that array, as the C allows. -/
theorem CopyTableOrigin.dynamic_geometry
    {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState}
    (good : Good h r zs z s)
    (dynamic : s.lencode = .ref (.istate_codes zs) 0) :
    ∃ nextOff distOff,
      s.next = .ref (.istate_codes zs) nextOff ∧ nextOff ≤ 1444 ∧
      s.distcode = .ref (.istate_codes zs) distOff ∧ distOff ≤ 1443 ∧
      Space.get h (CodeRef.istate_codes zs) = some s.codes ∧ s.codes.size = 1444 := by
  obtain ⟨nextGeom, tableGeom⟩ := good.inv.ptr
  obtain ⟨nextOff, nextPtr, nextBound⟩ := nextGeom
  rcases tableGeom with dynamicGeom | fixedGeom
  · obtain ⟨lenOff, distOff, lenPtr, distPtr, lenBound, distBound⟩ := dynamicGeom
    have lenZero : lenOff = 0 :=
      (Ptr.ref.inj (lenPtr.symm.trans dynamic)).2
    subst lenOff
    exact ⟨nextOff, distOff, nextPtr, nextBound, distPtr, distBound,
      CodeRef.get_istate_codes good.live.hs, good.inv.wf.2.2⟩
  · have impossible := fixedGeom.1.symm.trans dynamic
    cases impossible

/-- The unconditional `next - codes` in the copied C has the same-array
geometry even when `next` is one past the last table entry. -/
theorem copy_next_diff_safe
    {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState}
    (good : Good h r zs z s) :
    ∃ off : Nat, off ≤ 1444 ∧
      C.run (Ptr.diff s.next (.ref (.istate_codes zs) 0)) h =
        .ok (Int64.ofInt (off : Int), h) := by
  obtain ⟨off, pointer, bound⟩ := good.inv.ptr.1
  have get : Space.get h (CodeRef.istate_codes zs) = some s.codes :=
    CodeRef.get_istate_codes good.live.hs
  have size : s.codes.size = 1444 := good.inv.wf.2.2
  have run := Ptr.diff_ok (r := CodeRef.istate_codes zs)
    (a := s.codes) (o1 := off) (o2 := 0) get
    (by omega) (by omega)
    (by omega : -(2 ^ 63 : Int) ≤ (off : Int) - 0 ∧
      (off : Int) - 0 < 2 ^ 63)
  refine ⟨off, bound, ?_⟩
  rw [pointer]
  simpa [C.run, OkOn] using run

/-- On the equality branch, the C distance-pointer subtraction is within
the source `codes` array and produces the original nonnegative offset. -/
theorem copy_dist_diff_safe
    {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState}
    (good : Good h r zs z s)
    (dynamic : s.lencode = .ref (.istate_codes zs) 0) :
    ∃ off : Nat, off ≤ 1443 ∧
      C.run (Ptr.diff s.distcode (.ref (.istate_codes zs) 0)) h =
        .ok (Int64.ofInt (off : Int), h) := by
  obtain ⟨nextOff, distOff, nextPtr, nextBound,
    distPtr, distBound, get, size⟩ :=
    CopyTableOrigin.dynamic_geometry good dynamic
  have run := Ptr.diff_ok (r := CodeRef.istate_codes zs)
    (a := s.codes) (o1 := distOff) (o2 := 0) get
    (by omega) (by omega)
    (by omega : -(2 ^ 63 : Int) ≤ (distOff : Int) - 0 ∧
      (distOff : Int) - 0 < 2 ^ 63)
  refine ⟨distOff, distBound, ?_⟩
  rw [distPtr]
  simpa [C.run, OkOn] using run

theorem copy_codes_zero_diff
    {h : Heap} {i : Nat} {s : InflateState}
    (get : h.istates i = some s) :
    (Ptr.diff (.ref (CodeRef.istate_codes i) 0)
      (.ref (CodeRef.istate_codes i) 0)) h = .ok (0, h) := by
  have table : Space.get h (CodeRef.istate_codes i) = some s.codes :=
    CodeRef.get_istate_codes get
  have run := Ptr.diff_ok (r := CodeRef.istate_codes i)
    (a := s.codes) (o1 := 0) (o2 := 0) table
    (Nat.zero_le _) (Nat.zero_le _)
    (by decide : -(2 ^ 63 : Int) ≤ (0 : Int) - 0 ∧
      (0 : Int) - 0 < 2 ^ 63)
  simpa [OkOn] using run

theorem copy_codes_zero_add
    {h : Heap} {i : Nat} {s : InflateState}
    (get : h.istates i = some s) :
    (Ptr.add (.ref (CodeRef.istate_codes i) 0) 0) h =
      .ok (.ref (CodeRef.istate_codes i) 0, h) := by
  have table : Space.get h (CodeRef.istate_codes i) = some s.codes :=
    CodeRef.get_istate_codes get
  have run := Ptr.add_ok (r := CodeRef.istate_codes i)
    (a := s.codes) (off := 0) (k := 0) table
    (by omega) (by omega)
  simpa [OkOn] using run

theorem copy_allocIst_byte_view_sizes (h : Heap) (s : InflateState) :
    ByteViewSizes h (allocIstHeap h s) := by
  intro ref
  cases ref <;> rfl

/-- The first actual allocation in a valid copy returns a fresh state
record; it does not change the source stream or source state. -/
theorem copy_state_allocation_success
    {h : Heap} {source : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState}
    (good : Good h source zs z s)
    (allocator : DefAlloc z)
    (allocation : h.allocOk h.nalloc = true) :
    let allocated := allocIstHeap h (InflateState.garbage (h.garbage h.nalloc))
    C.run (ZALLOCS (some source)) h =
      .ok (some (.tab h.nextBlk), allocated) ∧
    source.get allocated = some z ∧ allocated.istates zs = some s := by
  dsimp only
  have freshBlock : h.slotUsed h.nextBlk = false := good.fresh.slotUsed_next
  have allocRun := allocInflateState_some allocation freshBlock
  have run : C.run (ZALLOCS (some source)) h =
      .ok (some (.tab h.nextBlk),
        allocIstHeap h (InflateState.garbage (h.garbage h.nalloc))) := by
    change (ZALLOCS (some source)) h = _
    simp [ZALLOCS, ldZ_eq, good.live.hz, allocator.1, allocRun,
      allocIstHeap]
  have distinct : zs ≠ h.nextBlk := by
    intro equal
    have live : h.live zs := by
      simp [Heap.live, good.live.hs]
    exact good.fresh zs (by omega) live
  refine ⟨run, ?_, ?_⟩
  · rw [ZStreamRef.get_allocIst]
    exact good.live.hz
  · rw [allocIstHeap_istates_ne _ _ _ distinct]
    exact good.live.hs

/-- The C whole-record stream copy runs after state allocation and leaves
the source stream unchanged. -/
theorem copy_stream_after_allocation
    {h : Heap} {source dest : ZStreamRef} {zs : Nat}
    {z oldDest : ZStream} {s : InflateState}
    (good : Good h source zs z s)
    (destGet : dest.get h = some oldDest)
    (different : source ≠ dest) :
    let allocated := allocIstHeap h (InflateState.garbage (h.garbage h.nalloc))
    C.run (copyZStream (some dest) (some source)) allocated =
      .ok ((), dest.put allocated z) ∧
    source.get (dest.put allocated z) = some z := by
  dsimp only
  let allocated := allocIstHeap h (InflateState.garbage (h.garbage h.nalloc))
  have sourceGet : source.get allocated = some z := by
    rw [ZStreamRef.get_allocIst]
    exact good.live.hz
  have destLive : dest.get allocated = some oldDest := by
    rw [ZStreamRef.get_allocIst]
    exact destGet
  have destRo : dest.isRo = false := by cases dest <;> rfl
  have run : C.run (copyZStream (some dest) (some source)) allocated =
      .ok ((), dest.put allocated z) := by
    change (copyZStream (some dest) (some source)) allocated = _
    simp [copyZStream, different.symm, ldZ_eq, sourceGet,
      stZStream_ok destLive destRo]
  exact ⟨run, (copy_stream_get_put_other allocated different z).trans sourceGet⟩

/-- After the new record is zeroed and the stream is copied, the C whole
state copy installs exactly the source state in the fresh record. -/
theorem copy_state_after_zeroed_stream
    {h : Heap} {source dest : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState}
    (good : Good h source zs z s) :
    let allocated := allocIstHeap h (InflateState.garbage (h.garbage h.nalloc))
    let zeroed := setI allocated h.nextBlk InflateState.zeroed
    let copiedStream := dest.put zeroed z
    C.run (copyInflateState (some (.tab h.nextBlk)) (some (.tab zs)))
      copiedStream = .ok ((), setI copiedStream h.nextBlk s) := by
  dsimp only
  have distinct : zs ≠ h.nextBlk := by
    intro equal
    have live : h.live zs := by simp [Heap.live, good.live.hs]
    exact good.fresh zs (by omega) live
  let allocated := allocIstHeap h (InflateState.garbage (h.garbage h.nalloc))
  let zeroed := setI allocated h.nextBlk InflateState.zeroed
  let copiedStream := dest.put zeroed z
  have sourceState : copiedStream.istates zs = some s := by
    rw [ZStreamRef.put_istates, setI_istates_ne _ _ _ _ distinct,
      allocIstHeap_istates_ne _ _ _ distinct]
    exact good.live.hs
  have destState : copiedStream.istates h.nextBlk = some InflateState.zeroed := by
    rw [ZStreamRef.put_istates, setI_istates_same]
  have run : (copyInflateState (some (.tab h.nextBlk)) (some (.tab zs)))
      copiedStream = .ok ((), setI copiedStream h.nextBlk s) := by
    simp [copyInflateState, distinct.symm, ldInflateState_tab sourceState,
      stInflateState_tab destState, setI]
  exact run

/-- The no-window branch immediately after initialization executes the
actual copy through state allocation, record copy, and pointer relocation. -/
theorem inflateCopy_default_no_window_exec
    {h : Heap} {source dest : ZStreamRef} {zs : Nat}
    {z oldDest : ZStream} {s : InflateState}
    (good : Good h source zs z s)
    (allocator : DefAlloc z)
    (destGet : dest.get h = some oldDest)
    (different : source ≠ dest)
    (allocation : h.allocOk h.nalloc = true)
    (noWindow : s.window = .null)
    (next0 : s.next = .ref (.istate_codes zs) 0)
    (len0 : s.lencode = .ref (.istate_codes zs) 0)
    (dist0 : s.distcode = .ref (.istate_codes zs) 0) :
    ∃ after,
      C.run (inflateCopy (some dest) (some source)) h = .ok (Z_OK, after) ∧
      source.get after = some z ∧ after.istates zs = some s ∧
      dest.get after = some { z with state := some (.inflate h.nextBlk) } ∧
      ∃ copied, after.istates h.nextBlk = some copied ∧
        copied = copiedNoWindow dest h.nextBlk s ∧
        after = allocIstHeap
          (dest.put h { z with state := some (.inflate h.nextBlk) })
          copied := by
  have sourceCheck := stateCheck_live good.live
  have allocRun := (copy_state_allocation_success good allocator allocation).1
  change (ZALLOCS (some source)) h = _ at allocRun
  let allocated := allocIstHeap h (InflateState.garbage (h.garbage h.nalloc))
  let zeroed := setI allocated h.nextBlk InflateState.zeroed
  have zeroGet : allocated.istates h.nextBlk =
      some (InflateState.garbage (h.garbage h.nalloc)) := by
    simp [allocated]
  have zeroRun : stInflateState (some (.tab h.nextBlk)) InflateState.zeroed allocated =
      .ok ((), zeroed) := by
    simpa [zeroed, setI] using
      (stInflateState_tab (i := h.nextBlk) (v' := InflateState.zeroed) zeroGet)
  simp only [allocated] at zeroRun
  have distinct : zs ≠ h.nextBlk := by
    intro equal
    have live : h.live zs := by simp [Heap.live, good.live.hs]
    exact good.fresh zs (by omega) live
  have zeroSource : zeroed.istates zs = some s := by
    rw [setI_istates_ne _ _ _ _ distinct,
      allocIstHeap_istates_ne _ _ _ distinct]
    exact good.live.hs
  have sourceZero : source.get zeroed = some z := by
    rw [ZStreamRef.get_setI, ZStreamRef.get_allocIst]
    exact good.live.hz
  have destZero : dest.get zeroed = some oldDest := by
    rw [ZStreamRef.get_setI, ZStreamRef.get_allocIst]
    exact destGet
  have destRo : dest.isRo = false := by cases dest <;> rfl
  have copyZRun : copyZStream (some dest) (some source) zeroed =
      .ok ((), dest.put zeroed z) := by
    simp [copyZStream, different.symm, ldZ_eq, sourceZero,
      stZStream_ok destZero destRo]
  have copyIRun : copyInflateState (some (.tab h.nextBlk))
      (some (.tab zs)) (dest.put zeroed z) =
      .ok ((), setI (dest.put zeroed z) h.nextBlk s) := by
    change C.run (copyInflateState (some (.tab h.nextBlk)) (some (.tab zs)))
      (dest.put zeroed z) = _
    simpa only [zeroed, allocated] using
      (copy_state_after_zeroed_stream (dest := dest) good)
  let copied := setI (dest.put zeroed z) h.nextBlk s
  let backlinked := setI copied h.nextBlk { s with strm := some dest }
  have copyGet : copied.istates h.nextBlk = some s := by
    simp [copied]
  have backlinkRun : wrS (some (.tab h.nextBlk))
      (fun v => { v with strm := some dest }) copied =
      .ok ((), backlinked) := by
    simp [wrS, ldInflateState_tab copyGet,
      stInflateState_tab copyGet, backlinked, setI]
  simp only [copied] at backlinkRun
  have sourceAfterBacklink : backlinked.istates zs = some s := by
    rw [setI_istates_ne _ _ _ _ distinct,
      setI_istates_ne _ _ _ _ distinct,
      ZStreamRef.put_istates,
      setI_istates_ne _ _ _ _ distinct,
      allocIstHeap_istates_ne _ _ _ distinct]
    exact good.live.hs
  let backState := { s with strm := some dest }
  have backGet : backlinked.istates h.nextBlk = some backState := by
    simp [backlinked, backState]
  let lenState := { backState with lencode := .ref (.istate_codes h.nextBlk) 0 }
  let afterLen := setI backlinked h.nextBlk lenState
  have lenRun : wrS (some (.tab h.nextBlk))
      (fun v => { v with lencode := codesP (some (.tab h.nextBlk)) })
      backlinked = .ok ((), afterLen) := by
    simp [wrI_eq, backGet, codesP, afterLen, lenState]
  simp only [codesP] at lenRun
  have sourceAfterLen : afterLen.istates zs = some s := by
    rw [setI_istates_ne _ _ _ _ distinct]
    exact sourceAfterBacklink
  have lenGet : afterLen.istates h.nextBlk = some lenState := by
    simp [afterLen]
  have distDiff : Ptr.diff (.ref (CodeRef.istate_codes zs) 0)
      (.ref (CodeRef.istate_codes zs) 0) afterLen = .ok (0, afterLen) :=
    copy_codes_zero_diff sourceAfterLen
  have distAdd : Ptr.add (.ref (CodeRef.istate_codes h.nextBlk) 0) 0
      afterLen = .ok (.ref (CodeRef.istate_codes h.nextBlk) 0, afterLen) :=
    copy_codes_zero_add lenGet
  let distState := { lenState with distcode := .ref (.istate_codes h.nextBlk) 0 }
  let afterDist := setI afterLen h.nextBlk distState
  have distRun : wrS (some (.tab h.nextBlk))
      (fun v => { v with distcode := .ref (.istate_codes h.nextBlk) 0 })
      afterLen = .ok ((), afterDist) := by
    simp [wrI_eq, lenGet, afterDist, distState]
  have sourceAfterDist : afterDist.istates zs = some s := by
    rw [setI_istates_ne _ _ _ _ distinct]
    exact sourceAfterLen
  have distGet : afterDist.istates h.nextBlk = some distState := by
    simp [afterDist]
  have nextDiff : Ptr.diff (.ref (CodeRef.istate_codes zs) 0)
      (.ref (CodeRef.istate_codes zs) 0) afterDist = .ok (0, afterDist) :=
    copy_codes_zero_diff sourceAfterDist
  have nextAdd : Ptr.add (.ref (CodeRef.istate_codes h.nextBlk) 0) 0
      afterDist = .ok (.ref (CodeRef.istate_codes h.nextBlk) 0, afterDist) :=
    copy_codes_zero_add distGet
  let nextState := { distState with next := .ref (.istate_codes h.nextBlk) 0 }
  let afterNext := setI afterDist h.nextBlk nextState
  have nextRun : wrS (some (.tab h.nextBlk))
      (fun v => { v with next := .ref (.istate_codes h.nextBlk) 0 })
      afterDist = .ok ((), afterNext) := by
    simp [wrI_eq, distGet, afterNext, nextState]
  have nextGet : afterNext.istates h.nextBlk = some nextState := by
    simp [afterNext]
  let windowState := { nextState with window := (.null : BPtr) }
  let afterWindow := setI afterNext h.nextBlk windowState
  have windowRun : wrS (some (.tab h.nextBlk))
      (fun v => { v with window := (.null : BPtr) })
      afterNext = .ok ((), afterWindow) := by
    simp [wrI_eq, nextGet, afterWindow, windowState]
  have destAfterWindow : dest.get afterWindow = some z := by
    simp only [afterWindow, afterNext, afterDist, afterLen,
      backlinked, copied, ZStreamRef.get_setI,
      ZStreamRef.get_put, destZero, Option.map_some]
  have destRun : wrZ (some dest)
      (fun v => { v with state := some (.inflate h.nextBlk) })
      afterWindow =
      .ok ((), dest.put afterWindow { z with state := some (.inflate h.nextBlk) }) := by
    simp [wrZ_eq, destAfterWindow]
  let finished := dest.put afterWindow { z with state := some (.inflate h.nextBlk) }
  have run : C.run (inflateCopy (some dest) (some source)) h =
      .ok (Z_OK, finished) := by
    change (inflateCopy (some dest) (some source)) h = _
    simp [inflateCopy, sourceCheck, ldZStream_ok good.live.hz,
    good.live.zst, castI, allocRun, zeroRun,
    ldInflateState_tab zeroSource, noWindow, next0, len0, dist0,
    copyZRun, copyIRun, backlinkRun,
    ldInflateState_tab sourceAfterBacklink, codesP, lenRun,
    distDiff, distAdd, distRun, nextDiff, nextAdd,
    nextRun, windowRun, destRun, StateRef.ofInflateState,
    finished]
  have sourceAfterWindow : source.get afterWindow = some z := by
    simp only [afterWindow, afterNext, afterDist, afterLen,
      backlinked, copied, ZStreamRef.get_setI]
    exact (copy_stream_get_put_other zeroed different z).trans sourceZero
  have sourceFinished : source.get finished = some z := by
    exact (copy_stream_get_put_other afterWindow different _).trans sourceAfterWindow
  have sourceStateFinished : finished.istates zs = some s := by
    simp only [finished, ZStreamRef.put_istates,
      afterWindow, afterNext, afterDist, afterLen,
      backlinked, copied, setI_istates_ne _ _ _ _ distinct,
      ZStreamRef.put_istates, zeroSource]
  have destFinished : dest.get finished =
      some { z with state := some (.inflate h.nextBlk) } := by
    simp [finished, ZStreamRef.get_put, destAfterWindow]
  have copiedFinished : finished.istates h.nextBlk = some windowState := by
    simp [finished, afterWindow]
  have copiedShape : windowState = copiedNoWindow dest h.nextBlk s := by
    simp [copiedNoWindow, windowState, nextState,
      distState, lenState, backState]
  have finalHeapEq : finished =
      allocIstHeap
        (dest.put h { z with state := some (.inflate h.nextBlk) })
        (copiedNoWindow dest h.nextBlk s) := by
    simp [finished, afterWindow, afterNext, afterDist, afterLen,
      backlinked, copied, zeroed, allocated, windowState, nextState,
      distState, lenState, backState, copiedNoWindow,
      ZStreamRef.put_setI, ZStreamRef.put_allocIst,
      setI_allocIst, ZStreamRef.put_put]
  exact ⟨finished, run, sourceFinished, sourceStateFinished,
    destFinished, windowState, copiedFinished, copiedShape,
    by rw [copiedShape]; exact finalHeapEq⟩

/-- The fresh no-window copy inherits the source representation invariant.
The destination was a live, distinct stream record before the call. -/
theorem inflateCopy_default_no_window_good
    {h : Heap} {source dest : ZStreamRef} {zs : Nat}
    {z oldDest : ZStream} {s : InflateState}
    (good : Good h source zs z s)
    (allocator : DefAlloc z)
    (destGet : dest.get h = some oldDest)
    (different : source ≠ dest)
    (allocation : h.allocOk h.nalloc = true)
    (noWindow : s.window = .null)
    (next0 : s.next = .ref (.istate_codes zs) 0)
    (len0 : s.lencode = .ref (.istate_codes zs) 0)
    (dist0 : s.distcode = .ref (.istate_codes zs) 0) :
    ∃ after copied,
      C.run (inflateCopy (some dest) (some source)) h = .ok (Z_OK, after) ∧
      Good after dest h.nextBlk
        { z with state := some (.inflate h.nextBlk) } copied ∧
      copied = copiedNoWindow dest h.nextBlk s ∧
      source.get after = some z ∧ after.istates zs = some s := by
  obtain ⟨after, run, sourceGet, sourceState, destState,
    copied, copiedGet, copiedEq, heapEq⟩ :=
    inflateCopy_default_no_window_exec good allocator destGet different
      allocation noWindow next0 len0 dist0
  subst copied
  let zNext : ZStream := { z with state := some (.inflate h.nextBlk) }
  let sNext : InflateState := copiedNoWindow dest h.nextBlk s
  have putShape : Shape h (dest.put h zNext) := shape_put destGet zNext
  have putFresh : Fresh (dest.put h zNext) :=
    putShape.fresh (by simp) good.fresh
  have putUniq : Uniq (dest.put h zNext) := putShape.uniq good.uniq
  have fresh : Fresh after := by
    rw [heapEq]
    exact fresh_allocIst putFresh sNext
  have uniq : Uniq after := by
    rw [heapEq]
    exact uniq_allocIst putUniq putFresh sNext
  have live : Live after dest h.nextBlk zNext sNext := by
    refine ⟨?_, ?_, rfl, ?_, ?_, ?_, ?_⟩
    · exact destState
    · exact copiedGet
    · rfl
    · simpa only [sNext, copiedNoWindow] using good.live.mode
    · exact good.live.zalloc
    · exact good.live.zfree
  have win : WinInv after sNext := by
    refine ⟨good.inv.win.wbits, Or.inl rfl, ?_,
      good.inv.win.ws, good.inv.win.hv, good.inv.win.wn, good.inv.win.eq⟩
    intro _
    exact good.inv.win.nullws noWindow
  have inv : StInv after h.nextBlk sNext := by
    refine ⟨?_, win, good.inv.reqbits, good.inv.bits, ?_⟩
    · simpa [InflateState.WellFormed, sNext, copiedNoWindow]
        using good.inv.wf
    · refine ⟨⟨0, rfl, by decide⟩, Or.inl ?_⟩
      exact ⟨0, 0, rfl, rfl, by decide, by decide⟩
  exact ⟨after, sNext, run, ⟨live, inv, uniq, fresh⟩,
    rfl, sourceGet, sourceState⟩

/-- An initialized default decoder remains in the same default relation
after a successful no-window copy into a distinct live destination. -/
theorem inflateCopy_default_no_window_J
    {h : Heap} {source dest : ZStreamRef} {zs : Nat}
    {z oldDest : ZStream} {s : InflateState}
    (invariant : DefaultStateJ h source zs z s)
    (allocator : DefAlloc z)
    (destGet : dest.get h = some oldDest)
    (different : source ≠ dest)
    (allocation : h.allocOk h.nalloc = true)
    (head : s.mode = HEAD)
    (noWindow : s.window = .null)
    (next0 : s.next = .ref (.istate_codes zs) 0)
    (len0 : s.lencode = .ref (.istate_codes zs) 0)
    (dist0 : s.distcode = .ref (.istate_codes zs) 0) :
    ∃ after copied,
      C.run (inflateCopy (some dest) (some source)) h = .ok (Z_OK, after) ∧
      DefaultStateJ after dest h.nextBlk
        { z with state := some (.inflate h.nextBlk) } copied ∧
      copied = copiedNoWindow dest h.nextBlk s ∧
      source.get after = some z ∧ after.istates zs = some s := by
  obtain ⟨after, copied, run, good, copiedEq, sourceGet, sourceState⟩ :=
    inflateCopy_default_no_window_good invariant.good allocator destGet
      different allocation noWindow next0 len0 dist0
  have exact := inflateCopy_default_no_window_exec invariant.good
    allocator destGet different allocation noWindow next0 len0 dist0
  obtain ⟨found, foundRun, _, _, _, foundCopy, _, foundEq, foundHeap⟩ := exact
  have sameAfter : after = found :=
    congrArg Prod.snd (Except.ok.inj (run.symm.trans foundRun))
  have sameCopied : copied = foundCopy := copiedEq.trans foundEq.symm
  have heapEq : after = allocIstHeap
      (dest.put h { z with state := some (.inflate h.nextBlk) })
      copied := by
    rw [sameAfter, sameCopied]
    exact foundHeap
  subst copied
  let sNext : InflateState := copiedNoWindow dest h.nextBlk s
  have headNext : sNext.mode = HEAD := by simpa [sNext, copiedNoWindow] using head
  have tables : DataTableInvariant after sNext := dataTableInvariant_head headNext
  have pending : DataPendingInvariant sNext := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [sNext, copiedNoWindow] using invariant.pending.sane
    all_goals intro active
    all_goals rw [headNext] at active
    all_goals contradiction
  have lengths : CodeLengthInvariant h.nextBlk sNext := by
    intro active
    rw [headNext] at active
    contradiction
  have headerLengths : LengthHeaderInvariant sNext := by
    intro active
    rw [headNext] at active
    contradiction
  have globals : LibraryGlobals after := by
    rw [heapEq]
    simpa [LibraryGlobals, allocIstHeap, ZStreamRef.put_static]
      using invariant.globals
  have sizes : ByteViewSizes h after := by
    rw [heapEq]
    exact (byte_view_sizes_stream_put h dest
      { z with state := some (.inflate h.nextBlk) }).trans
      (copy_allocIst_byte_view_sizes _ sNext)
  have platform : ZlibF.PlatformMemory.ByteObjectsFit after :=
    sizes.platform invariant.platform
  have nextJ : DefaultStateJ after dest h.nextBlk
      { z with state := some (.inflate h.nextBlk) } sNext := by
    refine ⟨⟨good, tables, pending, lengths, headerLengths,
      ?_, ?_, ?_, ?_, ?_, ?_, globals, platform⟩,
      ?_, ?_, ?_⟩
    · simpa [sNext, copiedNoWindow] using invariant.held
    · simpa [sNext, copiedNoWindow] using invariant.window
    · simpa [sNext, copiedNoWindow] using invariant.wrapper
    · simpa [sNext, copiedNoWindow] using invariant.header
    · simpa [sNext, copiedNoWindow] using invariant.modes
    · simpa [sNext, copiedNoWindow] using invariant.trailer
    · simpa [sNext, copiedNoWindow] using invariant.requestedBits
    · simpa [sNext, copiedNoWindow] using invariant.requestedWrap
    · simpa [sNext, copiedNoWindow] using invariant.phase
  exact ⟨after, sNext, run, nextJ, rfl, sourceGet, sourceState⟩

/-- The actual default initializer leaves the decoder in HEAD with no window
and all three mutable table pointers at the start of its `codes` array. -/
theorem inflate_default_copy_origin
    {h after : Heap} {r : ZStreamRef} {version : BPtr}
    (domain : InitDomain h r version)
    (allocation : h.allocOk h.nalloc = true)
    (run : C.run (inflateInit_ (some r) version 112) h = .ok (Z_OK, after))
    {z : ZStream} {s : InflateState}
    (good : Good after r h.nextBlk z s) :
    s.mode = HEAD ∧ s.window = .null ∧
      s.next = .ref (.istate_codes h.nextBlk) 0 ∧
      s.lencode = .ref (.istate_codes h.nextBlk) 0 ∧
      s.distcode = .ref (.istate_codes h.nextBlk) 0 ∧
      CopyTableOrigin h.nextBlk s := by
  obtain ⟨fresh, _, _, validVersion, before, get, allocators, _⟩ := domain
  obtain ⟨nonnull, first⟩ :=
    ZlibF.Spec.Public.Proofs.InflateInit.version_value_read validVersion
  have expected : C.run (inflateInit_ (some r) version 112) h =
      .ok (Z_OK, initOkHeap h r before 5 15) := by
    change inflateInit2_ (some r) 15 version 112 h = _
    exact inflateInit2_success get fresh allocation allocators.1
      allocators.2 nonnull first (by decide +kernel)
  have heapEq : after = initOkHeap h r before 5 15 :=
    congrArg Prod.snd (Except.ok.inj (run.symm.trans expected))
  have stateEq : s = resetKeepState h.nextBlk
      (resetPre (reset2Pre 5 15 (initState r))) := by
    apply Option.some.inj
    rw [← good.live.hs, heapEq]
    simp [initOkHeap]
  rw [stateEq]
  simp [CopyTableOrigin, resetKeepState, resetPre, reset2Pre,
    initState]

/-- The actual successful default initialization establishes both the
existing default relation and the code-origin field on one returned state. -/
theorem inflate_default_copy_ready
    (h : Heap) (r : ZStreamRef) (version : BPtr)
    (domain : InitDomain h r version)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit h)
    (allocation : h.allocOk h.nalloc = true) :
    ∃ after z s,
      C.run (inflateInit_ (some r) version 112) h = .ok (Z_OK, after) ∧
      DefaultStateJ after r h.nextBlk z s ∧
      StreamReachable .inflate after r ∧
      s.mode = HEAD ∧ s.window = .null ∧
      s.next = .ref (.istate_codes h.nextBlk) 0 ∧
      s.lencode = .ref (.istate_codes h.nextBlk) 0 ∧
      s.distcode = .ref (.istate_codes h.nextBlk) 0 ∧
      CopyTableOrigin h.nextBlk s := by
  obtain ⟨after, z, s, run, _, invariant, reachable⟩ :=
    inflate_default_state_initial h r version domain platform allocation
  have origin := inflate_default_copy_origin domain allocation run invariant.good
  exact ⟨after, z, s, run, invariant, reachable,
    origin.1, origin.2.1, origin.2.2.1, origin.2.2.2.1,
    origin.2.2.2.2.1, origin.2.2.2.2.2⟩

/-- Compose the actual default init producer with the no-window successful
copy. The new destination has the same internal default relation. -/
theorem inflateCopy_after_default_init_success
    {before after : Heap} {source dest : ZStreamRef}
    {version : BPtr} {oldDest : ZStream}
    (domain : InitDomain before source version)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit before)
    (initAllocation : before.allocOk before.nalloc = true)
    (initRun : C.run (inflateInit_ (some source) version 112) before =
      .ok (Z_OK, after))
    (destGet : dest.get after = some oldDest)
    (different : source ≠ dest)
    (copyAllocation : after.allocOk after.nalloc = true) :
    ∃ z s finished copied,
      C.run (inflateCopy (some dest) (some source)) after =
        .ok (Z_OK, finished) ∧
      DefaultStateJ finished dest after.nextBlk
        { z with state := some (.inflate after.nextBlk) } copied ∧
      copied = copiedNoWindow dest after.nextBlk s ∧
      source.get finished = some z ∧ finished.istates before.nextBlk = some s := by
  obtain ⟨initAfter, z, s, expected, initial, invariant, _⟩ :=
    inflate_default_state_initial before source version domain platform
      initAllocation
  have sameAfter : initAfter = after :=
    congrArg Prod.snd (Except.ok.inj (expected.symm.trans initRun))
  subst initAfter
  have origin := inflate_default_copy_origin domain initAllocation initRun
    invariant.good
  obtain ⟨z0, s0, good0, zalloc, zfree, _⟩ := initial
  have zEq : z0 = z := Option.some.inj
    (good0.live.hz.symm.trans invariant.good.live.hz)
  subst z0
  have allocator : DefAlloc z := ⟨zalloc, zfree⟩
  obtain ⟨finished, copied, run, copiedJ, copiedEq,
    sourceGet, sourceState⟩ :=
    inflateCopy_default_no_window_J invariant allocator destGet
      different copyAllocation origin.1 origin.2.1
      origin.2.2.1 origin.2.2.2.1 origin.2.2.2.2.1
  exact ⟨z, s, finished, copied, run, copiedJ, copiedEq,
    sourceGet, sourceState⟩

/-- If the first allocator call fails, the actual copy clears only the
destination state binding. It has allocated no live block. -/
theorem inflateCopy_first_allocation_failure
    {h : Heap} {source dest : ZStreamRef} {zs : Nat}
    {z oldDest : ZStream} {s : InflateState}
    (good : Good h source zs z s)
    (allocator : DefAlloc z)
    (destGet : dest.get h = some oldDest)
    (failure : h.allocOk h.nalloc = false) :
    C.run (inflateCopy (some dest) (some source)) h =
      .ok (Z_MEM_ERROR,
        dest.put { h with nalloc := h.nalloc + 1 }
          { oldDest with state := none }) := by
  have sourceCheck := stateCheck_live good.live
  have allocRun : ZALLOCS (some source) h =
      .ok (none, { h with nalloc := h.nalloc + 1 }) := by
    simp [ZALLOCS, ldZ_eq, good.live.hz, allocator.1,
      allocInflateState, failure]
  have destAfter : dest.get { h with nalloc := h.nalloc + 1 } =
      some oldDest := by
    cases dest <;> simpa [ZStreamRef.get] using destGet
  have destRo : dest.isRo = false := by cases dest <;> rfl
  change (inflateCopy (some dest) (some source)) h = _
  simp [inflateCopy, sourceCheck, ldZ_eq, good.live.hz,
    good.live.zst, castI, allocRun, wrZ, destAfter,
    stZStream_ok destAfter destRo]

/-- The first failure has a genuine failed-allocation witness and no new or
released live object, while the destination is safe to end. -/
theorem inflateCopy_first_failure_cleanup
    {h : Heap} {source dest : ZStreamRef} {zs : Nat}
    {z oldDest : ZStream} {s : InflateState}
    (good : Good h source zs z s)
    (allocator : DefAlloc z)
    (destGet : dest.get h = some oldDest)
    (failure : h.allocOk h.nalloc = false) :
    ∃ after,
      C.run (inflateCopy (some dest) (some source)) h =
        .ok (Z_MEM_ERROR, after) ∧
      dest.get after = some { oldDest with state := none } ∧
      AllocationFailed h after ∧
      LiveChange h after (fun _ => False) (fun _ => False) := by
  let middle := { h with nalloc := h.nalloc + 1 }
  let after := dest.put middle { oldDest with state := none }
  have run : C.run (inflateCopy (some dest) (some source)) h =
      .ok (Z_MEM_ERROR, after) :=
    inflateCopy_first_allocation_failure good allocator destGet failure
  have destMiddle : dest.get middle = some oldDest := by
    cases dest <;> simpa [middle, ZStreamRef.get] using destGet
  have destState : dest.get after = some { oldDest with state := none } := by
    simp [after, ZStreamRef.get_put, destMiddle]
  have failed : AllocationFailed h after := by
    refine ⟨h.nalloc, Nat.le_refl _, ?_, failure⟩
    simp only [after, ZStreamRef.put_nalloc, middle]
    omega
  have shapeMiddle : Shape h middle := by
    intro b
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have shapeAfter : Shape middle after := shape_put destMiddle _
  have shape : Shape h after := shapeMiddle.trans shapeAfter
  refine ⟨after, run, destState, failed, ?_⟩
  intro b
  simpa only [LiveChange, Bool.not_eq_true, not_false_eq_true, and_true,
    or_false] using (shape.live b)

#print axioms inflate_default_copy_origin
#print axioms inflate_default_copy_ready
#print axioms inflateCopy_first_allocation_failure
#print axioms inflateCopy_first_failure_cleanup
#print axioms CopyTableOrigin.dynamic_geometry
#print axioms copy_next_diff_safe
#print axioms copy_dist_diff_safe
#print axioms copy_state_allocation_success
#print axioms copy_stream_after_allocation
#print axioms copy_state_after_zeroed_stream
#print axioms inflateCopy_default_no_window_exec
#print axioms copy_allocIst_byte_view_sizes
#print axioms inflateCopy_default_no_window_good
#print axioms inflateCopy_default_no_window_J
#print axioms inflateCopy_after_default_init_success
end Zlib.Inflate.Proofs
