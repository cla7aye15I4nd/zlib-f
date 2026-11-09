import ZlibF.Proof.«inflate.c.copy-both-origin»
import ZlibF.Proof.«inflate.c.record-frame»
namespace Zlib.Inflate.Proofs.CopyResource
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem inflateCopy_dynamic_window_contents
    {h : Heap} {source dest : ZStreamRef} {zs nextOff distOff : Nat}
    {z oldDest : ZStream} {s : InflateState}
    (good : Good h source zs z s)
    (allocator : DefAlloc z)
    (destGet : dest.get h = some oldDest)
    (different : source ≠ dest)
    (first : h.allocOk h.nalloc = true)
    (second : h.allocOk (h.nalloc + 1) = true)
    (window : s.window ≠ .null)
    (nextPtr : s.next = .ref (.istate_codes zs) nextOff)
    (nextBound : nextOff ≤ 1444)
    (len0 : s.lencode = .ref (.istate_codes zs) 0)
    (distPtr : s.distcode = .ref (.istate_codes zs) distOff)
    (distBound : distOff ≤ 1443) :
    ∃ finished,
      C.run (inflateCopy (some dest) (some source)) h = .ok (Z_OK, finished) ∧
      source.get finished = some z ∧ finished.istates zs = some s ∧
      dest.get finished = some { z with state := some (.inflate h.nextBlk) } ∧
      finished.istates h.nextBlk =
        some (copiedGeneric dest zs h.nextBlk nextOff distOff (.ref (.blk (h.nextBlk + 1)) 0) s) ∧
      ∃ sourceArray w, s.window = .ref (.blk w) 0 ∧ h.bytes w = some sourceArray ∧
        finished = copiedWindowHeap h dest z s
        (copiedGeneric dest zs h.nextBlk nextOff distOff
          (.ref (.blk (h.nextBlk + 1)) 0) s) sourceArray := by
  have sourceCheck := stateCheck_live good.live
  have firstRun := (copy_state_allocation_success good allocator first).1
  change (ZALLOCS (some source)) h = _ at firstRun
  let stateAllocated := allocIstHeap h (InflateState.garbage (h.garbage h.nalloc))
  let zeroed := allocIstHeap h InflateState.zeroed
  let size := 2 ^ s.wbits.toNat
  let windowAllocated := Zlib.Zutil.Proofs.allocHeap zeroed size
  let windowRef : BPtr := .ref (.blk zeroed.nextBlk) 0
  have zeroGet : stateAllocated.istates h.nextBlk =
      some (InflateState.garbage (h.garbage h.nalloc)) := by
    simp [stateAllocated]
  have zeroRun : stInflateState (some (.tab h.nextBlk)) InflateState.zeroed stateAllocated =
      .ok ((), zeroed) := by
    simpa [zeroed, stateAllocated, setI, allocIstHeap, upd_upd] using
      (stInflateState_tab (i := h.nextBlk) (v' := InflateState.zeroed) zeroGet)
  simp only [stateAllocated] at zeroRun
  have distinct : zs ≠ h.nextBlk := by
    intro equal
    have live : h.live zs := by simp [Heap.live, good.live.hs]
    exact good.fresh zs (by omega) live
  have sourceZero : source.get zeroed = some z := by
    rw [ZStreamRef.get_allocIst]
    exact good.live.hz
  have stateZero : zeroed.istates zs = some s := by
    rw [allocIstHeap_istates_ne _ _ _ distinct]
    exact good.live.hs
  have shift : shl32 1 s.wbits = pure ((1 : UInt32) <<< s.wbits) :=
    shl32_one good.inv.win.wbits
  have windowRun : ZALLOCB (some source) ((1 : UInt32) <<< s.wbits) 1 zeroed =
      .ok (windowRef, windowAllocated) := by
    simpa [zeroed, windowRef, windowAllocated, size] using
      (inflateCopy_window_allocation_success good allocator second)
  have sourceWindow : source.get windowAllocated = some z := by
    rw [ZStreamRef.get_allocHeap, sourceZero]
  have destWindow : dest.get windowAllocated = some oldDest := by
    rw [ZStreamRef.get_allocHeap, ZStreamRef.get_allocIst]
    exact destGet
  have stateWindow : windowAllocated.istates zs = some s := by
    simpa [windowAllocated, Zlib.Zutil.Proofs.allocHeap] using stateZero
  have freshWindowState : windowAllocated.istates h.nextBlk = some InflateState.zeroed := by
    simp [windowAllocated, zeroed, Zlib.Zutil.Proofs.allocHeap, allocIstHeap]
  have destRo : dest.isRo = false := by cases dest <;> rfl
  have copyZRun : copyZStream (some dest) (some source) windowAllocated =
      .ok ((), dest.put windowAllocated z) := by
    simp [copyZStream, different.symm, ldZ_eq, sourceWindow,
      stZStream_ok destWindow destRo]
  let copiedStream := dest.put windowAllocated z
  have sourceCopied : copiedStream.istates zs = some s := by
    rw [ZStreamRef.put_istates]
    exact stateWindow
  have destCopied : copiedStream.istates h.nextBlk = some InflateState.zeroed := by
    rw [ZStreamRef.put_istates]
    exact freshWindowState
  have copyIRun : copyInflateState (some (.tab h.nextBlk))
      (some (.tab zs)) copiedStream =
      .ok ((), setI copiedStream h.nextBlk s) := by
    simp [copyInflateState, distinct.symm,
      ldInflateState_tab sourceCopied,
      stInflateState_tab destCopied, setI]
  simp only [copiedStream] at copyIRun
  let copied := setI copiedStream h.nextBlk s
  let backState := { s with strm := some dest }
  let backlinked := setI copied h.nextBlk backState
  have copyGet : copied.istates h.nextBlk = some s := by simp [copied]
  have backlinkRun : wrS (some (.tab h.nextBlk))
      (fun v => { v with strm := some dest }) copied =
      .ok ((), backlinked) := by
    simp [wrS, ldInflateState_tab copyGet,
      stInflateState_tab copyGet, backlinked, backState, setI]
  simp only [copied, copiedStream] at backlinkRun
  have sourceAfterBacklink : backlinked.istates zs = some s := by
    rw [setI_istates_ne _ _ _ _ distinct,
      setI_istates_ne _ _ _ _ distinct,
      ZStreamRef.put_istates]
    exact stateWindow
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
  have lenGet : afterLen.istates h.nextBlk = some lenState := by simp [afterLen]
  have codeSize : s.codes.size = 1444 := good.inv.wf.2.2
  have distDiff : Ptr.diff (.ref (CodeRef.istate_codes zs) distOff)
      (.ref (CodeRef.istate_codes zs) 0) afterLen =
        .ok (Int64.ofInt (distOff : Int), afterLen) :=
    copy_codes_off_diff sourceAfterLen codeSize (by omega)
  have distToInt : (Int64.ofInt (distOff : Int)).toInt = distOff := by
    rw [Int64.toInt_ofInt_of_le (by omega) (by omega)]
  have distAdd : Ptr.add (.ref (CodeRef.istate_codes h.nextBlk) 0) (distOff : Int)
      afterLen = .ok (.ref (CodeRef.istate_codes h.nextBlk) distOff, afterLen) :=
    copy_codes_off_add lenGet (by simpa [lenState, backState] using codeSize) (by omega)
  let distState := { lenState with distcode := .ref (.istate_codes h.nextBlk) distOff }
  let afterDist := setI afterLen h.nextBlk distState
  have distRun : wrS (some (.tab h.nextBlk))
      (fun v => { v with distcode := .ref (.istate_codes h.nextBlk) distOff })
      afterLen = .ok ((), afterDist) := by
    simp [wrI_eq, lenGet, afterDist, distState]
  have sourceAfterDist : afterDist.istates zs = some s := by
    rw [setI_istates_ne _ _ _ _ distinct]
    exact sourceAfterLen
  have distGet : afterDist.istates h.nextBlk = some distState := by simp [afterDist]
  have nextDiff : Ptr.diff (.ref (CodeRef.istate_codes zs) nextOff)
      (.ref (CodeRef.istate_codes zs) 0) afterDist =
        .ok (Int64.ofInt (nextOff : Int), afterDist) :=
    copy_codes_off_diff sourceAfterDist codeSize nextBound
  have nextToInt : (Int64.ofInt (nextOff : Int)).toInt = nextOff := by
    rw [Int64.toInt_ofInt_of_le (by omega) (by omega)]
  have nextAdd : Ptr.add (.ref (CodeRef.istate_codes h.nextBlk) 0) (nextOff : Int)
      afterDist = .ok (.ref (CodeRef.istate_codes h.nextBlk) nextOff, afterDist) :=
    copy_codes_off_add distGet (by simpa [distState, lenState, backState] using codeSize) nextBound
  let nextState := { distState with next := .ref (.istate_codes h.nextBlk) nextOff }
  let afterNext := setI afterDist h.nextBlk nextState
  have nextRun : wrS (some (.tab h.nextBlk))
      (fun v => { v with next := .ref (.istate_codes h.nextBlk) nextOff })
      afterDist = .ok ((), afterNext) := by
    simp [wrI_eq, distGet, afterNext, nextState]
  have nextGet : afterNext.istates h.nextBlk = some nextState := by simp [afterNext]
  rcases good.inv.win.block with noBlock | ⟨w, sourceArray, sourcePtr, sourceArrayGet,
    sourceRo, sourceSize⟩
  · exact False.elim (window noBlock)
  have sourceLive : h.live w := by simp [Heap.live, sourceArrayGet]
  have wBound : w < h.nextBlk := by
    by_cases bound : w < h.nextBlk
    · exact bound
    · exact False.elim (good.fresh w (by omega) sourceLive)
  have windowDifferent : zeroed.nextBlk ≠ w := by
    simp [zeroed, allocIstHeap]
    omega
  let freshArray : Array UInt8 := Array.ofFn (n := size)
    (fun i => Junk.of (zeroed.garbage zeroed.nalloc i.val))
  have bytesEq : afterNext.bytes = windowAllocated.bytes := by
    simp [afterNext, afterDist, afterLen, backlinked, copied, copiedStream]
  have windowArray : afterNext.bytes zeroed.nextBlk = some freshArray := by
    rw [bytesEq]
    simp [windowAllocated, Zlib.Zutil.Proofs.allocHeap, freshArray]
  have sourceArrayNext : afterNext.bytes w = some sourceArray := by
    rw [bytesEq]
    change (upd h.bytes (h.nextBlk + 1)
      (some (Array.ofFn (n := size)
        (fun i => Junk.of (zeroed.garbage zeroed.nalloc i.val))))).get w =
      some sourceArray
    rw [upd_ne _ _ _ _ (by omega)]
    exact sourceArrayGet
  have windowWritable : afterNext.ro zeroed.nextBlk = false := by
    simp [afterNext, afterDist, afterLen, backlinked, copied,
      copiedStream, windowAllocated, Zlib.Zutil.Proofs.allocHeap,
      zeroed, allocIstHeap]
  have count : s.whave.toNat ≤ size := by
    rcases good.inv.win.ws with small | full
    · have hv := good.inv.win.hv
      omega
    · have hv := good.inv.win.hv
      omega
  have freshRoom : 0 + s.whave.toNat ≤ freshArray.size := by
    simpa [freshArray, size] using count
  have sourceRoom : 0 + s.whave.toNat ≤ sourceArray.size := by omega
  let afterMemcpy := { afterNext with bytes := upd afterNext.bytes zeroed.nextBlk (some (copyRange freshArray sourceArray 0 0 s.whave.toNat)) }
  have memcpyRun : memcpyB windowRef s.window s.whave.toNat afterNext =
      .ok ((), afterMemcpy) := by
    rw [sourcePtr]
    simpa [afterMemcpy, windowRef] using
      (memcpyB_blk_ok windowArray sourceArrayNext windowWritable
        windowDifferent freshRoom sourceRoom)
  let windowState := { nextState with window := windowRef }
  let afterWindow := setI afterMemcpy h.nextBlk windowState
  have nextAfterMemcpy : afterMemcpy.istates h.nextBlk = some nextState := by
    simpa [afterMemcpy] using nextGet
  have windowWrite : wrS (some (.tab h.nextBlk))
      (fun v => { v with window := windowRef }) afterMemcpy =
      .ok ((), afterWindow) := by
    simp [wrI_eq, nextAfterMemcpy, afterWindow, windowState]
  have destCopiedStream : dest.get copiedStream = some z := by
    simp [copiedStream, ZStreamRef.get_put, destWindow]
  have destAfterNext : dest.get afterNext = some z := by
    simpa only [afterNext, afterDist, afterLen, backlinked, copied,
      ZStreamRef.get_setI] using destCopiedStream
  have destAfterMemcpy : dest.get afterMemcpy = some z := by
    cases dest <;> simpa [afterMemcpy, ZStreamRef.get] using destAfterNext
  have destAfterWindow : dest.get afterWindow = some z := by
    simpa only [afterWindow, ZStreamRef.get_setI] using destAfterMemcpy
  have destWrite : wrZ (some dest)
      (fun v => { v with state := some (.inflate h.nextBlk) }) afterWindow =
      .ok ((), dest.put afterWindow { z with state := some (.inflate h.nextBlk) }) := by
    simp [wrZ_eq, destAfterWindow]
  let finished := dest.put afterWindow { z with state := some (.inflate h.nextBlk) }
  have run : C.run (inflateCopy (some dest) (some source)) h =
      .ok (Z_OK, finished) := by
    change (inflateCopy (some dest) (some source)) h = _
    simp [inflateCopy, sourceCheck, ldZStream_ok good.live.hz,
      good.live.zst, castI, firstRun, zeroRun,
      ldInflateState_tab stateZero, window, shift,
      windowRun, copyZRun, copyIRun, backlinkRun,
      ldInflateState_tab sourceAfterBacklink, codesP, len0, distPtr, nextPtr, lenRun,
      distDiff, distToInt, distAdd, distRun, nextDiff, nextToInt, nextAdd,
      nextRun, memcpyRun, windowWrite, destWrite,
      StateRef.ofInflateState, finished]
  have sourceCopiedStream : source.get copiedStream = some z :=
    (copy_stream_get_put_other windowAllocated different z).trans sourceWindow
  have sourceAfterNext : source.get afterNext = some z := by
    simpa only [afterNext, afterDist, afterLen, backlinked, copied,
      ZStreamRef.get_setI] using sourceCopiedStream
  have sourceAfterMemcpy : source.get afterMemcpy = some z := by
    cases source <;> simpa [afterMemcpy, ZStreamRef.get] using sourceAfterNext
  have sourceAfterWindow : source.get afterWindow = some z := by
    simpa only [afterWindow, ZStreamRef.get_setI] using sourceAfterMemcpy
  have sourceFinished : source.get finished = some z :=
    (copy_stream_get_put_other afterWindow different _).trans sourceAfterWindow
  have sourceStateFinished : finished.istates zs = some s := by
    simp only [finished, ZStreamRef.put_istates, afterWindow,
      afterMemcpy, afterNext, afterDist, afterLen,
      setI_istates_ne _ _ _ _ distinct]
    exact sourceAfterBacklink
  have destFinished : dest.get finished =
      some { z with state := some (.inflate h.nextBlk) } := by
    simp [finished, ZStreamRef.get_put, destAfterWindow]
  have copiedFinished : finished.istates h.nextBlk =
      some (copiedGeneric dest zs h.nextBlk nextOff distOff (.ref (.blk (h.nextBlk + 1)) 0) s) := by
    simp [finished, afterWindow, afterMemcpy, afterNext, afterDist,
      afterLen, backlinked, copied, windowState, nextState, distState,
      lenState, backState, copiedGeneric, len0, windowRef, zeroed,
      allocIstHeap]
  have heapEq : finished = copiedWindowHeap h dest z s
      (copiedGeneric dest zs h.nextBlk nextOff distOff
        (.ref (.blk (h.nextBlk + 1)) 0) s) sourceArray := by
    cases dest with
    | tab i =>
      simp only [ZStreamRef.get] at destGet
      simp [finished, afterWindow, afterMemcpy, afterNext, afterDist,
      afterLen, backlinked, copied, copiedStream, windowAllocated,
      zeroed, windowState, nextState, distState,
      lenState, backState, copiedWindowHeap, copiedGeneric, len0,
      windowRef, freshArray, Zlib.Zutil.Proofs.allocHeap, allocIstHeap,
      ZStreamRef.put_setI,       setI, ZStreamRef.put, destGet, upd_upd]
      rfl
    | in_gzstate_strm i =>
      simp only [ZStreamRef.get] at destGet
      obtain ⟨g, hg, _⟩ := Option.map_eq_some_iff.mp destGet
      simp [finished, afterWindow, afterMemcpy, afterNext, afterDist,
      afterLen, backlinked, copied, copiedStream, windowAllocated,
      zeroed, windowState, nextState, distState,
      lenState, backState, copiedWindowHeap, copiedGeneric, len0,
      windowRef, freshArray, Zlib.Zutil.Proofs.allocHeap, allocIstHeap,
      ZStreamRef.put_setI,       setI, ZStreamRef.put, hg, upd_upd]
      rfl
  exact ⟨finished, run, sourceFinished, sourceStateFinished,
    destFinished, copiedFinished, sourceArray, w, sourcePtr, sourceArrayGet, heapEq⟩


#print axioms inflateCopy_dynamic_window_contents

theorem inflateCopy_fixed_window_contents
    {h : Heap} {source dest : ZStreamRef} {zs nextOff : Nat}
    {z oldDest : ZStream} {s : InflateState}
    (good : Good h source zs z s)
    (allocator : DefAlloc z)
    (destGet : dest.get h = some oldDest)
    (different : source ≠ dest)
    (first : h.allocOk h.nalloc = true)
    (second : h.allocOk (h.nalloc + 1) = true)
    (window : s.window ≠ .null)
    (nextPtr : s.next = .ref (.istate_codes zs) nextOff)
    (nextBound : nextOff ≤ 1444)
    (fixed : s.lencode = .ref .st_lenfix 0 ∧
      s.distcode = .ref .st_distfix 0) :
    ∃ finished,
      C.run (inflateCopy (some dest) (some source)) h = .ok (Z_OK, finished) ∧
      source.get finished = some z ∧ finished.istates zs = some s ∧
      dest.get finished = some { z with state := some (.inflate h.nextBlk) } ∧
      finished.istates h.nextBlk =
        some (copiedGeneric dest zs h.nextBlk nextOff 0 (.ref (.blk (h.nextBlk + 1)) 0) s) ∧
      ∃ sourceArray w, s.window = .ref (.blk w) 0 ∧ h.bytes w = some sourceArray ∧
        finished = copiedWindowHeap h dest z s
        (copiedGeneric dest zs h.nextBlk nextOff 0
          (.ref (.blk (h.nextBlk + 1)) 0) s) sourceArray := by
  have sourceCheck := stateCheck_live good.live
  have firstRun := (copy_state_allocation_success good allocator first).1
  change (ZALLOCS (some source)) h = _ at firstRun
  let stateAllocated := allocIstHeap h (InflateState.garbage (h.garbage h.nalloc))
  let zeroed := allocIstHeap h InflateState.zeroed
  let size := 2 ^ s.wbits.toNat
  let windowAllocated := Zlib.Zutil.Proofs.allocHeap zeroed size
  let windowRef : BPtr := .ref (.blk zeroed.nextBlk) 0
  have zeroGet : stateAllocated.istates h.nextBlk =
      some (InflateState.garbage (h.garbage h.nalloc)) := by
    simp [stateAllocated]
  have zeroRun : stInflateState (some (.tab h.nextBlk)) InflateState.zeroed stateAllocated =
      .ok ((), zeroed) := by
    simpa [zeroed, stateAllocated, setI, allocIstHeap, upd_upd] using
      (stInflateState_tab (i := h.nextBlk) (v' := InflateState.zeroed) zeroGet)
  simp only [stateAllocated] at zeroRun
  have distinct : zs ≠ h.nextBlk := by
    intro equal
    have live : h.live zs := by simp [Heap.live, good.live.hs]
    exact good.fresh zs (by omega) live
  have sourceZero : source.get zeroed = some z := by
    rw [ZStreamRef.get_allocIst]
    exact good.live.hz
  have stateZero : zeroed.istates zs = some s := by
    rw [allocIstHeap_istates_ne _ _ _ distinct]
    exact good.live.hs
  have shift : shl32 1 s.wbits = pure ((1 : UInt32) <<< s.wbits) :=
    shl32_one good.inv.win.wbits
  have windowRun : ZALLOCB (some source) ((1 : UInt32) <<< s.wbits) 1 zeroed =
      .ok (windowRef, windowAllocated) := by
    simpa [zeroed, windowRef, windowAllocated, size] using
      (inflateCopy_window_allocation_success good allocator second)
  have sourceWindow : source.get windowAllocated = some z := by
    rw [ZStreamRef.get_allocHeap, sourceZero]
  have destWindow : dest.get windowAllocated = some oldDest := by
    rw [ZStreamRef.get_allocHeap, ZStreamRef.get_allocIst]
    exact destGet
  have stateWindow : windowAllocated.istates zs = some s := by
    simpa [windowAllocated, Zlib.Zutil.Proofs.allocHeap] using stateZero
  have freshWindowState : windowAllocated.istates h.nextBlk = some InflateState.zeroed := by
    simp [windowAllocated, zeroed, Zlib.Zutil.Proofs.allocHeap, allocIstHeap]
  have destRo : dest.isRo = false := by cases dest <;> rfl
  have copyZRun : copyZStream (some dest) (some source) windowAllocated =
      .ok ((), dest.put windowAllocated z) := by
    simp [copyZStream, different.symm, ldZ_eq, sourceWindow,
      stZStream_ok destWindow destRo]
  let copiedStream := dest.put windowAllocated z
  have sourceCopied : copiedStream.istates zs = some s := by
    rw [ZStreamRef.put_istates]
    exact stateWindow
  have destCopied : copiedStream.istates h.nextBlk = some InflateState.zeroed := by
    rw [ZStreamRef.put_istates]
    exact freshWindowState
  have copyIRun : copyInflateState (some (.tab h.nextBlk))
      (some (.tab zs)) copiedStream =
      .ok ((), setI copiedStream h.nextBlk s) := by
    simp [copyInflateState, distinct.symm,
      ldInflateState_tab sourceCopied,
      stInflateState_tab destCopied, setI]
  simp only [copiedStream] at copyIRun
  let copied := setI copiedStream h.nextBlk s
  let backState := { s with strm := some dest }
  let backlinked := setI copied h.nextBlk backState
  have copyGet : copied.istates h.nextBlk = some s := by simp [copied]
  have backlinkRun : wrS (some (.tab h.nextBlk))
      (fun v => { v with strm := some dest }) copied =
      .ok ((), backlinked) := by
    simp [wrS, ldInflateState_tab copyGet,
      stInflateState_tab copyGet, backlinked, backState, setI]
  simp only [copied, copiedStream] at backlinkRun
  have sourceAfterBacklink : backlinked.istates zs = some s := by
    rw [setI_istates_ne _ _ _ _ distinct,
      setI_istates_ne _ _ _ _ distinct,
      ZStreamRef.put_istates]
    exact stateWindow
  have backGet : backlinked.istates h.nextBlk = some backState := by
    simp [backlinked, backState]
  have codeSize : s.codes.size = 1444 := good.inv.wf.2.2
  have nextDiff : Ptr.diff (.ref (CodeRef.istate_codes zs) nextOff)
      (.ref (CodeRef.istate_codes zs) 0) backlinked =
        .ok (Int64.ofInt (nextOff : Int), backlinked) :=
    copy_codes_off_diff sourceAfterBacklink codeSize nextBound
  have nextToInt : (Int64.ofInt (nextOff : Int)).toInt = nextOff := by
    rw [Int64.toInt_ofInt_of_le (by omega) (by omega)]
  have nextAdd : Ptr.add (.ref (CodeRef.istate_codes h.nextBlk) 0) (nextOff : Int)
      backlinked = .ok (.ref (CodeRef.istate_codes h.nextBlk) nextOff, backlinked) :=
    copy_codes_off_add backGet (by simpa [backState] using codeSize) nextBound
  let nextState := { backState with next := .ref (.istate_codes h.nextBlk) nextOff }
  let afterNext := setI backlinked h.nextBlk nextState
  have nextRun : wrS (some (.tab h.nextBlk))
      (fun v => { v with next := .ref (.istate_codes h.nextBlk) nextOff })
      backlinked = .ok ((), afterNext) := by
    simp [wrI_eq, backGet, afterNext, nextState]
  have nextGet : afterNext.istates h.nextBlk = some nextState := by
    simp [afterNext]
  rcases good.inv.win.block with noBlock | ⟨w, sourceArray, sourcePtr, sourceArrayGet,
    sourceRo, sourceSize⟩
  · exact False.elim (window noBlock)
  have sourceLive : h.live w := by simp [Heap.live, sourceArrayGet]
  have wBound : w < h.nextBlk := by
    by_cases bound : w < h.nextBlk
    · exact bound
    · exact False.elim (good.fresh w (by omega) sourceLive)
  have windowDifferent : zeroed.nextBlk ≠ w := by
    simp [zeroed, allocIstHeap]
    omega
  let freshArray : Array UInt8 := Array.ofFn (n := size)
    (fun i => Junk.of (zeroed.garbage zeroed.nalloc i.val))
  have bytesEq : afterNext.bytes = windowAllocated.bytes := by
    simp [afterNext, backlinked, copied, copiedStream]
  have windowArray : afterNext.bytes zeroed.nextBlk = some freshArray := by
    rw [bytesEq]
    simp [windowAllocated, Zlib.Zutil.Proofs.allocHeap, freshArray]
  have sourceArrayNext : afterNext.bytes w = some sourceArray := by
    rw [bytesEq]
    change (upd h.bytes (h.nextBlk + 1)
      (some (Array.ofFn (n := size)
        (fun i => Junk.of (zeroed.garbage zeroed.nalloc i.val))))).get w =
      some sourceArray
    rw [upd_ne _ _ _ _ (by omega)]
    exact sourceArrayGet
  have windowWritable : afterNext.ro zeroed.nextBlk = false := by
    simp [afterNext, backlinked, copied,
      copiedStream, windowAllocated, Zlib.Zutil.Proofs.allocHeap,
      zeroed, allocIstHeap]
  have count : s.whave.toNat ≤ size := by
    rcases good.inv.win.ws with small | full
    · have hv := good.inv.win.hv
      omega
    · have hv := good.inv.win.hv
      omega
  have freshRoom : 0 + s.whave.toNat ≤ freshArray.size := by
    simpa [freshArray, size] using count
  have sourceRoom : 0 + s.whave.toNat ≤ sourceArray.size := by omega
  let afterMemcpy := { afterNext with bytes := upd afterNext.bytes zeroed.nextBlk (some (copyRange freshArray sourceArray 0 0 s.whave.toNat)) }
  have memcpyRun : memcpyB windowRef s.window s.whave.toNat afterNext =
      .ok ((), afterMemcpy) := by
    rw [sourcePtr]
    simpa [afterMemcpy, windowRef] using
      (memcpyB_blk_ok windowArray sourceArrayNext windowWritable
        windowDifferent freshRoom sourceRoom)
  let windowState := { nextState with window := windowRef }
  let afterWindow := setI afterMemcpy h.nextBlk windowState
  have nextAfterMemcpy : afterMemcpy.istates h.nextBlk = some nextState := by
    simpa [afterMemcpy] using nextGet
  have windowWrite : wrS (some (.tab h.nextBlk))
      (fun v => { v with window := windowRef }) afterMemcpy =
      .ok ((), afterWindow) := by
    simp [wrI_eq, nextAfterMemcpy, afterWindow, windowState]
  have destCopiedStream : dest.get copiedStream = some z := by
    simp [copiedStream, ZStreamRef.get_put, destWindow]
  have destAfterNext : dest.get afterNext = some z := by
    simpa only [afterNext, backlinked, copied,
      ZStreamRef.get_setI] using destCopiedStream
  have destAfterMemcpy : dest.get afterMemcpy = some z := by
    cases dest <;> simpa [afterMemcpy, ZStreamRef.get] using destAfterNext
  have destAfterWindow : dest.get afterWindow = some z := by
    simpa only [afterWindow, ZStreamRef.get_setI] using destAfterMemcpy
  have destWrite : wrZ (some dest)
      (fun v => { v with state := some (.inflate h.nextBlk) }) afterWindow =
      .ok ((), dest.put afterWindow { z with state := some (.inflate h.nextBlk) }) := by
    simp [wrZ_eq, destAfterWindow]
  let finished := dest.put afterWindow { z with state := some (.inflate h.nextBlk) }
  have run : C.run (inflateCopy (some dest) (some source)) h =
      .ok (Z_OK, finished) := by
    change (inflateCopy (some dest) (some source)) h = _
    simp [inflateCopy, sourceCheck, ldZStream_ok good.live.hz,
      good.live.zst, castI, firstRun, zeroRun,
      ldInflateState_tab stateZero, window, shift,
      windowRun, copyZRun, copyIRun, backlinkRun,
      ldInflateState_tab sourceAfterBacklink, codesP, fixed.1, nextPtr,
      nextDiff, nextToInt, nextAdd,
      nextRun, memcpyRun, windowWrite, destWrite,
      StateRef.ofInflateState, finished]
  have sourceCopiedStream : source.get copiedStream = some z :=
    (copy_stream_get_put_other windowAllocated different z).trans sourceWindow
  have sourceAfterNext : source.get afterNext = some z := by
    simpa only [afterNext, backlinked, copied,
      ZStreamRef.get_setI] using sourceCopiedStream
  have sourceAfterMemcpy : source.get afterMemcpy = some z := by
    cases source <;> simpa [afterMemcpy, ZStreamRef.get] using sourceAfterNext
  have sourceAfterWindow : source.get afterWindow = some z := by
    simpa only [afterWindow, ZStreamRef.get_setI] using sourceAfterMemcpy
  have sourceFinished : source.get finished = some z :=
    (copy_stream_get_put_other afterWindow different _).trans sourceAfterWindow
  have sourceStateFinished : finished.istates zs = some s := by
    simp only [finished, ZStreamRef.put_istates, afterWindow,
      afterMemcpy, afterNext,
      setI_istates_ne _ _ _ _ distinct]
    exact sourceAfterBacklink
  have destFinished : dest.get finished =
      some { z with state := some (.inflate h.nextBlk) } := by
    simp [finished, ZStreamRef.get_put, destAfterWindow]
  have copiedFinished : finished.istates h.nextBlk =
      some (copiedGeneric dest zs h.nextBlk nextOff 0 (.ref (.blk (h.nextBlk + 1)) 0) s) := by
    simp [finished, afterWindow, afterMemcpy, afterNext,
      backlinked, copied, windowState, nextState,
      backState, copiedGeneric, fixed.1, fixed.2, windowRef, zeroed,
      allocIstHeap]
  have heapEq : finished = copiedWindowHeap h dest z s
      (copiedGeneric dest zs h.nextBlk nextOff 0
        (.ref (.blk (h.nextBlk + 1)) 0) s) sourceArray := by
    cases dest with
    | tab i =>
      simp only [ZStreamRef.get] at destGet
      simp [finished, afterWindow, afterMemcpy, afterNext,
        backlinked, copied, copiedStream, windowAllocated,
        zeroed, windowState, nextState,
        backState, copiedWindowHeap, copiedGeneric, fixed.1, fixed.2,
        windowRef, freshArray, Zlib.Zutil.Proofs.allocHeap, allocIstHeap,
        ZStreamRef.put_setI,         setI, ZStreamRef.put, destGet, upd_upd]
      rfl
    | in_gzstate_strm i =>
      simp only [ZStreamRef.get] at destGet
      obtain ⟨g, hg, _⟩ := Option.map_eq_some_iff.mp destGet
      simp [finished, afterWindow, afterMemcpy, afterNext,
        backlinked, copied, copiedStream, windowAllocated,
        zeroed, windowState, nextState,
        backState, copiedWindowHeap, copiedGeneric, fixed.1, fixed.2,
        windowRef, freshArray, Zlib.Zutil.Proofs.allocHeap, allocIstHeap,
        ZStreamRef.put_setI,         setI, ZStreamRef.put, hg, upd_upd]
      rfl
  exact ⟨finished, run, sourceFinished, sourceStateFinished,
    destFinished, copiedFinished, sourceArray, w, sourcePtr, sourceArrayGet, heapEq⟩


#print axioms inflateCopy_fixed_window_contents

end Zlib.Inflate.Proofs.CopyResource
