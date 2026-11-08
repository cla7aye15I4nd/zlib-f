import ZlibF.Proof.«inflate.c.copy-generic-state»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem inflateCopy_dynamic_no_window_exec
    {h : Heap} {source dest : ZStreamRef} {zs nextOff distOff : Nat}
    {z oldDest : ZStream} {s : InflateState}
    (good : Good h source zs z s)
    (allocator : DefAlloc z)
    (destGet : dest.get h = some oldDest)
    (different : source ≠ dest)
    (allocation : h.allocOk h.nalloc = true)
    (noWindow : s.window = .null)
    (nextPtr : s.next = .ref (.istate_codes zs) nextOff)
    (nextBound : nextOff ≤ 1444)
    (len0 : s.lencode = .ref (.istate_codes zs) 0)
    (distPtr : s.distcode = .ref (.istate_codes zs) distOff)
    (distBound : distOff ≤ 1443) :
    ∃ after,
      C.run (inflateCopy (some dest) (some source)) h = .ok (Z_OK, after) ∧
      source.get after = some z ∧ after.istates zs = some s ∧
      dest.get after = some { z with state := some (.inflate h.nextBlk) } ∧
      ∃ copied, after.istates h.nextBlk = some copied ∧
        copied = copiedGeneric dest zs h.nextBlk nextOff distOff .null s ∧
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
  have distGet : afterDist.istates h.nextBlk = some distState := by
    simp [afterDist]
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
    ldInflateState_tab zeroSource, noWindow, nextPtr, len0, distPtr,
    copyZRun, copyIRun, backlinkRun,
    ldInflateState_tab sourceAfterBacklink, codesP, lenRun,
    distDiff, distToInt, distAdd, distRun, nextDiff, nextToInt, nextAdd,
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
  have copiedShape : windowState = copiedGeneric dest zs h.nextBlk nextOff distOff .null s := by
    simp [copiedGeneric, len0, windowState, nextState,
      distState, lenState, backState]
  have finalHeapEq : finished =
      allocIstHeap
        (dest.put h { z with state := some (.inflate h.nextBlk) })
        (copiedGeneric dest zs h.nextBlk nextOff distOff .null s) := by
    simp [finished, afterWindow, afterNext, afterDist, afterLen,
      backlinked, copied, zeroed, allocated, windowState, nextState,
      distState, lenState, backState, copiedGeneric, len0,
      ZStreamRef.put_setI, ZStreamRef.put_allocIst,
      setI_allocIst, ZStreamRef.put_put]
  exact ⟨finished, run, sourceFinished, sourceStateFinished,
    destFinished, windowState, copiedFinished, copiedShape,
    by rw [copiedShape]; exact finalHeapEq⟩

/-- The actual no-window copy preserves J in every dynamic-table mode, with
the source offsets supplied by `Good` rather than assumed to be zero. -/
theorem inflateCopy_dynamic_no_window_J
    {h : Heap} {source dest : ZStreamRef} {zs : Nat}
    {z oldDest : ZStream} {s : InflateState}
    (invariant : DefaultStateJ h source zs z s)
    (allocator : DefAlloc z)
    (destGet : dest.get h = some oldDest)
    (different : source ≠ dest)
    (allocation : h.allocOk h.nalloc = true)
    (noWindow : s.window = .null)
    (dynamic : s.lencode = .ref (.istate_codes zs) 0) :
    ∃ after copied,
      C.run (inflateCopy (some dest) (some source)) h = .ok (Z_OK, after) ∧
      DefaultStateJ after dest h.nextBlk
        { z with state := some (.inflate h.nextBlk) } copied ∧
      source.get after = some z ∧ after.istates zs = some s := by
  obtain ⟨nextOff, distOff, nextPtr, nextBound,
    distPtr, distBound, _, _⟩ :=
    CopyTableOrigin.dynamic_geometry invariant.good dynamic
  obtain ⟨after, run, sourceGet, sourceState, _, copied, _,
    copiedEq, heapEq⟩ :=
    inflateCopy_dynamic_no_window_exec invariant.good allocator destGet
      different allocation noWindow nextPtr nextBound dynamic distPtr distBound
  subst copied
  have nextJ := copiedGeneric_no_window_J invariant destGet
    (Or.inl dynamic) nextBound distBound (fun _ => distPtr) noWindow
  refine ⟨after, copiedGeneric dest zs h.nextBlk nextOff distOff .null s,
    run, ?_, sourceGet, sourceState⟩
  rw [heapEq]
  exact nextJ

#print axioms inflateCopy_dynamic_no_window_J

end Zlib.Inflate.Proofs
