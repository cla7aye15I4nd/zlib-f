import ZlibF.Proof.«inflate.c.copy-generic-exec»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem inflateCopy_fixed_no_window_exec
    {h : Heap} {source dest : ZStreamRef} {zs nextOff : Nat}
    {z oldDest : ZStream} {s : InflateState}
    (good : Good h source zs z s)
    (allocator : DefAlloc z)
    (destGet : dest.get h = some oldDest)
    (different : source ≠ dest)
    (allocation : h.allocOk h.nalloc = true)
    (noWindow : s.window = .null)
    (nextPtr : s.next = .ref (.istate_codes zs) nextOff)
    (nextBound : nextOff ≤ 1444)
    (fixed : s.lencode = .ref .st_lenfix 0 ∧
      s.distcode = .ref .st_distfix 0) :
    ∃ after,
      C.run (inflateCopy (some dest) (some source)) h = .ok (Z_OK, after) ∧
      source.get after = some z ∧ after.istates zs = some s ∧
      dest.get after = some { z with state := some (.inflate h.nextBlk) } ∧
      ∃ copied, after.istates h.nextBlk = some copied ∧
        copied = copiedGeneric dest zs h.nextBlk nextOff 0 .null s ∧
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
  let windowState := { nextState with window := (.null : BPtr) }
  let afterWindow := setI afterNext h.nextBlk windowState
  have windowRun : wrS (some (.tab h.nextBlk))
      (fun v => { v with window := (.null : BPtr) })
      afterNext = .ok ((), afterWindow) := by
    simp [wrI_eq, nextGet, afterWindow, windowState]
  have destAfterWindow : dest.get afterWindow = some z := by
    simp only [afterWindow, afterNext,
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
    ldInflateState_tab zeroSource, noWindow, nextPtr, fixed.1,
    copyZRun, copyIRun, backlinkRun,
    ldInflateState_tab sourceAfterBacklink, codesP,
    nextDiff, nextToInt, nextAdd,
    nextRun, windowRun, destRun, StateRef.ofInflateState,
    finished]
  have sourceAfterWindow : source.get afterWindow = some z := by
    simp only [afterWindow, afterNext,
      backlinked, copied, ZStreamRef.get_setI]
    exact (copy_stream_get_put_other zeroed different z).trans sourceZero
  have sourceFinished : source.get finished = some z := by
    exact (copy_stream_get_put_other afterWindow different _).trans sourceAfterWindow
  have sourceStateFinished : finished.istates zs = some s := by
    simp only [finished, ZStreamRef.put_istates,
      afterWindow, afterNext,
      backlinked, copied, setI_istates_ne _ _ _ _ distinct,
      ZStreamRef.put_istates, zeroSource]
  have destFinished : dest.get finished =
      some { z with state := some (.inflate h.nextBlk) } := by
    simp [finished, ZStreamRef.get_put, destAfterWindow]
  have copiedFinished : finished.istates h.nextBlk = some windowState := by
    simp [finished, afterWindow]
  have copiedShape : windowState = copiedGeneric dest zs h.nextBlk nextOff 0 .null s := by
    simp [copiedGeneric, fixed.1, fixed.2, windowState, nextState,
       backState]
  have finalHeapEq : finished =
      allocIstHeap
        (dest.put h { z with state := some (.inflate h.nextBlk) })
        (copiedGeneric dest zs h.nextBlk nextOff 0 .null s) := by
    simp [finished, afterWindow, afterNext,
      backlinked, copied, zeroed, allocated, windowState, nextState,
       backState, copiedGeneric, fixed.1, fixed.2,
      ZStreamRef.put_setI, ZStreamRef.put_allocIst,
      setI_allocIst, ZStreamRef.put_put]
  exact ⟨finished, run, sourceFinished, sourceStateFinished,
    destFinished, windowState, copiedFinished, copiedShape,
    by rw [copiedShape]; exact finalHeapEq⟩

/-- The actual no-window copy preserves J while a fixed block is active.
The static table pointers remain unchanged; only `next` is relocated. -/
theorem inflateCopy_fixed_no_window_J
    {h : Heap} {source dest : ZStreamRef} {zs : Nat}
    {z oldDest : ZStream} {s : InflateState}
    (invariant : DefaultStateJ h source zs z s)
    (allocator : DefAlloc z)
    (destGet : dest.get h = some oldDest)
    (different : source ≠ dest)
    (allocation : h.allocOk h.nalloc = true)
    (noWindow : s.window = .null)
    (fixed : s.lencode = .ref .st_lenfix 0 ∧
      s.distcode = .ref .st_distfix 0) :
    ∃ after copied,
      C.run (inflateCopy (some dest) (some source)) h = .ok (Z_OK, after) ∧
      DefaultStateJ after dest h.nextBlk
        { z with state := some (.inflate h.nextBlk) } copied ∧
      source.get after = some z ∧ after.istates zs = some s := by
  obtain ⟨nextOff, nextPtr, nextBound⟩ := invariant.good.inv.ptr.1
  obtain ⟨after, run, sourceGet, sourceState, _, copied, _,
    copiedEq, heapEq⟩ :=
    inflateCopy_fixed_no_window_exec invariant.good allocator destGet
      different allocation noWindow nextPtr nextBound fixed
  subst copied
  have nextJ := copiedGeneric_no_window_J invariant destGet
    (Or.inr fixed) nextBound (by decide : 0 ≤ 1443) (by intro impossible; cases fixed.1.symm.trans impossible) noWindow
  refine ⟨after, copiedGeneric dest zs h.nextBlk nextOff 0 .null s,
    run, ?_, sourceGet, sourceState⟩
  rw [heapEq]
  exact nextJ

#print axioms inflateCopy_fixed_no_window_J

/-- Both source-derived table origins have a successful, J-preserving actual
copy path without a window. -/
theorem inflateCopy_origin_no_window_J
    {h : Heap} {source dest : ZStreamRef} {zs : Nat}
    {z oldDest : ZStream} {s : InflateState}
    (invariant : DefaultStateJ h source zs z s)
    (allocator : DefAlloc z)
    (destGet : dest.get h = some oldDest)
    (different : source ≠ dest)
    (allocation : h.allocOk h.nalloc = true)
    (noWindow : s.window = .null)
    (origin : CopyTableOrigin zs s) :
    ∃ after copied,
      C.run (inflateCopy (some dest) (some source)) h = .ok (Z_OK, after) ∧
      DefaultStateJ after dest h.nextBlk
        { z with state := some (.inflate h.nextBlk) } copied ∧
      source.get after = some z ∧ after.istates zs = some s := by
  rcases origin with dynamic | fixed
  · exact inflateCopy_dynamic_no_window_J invariant allocator destGet
      different allocation noWindow dynamic
  · exact inflateCopy_fixed_no_window_J invariant allocator destGet
      different allocation noWindow fixed

#print axioms inflateCopy_origin_no_window_J

end Zlib.Inflate.Proofs
