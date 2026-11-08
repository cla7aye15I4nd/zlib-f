import ZlibF.Proof.«inflate.c.copy-origin»
import ZlibF.Proof.«inflate.c.uw»
import ZlibF.Proof.«zutil.c»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The second allocation failure in the actual window-present copy frees
the freshly allocated state and clears the destination state pointer. -/
theorem inflateCopy_window_allocation_failure
    {h : Heap} {source dest : ZStreamRef} {zs : Nat}
    {z oldDest : ZStream} {s : InflateState}
    (good : Good h source zs z s)
    (allocator : DefAlloc z)
    (destGet : dest.get h = some oldDest)
    (first : h.allocOk h.nalloc = true)
    (window : s.window ≠ .null)
    (second : h.allocOk (h.nalloc + 1) = false) :
    let zeroed := allocIstHeap h InflateState.zeroed
    let failed := { zeroed with nalloc := zeroed.nalloc + 1 }
    C.run (inflateCopy (some dest) (some source)) h =
      .ok (Z_MEM_ERROR,
        dest.put (freeIst failed h.nextBlk) { oldDest with state := none }) := by
  dsimp only
  have sourceCheck := stateCheck_live good.live
  have firstRun := (copy_state_allocation_success good allocator first).1
  change (ZALLOCS (some source)) h = _ at firstRun
  let allocated := allocIstHeap h (InflateState.garbage (h.garbage h.nalloc))
  let zeroed := allocIstHeap h InflateState.zeroed
  have zeroGet : allocated.istates h.nextBlk =
      some (InflateState.garbage (h.garbage h.nalloc)) := by
    simp [allocated]
  have zeroRun : stInflateState (some (.tab h.nextBlk)) InflateState.zeroed allocated =
      .ok ((), zeroed) := by
    simpa [zeroed, allocated, setI, allocIstHeap, upd_upd] using
      (stInflateState_tab (i := h.nextBlk) (v' := InflateState.zeroed) zeroGet)
  simp only [allocated] at zeroRun
  have distinct : zs ≠ h.nextBlk := by
    intro equal
    have live : h.live zs := by simp [Heap.live, good.live.hs]
    exact good.fresh zs (by omega) live
  have sourceState : zeroed.istates zs = some s := by
    rw [allocIstHeap_istates_ne _ _ _ distinct]
    exact good.live.hs
  have sourceZero : source.get zeroed = some z := by
    rw [ZStreamRef.get_allocIst]
    exact good.live.hz
  have shift : shl32 1 s.wbits = pure ((1 : UInt32) <<< s.wbits) :=
    shl32_one good.inv.win.wbits
  have secondZero : zeroed.allocOk zeroed.nalloc = false := by
    simpa [zeroed, allocIstHeap] using second
  let failed : Heap := { zeroed with nalloc := zeroed.nalloc + 1 }
  have windowRun : ZALLOCB (some source) ((1 : UInt32) <<< s.wbits) 1 zeroed =
      .ok (.null, failed) := by
    rw [zallocb_run sourceZero allocator.1]
    simpa [failed, Zlib.Zutil.Proofs.failHeap] using
      Zlib.Zutil.Proofs.zcalloc_fail_run zeroed z.«opaque»
        ((1 : UInt32) <<< s.wbits) 1 (by simp [secondZero])
  have sourceFailed : source.get failed = some z := by
    cases source <;> simpa [failed, ZStreamRef.get] using sourceZero
  have freshGet : failed.istates h.nextBlk = some InflateState.zeroed := by
    simp [failed, zeroed]
  have freeRun : ZFREES (some source) (some (.tab h.nextBlk)) failed =
      .ok ((), freeIst failed h.nextBlk) :=
    zfrees_run sourceFailed allocator.2 freshGet
  have destFreed : dest.get (freeIst failed h.nextBlk) = some oldDest := by
    rw [ZStreamRef.get_freeIst]
    cases dest <;> simpa [failed, zeroed, allocated, ZStreamRef.get] using destGet
  have destRo : dest.isRo = false := by cases dest <;> rfl
  have clearRun : wrZ (some dest) (fun v => { v with state := none })
      (freeIst failed h.nextBlk) =
      .ok ((), dest.put (freeIst failed h.nextBlk) { oldDest with state := none }) := by
    simp [wrZ_eq, destFreed]
  change (inflateCopy (some dest) (some source)) h = _
  simp [inflateCopy, sourceCheck, ldZStream_ok good.live.hz,
    good.live.zst, castI, firstRun, zeroRun,
    ldInflateState_tab sourceState, window, shift,
    windowRun, freeRun, clearRun]
  simp [failed, zeroed, allocIstHeap, Nat.add_assoc]

#print axioms inflateCopy_window_allocation_failure
end Zlib.Inflate.Proofs
