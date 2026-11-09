import ZlibF.Proof.«inflate.c.sync-search-origin»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Actual four-byte local cleanup retains both history origins. -/
theorem DefaultOriginState.free_local {h : Heap} {r : ZStreamRef} {zs block : Nat}
    {z : ZStream} {s : InflateState} {array : Array UInt8}
    (before : DefaultOriginState h r zs z s) (get : h.bytes block = some array) (size : array.size = 4) :
    DefaultOriginState (freeWin h (.ref (.blk block) 0)) r zs z s :=
  ⟨before.toDefaultStateJ.free_local get size, before.flagsOrigin, before.tableOrigin⟩

/-- The actual input-search tail followed by its one real local free
retains the strengthened state. The scratch block survives the tail
because both actual default tail branches preserve byte storage. -/
theorem syncTail_cleanup_default_origin_of_run {h after : Heap} {r : ZStreamRef} {zs block : Nat}
    {z : ZStream} {s : InflateState} {array : Array UInt8} {rc : Int32}
    (before : DefaultOriginState h r zs z s) (allocator : DefAlloc z) (mode : s.mode = SYNC)
    (get : h.bytes block = some array) (size : array.size = 4) (write : h.ro block = false)
    (actual : C.run (do
      let code ← syncTail (some r) (some (.tab zs))
      freeB (.ref (.blk block) 0)
      pure code) h = .ok (rc, after)) :
    ∃ stream state, DefaultOriginState after r zs stream state ∧ DefAlloc stream := by
  change (do
    let code ← syncTail (some r) (some (.tab zs))
    freeB (.ref (.blk block) 0)
    pure code) h = _ at actual
  rw [bind_app] at actual
  cases searched : syncTail (some r) (some (.tab zs)) h with
  | error fault => rw [searched] at actual; cases actual
  | ok pair =>
    obtain ⟨code, middle⟩ := pair
    obtain ⟨stream, state, current, currentAllocator, bytes, readonly⟩ :=
      syncTail_default_origin_of_run before allocator mode searched
    have currentGet : middle.bytes block = some array := by rw [bytes]; exact get
    have currentWrite : middle.ro block = false := by rw [readonly]; exact write
    have freed := freeBuf_run (H := middle) currentGet currentWrite
    rw [searched] at actual
    simp only [bind_app, freed, pure_app] at actual
    have heapEq : freeWin middle (.ref (.blk block) 0) = after :=
      congrArg Prod.snd (Except.ok.inj actual)
    rw [← heapEq]
    exact ⟨stream, state, current.free_local currentGet size, currentAllocator⟩

/-- Every actual fault-free default Sync call preserves the strengthened
history state. This covers initial restore, resumed search, early buffer
refusal and both tail results, including the real final local free.
It is a history observer, not a totality theorem for arbitrary Sync input. -/
theorem inflateSync_default_origin_of_run {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {rc : Int32} (before : DefaultOriginState h r zs z s)
    (allocator : DefAlloc z)
    (actual : C.run (inflateSync (some r)) h = .ok (rc, after)) :
    ∃ stream state, DefaultOriginState after r zs stream state ∧ DefAlloc stream := by
  have initial := default_origin_syncAlloc before
  have get := syncAlloc_bytes_buf h
  have size : (syncJunk h).size = 4 := by simp [syncJunk]
  have write := syncAlloc_ro_buf h
  by_cases empty : z.avail_in = 0 ∧ s.bits < 8
  · have expected := inflateSync_buf_error before.good empty.1 empty.2
    have heapEq : tmpFreed h = after := congrArg Prod.snd (Except.ok.inj (expected.symm.trans actual))
    rw [← heapEq]
    exact ⟨z, s, initial.free_local get size, allocator⟩
  change inflateSync (some r) h = _ at actual
  rw [inflateSync_split] at actual
  simp only [bind_app, allocLocalB_run h before.good.fresh, stateCheck_live initial.good.live,
    show ((0 : Int32) != 0) = false from by decide, Bool.false_eq_true, ↓reduceIte,
    ldZ_eq, initial.good.live.hz, initial.good.live.zst, castI, ldI_eq, initial.good.live.hs,
    Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, empty] at actual
  by_cases resumed : s.mode = SYNC
  · simp only [bne_iff_ne, resumed, not_true_eq_false, ↓reduceIte, pure_app] at actual
    exact syncTail_cleanup_default_origin_of_run initial allocator resumed get size write actual
  · have separate := win_ne_buf before.good.fresh before.good.inv.win
    obtain ⟨first, current⟩ := syncFirst_default_origin_run initial get size write separate
    change syncFirst (some (.tab zs)) (syncBuf h) s (syncAlloc h) = _ at first
    simp only [bne_iff_ne] at actual
    rw [if_pos resumed] at actual
    simp only [bind_app, first] at actual
    have currentGet : (syncFirstHeap (syncAlloc h) zs h.nextBlk s (syncJunk h)).bytes h.nextBlk =
        some (fillBuf (syncJunk h) (syncHold0 s) (syncNB s)) := by
      simp [syncFirstHeap]
    have currentSize : (fillBuf (syncJunk h) (syncHold0 s) (syncNB s)).size = 4 := by
      rw [fillBuf_size, size]
    have currentWrite : (syncFirstHeap (syncAlloc h) zs h.nextBlk s (syncJunk h)).ro h.nextBlk = false := by
      simp [syncFirstHeap, syncAlloc_ro_buf]
    exact syncTail_cleanup_default_origin_of_run current allocator rfl currentGet currentSize currentWrite actual

#print axioms syncTail_cleanup_default_origin_of_run
#print axioms inflateSync_default_origin_of_run
end Zlib.Inflate.Proofs
