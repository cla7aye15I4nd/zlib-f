import ZlibF.Proof.«inflate.c.copy-window-failure»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The second actual allocator call returns a fresh byte block of the
window size after the state record has been allocated and zeroed. -/
theorem inflateCopy_window_allocation_success
    {h : Heap} {source : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState}
    (good : Good h source zs z s)
    (allocator : DefAlloc z)
    (second : h.allocOk (h.nalloc + 1) = true) :
    let zeroed := allocIstHeap h InflateState.zeroed
    let bytes := 2 ^ s.wbits.toNat
    ZALLOCB (some source) ((1 : UInt32) <<< s.wbits) 1 zeroed =
      .ok (.ref (.blk zeroed.nextBlk) 0,
        Zlib.Zutil.Proofs.allocHeap zeroed bytes) := by
  dsimp only
  let zeroed := allocIstHeap h InflateState.zeroed
  have sourceZero : source.get zeroed = some z := by
    rw [ZStreamRef.get_allocIst]
    exact good.live.hz
  have freshZero : Fresh zeroed := fresh_allocIst good.fresh InflateState.zeroed
  have secondZero : zeroed.allocOk zeroed.nalloc = true := by
    simpa [zeroed, allocIstHeap] using second
  have size : ((1 : UInt32) <<< s.wbits).toNat = 2 ^ s.wbits.toNat :=
    shl_toNat_aux good.inv.win.wbits
  rw [zallocb_run sourceZero allocator.1]
  simpa [Zlib.Zutil.zcalloc, size, zeroed, allocIstHeap] using
    Zlib.Zutil.Proofs.zcalloc_ok_run zeroed z.«opaque»
      ((1 : UInt32) <<< s.wbits) 1 secondZero freshZero

/-- The actual window copy reads exactly `whave` source bytes and writes
them into the fresh allocation; the remaining bytes retain allocator
garbage, as in the translated `malloc` model. -/
theorem inflateCopy_window_memcpy_success
    {h : Heap} {source : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState}
    (good : Good h source zs z s)
    (window : s.window ≠ .null) :
    let zeroed := allocIstHeap h InflateState.zeroed
    let size := 2 ^ s.wbits.toNat
    let allocated := Zlib.Zutil.Proofs.allocHeap zeroed size
    let fresh : Array UInt8 := Array.ofFn (n := size)
      (fun i => Junk.of (zeroed.garbage zeroed.nalloc i.val))
    ∃ w a, s.window = .ref (.blk w) 0 ∧ h.bytes w = some a ∧
      C.run (memcpyB (.ref (.blk zeroed.nextBlk) 0) s.window s.whave.toNat)
        allocated =
        .ok ((), { allocated with bytes := upd allocated.bytes zeroed.nextBlk (some (copyRange fresh a 0 0 s.whave.toNat)) }) := by
  dsimp only
  rcases good.inv.win.block with empty | ⟨w, a, ptr, get, ro, size⟩
  · exact False.elim (window empty)
  let zeroed := allocIstHeap h InflateState.zeroed
  let n := 2 ^ s.wbits.toNat
  let allocated := Zlib.Zutil.Proofs.allocHeap zeroed n
  let fresh : Array UInt8 := Array.ofFn (n := n)
    (fun i => Junk.of (zeroed.garbage zeroed.nalloc i.val))
  have sourceLive : h.live w := by simp [Heap.live, get]
  have wBound : w < h.nextBlk := by
    by_cases bound : w < h.nextBlk
    · exact bound
    · exact False.elim (good.fresh w (by omega) sourceLive)
  have different : zeroed.nextBlk ≠ w := by
    simp [zeroed, allocIstHeap]
    omega
  have destination : allocated.bytes zeroed.nextBlk = some fresh := by
    simp [allocated, Zlib.Zutil.Proofs.allocHeap, fresh]
  have sourceGet : allocated.bytes w = some a := by
    change (upd h.bytes (h.nextBlk + 1)
      (some (Array.ofFn (n := n)
        (fun i => Junk.of (zeroed.garbage zeroed.nalloc i.val))))).get w = some a
    rw [upd_ne _ _ _ _ (by omega)]
    exact get
  have writable : allocated.ro zeroed.nextBlk = false := by
    simp [allocated, Zlib.Zutil.Proofs.allocHeap]
  have count : s.whave.toNat ≤ n := by
    rcases good.inv.win.ws with small | full
    · have hv := good.inv.win.hv
      omega
    · have hv := good.inv.win.hv
      omega
  have destinationRoom : 0 + s.whave.toNat ≤ fresh.size := by
    simpa [fresh, n] using count
  have sourceRoom : 0 + s.whave.toNat ≤ a.size := by omega
  refine ⟨w, a, ptr, get, ?_⟩
  rw [ptr]
  simpa [C.run, zeroed, n, allocated, fresh] using
    (memcpyB_blk_ok destination sourceGet writable different
      destinationRoom sourceRoom :
      memcpyB (.ref (.blk zeroed.nextBlk) 0) (.ref (.blk w) 0) s.whave.toNat
        allocated = .ok ((), { allocated with bytes := upd allocated.bytes zeroed.nextBlk (some (copyRange fresh a 0 0 s.whave.toNat)) }))

#print axioms inflateCopy_window_allocation_success
#print axioms inflateCopy_window_memcpy_success
end Zlib.Inflate.Proofs
