import ZlibF.Proof.«inflate.c.local-window-core»
import ZlibF.Proof.«inflate.c.local-end»
import ZlibF.Proof.«inflate.c.default-local»
import ZlibF.Proof.«inflate.c.leave-default-state»

/-! Actual public inflate temporary storage under local uniqueness. -/
namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

theorem unique_syncAlloc {h : Heap} {cutoff : Nat} (unique : UniqueFrom h cutoff)
    (fresh : Fresh h) : UniqueFrom (syncAlloc h) cutoff := by
  intro b lower
  by_cases same : b = h.nextBlk
  · subst b
    obtain ⟨e0, e1, e2, e3, e4, e5, e6⟩ := fresh_dead fresh (Nat.le_refl _)
    simp [syncAlloc, e1, e2, e3, e4, e5, e6, cnt]
  · have bound := unique b lower
    simpa [syncAlloc, upd_ne _ _ _ _ same] using bound

theorem good_syncAlloc {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (good : LocalGood h cutoff r zs z s) :
    LocalGood (syncAlloc h) cutoff r zs z s := by
  exact ⟨⟨by simpa using good.live.hz, by simpa using good.live.hs,
    good.live.zst, good.live.back, good.live.mode, good.live.zalloc, good.live.zfree⟩,
    ⟨good.inv.wf, winInv_syncAlloc good.fresh good.inv.win, good.inv.reqbits,
      good.inv.bits, good.inv.ptr⟩, fresh_syncAlloc good.fresh,
    unique_syncAlloc good.unique good.fresh⟩

theorem good_freeBuf {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {nb : Nat} (good : LocalGood h cutoff r zs z s)
    (separate : ∀ w, s.window = .ref (.blk w) 0 → w ≠ nb) :
    LocalGood (freeWin h (.ref (.blk nb) 0)) cutoff r zs z s := by
  refine ⟨⟨by simpa using good.live.hz, by simpa using good.live.hs,
    good.live.zst, good.live.back, good.live.mode, good.live.zalloc, good.live.zfree⟩,
    ⟨good.inv.wf, ?_, good.inv.reqbits, good.inv.bits, good.inv.ptr⟩,
    fresh_freeWin good.fresh _, good.unique.freeWin _⟩
  have win := good.inv.win
  refine ⟨win.wbits, ?_, win.nullws, win.ws, win.hv, win.wn, win.eq⟩
  rcases win.block with null | ⟨w, a, ptr, get, ro, size⟩
  · exact Or.inl null
  · have different := separate w ptr
    have retained := freeWin_bytes_ne h (.ref (.blk nb) 0) (b := w) (by
      intro w' same
      have sameIndex := BRef.blk.inj (Ptr.ref.inj same).1
      subst sameIndex
      exact Ne.symm different)
    exact Or.inr ⟨w, a, ptr, by rw [retained.1]; exact get,
      by rw [retained.2]; exact ro, size⟩

theorem default_local_not_window {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} {block : Nat} {array : Array UInt8} (good : LocalGood h cutoff r zs z s)
    (get : h.bytes block = some array) (size : array.size = 4) (bits : s.wbits = 15) :
    s.window ≠ .ref (.blk block) 0 := by
  intro window
  rcases good.inv.win.block with null | ⟨w, bytes, win, bytesGet, ro, bytesSize⟩
  · rw [window] at null
    cases null
  · rw [window] at win
    cases win
    have same : bytes = array := Option.some.inj (bytesGet.symm.trans get)
    subst bytes
    rw [size, bits] at bytesSize
    change 4 = 32768 at bytesSize
    omega

theorem default_state_syncAlloc {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (invariant : LocalStateJ h cutoff r zs z s) :
    LocalStateJ (syncAlloc h) cutoff r zs z s := by
  have tables : DataTableInvariant (syncAlloc h) s := by
    intro active
    have old := invariant.tables active
    constructor
    · obtain ⟨ref, offset, array, pointer, get, safe⟩ := old.lengthTable
      exact ⟨ref, offset, array, pointer, by cases ref <;> exact get, safe⟩
    · obtain ⟨ref, offset, array, pointer, get, safe⟩ := old.distanceTable
      exact ⟨ref, offset, array, pointer, by cases ref <;> exact get, safe⟩
  exact ⟨⟨good_syncAlloc invariant.good, tables, invariant.pending, invariant.lengths,
    invariant.headerLengths, invariant.held, invariant.window, invariant.wrapper,
    invariant.header, invariant.modes, invariant.trailer, invariant.globals,
    default_platform_syncAlloc invariant.platform⟩,
    invariant.requestedBits, invariant.requestedWrap, invariant.phase, invariant.roots⟩

theorem LocalStateJ.free_local {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {block : Nat} {array : Array UInt8}
    (invariant : LocalStateJ h cutoff r zs z s) (localGet : h.bytes block = some array)
    (localSize : array.size = 4) :
    LocalStateJ (freeWin h (.ref (.blk block) 0)) cutoff r zs z s := by
  have good := good_freeBuf invariant.good (nb := block) (by
    intro w window same
    subst w
    exact default_local_not_window invariant.good localGet localSize invariant.window window)
  have tables : DataTableInvariant (freeWin h (.ref (.blk block) 0)) s := by
    intro active
    have old := invariant.tables active
    constructor
    · obtain ⟨ref, offset, array, pointer, get, safe⟩ := old.lengthTable
      exact ⟨ref, offset, array, pointer, by cases ref <;> exact get, safe⟩
    · obtain ⟨ref, offset, array, pointer, get, safe⟩ := old.distanceTable
      exact ⟨ref, offset, array, pointer, by cases ref <;> exact get, safe⟩
  exact ⟨⟨good, tables, invariant.pending, invariant.lengths, invariant.headerLengths,
    invariant.held, invariant.window, invariant.wrapper, invariant.header, invariant.modes,
    invariant.trailer, invariant.globals, platform_free_local invariant.platform block⟩,
    invariant.requestedBits, invariant.requestedWrap, invariant.phase, invariant.roots⟩


#print axioms default_state_syncAlloc
#print axioms LocalStateJ.free_local
end Zlib.Inflate.Local
