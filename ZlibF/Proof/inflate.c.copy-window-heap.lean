import ZlibF.Proof.«inflate.c.copy-fixed-window»
import ZlibF.Proof.«inflate.c.window-platform»
import ZlibF.Proof.«inflate.c.copy-window-heap-def»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

theorem copiedWindowHeap_state
    (h : Heap) (dest : ZStreamRef) (z : ZStream)
    (s copied : InflateState) (sourceArray : Array UInt8) :
    (copiedWindowHeap h dest z s copied sourceArray).istates h.nextBlk =
      some copied := by
  simp [copiedWindowHeap, Zlib.Zutil.Proofs.allocHeap]

theorem copiedWindowHeap_stream
    (h : Heap) (dest : ZStreamRef) (z : ZStream)
    (s copied : InflateState) (sourceArray : Array UInt8)
    {oldDest : ZStream} (destGet : dest.get h = some oldDest) :
    dest.get (copiedWindowHeap h dest z s copied sourceArray) =
      some { z with state := some (.inflate h.nextBlk) } := by
  cases dest with
  | tab i =>
    simp only [ZStreamRef.get] at destGet
    simp [copiedWindowHeap, Zlib.Zutil.Proofs.allocHeap,
      allocIstHeap, ZStreamRef.get, ZStreamRef.put, destGet]
  | in_gzstate_strm i =>
    simp only [ZStreamRef.get] at destGet
    obtain ⟨g, get, _⟩ := Option.map_eq_some_iff.mp destGet
    simp [copiedWindowHeap, Zlib.Zutil.Proofs.allocHeap,
      allocIstHeap, ZStreamRef.get, ZStreamRef.put, get]

theorem copiedWindowHeap_window
    (h : Heap) (dest : ZStreamRef) (z : ZStream)
    (s copied : InflateState) (sourceArray : Array UInt8) :
    ∃ a,
      (copiedWindowHeap h dest z s copied sourceArray).bytes (h.nextBlk + 1) = some a ∧
      (copiedWindowHeap h dest z s copied sourceArray).ro (h.nextBlk + 1) = false ∧
      a.size = 2 ^ s.wbits.toNat := by
  let size := 2 ^ s.wbits.toNat
  let freshArray : Array UInt8 := Array.ofFn (n := size)
    (fun i => Junk.of (h.garbage (h.nalloc + 1) i.val))
  refine ⟨copyRange freshArray sourceArray 0 0 s.whave.toNat, ?_, ?_, ?_⟩
  · simp [copiedWindowHeap, Zlib.Zutil.Proofs.allocHeap,
      freshArray, size]
  · simp [copiedWindowHeap, Zlib.Zutil.Proofs.allocHeap]
  · simp [freshArray, size, size_copyRange]

theorem copiedWindowHeap_fresh_uniq
    (h : Heap) (dest : ZStreamRef) (z : ZStream)
    (s copied : InflateState) (sourceArray : Array UInt8)
    {oldDest : ZStream} (destGet : dest.get h = some oldDest)
    (fresh : Fresh h) (uniq : Uniq h) :
    Fresh (copiedWindowHeap h dest z s copied sourceArray) ∧
      Uniq (copiedWindowHeap h dest z s copied sourceArray) := by
  let size := 2 ^ s.wbits.toNat
  let zNext : ZStream := { z with state := some (.inflate h.nextBlk) }
  let stateHeap := allocIstHeap (dest.put h zNext) copied
  let allocated := Zlib.Zutil.Proofs.allocHeap stateHeap size
  let freshArray : Array UInt8 := Array.ofFn (n := size)
    (fun i => Junk.of (h.garbage (h.nalloc + 1) i.val))
  let written := copyRange freshArray sourceArray 0 0 s.whave.toNat
  have putShape : Shape h (dest.put h zNext) := shape_put destGet zNext
  have putFresh : Fresh (dest.put h zNext) :=
    putShape.fresh (by simp) fresh
  have putUniq : Uniq (dest.put h zNext) := putShape.uniq uniq
  have stateFresh : Fresh stateHeap := fresh_allocIst putFresh copied
  have stateUniq : Uniq stateHeap := uniq_allocIst putUniq putFresh copied
  have allocatedFresh : Fresh allocated :=
    (Zlib.Zutil.Proofs.allocHeap_frame stateHeap size).2.1 stateFresh
  have allocatedUniq : Uniq allocated :=
    uniq_allocHeap stateUniq stateFresh size
  have arrayGet : allocated.bytes (h.nextBlk + 1) = some freshArray := by
    simp [allocated, stateHeap, Zlib.Zutil.Proofs.allocHeap,
      allocIstHeap, freshArray]
  have shape : Shape allocated (copiedWindowHeap h dest z s copied sourceArray) := by
    simpa [copiedWindowHeap, allocated, stateHeap,
      zNext, freshArray, written] using
      (shape_setB arrayGet written)
  constructor
  · exact shape.fresh (by simp [copiedWindowHeap, allocated,
      stateHeap, Zlib.Zutil.Proofs.allocHeap]) allocatedFresh
  · exact shape.uniq allocatedUniq

theorem copiedWindowHeap_platform
    (h : Heap) (dest : ZStreamRef) (z : ZStream)
    (s copied : InflateState) (sourceArray : Array UInt8)
    (fit : ZlibF.PlatformMemory.ByteObjectsFit h)
    (wbits : s.wbits = 15) :
    ZlibF.PlatformMemory.ByteObjectsFit
      (copiedWindowHeap h dest z s copied sourceArray) := by
  let size := 2 ^ s.wbits.toNat
  let zNext : ZStream := { z with state := some (.inflate h.nextBlk) }
  let stateHeap := allocIstHeap (dest.put h zNext) copied
  let freshArray : Array UInt8 := Array.ofFn (n := size)
    (fun i => Junk.of (h.garbage (h.nalloc + 1) i.val))
  let allocated := Zlib.Zutil.Proofs.allocHeap stateHeap size
  let written := copyRange freshArray sourceArray 0 0 s.whave.toNat
  have bound : size < ZlibF.PlatformMemory.byteObjectLimit := by
    simp [size, wbits, ZlibF.PlatformMemory.byteObjectLimit]
  have fitPut : ZlibF.PlatformMemory.ByteObjectsFit (dest.put h zNext) :=
    fit.put_stream dest zNext
  have fitState : ZlibF.PlatformMemory.ByteObjectsFit stateHeap := by
    apply fitPut.of_storage_eq
    all_goals simp [stateHeap, allocIstHeap]
  have rawBound : freshArray.size < ZlibF.PlatformMemory.byteObjectLimit := by
    simpa [freshArray] using bound
  have fitRaw := fitState.with_bytes (block := stateHeap.nextBlk)
    (a := freshArray) rawBound
  have fitAllocated : ZlibF.PlatformMemory.ByteObjectsFit allocated := by
    apply fitRaw.of_storage_eq
    · simp [allocated, Zlib.Zutil.Proofs.allocHeap, stateHeap,
        freshArray, allocIstHeap]
    · rfl
    · rfl
  have writtenBound : written.size < ZlibF.PlatformMemory.byteObjectLimit := by
    simpa [written, size_copyRange, freshArray] using bound
  have fitWritten := fitAllocated.with_bytes (block := h.nextBlk + 1)
    (a := written) writtenBound
  simpa [copiedWindowHeap, allocated, stateHeap, freshArray, written,
    zNext] using fitWritten

/-- The common concrete windowed heap carries the full default invariant
once the source-derived table origin and bounded cursor offsets are known. -/
theorem copiedWindowHeap_J
    {h : Heap} {source dest : ZStreamRef}
    {old nextOff distOff : Nat} {z oldDest : ZStream}
    {s : InflateState} (sourceArray : Array UInt8)
    (invariant : DefaultStateJ h source old z s)
    (destGet : dest.get h = some oldDest)
    (origin : CopyTableOrigin old s)
    (nextBound : nextOff ≤ 1444)
    (distBound : distOff ≤ 1443)
    (dynamicDist : s.lencode = .ref (.istate_codes old) 0 →
      s.distcode = .ref (.istate_codes old) distOff) :
    let fresh := h.nextBlk
    let window : BPtr := .ref (.blk (h.nextBlk + 1)) 0
    let copied := copiedGeneric dest old fresh nextOff distOff window s
    DefaultStateJ (copiedWindowHeap h dest z s copied sourceArray)
      dest fresh { z with state := some (.inflate fresh) } copied := by
  dsimp only
  let fresh := h.nextBlk
  let window : BPtr := .ref (.blk (h.nextBlk + 1)) 0
  let copied := copiedGeneric dest old fresh nextOff distOff window s
  let after := copiedWindowHeap h dest z s copied sourceArray
  have stateGet : after.istates fresh = some copied := by
    simpa [after, fresh] using
      copiedWindowHeap_state h dest z s copied sourceArray
  have streamGet : dest.get after =
      some { z with state := some (.inflate fresh) } := by
    simpa [after, fresh] using
      copiedWindowHeap_stream h dest z s copied sourceArray destGet
  obtain ⟨windowArray, windowGet, windowWritable, windowSize⟩ :=
    copiedWindowHeap_window h dest z s copied sourceArray
  have freshUniq := copiedWindowHeap_fresh_uniq h dest z s copied
    sourceArray destGet invariant.good.fresh invariant.good.uniq
  have goodAfter : Good after dest fresh
      { z with state := some (.inflate fresh) } copied :=
    copiedGeneric_window_good_of_heap_facts invariant.good origin
      nextBound distBound streamGet stateGet windowGet windowWritable
      windowSize freshUniq.1 freshUniq.2
  have freshCodes : Space.get after (CodeRef.istate_codes fresh) =
      some s.codes := by
    simpa [copied, copiedGeneric] using
      (CodeRef.get_istate_codes stateGet)
  have fixedLen : Space.get after CodeRef.st_lenfix =
      Space.get h CodeRef.st_lenfix := by
    simp [after, copiedWindowHeap, Zlib.Zutil.Proofs.allocHeap,
      allocIstHeap, Space.get]
  have fixedDist : Space.get after CodeRef.st_distfix =
      Space.get h CodeRef.st_distfix := by
    simp [after, copiedWindowHeap, Zlib.Zutil.Proofs.allocHeap,
      allocIstHeap, Space.get]
  have globalsAfter : LibraryGlobals after := by
    simpa [after, copiedWindowHeap, Zlib.Zutil.Proofs.allocHeap,
      allocIstHeap, LibraryGlobals] using invariant.globals
  have platformAfter : ZlibF.PlatformMemory.ByteObjectsFit after :=
    copiedWindowHeap_platform h dest z s copied sourceArray
      invariant.platform invariant.window
  exact copiedGeneric_J_of_heap_facts invariant origin dynamicDist
    freshCodes fixedLen fixedDist goodAfter globalsAfter platformAfter

#print axioms copiedWindowHeap_J

end Zlib.Inflate.Proofs
