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
    (wbits : s.wbits.toNat ≤ 15) :
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
    have small : 2 ^ s.wbits.toNat ≤ 2 ^ 15 := Nat.pow_le_pow_right (by decide) wbits
    simp only [size, ZlibF.PlatformMemory.byteObjectLimit]
    omega
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

/-- The windowed copy heap keeps the header table, every existing byte view
and its read-only flag; only the two fresh blocks are new. -/
theorem copiedWindowHeap_preserves (h : Heap) (dest : ZStreamRef) (z : ZStream)
    (s copied : InflateState) (sourceArray : Array UInt8) (fresh : Fresh h) :
    (∀ i, (copiedWindowHeap h dest z s copied sourceArray).gzheaders i = h.gzheaders i) ∧
    (∀ (ref : BRef) (a : Array UInt8), (Space.get h ref : Option (Array UInt8)) = some a →
      ∃ a', (Space.get (copiedWindowHeap h dest z s copied sourceArray) ref : Option (Array UInt8)) = some a' ∧
        a'.size = a.size) ∧
    (∀ (ref : BRef) (a : Array UInt8), (Space.get h ref : Option (Array UInt8)) = some a →
      (Space.ro (copiedWindowHeap h dest z s copied sourceArray) ref : Bool) = Space.ro h ref) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    cases dest <;> simp [copiedWindowHeap, Zlib.Zutil.Proofs.allocHeap, allocIstHeap, ZStreamRef.put] <;>
      (try split) <;> (try rfl)
  · intro ref a get
    cases ref with
    | blk b =>
      have live : h.live b := by
        simp only [Space.get] at get
        simp [Heap.live, get]
      have below : b < h.nextBlk := by
        by_cases bound : b < h.nextBlk
        · exact bound
        · exact False.elim (fresh b (by omega) live)
      have ne1 : b ≠ h.nextBlk + 1 := by omega
      refine ⟨a, ?_, rfl⟩
      simp only [Space.get] at get ⊢
      cases dest <;> simp [copiedWindowHeap, Zlib.Zutil.Proofs.allocHeap, allocIstHeap,
        ZStreamRef.put, upd_ne _ _ _ _ ne1, get] <;> (try split) <;> (try simp [upd_ne _ _ _ _ ne1, get])
    | _ =>
      refine ⟨a, ?_, rfl⟩
      simp only [Space.get] at get ⊢
      cases dest <;> simp [copiedWindowHeap, Zlib.Zutil.Proofs.allocHeap, allocIstHeap,
        ZStreamRef.put, get] <;> (try split) <;> (try simp [get])
  · intro ref a get
    cases ref with
    | blk b =>
      have live : h.live b := by
        simp only [Space.get] at get
        simp [Heap.live, get]
      have below : b < h.nextBlk := by
        by_cases bound : b < h.nextBlk
        · exact bound
        · exact False.elim (fresh b (by omega) live)
      have ne1 : b ≠ h.nextBlk + 1 := by omega
      simp only [Space.ro]
      cases dest <;> simp [copiedWindowHeap, Zlib.Zutil.Proofs.allocHeap, allocIstHeap,
        ZStreamRef.put, upd_ne _ _ _ _ ne1] <;> (try split) <;> (try simp [upd_ne _ _ _ _ ne1])
    | _ =>
      simp only [Space.ro]
      cases dest <;> simp [copiedWindowHeap, Zlib.Zutil.Proofs.allocHeap, allocIstHeap,
        ZStreamRef.put] <;> (try split) <;> (try rfl)

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
      invariant.platform invariant.window.2
  obtain ⟨headers, views, readonly⟩ :=
    copiedWindowHeap_preserves h dest z s copied sourceArray invariant.good.fresh
  exact copiedGeneric_J_of_heap_facts invariant origin dynamicDist
    freshCodes fixedLen fixedDist goodAfter headers views readonly (fun b owner => by
      right
      rw [goodAfter.streamOwned_iff] at owner
      rcases owner with same | win
      · subst b
        exact invariant.good.fresh h.nextBlk (Nat.le_refl _)
      · have block : b = h.nextBlk + 1 := by
          simp [copied, copiedGeneric, window] at win
          exact win.symm
        subst b
        exact invariant.good.fresh (h.nextBlk + 1) (by omega)) globalsAfter platformAfter

/-- The source decoder retains J when a distinct destination and fresh
window are installed. The source window is an older block, so its bytes and
extent are unaffected by the new allocation and copy. -/
theorem copiedWindowHeap_source_J
    {h : Heap} {source dest : ZStreamRef}
    {old nextOff distOff : Nat} {z : ZStream}
    {s copied : InflateState} (sourceArray : Array UInt8)
    (invariant : DefaultStateJ h source old z s)
    (origin : CopyTableOrigin old s)
    (nextPtr : s.next = .ref (.istate_codes old) nextOff)
    (dynamicDist : s.lencode = .ref (.istate_codes old) 0 →
      s.distcode = .ref (.istate_codes old) distOff)
    (sourceGet : source.get
      (copiedWindowHeap h dest z s copied sourceArray) = some z)
    (stateGet : (copiedWindowHeap h dest z s copied sourceArray).istates old = some s)
    (destJ : DefaultStateJ
      (copiedWindowHeap h dest z s copied sourceArray)
      dest h.nextBlk { z with state := some (.inflate h.nextBlk) } copied) :
    DefaultStateJ (copiedWindowHeap h dest z s copied sourceArray)
      source old z s := by
  let after := copiedWindowHeap h dest z s copied sourceArray
  have windowFrame : ∀ w, s.window = .ref (.blk w) 0 →
      after.bytes w = h.bytes w ∧ after.ro w = h.ro w := by
    intro w ptr
    rcases invariant.good.inv.win.block with noWindow | ⟨v, a, sourcePtr, get, _, _⟩
    · rw [noWindow] at ptr
      cases ptr
    · have same : v = w := by
        have pair := Ptr.ref.inj (sourcePtr.symm.trans ptr)
        exact (BRef.blk.inj pair.1)
      subst v
      have live : h.live w := by simp [Heap.live, get]
      have bound : w < h.nextBlk := by
        by_cases hb : w < h.nextBlk
        · exact hb
        · exact False.elim (invariant.good.fresh w (by omega) live)
      have ne : w ≠ h.nextBlk + 1 := by omega
      constructor
      · simp [after, copiedWindowHeap, Zlib.Zutil.Proofs.allocHeap,
          allocIstHeap, upd_ne _ _ _ _ ne]
      · simp [after, copiedWindowHeap, Zlib.Zutil.Proofs.allocHeap,
          allocIstHeap, upd_ne _ _ _ _ ne]
  have goodAfter : Good after source old z s :=
    copiedSource_good_of_heap_facts invariant.good sourceGet stateGet
      windowFrame destJ.good.fresh destJ.good.uniq
  have freshCodes : Space.get after (CodeRef.istate_codes old) = some s.codes :=
    CodeRef.get_istate_codes stateGet
  have fixedLen : Space.get after CodeRef.st_lenfix =
      Space.get h CodeRef.st_lenfix := by
    simp [after, copiedWindowHeap, Zlib.Zutil.Proofs.allocHeap,
      allocIstHeap, Space.get]
  have fixedDist : Space.get after CodeRef.st_distfix =
      Space.get h CodeRef.st_distfix := by
    simp [after, copiedWindowHeap, Zlib.Zutil.Proofs.allocHeap,
      allocIstHeap, Space.get]
  obtain ⟨headers, views, readonly⟩ :=
    copiedWindowHeap_preserves h dest z s copied sourceArray invariant.good.fresh
  exact copiedSource_J_of_heap_facts invariant origin nextPtr dynamicDist
    goodAfter freshCodes fixedLen fixedDist headers views readonly destJ.globals destJ.platform

#print axioms copiedWindowHeap_J
#print axioms copiedWindowHeap_source_J

end Zlib.Inflate.Proofs
