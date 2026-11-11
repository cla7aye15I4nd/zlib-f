import ZlibF.Proof.«inflate.c.head-default-state»
import ZlibF.Proof.«inflate.c.gzip-header-state»

/-!
# inflate.c: `case HEAD` under the default relation when gzip is allowed

With `wrap & 2`, `case HEAD` either sees the gzip magic bytes and enters
`FLAGS` (writing `hbuf` and the CRC-32 of the two bytes), or marks an
attached header record as not gzip (`done = -1`) and runs the zlib header
checks on that heap. Both keep `DefaultStateJ`.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The record write of `headDoneHeap`, as a `gz_header` store. -/
theorem headDoneHeap_tab {h : Heap} {i : Nat} {g : GzHeader} (get : h.gzheaders i = some g) :
    headDoneHeap h (some (.tab i)) = (GzHeaderRef.tab i).put h { g with done := -1 } := by
  simp only [headDoneHeap, get, GzHeaderRef.put_tab get]

theorem headDoneHeap_views (h : Heap) (head : GzHeaderPtr) (ref : BRef) :
    (Space.get (headDoneHeap h head) ref : Option (Array UInt8)) = Space.get h ref := by
  unfold headDoneHeap
  split
  · rfl
  · split
    · cases ref <;> rfl
    · rfl

theorem headDoneHeap_ro (h : Heap) (head : GzHeaderPtr) (ref : BRef) :
    Space.ro (headDoneHeap h head) ref = Space.ro h ref := by
  unfold headDoneHeap
  split
  · rfl
  · split
    · cases ref <;> rfl
    · rfl

theorem headDoneHeap_static (h : Heap) (head : GzHeaderPtr) :
    (headDoneHeap h head).static = h.static := by
  unfold headDoneHeap
  split
  · rfl
  · split <;> rfl

theorem headDoneHeap_good {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (good : Good h r zs z s) (head : GzHeaderPtr) : Good (headDoneHeap h head) r zs z s := by
  cases head with
  | none => exact good
  | some ref =>
    cases ref with
    | tab i =>
      cases get : h.gzheaders i with
      | none => simp only [headDoneHeap, get]; exact good
      | some g =>
        rw [headDoneHeap_tab get]
        exact good.headerPut get _

/-- `HEAD` keeps `DefaultStateJ` across the header record's `done = -1`. -/
theorem DefaultStateJ.headDone {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (invariant : DefaultStateJ h r zs z s) (mode : s.mode = HEAD) :
    DefaultStateJ (headDoneHeap h s.head) r zs z s := by
  have sizes : ByteViewSizes h (headDoneHeap h s.head) := by
    intro ref
    rw [headDoneHeap_views]
  refine ⟨⟨headDoneHeap_good invariant.good s.head,
    dataTableInvariant_inactive (by rw [mode]; unfold DataTableMode; decide),
    invariant.pending, invariant.lengths, invariant.headerLengths, invariant.held, invariant.window,
    invariant.wrapper, invariant.header, invariant.modes, invariant.trailer, ?_,
    sizes.platform invariant.platform⟩, invariant.requestedBits, invariant.requestedWrap, invariant.phase⟩
  change (headDoneHeap h s.head).static = _
  rw [headDoneHeap_static]
  exact invariant.globals

#print axioms DefaultStateJ.headDone

end Zlib.Inflate.Proofs
