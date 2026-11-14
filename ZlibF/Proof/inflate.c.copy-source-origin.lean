import ZlibF.Proof.«inflate.c.copy-window-content»
import ZlibF.Spec.Public.Copy
import ZlibF.Proof.«inflate.c.origin-fields-memory-contract»
import ZlibF.Proof.«inflate.c.dictionary-install-origin»
import ZlibF.Proof.«inflate.c.default-readonly-controls»
import ZlibF.Proof.«inflate.c.copy-both-origin»
import ZlibF.Spec.Functional.Api.Compress

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Transport the unchanged source decoder through the real copy heap
updates. Table contents come from its state record and retained globals. -/
theorem DefaultOriginState.same_source_heap
    {h after : Heap} {source : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (before : DefaultOriginState h source zs z s) (good : Good after source zs z s)
    (sizes : ByteViewSizes h after) (static : after.static = h.static) :
    DefaultOriginState after source zs z s := by
  have globals : LibraryGlobals after := static.trans before.globals
  have platform := sizes.platform before.platform
  have codes := CodeRef.get_istate_codes good.live.hs
  have fixedLen : Space.get after CodeRef.st_lenfix = Space.get h CodeRef.st_lenfix := by
    simp only [Space.get, static]
  have fixedDist : Space.get after CodeRef.st_distfix = Space.get h CodeRef.st_distfix := by
    simp only [Space.get, static]
  have current : DefaultStateJ after source zs z s := by
    rcases before.tableOrigin with dynamic | fixed
    · obtain ⟨nextOff, distOff, next, _nextBound, dist, _distBound, _⟩ :=
        CopyTableOrigin.dynamic_geometry before.good dynamic
      exact copiedSource_J_of_heap_facts before.toDefaultStateJ (Or.inl dynamic) next
        (fun _ => dist) good codes fixedLen fixedDist globals platform
    · obtain ⟨nextOff, next, _nextBound⟩ := before.good.inv.ptr.1
      have impossible : s.lencode = .ref (.istate_codes zs) 0 →
          s.distcode = .ref (.istate_codes zs) 0 := by
        intro eq
        cases fixed.1.symm.trans eq
      exact copiedSource_J_of_heap_facts before.toDefaultStateJ (Or.inr fixed) next
        impossible good codes fixedLen fixedDist globals platform
  exact ⟨current, before.tableOrigin⟩

/-- First-allocation failure only changes the destination record and the
allocation counter. The actual source remains fully initialized. -/
theorem inflateCopy_first_failure_source_origin
    {h : Heap} {source dest : ZStreamRef} {zs : Nat} {z oldDest : ZStream} {s : InflateState}
    (before : DefaultOriginState h source zs z s) (allocator : DefAlloc z)
    (get : dest.get h = some oldDest) (different : source ≠ dest)
    (failure : h.allocOk h.nalloc = false) :
    ∃ after, C.run (inflateCopy (some dest) (some source)) h = .ok (Z_MEM_ERROR, after) ∧
      DefaultOriginState after source zs z s := by
  let middle := {h with nalloc := h.nalloc + 1}
  let after := dest.put middle {oldDest with state := none}
  have run : C.run (inflateCopy (some dest) (some source)) h = .ok (Z_MEM_ERROR, after) :=
    inflateCopy_first_allocation_failure before.good allocator get failure
  have midGet : dest.get middle = some oldDest := by cases dest <;> simpa [middle, ZStreamRef.get] using get
  have sourceGet : source.get after = some z := by
    rw [copy_stream_get_put_other middle different]
    cases source <;> simpa [middle, ZStreamRef.get] using before.good.live.hz
  have stateGet : after.istates zs = some s := by simpa [after, middle] using before.good.live.hs
  have middleFresh : Fresh middle := before.good.fresh
  have middleUniq : Uniq middle := before.good.uniq
  have shape := shape_put midGet {oldDest with state := none}
  have good : Good after source zs z s := copiedSource_good_of_heap_facts before.good sourceGet stateGet
    (fun _ _ => ⟨by simp [after, middle], by simp [after, middle]⟩)
    (shape.fresh (by simp [middle]) middleFresh) (shape.uniq middleUniq)
  have views : ∀ ref : BRef, Space.get after ref = Space.get h ref := by
    intro ref
    rw [byte_view_get_stream_put]
    cases ref <;> rfl
  have sizes : ByteViewSizes h after := fun ref => congrArg (Option.map Array.size) (views ref)
  exact ⟨after, run, before.same_source_heap good sizes (by simp [after, middle])⟩

/-- A later allocation failure frees its fresh temporary state. No source
record or byte view is changed by allocation, free or destination clearing. -/
theorem inflateCopy_second_failure_source_origin
    {h : Heap} {source dest : ZStreamRef} {zs : Nat} {z oldDest : ZStream} {s : InflateState}
    (before : DefaultOriginState h source zs z s) (allocator : DefAlloc z)
    (get : dest.get h = some oldDest) (different : source ≠ dest)
    (first : h.allocOk h.nalloc = true) (window : s.window ≠ .null)
    (failure : h.allocOk (h.nalloc + 1) = false) :
    ∃ after, C.run (inflateCopy (some dest) (some source)) h = .ok (Z_MEM_ERROR, after) ∧
      DefaultOriginState after source zs z s := by
  let zeroed := allocIstHeap h InflateState.zeroed
  let failed := {zeroed with nalloc := zeroed.nalloc + 1}
  let freed := freeIst failed h.nextBlk
  let after := dest.put freed {oldDest with state := none}
  have run : C.run (inflateCopy (some dest) (some source)) h = .ok (Z_MEM_ERROR, after) :=
    inflateCopy_window_allocation_failure before.good allocator get first window failure
  have freeGet : dest.get freed = some oldDest := by
    rw [ZStreamRef.get_freeIst]
    cases dest <;> simpa [failed, zeroed, allocIstHeap, ZStreamRef.get] using get
  have sourceGet : source.get after = some z := by
    rw [copy_stream_get_put_other freed different, ZStreamRef.get_freeIst]
    cases source <;> simpa [failed, zeroed, allocIstHeap, ZStreamRef.get] using before.good.live.hz
  have zsOld : zs ≠ h.nextBlk := by
    intro equal
    have live : h.live zs := by simp [Heap.live, before.good.live.hs]
    exact before.good.fresh zs (by omega) live
  have stateGet : after.istates zs = some s := by
    simpa [after, freed, failed, zeroed, freeIst, allocIstHeap, upd_ne _ _ _ _ zsOld] using before.good.live.hs
  have dead : h.istates h.nextBlk = none :=
    (fresh_dead before.good.fresh (Nat.le_refl _)).2.2.2.2.2.1
  have shape : Shape h freed := by
    intro b
    by_cases equal : b = h.nextBlk
    · subst b
      simp [freed, failed, zeroed, freeIst, allocIstHeap, dead]
    · simp [freed, failed, zeroed, freeIst, allocIstHeap, upd_ne _ _ _ _ equal]
  have fullShape := shape.trans (shape_put freeGet {oldDest with state := none})
  have good : Good after source zs z s := copiedSource_good_of_heap_facts before.good sourceGet stateGet
    (fun _ _ => ⟨by simp [after, freed, failed, zeroed, freeIst, allocIstHeap],
      by simp [after, freed, failed, zeroed, freeIst, allocIstHeap]⟩)
    (fullShape.fresh_le (by simp [freed, failed, zeroed, freeIst, allocIstHeap]) before.good.fresh)
    (fullShape.uniq before.good.uniq)
  have views : ∀ ref : BRef, Space.get after ref = Space.get h ref := by
    intro ref
    rw [byte_view_get_stream_put]
    cases ref <;> rfl
  have sizes : ByteViewSizes h after := fun ref => congrArg (Option.map Array.size) (views ref)
  exact ⟨after, run, before.same_source_heap good sizes
    (by simp [after, freed, failed, zeroed, freeIst, allocIstHeap])⟩

/-- Every actual result of a well-formed default copy preserves the full
source relation. Both genuine allocation failures are included. -/
theorem inflateCopy_source_origin_of_run
    {h after : Heap} {source dest : ZStreamRef} {zs : Nat}
    {z oldDest : ZStream} {s : InflateState} {rc : Int32}
    (before : DefaultOriginState h source zs z s) (allocator : DefAlloc z)
    (get : dest.get h = some oldDest) (different : source ≠ dest)
    (run : C.run (inflateCopy (some dest) (some source)) h = .ok (rc, after)) :
    DefaultOriginState after source zs z s := by
  have success : h.allocOk h.nalloc = true →
      (s.window ≠ .null → h.allocOk (h.nalloc + 1) = true) →
      DefaultOriginState after source zs z s := by
    intro first second
    obtain ⟨computed, copied, actual, _destination, original⟩ :=
      inflateCopy_success_both_origin before allocator get different first second
    have same := Except.ok.inj (actual.symm.trans run)
    cases same
    exact original
  cases first : h.allocOk h.nalloc with
  | false =>
    obtain ⟨computed, actual, original⟩ :=
      inflateCopy_first_failure_source_origin before allocator get different first
    have same := Except.ok.inj (actual.symm.trans run)
    cases same
    exact original
  | true =>
    by_cases window : s.window = .null
    · exact success first (fun nonnull => False.elim (nonnull window))
    · cases second : h.allocOk (h.nalloc + 1) with
      | true => exact success first (fun _ => second)
      | false =>
        obtain ⟨computed, actual, original⟩ :=
          inflateCopy_second_failure_source_origin before allocator get different first window second
        have same := Except.ok.inj (actual.symm.trans run)
        cases same
        exact original

#print axioms DefaultOriginState.same_source_heap
#print axioms inflateCopy_first_failure_source_origin
#print axioms inflateCopy_second_failure_source_origin
#print axioms inflateCopy_source_origin_of_run
end Zlib.Inflate.Proofs
