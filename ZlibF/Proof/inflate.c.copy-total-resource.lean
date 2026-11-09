import ZlibF.Proof.«inflate.c.copy-window-content»
import ZlibF.Spec.Public.Copy
import ZlibF.Proof.«inflate.c.origin-history»
namespace Zlib.Inflate.Proofs.CopyResource
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem stream_put_frame {h : Heap} {dest : ZStreamRef} {oldDest : ZStream}
    (get : dest.get h = some oldDest) (value : ZStream) :
    Frame h (dest.put h value) (StreamRoot dest) := by
  have wide := (RecordFrame.put_stream get none value).1
  simpa only [DecoderRecordRoot, or_false] using wide

theorem no_window_heap_frame {h : Heap} {dest : ZStreamRef} {oldDest : ZStream}
    (fresh : Fresh h) (get : dest.get h = some oldDest) (value : ZStream) (copied : InflateState) :
    Frame h (allocIstHeap (dest.put h value) copied) (StreamRoot dest) := by
  have placed := stream_put_frame get value
  refine ⟨placed.1, placed.2.1, ?_, ?_, ?_, ?_⟩
  · simpa [allocIstHeap] using placed.2.2.1
  · simp [allocIstHeap]
  · simp [allocIstHeap]
  intro b live outside
  have different : b ≠ h.nextBlk := fun same => fresh b (by omega) live
  simpa [allocIstHeap, ZStreamRef.put_nextBlk, upd_ne _ _ _ _ different] using placed.2.2.2.2.2 b live outside

theorem no_window_heap_live {h : Heap} {dest : ZStreamRef} {oldDest : ZStream}
    (get : dest.get h = some oldDest) (value : ZStream) (copied : InflateState)
    (window : copied.window = .null) :
    LiveChange h (allocIstHeap (dest.put h value) copied) (InflateOwned h.nextBlk copied) (fun _ => False) := by
  intro b
  have same := (shape_put get value).live b
  by_cases equal : b = h.nextBlk
  · subst b
    simp [Heap.live, allocIstHeap, InflateOwned]
  · simpa [Heap.live, allocIstHeap, InflateOwned, window, equal, upd_ne _ _ _ _ equal] using same

theorem window_heap_frame {h : Heap} {dest : ZStreamRef} {oldDest : ZStream}
    (fresh : Fresh h) (get : dest.get h = some oldDest) (z : ZStream)
    (s copied : InflateState) (a : Array UInt8) :
    Frame h (copiedWindowHeap h dest z s copied a) (StreamRoot dest) := by
  have placed := stream_put_frame get {z with state := some (.inflate h.nextBlk)}
  refine ⟨placed.1, placed.2.1, ?_, ?_, ?_, ?_⟩
  · simpa [copiedWindowHeap, Zlib.Zutil.Proofs.allocHeap, allocIstHeap] using placed.2.2.1
  · simp [copiedWindowHeap, Zlib.Zutil.Proofs.allocHeap, allocIstHeap] <;> omega
  · simp [copiedWindowHeap, Zlib.Zutil.Proofs.allocHeap, allocIstHeap] <;> omega
  intro b live outside
  have first : b ≠ h.nextBlk := fun same => fresh b (by omega) live
  have second : b ≠ h.nextBlk + 1 := fun same => fresh b (by omega) live
  simpa [copiedWindowHeap, Zlib.Zutil.Proofs.allocHeap, allocIstHeap,
    upd_ne _ _ _ _ first, upd_ne _ _ _ _ second] using placed.2.2.2.2.2 b live outside

theorem window_heap_live {h : Heap} {dest : ZStreamRef} {oldDest : ZStream}
    (get : dest.get h = some oldDest) (z : ZStream)
    (s copied : InflateState) (a : Array UInt8)
    (window : copied.window = .ref (.blk (h.nextBlk + 1)) 0) :
    LiveChange h (copiedWindowHeap h dest z s copied a) (InflateOwned h.nextBlk copied) (fun _ => False) := by
  intro b
  have same := (shape_put get {z with state := some (.inflate h.nextBlk)}).live b
  by_cases first : b = h.nextBlk
  · subst b
    simp [Heap.live, copiedWindowHeap, Zlib.Zutil.Proofs.allocHeap, allocIstHeap, InflateOwned]
  by_cases second : b = h.nextBlk + 1
  · subst b
    simp [Heap.live, copiedWindowHeap, Zlib.Zutil.Proofs.allocHeap, allocIstHeap, InflateOwned, window]
  · simpa [Heap.live, copiedWindowHeap, Zlib.Zutil.Proofs.allocHeap, allocIstHeap,
      InflateOwned, window, first, second, Ne.symm second, upd_ne _ _ _ _ first, upd_ne _ _ _ _ second] using same

theorem copied_prefix (fresh source : Array UInt8) (n : Nat)
    (destinationRoom : n ≤ fresh.size) (sourceRoom : n ≤ source.size) :
    (copyRange fresh source 0 0 n).toList.take n = source.toList.take n := by
  apply List.ext_getElem
  · simp only [List.length_take, Array.length_toList, size_copyRange]
    omega
  · intro i hi hj
    have inside : i < n := by simp only [List.length_take] at hi; omega
    have outBound : i < (copyRange fresh source 0 0 n).size := by rw [size_copyRange]; omega
    have inBound : i < source.size := by omega
    have value := copyRange_bang fresh source 0 0 n (by omega) (by omega) i (by omega)
    simp only [Nat.zero_le, inside, and_self, if_true, Nat.sub_zero, Nat.zero_add] at value
    rw [getElem!_pos (copyRange fresh source 0 0 n) i outBound, getElem!_pos source i inBound] at value
    simpa only [List.getElem_take, Array.getElem_toList] using value

theorem window_heap_prefix {h : Heap} {source : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (good : Good h source zs z s) (dest : ZStreamRef) (copied : InflateState)
    {w : Nat} {a : Array UInt8} (pointer : s.window = .ref (.blk w) 0) (get : h.bytes w = some a)
    (copiedWindow : copied.window = .ref (.blk (h.nextBlk + 1)) 0) :
    SameBytePrefix h (copiedWindowHeap h dest z s copied a) s.window copied.window s.whave.toNat := by
  have extent : a.size = 2 ^ s.wbits.toNat := by
    rcases good.inv.win.block with null | ⟨other, b, otherPointer, otherGet, _, size⟩
    · rw [null] at pointer
      cases pointer
    · have same : other = w := BRef.blk.inj (Ptr.ref.inj (otherPointer.symm.trans pointer)).1
      subst other
      have sameArray : b = a := Option.some.inj (otherGet.symm.trans get)
      simpa [sameArray] using size
  have count : s.whave.toNat ≤ 2 ^ s.wbits.toNat := by
    rcases good.inv.win.ws with small | full
    · have hv := good.inv.win.hv
      omega
    · have hv := good.inv.win.hv
      omega
  let fresh : Array UInt8 := Array.ofFn (n := 2 ^ s.wbits.toNat)
    (fun i => Junk.of (h.garbage (h.nalloc + 1) i.val))
  let written := copyRange fresh a 0 0 s.whave.toNat
  refine ⟨a.toList.take s.whave.toNat, ?_, ?_⟩
  · exact Or.inr ⟨.blk w, 0, a, pointer, get, by omega, by simp⟩
  · refine Or.inr ⟨.blk (h.nextBlk + 1), 0, written, copiedWindow, ?_, ?_, ?_⟩
    · simp [copiedWindowHeap, written, fresh, Zlib.Zutil.Proofs.allocHeap, allocIstHeap]
    · simpa [written, fresh, size_copyRange] using count
    · simp only [List.drop_zero]
      exact (copied_prefix fresh a s.whave.toNat (by simpa [fresh] using count) (by omega)).symm

theorem generic_relocated {old fresh nextOff distOff : Nat} {s : InflateState}
    (origin : CopyTableOrigin old s) (dest : ZStreamRef) (window : BPtr)
    (next : s.next = .ref (.istate_codes old) nextOff)
    (dist : s.lencode = .ref (.istate_codes old) 0 → s.distcode = .ref (.istate_codes old) distOff) :
    copiedGeneric dest old fresh nextOff distOff window s =
      {s with
        strm := some dest, window := window
        lencode := relocateCode old fresh s.lencode,
        distcode := relocateCode old fresh s.distcode,
        next := relocateCode old fresh s.next} := by
  rcases origin with dynamic | fixed
  · simp [copiedGeneric, dynamic, dist dynamic, next, relocateCode]
  · have notDynamic : s.lencode ≠ .ref (.istate_codes old) 0 := by
      rw [fixed.1]
      intro impossible
      cases impossible
    simp [copiedGeneric, notDynamic, fixed.1, fixed.2, next, relocateCode]

theorem first_failure_resources
    {h : Heap} {source dest : ZStreamRef} {zs : Nat} {z oldDest : ZStream} {s : InflateState}
    (before : DefaultOriginState h source zs z s) (allocator : DefAlloc z)
    (get : dest.get h = some oldDest) (different : source ≠ dest)
    (failure : h.allocOk h.nalloc = false) :
    ∃ after, C.run (inflateCopy (some dest) (some source)) h = .ok (Z_MEM_ERROR, after) ∧
      source.get after = some z ∧ after.istates zs = some s ∧
      Frame h after (StreamRoot dest) ∧ AllocationFailed h after ∧
      dest.get after = some {oldDest with state := none} ∧
      LiveChange h after (fun _ => False) (fun _ => False) := by
  let middle := {h with nalloc := h.nalloc + 1}
  let after := dest.put middle {oldDest with state := none}
  have run : C.run (inflateCopy (some dest) (some source)) h = .ok (Z_MEM_ERROR, after) :=
    inflateCopy_first_allocation_failure before.good allocator get failure
  obtain ⟨computed, computedRun, destFinal, failed, ledger⟩ :=
    inflateCopy_first_failure_cleanup before.good allocator get failure
  have same : computed = after := congrArg Prod.snd (Except.ok.inj (computedRun.symm.trans run))
  subst computed
  have midGet : dest.get middle = some oldDest := by cases dest <;> simpa [middle, ZStreamRef.get] using get
  have placed := stream_put_frame midGet {oldDest with state := none}
  have frame : Frame h after (StreamRoot dest) := by
    refine ⟨placed.1, placed.2.1, placed.2.2.1, ?_, ?_, ?_⟩
    · simp [after, middle]
    · simp [after, middle]
    · exact placed.2.2.2.2.2
  refine ⟨after, run, ?_, ?_, frame, failed, destFinal, ledger⟩
  · rw [copy_stream_get_put_other middle different]
    cases source <;> simpa [middle, ZStreamRef.get] using before.good.live.hz
  · simpa [after, middle] using before.good.live.hs

theorem second_failure_resources
    {h : Heap} {source dest : ZStreamRef} {zs : Nat} {z oldDest : ZStream} {s : InflateState}
    (before : DefaultOriginState h source zs z s) (allocator : DefAlloc z)
    (get : dest.get h = some oldDest) (different : source ≠ dest)
    (first : h.allocOk h.nalloc = true) (window : s.window ≠ .null)
    (failure : h.allocOk (h.nalloc + 1) = false) :
    ∃ after, C.run (inflateCopy (some dest) (some source)) h = .ok (Z_MEM_ERROR, after) ∧
      source.get after = some z ∧ after.istates zs = some s ∧
      Frame h after (StreamRoot dest) ∧ AllocationFailed h after ∧
      dest.get after = some {oldDest with state := none} ∧
      LiveChange h after (fun _ => False) (fun _ => False) := by
  let zeroed := allocIstHeap h InflateState.zeroed
  let failed := {zeroed with nalloc := zeroed.nalloc + 1}
  let freed := freeIst failed h.nextBlk
  let after := dest.put freed {oldDest with state := none}
  have run : C.run (inflateCopy (some dest) (some source)) h = .ok (Z_MEM_ERROR, after) :=
    inflateCopy_window_allocation_failure before.good allocator get first window failure
  have freeGet : dest.get freed = some oldDest := by
    rw [ZStreamRef.get_freeIst]
    cases dest <;> simpa [failed, zeroed, allocIstHeap, ZStreamRef.get] using get
  have placed := stream_put_frame freeGet {oldDest with state := none}
  have frame : Frame h after (StreamRoot dest) := by
    refine ⟨placed.1, placed.2.1, placed.2.2.1, ?_, ?_, ?_⟩
    · simp [after, freed, failed, zeroed, freeIst, allocIstHeap]
    · simp [after, freed, failed, zeroed, freeIst, allocIstHeap] <;> omega
    intro b live outside
    have ne : b ≠ h.nextBlk := fun same => before.good.fresh b (by omega) live
    have midLive : freed.live b := by
      simpa [freed, failed, zeroed, freeIst, allocIstHeap, Heap.live, upd_ne _ _ _ _ ne] using live
    obtain ⟨bytes, words, streams, headers, deflates, inflates, gzstates, ro⟩ :=
      placed.2.2.2.2.2 b midLive outside
    refine ⟨bytes, words, streams, headers, deflates, ?_, gzstates, ro⟩
    exact inflates.trans (by simp [freed, failed, zeroed, freeIst, allocIstHeap, upd_ne _ _ _ _ ne])
  have dead : h.istates h.nextBlk = none := (fresh_dead before.good.fresh (Nat.le_refl _)).2.2.2.2.2.1
  have shape : Shape h freed := by
    intro b
    by_cases equal : b = h.nextBlk
    · subst b
      simp [freed, failed, zeroed, freeIst, allocIstHeap, dead]
    · simp [freed, failed, zeroed, freeIst, allocIstHeap, upd_ne _ _ _ _ equal]
  have fullShape := shape.trans (shape_put freeGet {oldDest with state := none})
  have ledger : LiveChange h after (fun _ => False) (fun _ => False) := by
    intro b
    simpa only [not_false_eq_true, and_true, or_false] using fullShape.live b
  have zsOld : zs ≠ h.nextBlk := by
    intro equal
    have live : h.live zs := by simp [Heap.live, before.good.live.hs]
    exact before.good.fresh zs (by omega) live
  refine ⟨after, run, ?_, ?_, frame, ?_, ?_, ledger⟩
  · rw [copy_stream_get_put_other freed different, ZStreamRef.get_freeIst]
    cases source <;> simpa [failed, zeroed, allocIstHeap, ZStreamRef.get] using before.good.live.hz
  · simpa [after, freed, failed, zeroed, freeIst, allocIstHeap, upd_ne _ _ _ _ zsOld] using before.good.live.hs
  · refine ⟨h.nalloc + 1, by omega, ?_, failure⟩
    simp [after, freed, failed, zeroed, freeIst, allocIstHeap] <;> omega
  · exact ZStreamRef.get_put_same freeGet _

def CopyLayout (h after : Heap) (dest : ZStreamRef) (old : Nat)
    (s copied : InflateState) : Prop :=
  after.istates h.nextBlk = some copied ∧ Frame h after (StreamRoot dest) ∧
  copied = {s with
    strm := some dest, window := copied.window
    lencode := relocateCode old h.nextBlk s.lencode
    distcode := relocateCode old h.nextBlk s.distcode
    next := relocateCode old h.nextBlk s.next} ∧
  (s.window = .null ↔ copied.window = .null) ∧
  (s.window ≠ .null → SameBytePrefix h after s.window copied.window s.whave.toNat) ∧
  (∀ b, InflateOwned h.nextBlk copied b → h.nextBlk ≤ b) ∧
  LiveChange h after (InflateOwned h.nextBlk copied) (fun _ => False)

theorem successful_copy_layout
    {h : Heap} {source dest : ZStreamRef} {zs : Nat} {z oldDest : ZStream} {s : InflateState}
    (before : DefaultOriginState h source zs z s) (allocator : DefAlloc z)
    (get : dest.get h = some oldDest) (different : source ≠ dest)
    (first : h.allocOk h.nalloc = true)
    (second : s.window ≠ .null → h.allocOk (h.nalloc + 1) = true) :
    ∃ after copied, C.run (inflateCopy (some dest) (some source)) h = .ok (Z_OK, after) ∧
      CopyLayout h after dest zs s copied := by
  by_cases window : s.window = .null
  · rcases before.tableOrigin with dynamic | fixed
    · obtain ⟨nextOff, distOff, nextPtr, nextBound, distPtr, distBound, _, _⟩ :=
        CopyTableOrigin.dynamic_geometry before.good dynamic
      obtain ⟨after, run, _source, _state, _dest, copied, stateGet, copiedEq, heapEq⟩ :=
        inflateCopy_dynamic_no_window_exec before.good allocator get different first window
          nextPtr nextBound dynamic distPtr distBound
      subst copied
      refine ⟨after, copiedGeneric dest zs h.nextBlk nextOff distOff .null s, run, stateGet, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [heapEq]
        exact no_window_heap_frame before.good.fresh get _ _
      · exact generic_relocated (Or.inl dynamic) dest .null nextPtr (fun _ => distPtr)
      · simp [copiedGeneric, window]
      · intro impossible
        exact False.elim (impossible window)
      · intro b owned
        rcases owned with state | ownedWindow
        · omega
        · cases ownedWindow
      · rw [heapEq]
        exact no_window_heap_live get _ _ rfl
    · obtain ⟨nextOff, nextPtr, nextBound⟩ := before.good.inv.ptr.1
      have distArg : s.lencode = .ref (.istate_codes zs) 0 → s.distcode = .ref (.istate_codes zs) 0 := by
        intro impossible
        cases fixed.1.symm.trans impossible
      obtain ⟨after, run, _source, _state, _dest, copied, stateGet, copiedEq, heapEq⟩ :=
        inflateCopy_fixed_no_window_exec before.good allocator get different first window
          nextPtr nextBound fixed
      subst copied
      refine ⟨after, copiedGeneric dest zs h.nextBlk nextOff 0 .null s, run, stateGet, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [heapEq]
        exact no_window_heap_frame before.good.fresh get _ _
      · exact generic_relocated (Or.inr fixed) dest .null nextPtr distArg
      · simp [copiedGeneric, window]
      · intro impossible
        exact False.elim (impossible window)
      · intro b owned
        rcases owned with state | ownedWindow
        · omega
        · cases ownedWindow
      · rw [heapEq]
        exact no_window_heap_live get _ _ rfl
  · rcases before.tableOrigin with dynamic | fixed
    · obtain ⟨nextOff, distOff, nextPtr, nextBound, distPtr, distBound, _, _⟩ :=
        CopyTableOrigin.dynamic_geometry before.good dynamic
      obtain ⟨after, run, _source, _state, _dest, stateGet, a, w, ptr, arrayGet, heapEq⟩ :=
        inflateCopy_dynamic_window_contents before.good allocator get different first (second window) window
          nextPtr nextBound dynamic distPtr distBound
      let copied := copiedGeneric dest zs h.nextBlk nextOff distOff (.ref (.blk (h.nextBlk + 1)) 0) s
      refine ⟨after, copied, run, stateGet, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [heapEq]
        exact window_heap_frame before.good.fresh get z s copied a
      · exact generic_relocated (Or.inl dynamic) dest _ nextPtr (fun _ => distPtr)
      · simp [copied, copiedGeneric, window]
      · intro _
        rw [heapEq]
        exact window_heap_prefix before.good dest copied ptr arrayGet rfl
      · intro b owned
        rcases owned with state | ownedWindow
        · omega
        · have equal : h.nextBlk + 1 = b := BRef.blk.inj (Ptr.ref.inj ownedWindow).1
          omega
      · rw [heapEq]
        exact window_heap_live get z s copied a rfl
    · obtain ⟨nextOff, nextPtr, nextBound⟩ := before.good.inv.ptr.1
      have distArg : s.lencode = .ref (.istate_codes zs) 0 → s.distcode = .ref (.istate_codes zs) 0 := by
        intro impossible
        cases fixed.1.symm.trans impossible
      obtain ⟨after, run, _source, _state, _dest, stateGet, a, w, ptr, arrayGet, heapEq⟩ :=
        inflateCopy_fixed_window_contents before.good allocator get different first (second window) window
          nextPtr nextBound fixed
      let copied := copiedGeneric dest zs h.nextBlk nextOff 0 (.ref (.blk (h.nextBlk + 1)) 0) s
      refine ⟨after, copied, run, stateGet, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [heapEq]
        exact window_heap_frame before.good.fresh get z s copied a
      · exact generic_relocated (Or.inr fixed) dest _ nextPtr distArg
      · simp [copied, copiedGeneric, window]
      · intro _
        rw [heapEq]
        exact window_heap_prefix before.good dest copied ptr arrayGet rfl
      · intro b owned
        rcases owned with state | ownedWindow
        · omega
        · have equal : h.nextBlk + 1 = b := BRef.blk.inj (Ptr.ref.inj ownedWindow).1
          omega
      · rw [heapEq]
        exact window_heap_live get z s copied a rfl

#print axioms successful_copy_layout
/-- Exactly the third public copy postcondition, instantiated at a source
whose stronger state is derived by the selected default history. -/
def CopyResult (h after : Heap) (source dest : ZStreamRef) (zs : Nat)
    (z oldDest : ZStream) (s : InflateState) (rc : Int32) : Prop :=
  source.get after = some z ∧ after.istates zs = some s ∧ Frame h after (StreamRoot dest) ∧
  ((rc = Z_MEM_ERROR ∧ AllocationFailed h after ∧
    dest.get after = some {oldDest with state := none} ∧
    LiveChange h after (fun _ => False) (fun _ => False)) ∨
   (rc = Z_OK ∧ ∃ copied,
    Good after dest h.nextBlk {z with state := some (.inflate h.nextBlk)} copied ∧
    copied = {s with
      strm := some dest, window := copied.window
      lencode := relocateCode zs h.nextBlk s.lencode
      distcode := relocateCode zs h.nextBlk s.distcode
      next := relocateCode zs h.nextBlk s.next} ∧
    (s.window = .null ↔ copied.window = .null) ∧
    (s.window ≠ .null → SameBytePrefix h after s.window copied.window s.whave.toNat) ∧
    (∀ b, InflateOwned h.nextBlk copied b → h.nextBlk ≤ b) ∧
    LiveChange h after (InflateOwned h.nextBlk copied) (fun _ => False)))

/-- Actual total copy includes both allocation failures. Allocation successes
are split internally. No actual-run equation is required from the caller. -/
theorem inflateCopy_default_origin_total
    {h : Heap} {source dest : ZStreamRef} {zs : Nat} {z oldDest : ZStream} {s : InflateState}
    (before : DefaultOriginState h source zs z s) (allocator : DefAlloc z)
    (get : dest.get h = some oldDest) (different : source ≠ dest) :
    ∃ rc after, C.run (inflateCopy (some dest) (some source)) h = .ok (rc, after) ∧
      CopyResult h after source dest zs z oldDest s rc ∧
      (rc = Z_OK → ∃ copied,
        DefaultOriginState after dest h.nextBlk {z with state := some (.inflate h.nextBlk)} copied ∧
        DefaultOriginState after source zs z s) := by
  cases first : h.allocOk h.nalloc with
  | false =>
    obtain ⟨after, run, sourceGet, stateGet, frame, failed, destGet, ledger⟩ :=
      first_failure_resources before allocator get different first
    refine ⟨Z_MEM_ERROR, after, run, ⟨sourceGet, stateGet, frame, Or.inl ⟨rfl, failed, destGet, ledger⟩⟩, ?_⟩
    intro impossible
    exact False.elim ((by decide : Z_MEM_ERROR ≠ Z_OK) impossible)
  | true =>
    have success : (s.window ≠ .null → h.allocOk (h.nalloc + 1) = true) →
        ∃ rc after, C.run (inflateCopy (some dest) (some source)) h = .ok (rc, after) ∧
          CopyResult h after source dest zs z oldDest s rc ∧
          (rc = Z_OK → ∃ copied,
            DefaultOriginState after dest h.nextBlk {z with state := some (.inflate h.nextBlk)} copied ∧
            DefaultOriginState after source zs z s) := by
      intro second
      obtain ⟨after, copied, run, layout⟩ := successful_copy_layout before allocator get different first second
      obtain ⟨other, destination, original⟩ :=
        inflateCopy_actual_success_both_origin before allocator get different run
      have equal : other = copied := Option.some.inj (destination.good.live.hs.symm.trans layout.1)
      subst other
      exact ⟨Z_OK, after, run,
        ⟨original.good.live.hz, original.good.live.hs, layout.2.1,
          Or.inr ⟨rfl, copied, destination.good, layout.2.2⟩⟩,
        fun _ => ⟨copied, destination, original⟩⟩
    by_cases window : s.window = .null
    · exact success (fun impossible => False.elim (impossible window))
    · cases second : h.allocOk (h.nalloc + 1) with
      | true => exact success (fun _ => second)
      | false =>
        obtain ⟨after, run, sourceGet, stateGet, frame, failed, destGet, ledger⟩ :=
          second_failure_resources before allocator get different first window second
        refine ⟨Z_MEM_ERROR, after, run, ⟨sourceGet, stateGet, frame, Or.inl ⟨rfl, failed, destGet, ledger⟩⟩, ?_⟩
        intro impossible
        exact False.elim ((by decide : Z_MEM_ERROR ≠ Z_OK) impossible)

/-- History supplies J, the table-pair origin and allocator. The remaining
premises are exactly the original copy target's source/destination geometry. -/
theorem default_history_copy_total
    {h : Heap} {source dest : ZStreamRef} {zs : Nat} {z oldDest : ZStream} {s : InflateState}
    (history : DefaultOriginHistory h source) (good : Good h source zs z s)
    (allocator : DefAlloc z) (different : source ≠ dest) (get : dest.get h = some oldDest) :
    ∃ rc after, C.run (inflateCopy (some dest) (some source)) h = .ok (rc, after) ∧
      CopyResult h after source dest zs z oldDest s rc := by
  obtain ⟨⟨old, stream, state, before, _⟩, _reachable⟩ := history.sound
  have sameStream : stream = z := Option.some.inj (before.good.live.hz.symm.trans good.live.hz)
  subst stream
  have sameIndex : old = zs := StateRef.inflate.inj (Option.some.inj (before.good.live.zst.symm.trans good.live.zst))
  subst old
  have sameState : state = s := Option.some.inj (before.good.live.hs.symm.trans good.live.hs)
  subst state
  obtain ⟨rc, after, run, result, _origins⟩ := inflateCopy_default_origin_total before allocator get different
  exact ⟨rc, after, run, result⟩

theorem inflateCopy_null_destination (h : Heap) (source : ZStreamPtr) :
    C.run (inflateCopy none source) h = .ok (Z_STREAM_ERROR, h) := by
  simp [C.run, inflateCopy]

theorem inflateCopy_null_source {h : Heap} {dest : ZStreamRef} {oldDest : ZStream}
    (get : dest.get h = some oldDest) :
    C.run (inflateCopy (some dest) none) h =
      .ok (Z_STREAM_ERROR, dest.put h {oldDest with state := none}) := by
  have writable : dest.isRo = false := by cases dest <;> rfl
  simp [C.run, inflateCopy, inflateStateCheck, wrZ_eq, get, writable]

/-- The public copy target's two refusal clauses and complete resource
conclusion, with only its reachable-source domain specialized to the
announced default history. Other destination fields are unrestricted. -/
theorem default_public_copy_contract :
    (∀ h source, C.run (inflateCopy none source) h = .ok (Z_STREAM_ERROR, h)) ∧
    (∀ h dest oldDest, dest.get h = some oldDest →
      C.run (inflateCopy (some dest) none) h =
        .ok (Z_STREAM_ERROR, dest.put h {oldDest with state := none})) ∧
    (∀ h source zs z s dest oldDest,
      DefaultOriginHistory h source → Good h source zs z s → DefAlloc z →
      source ≠ dest → dest.get h = some oldDest →
      ∃ rc after, C.run (inflateCopy (some dest) (some source)) h = .ok (rc, after) ∧
        CopyResult h after source dest zs z oldDest s rc) := by
  exact ⟨inflateCopy_null_destination, fun _ _ _ get => inflateCopy_null_source get,
    fun _ _ _ _ _ _ _ history good allocator different get =>
      default_history_copy_total history good allocator different get⟩

/-- A caller supplies only selected actual history and the original
source/destination record geometry. J and allocator facts are conclusions
of history soundness, and successful destination history is produced. -/
theorem default_history_copy_total_derived
    {h : Heap} {source dest : ZStreamRef} {oldDest : ZStream}
    (history : DefaultOriginHistory h source) (different : source ≠ dest)
    (get : dest.get h = some oldDest) :
    ∃ zs z s rc after, DefaultOriginState h source zs z s ∧ DefAlloc z ∧
      C.run (inflateCopy (some dest) (some source)) h = .ok (rc, after) ∧
      CopyResult h after source dest zs z oldDest s rc ∧
      (rc = Z_OK → DefaultOriginHistory after dest) ∧
      (rc = Z_OK → ∃ copied,
        DefaultOriginState after dest h.nextBlk {z with state := some (.inflate h.nextBlk)} copied ∧
        DefaultOriginState after source zs z s) := by
  obtain ⟨⟨zs, z, s, before, allocator⟩, _reachable⟩ := history.sound
  obtain ⟨rc, after, run, result, origins⟩ := inflateCopy_default_origin_total before allocator get different
  refine ⟨zs, z, s, rc, after, before, allocator, run, result, ?_, origins⟩
  intro success
  exact .copy history different get (by simpa only [success] using run)

#print axioms default_history_copy_total_derived
#print axioms inflateCopy_null_destination
#print axioms inflateCopy_null_source
#print axioms default_public_copy_contract
#print axioms first_failure_resources
#print axioms second_failure_resources
#print axioms window_heap_prefix
#print axioms inflateCopy_default_origin_total
#print axioms default_history_copy_total
#print axioms no_window_heap_frame
#print axioms no_window_heap_live
#print axioms window_heap_frame
#print axioms window_heap_live
end Zlib.Inflate.Proofs.CopyResource
