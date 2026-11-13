import ZlibF.Proof.«inflate.c.copy-public»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- `int inflateCopy(z_streamp dest, z_streamp source)`.
Null arguments are refused; from every reachable source the copy returns,
writes only the destination record and new blocks, and either fails with a
genuine allocation failure that frees what it allocated, or succeeds with the
relocated state, the window prefix and exactly its new blocks in the ledger. -/
theorem inflate_copy_public : ZlibF.Spec.Public.Goal.inflateCopy := by
  refine ⟨fun h source => inflateCopy_null_dest h source,
    fun h dest z get => inflateCopy_null_source get, ?_⟩
  intro h source i z s dest oldDest reach good allocator different destGet
  obtain ⟨current, _⟩ := inflate_reachable_invariant reach good
  have fresh := good.fresh
  have stateBelow : i < h.nextBlk := live_lt_next fresh (by simp [Heap.live, good.live.hs])
  cases first : h.allocOk h.nalloc with
  | false =>
    have run := inflateCopy_first_allocation_failure good allocator destGet first
    obtain ⟨after', run', destState, failed, ledger⟩ :=
      inflateCopy_first_failure_cleanup good allocator destGet first
    have same := Except.ok.inj (run'.symm.trans run)
    cases same
    refine ⟨Z_MEM_ERROR, _, run, ?_, ?_, ?_, Or.inl ⟨rfl, failed, destState, ledger⟩⟩
    · rw [copy_stream_get_put_other _ different]
      cases source <;> simpa [ZStreamRef.get] using good.live.hz
    · simpa using good.live.hs
    · refine copy_frame fresh (by simp) (by simp) (by simp) (by simp) (by simp) ?_
      intro b _ root
      obtain ⟨streams, gzstates⟩ := put_other_block { h with nalloc := h.nalloc + 1 } dest
        { oldDest with state := none } root
      exact ⟨by simp, by simp, streams, by simp, by simp, by simp, gzstates, by simp⟩
  | true =>
    by_cases window : s.window = .null
    · rcases current.origin with dynamic | fixed
      · obtain ⟨nextOff, distOff, nextPtr, nextBound, distPtr, distBound, _, _⟩ :=
          CopyTableOrigin.dynamic_geometry good dynamic
        obtain ⟨after, run, sourceGet, stateGet, destAfter, copied, copiedGet, copiedEq, heapEq⟩ :=
          inflateCopy_dynamic_no_window_exec good allocator destGet different first window nextPtr
            nextBound dynamic distPtr distBound
        subst copiedEq
        obtain ⟨frame, success⟩ := copy_no_window_success current different destGet window nextPtr
          (Or.inl ⟨dynamic, distPtr⟩) run destAfter copiedGet heapEq
        exact ⟨Z_OK, after, run, sourceGet, stateGet, frame, Or.inr ⟨rfl, success⟩⟩
      · obtain ⟨nextOff, nextPtr, nextBound⟩ := good.inv.ptr.1
        obtain ⟨after, run, sourceGet, stateGet, destAfter, copied, copiedGet, copiedEq, heapEq⟩ :=
          inflateCopy_fixed_no_window_exec good allocator destGet different first window nextPtr
            nextBound fixed
        subst copiedEq
        obtain ⟨frame, success⟩ := copy_no_window_success (distOff := 0) current different destGet
          window nextPtr (Or.inr fixed) run destAfter copiedGet heapEq
        exact ⟨Z_OK, after, run, sourceGet, stateGet, frame, Or.inr ⟨rfl, success⟩⟩
    · cases second : h.allocOk (h.nalloc + 1) with
      | false =>
        have run := inflateCopy_window_allocation_failure good allocator destGet first window second
        dsimp only at run
        obtain ⟨frame, ledger, count⟩ := copy_second_failure_heap
          (v := { oldDest with state := none }) destGet fresh
        refine ⟨Z_MEM_ERROR, _, run, ?_, ?_, frame, Or.inl ⟨rfl, ?_, ?_, ledger⟩⟩
        · rw [copy_stream_get_put_other _ different]
          cases source <;> simpa [ZStreamRef.get, freeIst, allocIstHeap] using good.live.hz
        · have ne : i ≠ h.nextBlk := by omega
          simpa [freeIst, allocIstHeap, upd_ne _ _ _ _ ne] using good.live.hs
        · exact ⟨h.nalloc + 1, by omega, by rw [count]; omega, second⟩
        · simp only [ZStreamRef.get_put]
          cases dest with
          | tab k =>
            have e : h.streams k = some oldDest := destGet
            simp [ZStreamRef.get, freeIst, allocIstHeap, e]
          | in_gzstate_strm k =>
            cases e : h.gzstates k with
            | none => simp [ZStreamRef.get, e] at destGet
            | some g =>
              simp [ZStreamRef.get, e] at destGet
              simp [ZStreamRef.get, freeIst, allocIstHeap, e, ← destGet]
      | true =>
        rcases current.origin with dynamic | fixed
        · obtain ⟨nextOff, distOff, nextPtr, nextBound, distPtr, distBound, _, _⟩ :=
            CopyTableOrigin.dynamic_geometry good dynamic
          obtain ⟨after, run, sourceGet, stateGet, destAfter, copiedGet, sourceArray, w, ptr, get,
            heapEq⟩ := CopyResource.inflateCopy_dynamic_window_contents good allocator destGet different first second
              window nextPtr nextBound dynamic distPtr distBound
          obtain ⟨frame, success⟩ := copy_window_success current different destGet nextPtr
            (Or.inl ⟨dynamic, distPtr⟩) run destAfter copiedGet ptr get heapEq
          exact ⟨Z_OK, after, run, sourceGet, stateGet, frame, Or.inr ⟨rfl, success⟩⟩
        · obtain ⟨nextOff, nextPtr, nextBound⟩ := good.inv.ptr.1
          obtain ⟨after, run, sourceGet, stateGet, destAfter, copiedGet, sourceArray, w, ptr, get,
            heapEq⟩ := CopyResource.inflateCopy_fixed_window_contents good allocator destGet different first second
              window nextPtr nextBound fixed
          obtain ⟨frame, success⟩ := copy_window_success (distOff := 0) current different destGet
            nextPtr (Or.inr fixed) run destAfter copiedGet ptr get heapEq
          exact ⟨Z_OK, after, run, sourceGet, stateGet, frame, Or.inr ⟨rfl, success⟩⟩

#print axioms inflate_copy_public
end Zlib.Inflate.Proofs
