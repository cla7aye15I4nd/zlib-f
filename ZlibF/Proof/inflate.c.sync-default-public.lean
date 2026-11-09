import ZlibF.Proof.«inflate.c.sync-default-origin»
import ZlibF.Proof.«inflate.c.construction-record-read-tail»
import ZlibF.Proof.«inflate.c.output-frame-local-cleanup»
import ZlibF.Proof.«inflate.c.live-frame-local»
import ZlibF.Spec.Public.Sequences

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Readable public Sync input supplies a total real search for every
search-counter value. No semantic search-history hypothesis is needed. -/
theorem syncsearch_public_readable {h : Heap} {p : BPtr} {len : UInt32}
    (range : p = .null ∨ ∃ xs, Bytes h p len.toNat xs) (nonnull : p = .null → len = 0) (start : UInt32) :
    ∃ used found, syncsearch start p len h = .ok ((used, found), h) ∧ used.toNat ≤ len.toNat := by
  rcases range with null | ⟨xs, bytes⟩
  · subst p
    have zero := nonnull rfl
    subst len
    exact ⟨0, start, syncsearch_null start h, Nat.le_refl _⟩
  · rcases bytes with ⟨null, zero, _⟩ | ⟨ref, off, array, ptr, get, room, _⟩
    · subst p
      have zero := nonnull rfl
      subst len
      exact ⟨0, start, syncsearch_null start h, Nat.le_refl _⟩
    · subst p
      refine ⟨UInt32.ofNat (syncScan start (syncBytes array off len)).2,
        (syncScan start (syncBytes array off len)).1, syncsearch_run start get room, ?_⟩
      have bound := syncScan_le start (syncBytes array off len)
      have length := syncBytes_length room
      have size := len.toNat_lt
      rw [UInt32.toNat_ofNat_of_lt' (by simp only [UInt32.size]; omega)]
      omega

/-- The pointer advance after a real bounded search is defined on the
same caller byte object. Zero-length null input takes the zero advance. -/
theorem sync_public_input_add {h : Heap} {p : BPtr} {len used : UInt32}
    (range : p = .null ∨ ∃ xs, Bytes h p len.toNat xs) (nonnull : p = .null → len = 0)
    (bound : used.toNat ≤ len.toNat) (zs : Nat) (state : InflateState) :
    ∃ next, Ptr.add p (used.toNat : Int) (setI h zs state) = .ok (next, setI h zs state) := by
  rcases range with null | ⟨xs, bytes⟩
  · subst p
    have zero := nonnull rfl
    have usedZero : used.toNat = 0 := by rw [zero] at bound; simpa using bound
    rw [usedZero]
    exact ⟨.null, rfl⟩
  · rcases bytes with ⟨null, zero, _⟩ | ⟨ref, off, array, ptr, get, room, _⟩
    · subst p
      have zero := nonnull rfl
      have usedZero : used.toNat = 0 := by rw [zero] at bound; simpa using bound
      rw [usedZero]
      exact ⟨.null, rfl⟩
    · subst p
      exact ⟨.ref ref (off + used.toNat), Ptr.add_nat_ok (by simpa only [byte_view_get_setI] using get) (by omega)⟩

/-- The complete default Sync input-search tail returns on every readable
caller input. Both real search outcomes preserve initialized origin state
and modify only the existing stream and private decoder records. -/
theorem syncTail_default_origin_total {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (before : DefaultOriginState h r zs z s) (allocator : DefAlloc z)
    (mode : s.mode = SYNC) (range : z.next_in = .null ∨ ∃ xs, Bytes h z.next_in z.avail_in.toNat xs)
    (nonnull : z.next_in = .null → z.avail_in = 0) :
    ∃ rc after stream state,
      C.run (syncTail (some r) (some (.tab zs))) h = .ok (rc, after) ∧
      DefaultOriginState after r zs stream state ∧ DefAlloc stream ∧
      RecordFrame r (some (.tab zs)) h after ∧
      after = setI (r.put h stream) zs state ∧ state.window = s.window ∧ (rc = Z_OK ∨ rc = Z_DATA_ERROR) := by
  obtain ⟨used, found, search, bound⟩ := syncsearch_public_readable range nonnull s.«have»
  obtain ⟨next, advance⟩ := sync_public_input_add range nonnull bound zs { s with «have» := found }
  let stream := { z with avail_in := z.avail_in - used, next_in := next, total_in := z.total_in + used.toUInt64 }
  let state := syncHave s found
  let heap := setI (r.put h stream) zs state
  have current : DefaultOriginState heap r zs stream state := default_origin_sync_search_state before mode used found next
  have tailPrefix : C.run (syncTail (some r) (some (.tab zs))) h =
      (if found != 4 then pure Z_DATA_ERROR else syncDone (some r) (some (.tab zs))) heap := by
    unfold C.run syncTail
    simp only [bind_app, ldZ_eq, rdI_eq, before.good.live.hs, search,
      wrI_eq, advance, wrZ_eq, ZStreamRef.get_setI, before.good.live.hz,
      setI_istates_same, ZStreamRef.put_setI]
    rfl
  have frame : RecordFrame r (some (.tab zs)) h heap := RecordFrame.stream_state before.good.live.hz before.good.live.hs stream state
  by_cases complete : found = 4
  · subst found
    obtain ⟨doneRun, doneJ⟩ := syncDone_default_origin_run current allocator.2
    have noFree : resetHeap heap state = heap := by simp [resetHeap, current.window, current.requestedBits]
    have finalBits : (syncC zs state).wbits = 15 := (syncC_field zs state).1.trans current.requestedBits
    have doneHeap : syncOkHeap heap r zs stream state = setI (r.put heap (syncOkStream stream state)) zs (syncOkState zs state) := by
      simp [syncOkHeap, noFree, finalBits]
    have heapEq : syncOkHeap heap r zs stream state = setI (r.put h (syncOkStream stream state)) zs (syncOkState zs state) := by
      rw [doneHeap]
      simp only [heap, ZStreamRef.put_setI, ZStreamRef.put_put, setI_setI]
    refine ⟨Z_OK, syncOkHeap heap r zs stream state, syncOkStream stream state, syncOkState zs state, ?_, doneJ, ?_, ?_, heapEq, ?_, Or.inl rfl⟩
    · rw [tailPrefix]; simpa only [C.run, bne_self_eq_false, Bool.false_eq_true, ite_false] using doneRun
    · simpa only [DefAlloc, syncOkStream, resetKeepStream, stream] using allocator
    · rw [doneHeap]
      exact frame.trans (RecordFrame.stream_state current.good.live.hz current.good.live.hs _ _)
    · rw [syncOkState_ne0 (by rw [current.requestedBits]; decide)]
      change (syncC zs state).window = s.window
      rw [(syncC_field zs state).2.1, resetPre_window]
      simp only [current.window, current.requestedBits, ite_true]
      rfl
  · refine ⟨Z_DATA_ERROR, heap, stream, state, ?_, current, allocator, frame, rfl, rfl, Or.inr rfl⟩
    rw [tailPrefix]
    simp [complete, pure_app]


/-- Restoring held bytes writes only the fresh local block. Every original
readable input object, including static and embedded byte views, survives. -/
theorem sync_readable_first {h : Heap} {p : BPtr} {len : UInt32} {zs : Nat} {s : InflateState}
    (fresh : Fresh h) (range : p = .null ∨ ∃ xs, Bytes h p len.toNat xs) :
    p = .null ∨ ∃ xs, Bytes (syncFirstHeap (syncAlloc h) zs h.nextBlk s (syncJunk h)) p len.toNat xs := by
  rcases range with null | ⟨xs, bytes⟩
  · exact Or.inl null
  · right
    refine ⟨xs, ?_⟩
    rcases bytes with null | ⟨ref, off, array, ptr, get, room, values⟩
    · exact Or.inl null
    · refine Or.inr ⟨ref, off, array, ptr, ?_, room, values⟩
      have separate := original_byte_view_not_local fresh get
      have allocated := (byte_view_syncAlloc fresh get).1
      cases ref with
      | blk block =>
        have different : block ≠ h.nextBlk := fun equal => separate (by rw [equal])
        simpa only [syncFirstHeap, Space.get, upd_ne _ _ _ _ different] using allocated
      | str _ | st_dist_code | st_length_code | dstate_depth _ =>
        simpa only [syncFirstHeap, Space.get] using allocated

/-- Every legal default Sync call returns. The actual scratch declaration,
held-byte restoration, general caller search, reset and free are included.
Only the corrected public readable-input arguments are required. -/
theorem inflateSync_default_origin_total {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (before : DefaultOriginState h r zs z s) (allocator : DefAlloc z)
    (arguments : StreamArguments h r (.inflateSync (some r))) :
    ∃ rc after stream state,
      C.run (inflateSync (some r)) h = .ok (rc, after) ∧
      DefaultOriginState after r zs stream state ∧ DefAlloc stream ∧
      after = setI (r.put (tmpFreed h) stream) zs state ∧ state.window = s.window ∧
      (rc = Z_OK ∨ rc = Z_DATA_ERROR ∨ rc = Z_BUF_ERROR) := by
  obtain ⟨z0, get0, nonnull, range⟩ := arguments
  have sameZ : z0 = z := Option.some.inj (get0.symm.trans before.good.live.hz)
  subst z0
  have readable : z.next_in = .null ∨ ∃ xs, Bytes h z.next_in z.avail_in.toNat xs := by
    rcases range with null | ⟨bytes, _⟩
    · exact Or.inl null
    · exact Or.inr bytes
  have allocated := default_origin_syncAlloc before
  have localGet := syncAlloc_bytes_buf h
  have localSize : (syncJunk h).size = 4 := by simp [syncJunk]
  have localWrite := syncAlloc_ro_buf h
  by_cases empty : z.avail_in = 0 ∧ s.bits < 8
  · have run := inflateSync_buf_error before.good empty.1 empty.2
    have final := allocated.free_local localGet localSize
    refine ⟨Z_BUF_ERROR, tmpFreed h, z, s, run, final, allocator, ?_, rfl, Or.inr (Or.inr rfl)⟩
    have getZ : r.get (tmpFreed h) = some z := final.good.live.hz
    have getS : (tmpFreed h).istates zs = some s := final.good.live.hs
    rw [ZStreamRef.put_self getZ, tcSetI_same getS]
  have readable0 : z.next_in = .null ∨ ∃ xs, Bytes (syncAlloc h) z.next_in z.avail_in.toNat xs := by
    rcases callerRange_syncAlloc before.good.fresh range with null | ⟨bytes, _⟩
    · exact Or.inl null
    · exact Or.inr bytes
  by_cases resumed : s.mode = SYNC
  · obtain ⟨rc, middle, stream, state, tailRun, current, currentAllocator, frame, exactHeap, finalWindow, kinds⟩ :=
      syncTail_default_origin_total allocated allocator resumed readable0 nonnull
    have get : middle.bytes h.nextBlk = some (syncJunk h) := by
      rw [exactHeap, setI_bytes, ZStreamRef.put_bytes]
      exact localGet
    have write : middle.ro h.nextBlk = false := by rw [frame.2.2.2]; exact localWrite
    have free := freeBuf_run get write
    simp only [C.run] at tailRun
    refine ⟨rc, freeWin middle (syncBuf h), stream, state, ?_, current.free_local get localSize, currentAllocator, ?_, finalWindow, ?_⟩
    · unfold C.run
      rw [inflateSync_split]
      simp [bind_app, syncBuf, allocLocalB_run h before.good.fresh, stateCheck_live allocated.good.live,
        ldZ_eq, allocated.good.live.hz, allocated.good.live.zst, castI, ldI_eq, before.good.live.hs,
        Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, empty, bne_iff_ne, resumed, pure_app, tailRun, free]
    · rw [exactHeap]
      rw [← setI_freeWin, ← ZStreamRef.put_freeWin]
      rfl
    · rcases kinds with good | bad
      · exact Or.inl good
      · exact Or.inr (Or.inl bad)
  · obtain ⟨firstRun, firstJ⟩ := syncFirst_default_origin_run allocated localGet localSize localWrite
      (win_ne_buf before.good.fresh before.good.inv.win)
    simp only [C.run] at firstRun
    have firstReadable := sync_readable_first (zs := zs) (s := s) before.good.fresh readable
    obtain ⟨rc, middle, stream, state, tailRun, current, currentAllocator, frame, exactHeap, finalWindow, kinds⟩ :=
      syncTail_default_origin_total firstJ allocator rfl firstReadable nonnull
    have get : middle.bytes h.nextBlk = some (fillBuf (syncJunk h) (syncHold0 s) (syncNB s)) := by
      rw [exactHeap, setI_bytes, ZStreamRef.put_bytes]
      simp only [syncFirstHeap, upd_same]
    have size : (fillBuf (syncJunk h) (syncHold0 s) (syncNB s)).size = 4 := by rw [fillBuf_size]; exact localSize
    have write : middle.ro h.nextBlk = false := by rw [frame.2.2.2]; exact localWrite
    have free := freeBuf_run get write
    simp only [C.run] at tailRun
    refine ⟨rc, freeWin middle (syncBuf h), stream, state, ?_, current.free_local get size, currentAllocator, ?_, finalWindow, ?_⟩
    · unfold C.run
      rw [inflateSync_split]
      simp [bind_app, syncBuf, allocLocalB_run h before.good.fresh, stateCheck_live allocated.good.live,
        ldZ_eq, allocated.good.live.hz, allocated.good.live.zst, castI, ldI_eq, before.good.live.hs,
        Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, empty, bne_iff_ne, resumed, firstRun, tailRun, free, pure_app]
    · rw [exactHeap]
      rw [← setI_freeWin, ← ZStreamRef.put_freeWin]
      have freedFirst : freeWin (syncFirstHeap (syncAlloc h) zs h.nextBlk s (syncJunk h)) (syncBuf h) =
          setI (tmpFreed h) zs (syncFirstState s) := by
        simp only [freeWin, syncBuf, syncFirstHeap, setI, tmpFreed, upd_upd]
      rw [freedFirst, ZStreamRef.put_setI, setI_setI]
    · rcases kinds with good | bad
      · exact Or.inl good
      · exact Or.inr (Or.inl bad)


/-- The actual local allocation/free retains the entire live-object shape.
Its fresh, now-dead byte slot cannot remove an earlier caller allocation. -/
theorem sync_tmp_freed_shape {h : Heap} (fresh : Fresh h) : Shape h (tmpFreed h) := by
  intro b
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  by_cases same : b = h.nextBlk
  · subst b
    have absent := (fresh_dead fresh (Nat.le_refl h.nextBlk)).1
    simp only [tmpFreed, freeWin, syncBuf, upd_same, absent]
  · simp only [tmpFreed, freeWin, syncBuf, syncAlloc, upd_ne _ _ _ _ same]

/-- The default Sync public safety contract. The real translated call
returns from every corrected public caller input, preserves initialized
origins, modifies only the stream/private records and retains its exact
ownership ledger. Search semantics is not assumed as a callee contract. -/
theorem inflateSync_default_public_contract {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (before : DefaultOriginState h r zs z s) (allocator : DefAlloc z)
    (arguments : StreamArguments h r (.inflateSync (some r))) :
    ∃ rc after stream state,
      C.run (inflateSync (some r)) h = .ok (rc, after) ∧
      DefaultOriginState after r zs stream state ∧ DefAlloc stream ∧
      (rc = Z_OK ∨ rc = Z_DATA_ERROR ∨ rc = Z_BUF_ERROR) ∧
      BufferFrame h after
        (fun b => StreamRoot r b ∨ StreamOwned h r b ∨ StreamHeaderRecord h r (.inflateSync (some r)) b)
        (StreamWriteRegions h r (.inflateSync (some r))) ∧
      LiveChange h after
        (fun b => StreamOwned after r b ∧ ¬ h.live b)
        (fun b => StreamOwned h r b ∧ ¬ StreamOwned after r b) := by
  obtain ⟨rc, after, stream, state, run, current, currentAllocator, exactHeap, window, kinds⟩ :=
    inflateSync_default_origin_total before allocator arguments
  have baseShape := sync_tmp_freed_shape before.good.fresh
  have getZ : r.get (tmpFreed h) = some z := by
    simpa only [tmpFreed, ZStreamRef.get_freeWin, ZStreamRef.get_syncAlloc] using before.good.live.hz
  have getS : (tmpFreed h).istates zs = some s := before.good.live.hs
  have metadata := RecordFrame.stream_state getZ getS stream state
  rw [← exactHeap] at metadata
  have shape := baseShape.trans metadata.2.2.1
  have owned : ∀ b, StreamOwned after r b ↔ StreamOwned h r b := by
    intro b
    rw [current.good.streamOwned_iff, before.good.streamOwned_iff]
    simp only [InflateOwned, window]
  refine ⟨rc, after, stream, state, run, current, currentAllocator, kinds, ?_, ?_⟩
  · have temporary := tmp_freed_buffer_frame (h := h) before.good.fresh
      (fun b => StreamRoot r b ∨ DecoderRecordRoot (some (.tab zs)) b) []
    have frame := frame_trans_shape temporary.1 metadata.1 baseShape
    refine ⟨?_, ?_⟩
    · change Frame h after _
      obtain ⟨statics, allocations, garbage, frontier, count, outside⟩ := frame
      refine ⟨statics, allocations, garbage, frontier, count, ?_⟩
      intro b live unmodified
      apply outside b live
      rintro (streamRoot | stateRoot)
      · exact unmodified (Or.inl streamRoot)
      · apply unmodified
        right
        left
        apply (before.good.streamOwned_iff b).mpr
        exact Or.inl stateRoot
    · intro region member
      cases member
  · intro b
    have ownerLive : StreamOwned h r b → h.live b := fun owner =>
      good_inflate_owned_live before.good ((before.good.streamOwned_iff b).mp owner)
    dsimp only
    rw [owned, shape.live b]
    simp only [and_not_self, not_false_eq_true, and_true]
    constructor
    · exact Or.inl
    · rintro (old | ⟨owner, fresh⟩)
      · exact old
      · exact False.elim (fresh (ownerLive owner))

#print axioms syncsearch_public_readable
#print axioms sync_public_input_add
#print axioms syncTail_default_origin_total
#print axioms sync_readable_first
#print axioms inflateSync_default_origin_total
#print axioms sync_tmp_freed_shape
#print axioms inflateSync_default_public_contract
end Zlib.Inflate.Proofs
