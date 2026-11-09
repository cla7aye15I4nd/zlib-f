import ZlibF.Proof.«inflate.c.sync-done-origin»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The sync input-search state write changes only its scalar search count
and stream cursors. The exact pointer value comes from actual arithmetic;
it need not be supplied as a callee safety contract. -/
theorem default_origin_sync_search_state {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (before : DefaultOriginState h r zs z s)
    (mode : s.mode = SYNC) (used found : UInt32) (next : BPtr) :
    let stream := { z with avail_in := z.avail_in - used, next_in := next, total_in := z.total_in + used.toUInt64 }
    DefaultOriginState (setI (r.put h stream) zs (syncHave s found)) r zs stream (syncHave s found) := by
  dsimp only
  let stream := { z with avail_in := z.avail_in - used, next_in := next, total_in := z.total_in + used.toUInt64 }
  let state := syncHave s found
  have currentMode : state.mode = SYNC := mode
  have inv : StInv h zs state := before.good.inv.of_fields rfl rfl rfl rfl rfl rfl rfl rfl rfl
    before.good.inv.bits rfl rfl rfl
  have good : Good (setI (r.put h stream) zs state) r zs stream state :=
    before.good.setZI rfl before.good.live.zalloc before.good.live.zfree rfl before.good.live.mode inv
  have tables : DataTableInvariant (setI (r.put h stream) zs state) state :=
    dataTableInvariant_inactive (by rw [currentMode]; unfold DataTableMode; decide)
  have pending : DataPendingInvariant state :=
    dataPendingInvariant_idle before.pending.sane (by rw [currentMode]; decide)
  have sizes := (byte_view_sizes_stream_put h r stream).trans
    (byte_view_sizes_setI (r.put h stream) zs state)
  have current : DefaultStateJ (setI (r.put h stream) zs state) r zs stream state := by
    refine ⟨⟨good, tables, pending, ?_, ?_, before.held, before.window, before.wrapper,
      before.header, Or.inr ?_, ?_, ?_, sizes.platform before.platform⟩,
      before.requestedBits, before.requestedWrap, Or.inr (Or.inr (Or.inr (Or.inl currentMode)))⟩
    · intro active
      change state.mode = CODELENS at active
      rw [currentMode] at active
      contradiction
    · intro active
      change state.mode = LENLENS at active
      rw [currentMode] at active
      contradiction
    · rw [currentMode]
      decide
    · rintro (active | active) <;> rw [currentMode] at active <;> contradiction
    · simpa only [LibraryGlobals, setI, ZStreamRef.put_static] using before.globals
  exact ⟨current, before.flagsOrigin, before.tableOrigin⟩

/-- An actual completed input-search tail retains the origin state on
both DATA_ERROR and successful recovery. Read-only search and pointer
arithmetic are observed from execution; no callee contract or raw-input
restriction is assumed. -/
theorem syncTail_default_origin_of_run {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {rc : Int32} (before : DefaultOriginState h r zs z s)
    (allocator : DefAlloc z) (mode : s.mode = SYNC)
    (actual : C.run (syncTail (some r) (some (.tab zs))) h = .ok (rc, after)) :
    ∃ stream state, DefaultOriginState after r zs stream state ∧ DefAlloc stream ∧
      after.bytes = h.bytes ∧ after.ro = h.ro := by
  change syncTail (some r) (some (.tab zs)) h = _ at actual
  unfold syncTail at actual
  simp only [bind_app, ldZ_eq, before.good.live.hz, rdI_eq, before.good.live.hs] at actual
  cases searchRun : syncsearch s.«have» z.next_in z.avail_in h with
  | error fault => rw [searchRun] at actual; cases actual
  | ok pair =>
    obtain ⟨⟨used, found⟩, middle⟩ := pair
    have same := syncsearch_heap_unchanged searchRun
    subst middle
    rw [searchRun] at actual
    simp only [bind_app, wrI_eq, before.good.live.hs] at actual
    cases addRun : Ptr.add z.next_in (used.toNat : Int) (setI h zs { s with «have» := found }) with
    | error fault => rw [addRun] at actual; cases actual
    | ok pair =>
      obtain ⟨next, middle⟩ := pair
      have same := sync_pointer_add_heap addRun
      subst middle
      rw [addRun] at actual
      simp only [bind_app, wrZ_eq, ZStreamRef.get_setI, before.good.live.hz,
        rdI_eq, ZStreamRef.put_istates, setI_istates_same, ZStreamRef.put_setI] at actual
      let stream := { z with avail_in := z.avail_in - used, next_in := next, total_in := z.total_in + used.toUInt64 }
      let state := syncHave s found
      let heap := setI (r.put h stream) zs state
      have current : DefaultOriginState heap r zs stream state :=
        default_origin_sync_search_state before mode used found next
      by_cases finish : found = 4
      · subst found
        simp only [show ((4 : UInt32) != 4) = false from by decide, Bool.false_eq_true, ↓reduceIte] at actual
        have complete := syncDone_default_origin_run current allocator.2
        have noFree : resetHeap heap state = heap := by
          simp [resetHeap, current.window, current.requestedBits]
        have finalBits : (syncC zs state).wbits = 15 :=
          (syncC_field zs state).1.trans current.requestedBits
        have doneHeap : syncOkHeap heap r zs stream state =
            setI (r.put heap (syncOkStream stream state)) zs (syncOkState zs state) := by
          simp [syncOkHeap, noFree, finalBits]
        have aligned := Except.ok.inj (complete.1.symm.trans actual)
        have heapEq : syncOkHeap heap r zs stream state = after := congrArg Prod.snd aligned
        rw [← heapEq]
        refine ⟨syncOkStream stream state, syncOkState zs state, complete.2, ?_, ?_, ?_⟩
        · simpa only [DefAlloc, syncOkStream, resetKeepStream, stream] using allocator
        · rw [doneHeap]
          simp only [heap, setI, ZStreamRef.put_bytes]
        · rw [doneHeap]
          simp only [heap, setI, ZStreamRef.put_ro]
      · simp [finish] at actual
        have heapEq : heap = after := actual.2
        rw [← heapEq]
        refine ⟨stream, state, current, allocator, ?_, ?_⟩
        · simp only [heap, setI, ZStreamRef.put_bytes]
        · simp only [heap, setI, ZStreamRef.put_ro]

#print axioms default_origin_sync_search_state
#print axioms syncTail_default_origin_of_run
end Zlib.Inflate.Proofs
