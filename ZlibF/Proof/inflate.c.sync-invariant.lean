import ZlibF.Proof.«inflate.c.dictionary-invariant»
import ZlibF.Proof.«inflate.c.sync-default-origin»

/-!
# inflate.c: `inflateSync` preserves the general invariant

Every actual return: the early buffer refusal, the restore of held bits,
the input search with or without a found pattern, and the successful
resynchronization, which resets the decoder, may free the window and sets a
width of 15 when no header gave one. The four-byte local buffer is freed in
every path.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual run behind a public call that returned. -/
theorem run_of_heapCall {α : Type} {program : M α} {h after : Heap} {value : α}
    {fs fs' : Zlib.GzFs.Fs} (call : heapCall program fs h = .ok ((value, fs'), after)) :
    C.run program h = .ok (value, after) := by
  change program h = _
  cases e : program h with
  | error f => simp [heapCall, e] at call
  | ok p =>
    obtain ⟨v, a⟩ := p
    simp [heapCall, e] at call
    obtain ⟨⟨rfl, -⟩, rfl⟩ := call
    rfl

/-- A four-byte block is never the window. -/
theorem InflateInv.local_not_window {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} {block : Nat} {array : Array UInt8} (current : InflateInv h r zs z s)
    (get : h.bytes block = some array) (size : array.size = 4) :
    s.window ≠ .ref (.blk block) 0 := by
  rcases current.config.window with range | ⟨_, null, _⟩
  · exact default_local_not_window current.good get size range.1
  · rw [null]
    intro same
    cases same

/-- Code-table views do not read byte storage. -/
theorem dataTableInvariant_of_views {h after : Heap} {s : InflateState}
    (tables : DataTableInvariant h s)
    (views : ∀ ref : CodeRef, (Space.get after ref : Option (Array Code)) = Space.get h ref) :
    DataTableInvariant after s := by
  intro active
  have old := tables active
  constructor
  · obtain ⟨ref, offset, array, pointer, get, safe⟩ := old.lengthTable
    exact ⟨ref, offset, array, pointer, (views ref).trans get, safe⟩
  · obtain ⟨ref, offset, array, pointer, get, safe⟩ := old.distanceTable
    exact ⟨ref, offset, array, pointer, (views ref).trans get, safe⟩

/-- The local allocation keeps the invariant. -/
theorem InflateInv.sync_alloc {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} (current : InflateInv h r zs z s) :
    InflateInv (syncAlloc h) r zs z s := by
  have tables : DataTableInvariant (syncAlloc h) s :=
    dataTableInvariant_of_views current.tables (fun ref => by cases ref <;> rfl)
  exact ⟨good_syncAlloc current.good, current.alloc, tables, current.pending, current.lengths,
    current.headerLengths, current.held, current.config, current.modes, current.phase,
    current.origin, current.globals⟩

/-- Freeing the local buffer keeps the invariant. -/
theorem InflateInv.free_local {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} {block : Nat} {array : Array UInt8} (current : InflateInv h r zs z s)
    (get : h.bytes block = some array) (size : array.size = 4) :
    InflateInv (freeWin h (.ref (.blk block) 0)) r zs z s := by
  have good := good_freeBuf current.good (nb := block) (by
    intro w window same
    subst w
    exact current.local_not_window get size window)
  have tables : DataTableInvariant (freeWin h (.ref (.blk block) 0)) s :=
    dataTableInvariant_of_views current.tables (fun ref => by cases ref <;> rfl)
  exact ⟨good, current.alloc, tables, current.pending, current.lengths, current.headerLengths,
    current.held, current.config, current.modes, current.phase, current.origin, current.globals⟩

/-- The restore of held bits into the local buffer enters `SYNC` with an
empty bit buffer. -/
theorem InflateInv.sync_first {h : Heap} {r : ZStreamRef} {zs nb : Nat}
    {z : ZStream} {s : InflateState} {array : Array UInt8}
    (current : InflateInv h r zs z s) (get : h.bytes nb = some array)
    (separate : ∀ w, s.window = .ref (.blk w) 0 → w ≠ nb) :
    InflateInv (syncFirstHeap h zs nb s array) r zs z (syncFirstState s) := by
  have good := good_firstState current.good get separate
  have tables : DataTableInvariant (syncFirstHeap h zs nb s array) (syncFirstState s) :=
    dataTableInvariant_inactive (by change ¬ DataTableMode SYNC; unfold DataTableMode; decide)
  have pending : DataPendingInvariant (syncFirstState s) :=
    dataPendingInvariant_idle current.pending.sane (by
      change SYNC ≠ LENEXT ∧ SYNC ≠ DIST ∧ SYNC ≠ DISTEXT ∧ SYNC ≠ MATCH
      decide)
  refine ⟨good, current.alloc, tables, pending, ?_, ?_, ?_,
    ⟨current.config.wrap, current.config.reqwrap, ?_, current.config.reqbits,
      current.config.header, current.config.raw, current.config.reqraw, current.config.pair⟩,
    good.live.mode,
    ⟨Or.inr (Or.inr (Or.inr (Or.inl rfl))), current.phase.flags, current.phase.gzipFlags,
      fun _ high => absurd high (by decide : ¬ SYNC ≤ HCRC)⟩,
    current.origin, current.globals⟩
  · intro active
    exact False.elim ((by decide : SYNC ≠ CODELENS) active)
  · intro active
    exact False.elim ((by decide : SYNC ≠ LENLENS) active)
  · change (syncFirstState s).hold.toNat < 2 ^ (0 : UInt32).toNat
    rw [syncFirstState_hold_zero current.held]
    decide
  · rcases current.config.window with range | ⟨zero, null, _, unread⟩
    · exact Or.inl range
    · exact Or.inr ⟨zero, null, Or.inr (Or.inr (Or.inr rfl)), unread⟩

/-- The search writes only the matched count and the input cursors. -/
theorem InflateInv.sync_search_state {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (current : InflateInv h r zs z s)
    (mode : s.mode = SYNC) (used found : UInt32) (next : BPtr) :
    let stream := { z with avail_in := z.avail_in - used, next_in := next, total_in := z.total_in + used.toUInt64 }
    InflateInv (setI (r.put h stream) zs (syncHave s found)) r zs stream (syncHave s found) := by
  dsimp only
  let stream := { z with avail_in := z.avail_in - used, next_in := next, total_in := z.total_in + used.toUInt64 }
  let state := syncHave s found
  have currentMode : state.mode = SYNC := mode
  have inv : StInv h zs state := current.good.inv.of_fields rfl rfl rfl rfl rfl rfl rfl rfl rfl
    current.good.inv.bits rfl rfl rfl
  have good : Good (setI (r.put h stream) zs state) r zs stream state :=
    current.good.setZI rfl current.good.live.zalloc current.good.live.zfree rfl
      current.good.live.mode inv
  have tables : DataTableInvariant (setI (r.put h stream) zs state) state :=
    dataTableInvariant_inactive (by rw [currentMode]; unfold DataTableMode; decide)
  have pending : DataPendingInvariant state :=
    dataPendingInvariant_idle current.pending.sane (by rw [currentMode]; decide)
  refine ⟨good, current.alloc, tables, pending, ?_, ?_, current.held,
    ⟨current.config.wrap, current.config.reqwrap, current.config.window, current.config.reqbits,
      current.config.header, current.config.raw, current.config.reqraw, current.config.pair⟩,
    current.modes, ⟨current.phase.started, current.phase.flags, current.phase.gzipFlags,
      current.phase.gzipModes⟩,
    current.origin, ?_⟩
  · intro active
    change state.mode = CODELENS at active
    rw [currentMode] at active
    contradiction
  · intro active
    change state.mode = LENLENS at active
    rw [currentMode] at active
    contradiction
  · simpa only [LibraryGlobals, setI, ZStreamRef.put_static] using current.globals

/-- Clearing bit 2 keeps a reachable wrapper value. -/
theorem clearValidate_value {w : Int32} (value : WrapValue w) : WrapValue (w &&& ~~~4) := by
  unfold WrapValue at value ⊢
  rcases value with v | v | v | v | v | v | v <;> subst v <;> decide

/-- Clearing bit 2 keeps bit 1. -/
theorem clearValidate_gzip_iff {w : Int32} (value : WrapValue w) :
    GzipAllowed (w &&& ~~~4) ↔ GzipAllowed w := by
  unfold WrapValue at value
  unfold GzipAllowed
  rcases value with v | v | v | v | v | v | v <;> subst v <;> decide

/-- The exact fields of the state after a successful resynchronization. -/
theorem syncOkState_fields (zs : Nat) (s : InflateState) :
    (syncOkState zs s).mode = TYPE ∧
    (syncOkState zs s).wrap = (if s.flags = -1 then 0 else s.reqwrap &&& ~~~4) ∧
    (syncOkState zs s).reqwrap = s.reqwrap ∧
    (syncOkState zs s).wbits = (if s.reqbits = 0 then 15 else s.reqbits) ∧
    (syncOkState zs s).reqbits = s.reqbits ∧
    (syncOkState zs s).flags = s.flags ∧
    (syncOkState zs s).head = none ∧
    (syncOkState zs s).hold = 0 ∧ (syncOkState zs s).bits = 0 ∧
    (syncOkState zs s).sane = 1 ∧
    (syncOkState zs s).lencode = .ref (.istate_codes zs) 0 := by
  unfold syncOkState syncC resetKeepState resetPre
  by_cases same : s.wbits = s.reqbits <;> by_cases zero : s.reqbits = 0 <;>
    by_cases unread : s.flags = -1 <;> by_cases wzero : s.wbits = 0 <;>
    (try have zero' : ¬ (0 : UInt32) = s.reqbits := fun e => zero e.symm) <;>
    simp [same, zero, unread, wzero] <;> simp_all

/-- The successful resynchronization keeps the invariant. -/
theorem InflateInv.sync_done {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} (current : InflateInv h r zs z s) :
    C.run (syncDone (some r) (some (.tab zs))) h = .ok (Z_OK, syncOkHeap h r zs z s) ∧
      InflateInv (syncOkHeap h r zs z s) r zs (syncOkStream z s) (syncOkState zs s) := by
  refine ⟨syncDone_run current.good current.alloc.2, ?_⟩
  obtain ⟨mode, wrap, reqwrap, wbits, reqbits, flags, head, hold, bits, sane, lencode⟩ :=
    syncOkState_fields zs s
  have good := (syncDone_good current.good).1
  have tables : DataTableInvariant (syncOkHeap h r zs z s) (syncOkState zs s) :=
    dataTableInvariant_inactive (by rw [mode]; unfold DataTableMode; decide)
  have pending : DataPendingInvariant (syncOkState zs s) :=
    dataPendingInvariant_idle sane (by rw [mode]; decide)
  have width : 8 ≤ (syncOkState zs s).wbits.toNat ∧ (syncOkState zs s).wbits.toNat ≤ 15 := by
    rw [wbits]
    by_cases zero : s.reqbits = 0
    · rw [if_pos zero]
      decide
    · rw [if_neg zero]
      rcases current.config.reqbits with same | ⟨unset, _⟩
      · rw [same]
        rcases current.config.window with range | ⟨wzero, _⟩
        · exact range
        · exact absurd (same.trans wzero) zero
      · exact absurd unset zero
  refine ⟨good, ?_, tables, pending, ?_, ?_, ?_, ?_, good.live.mode, ?_, ?_, ?_⟩
  · simpa only [DefAlloc, syncOkStream, resetKeepStream] using current.alloc
  · intro active
    rw [mode] at active
    contradiction
  · intro active
    rw [mode] at active
    contradiction
  · rw [hold, bits]
    decide
  · refine ⟨?_, by rw [reqwrap]; exact current.config.reqwrap, Or.inl width, ?_, ?_, ?_,
      ?_, ?_⟩
    · rw [wrap]
      split
      · unfold WrapValue
        exact Or.inl rfl
      · exact clearValidate_value current.config.reqwrap
    · rw [reqbits, wbits]
      by_cases zero : s.reqbits = 0
      · rw [if_pos zero]
        exact Or.inr ⟨zero, by decide, by decide⟩
      · rw [if_neg zero]
        exact Or.inl rfl
    · intro attached
      exact absurd head attached
    · intro _ zero
      rw [zero] at width
      exact absurd width.1 (by decide)
    · rw [reqwrap, reqbits]
      exact current.config.reqraw
    · rw [wrap, reqwrap]
      split
      · exact Or.inl rfl
      · exact Or.inr (clearValidate_gzip_iff current.config.reqwrap)
  · refine ⟨?_, by rw [flags]; exact current.phase.flags, ?_,
      fun _ high => absurd high (by rw [mode]; decide)⟩
    · by_cases unread : s.flags = -1
      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
        rw [wrap, if_pos unread]
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [flags]; exact unread))))))
    · intro read zlib
      rw [flags] at read zlib
      rw [wrap, if_neg read]
      have gzip := current.phase.gzipFlags read zlib
      rcases current.config.pair with zero | same
      · rw [zero] at gzip
        exact absurd gzip (by unfold GzipAllowed; decide)
      · exact (clearValidate_gzip_iff current.config.reqwrap).mpr (same.mp gzip)
  · exact Or.inl lencode
  · change (syncOkHeap h r zs z s).static = _
    unfold syncOkHeap
    simp only []
    split
    · simp only [freeWin]
      split <;> simpa only [LibraryGlobals, setI, ZStreamRef.put_static, resetHeap_static] using current.globals
    · simpa only [LibraryGlobals, setI, ZStreamRef.put_static, resetHeap_static] using current.globals

/-- The resynchronization frees at most the window. -/
theorem syncOkHeap_bytes_other {h : Heap} {r : ZStreamRef} {zs block : Nat} {z : ZStream}
    {s : InflateState} (separate : s.window ≠ .ref (.blk block) 0) :
    (syncOkHeap h r zs z s).bytes block = h.bytes block ∧
      (syncOkHeap h r zs z s).ro block = h.ro block := by
  have window : (syncC zs s).window = s.window ∨ (syncC zs s).window = .null := by
    rw [(syncC_field zs s).2.1]
    unfold resetPre
    split
    · exact Or.inr rfl
    · exact Or.inl rfl
  have resetBytes : (resetHeap h s).bytes block = h.bytes block ∧
      (resetHeap h s).ro block = h.ro block := by
    unfold resetHeap freeWin
    split
    · split
      · rename_i w pointer
        have other : block ≠ w := by
          intro same
          subst same
          exact separate pointer
        exact ⟨upd_ne _ _ _ _ other, rfl⟩
      · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
  unfold syncOkHeap
  simp only []
  split
  · unfold freeWin
    split
    · rename_i w pointer
      have other : block ≠ w := by
        intro same
        subst same
        rcases window with same | null
        · exact separate (same ▸ pointer)
        · rw [null] at pointer
          cases pointer
      simp only [upd_ne _ _ _ _ other, setI, ZStreamRef.put_bytes, ZStreamRef.put_ro]
      exact resetBytes
    · simpa only [setI, ZStreamRef.put_bytes, ZStreamRef.put_ro] using resetBytes
  · simpa only [setI, ZStreamRef.put_bytes, ZStreamRef.put_ro] using resetBytes

/-- An actual input-search tail keeps the invariant and the local buffer. -/
theorem syncTail_invariant_of_run {h after : Heap} {r : ZStreamRef} {zs block : Nat}
    {z : ZStream} {s : InflateState} {rc : Int32} (current : InflateInv h r zs z s)
    (mode : s.mode = SYNC) (separate : s.window ≠ .ref (.blk block) 0)
    (actual : C.run (syncTail (some r) (some (.tab zs))) h = .ok (rc, after)) :
    ∃ stream state, InflateInv after r zs stream state ∧
      after.bytes block = h.bytes block ∧ after.ro block = h.ro block := by
  change syncTail (some r) (some (.tab zs)) h = _ at actual
  unfold syncTail at actual
  simp only [bind_app, ldZ_eq, current.good.live.hz, rdI_eq, current.good.live.hs] at actual
  cases searchRun : syncsearch s.«have» z.next_in z.avail_in h with
  | error fault => rw [searchRun] at actual; cases actual
  | ok pair =>
    obtain ⟨⟨used, found⟩, middle⟩ := pair
    have same := syncsearch_heap_unchanged searchRun
    subst middle
    rw [searchRun] at actual
    simp only [bind_app, wrI_eq, current.good.live.hs] at actual
    cases addRun : Ptr.add z.next_in (used.toNat : Int) (setI h zs { s with «have» := found }) with
    | error fault => rw [addRun] at actual; cases actual
    | ok pair =>
      obtain ⟨next, middle⟩ := pair
      have same := sync_pointer_add_heap addRun
      subst middle
      rw [addRun] at actual
      simp only [bind_app, wrZ_eq, ZStreamRef.get_setI, current.good.live.hz,
        rdI_eq, ZStreamRef.put_istates, setI_istates_same, ZStreamRef.put_setI] at actual
      let stream := { z with avail_in := z.avail_in - used, next_in := next, total_in := z.total_in + used.toUInt64 }
      let state := syncHave s found
      let heap := setI (r.put h stream) zs state
      have searched : InflateInv heap r zs stream state :=
        current.sync_search_state mode used found next
      have heapBytes : heap.bytes block = h.bytes block ∧ heap.ro block = h.ro block := by
        constructor <;> simp [heap, setI, ZStreamRef.put_bytes, ZStreamRef.put_ro]
      by_cases finish : found = 4
      · subst found
        simp only [show ((4 : UInt32) != 4) = false from by decide, Bool.false_eq_true,
          ↓reduceIte] at actual
        have complete := searched.sync_done
        have aligned := Except.ok.inj (complete.1.symm.trans actual)
        have heapEq : syncOkHeap heap r zs stream state = after := congrArg Prod.snd aligned
        rw [← heapEq]
        have kept := syncOkHeap_bytes_other (h := heap) (r := r) (zs := zs) (z := stream)
          (s := state) separate
        exact ⟨syncOkStream stream state, syncOkState zs state, complete.2,
          kept.1.trans heapBytes.1, kept.2.trans heapBytes.2⟩
      · simp [finish] at actual
        have heapEq : heap = after := actual.2
        rw [← heapEq]
        exact ⟨stream, state, searched, heapBytes⟩

/-- The search tail followed by the free of the local buffer. -/
theorem syncTail_cleanup_invariant_of_run {h after : Heap} {r : ZStreamRef} {zs block : Nat}
    {z : ZStream} {s : InflateState} {array : Array UInt8} {rc : Int32}
    (current : InflateInv h r zs z s) (mode : s.mode = SYNC)
    (get : h.bytes block = some array) (size : array.size = 4) (write : h.ro block = false)
    (actual : C.run (do
      let code ← syncTail (some r) (some (.tab zs))
      freeB (.ref (.blk block) 0)
      pure code) h = .ok (rc, after)) :
    ∃ stream state, InflateInv after r zs stream state := by
  change (do
    let code ← syncTail (some r) (some (.tab zs))
    freeB (.ref (.blk block) 0)
    pure code) h = _ at actual
  rw [bind_app] at actual
  cases searched : syncTail (some r) (some (.tab zs)) h with
  | error fault => rw [searched] at actual; cases actual
  | ok pair =>
    obtain ⟨code, middle⟩ := pair
    obtain ⟨stream, state, next, bytes, readonly⟩ :=
      syncTail_invariant_of_run current mode (current.local_not_window get size) searched
    have middleGet : middle.bytes block = some array := by rw [bytes]; exact get
    have middleWrite : middle.ro block = false := by rw [readonly]; exact write
    have freed := freeBuf_run (H := middle) middleGet middleWrite
    rw [searched] at actual
    simp only [bind_app, freed, pure_app] at actual
    have heapEq : freeWin middle (.ref (.blk block) 0) = after :=
      congrArg Prod.snd (Except.ok.inj actual)
    rw [← heapEq]
    exact ⟨stream, state, next.free_local middleGet size⟩

/-- Every actual `inflateSync` return keeps the invariant. -/
theorem inflateSync_preserves (r : ZStreamRef) : InflatePreserves r (.inflateSync (some r)) := by
  intro h after zs z s result current _platform _ actual
  have finish : ∀ {rc : Int32},
      C.run (inflateSync (some r)) h = .ok (rc, after) → ∃ z' s', InflateInv after r zs z' s' := by
    intro rc run
    clear actual
    have initial := current.sync_alloc
    have get := syncAlloc_bytes_buf h
    have size : (syncJunk h).size = 4 := by simp [syncJunk]
    have write := syncAlloc_ro_buf h
    by_cases empty : z.avail_in = 0 ∧ s.bits < 8
    · have expected := inflateSync_buf_error current.good empty.1 empty.2
      have heapEq : tmpFreed h = after :=
        congrArg Prod.snd (Except.ok.inj (expected.symm.trans run))
      rw [← heapEq]
      exact ⟨z, s, initial.free_local get size⟩
    change inflateSync (some r) h = _ at run
    rw [inflateSync_split] at run
    simp only [bind_app, allocLocalB_run h current.good.fresh, stateCheck_live initial.good.live,
      show ((0 : Int32) != 0) = false from by decide, Bool.false_eq_true, ↓reduceIte,
      ldZ_eq, initial.good.live.hz, initial.good.live.zst, castI, ldI_eq, initial.good.live.hs,
      Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, empty] at run
    by_cases resumed : s.mode = SYNC
    · simp only [bne_iff_ne, resumed, not_true_eq_false, ↓reduceIte, pure_app] at run
      exact syncTail_cleanup_invariant_of_run initial resumed get size write run
    · have separate := win_ne_buf current.good.fresh current.good.inv.win
      have first := syncFirst_run (initial.good.live.hs) get size write initial.good.inv.bits
      have firstState := initial.sync_first get separate
      change syncFirst (some (.tab zs)) (syncBuf h) s (syncAlloc h) = _ at first
      simp only [bne_iff_ne] at run
      rw [if_pos resumed] at run
      simp only [bind_app, first] at run
      have currentGet : (syncFirstHeap (syncAlloc h) zs h.nextBlk s (syncJunk h)).bytes h.nextBlk =
          some (fillBuf (syncJunk h) (syncHold0 s) (syncNB s)) := by
        simp [syncFirstHeap]
      have currentSize : (fillBuf (syncJunk h) (syncHold0 s) (syncNB s)).size = 4 := by
        rw [fillBuf_size, size]
      have currentWrite :
          (syncFirstHeap (syncAlloc h) zs h.nextBlk s (syncJunk h)).ro h.nextBlk = false := by
        simp [syncFirstHeap, syncAlloc_ro_buf]
      exact syncTail_cleanup_invariant_of_run firstState rfl currentGet currentSize currentWrite run
  change heapCall (inflateSync (some r)) default h = _ at actual
  exact finish (run_of_heapCall actual)

#print axioms inflateSync_preserves

end Zlib.Inflate.Proofs
