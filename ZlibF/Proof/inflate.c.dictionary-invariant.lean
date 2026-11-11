import ZlibF.Proof.«inflate.c.history-invariant»
import ZlibF.Proof.«inflate.c.window-static»

/-!
# inflate.c: `inflateSetDictionary` preserves the general invariant

A dictionary is installed only in raw mode or in `DICT`; in both the window
width is known, so the window can be allocated.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- A window update with a known width keeps the invariant. -/
theorem InflateInv.window_update {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState} (current : InflateInv h r zs z s)
    (good : Good after r zs stream state) (frame : WindowStateFrame s state)
    (codeViews : ∀ ref : CodeRef, (Space.get after ref : Option (Array Code)) = Space.get h ref)
    (static : after.static = h.static) (allocator : DefAlloc stream) (nonzero : s.wbits ≠ 0) :
    InflateInv after r zs stream state := by
  have window : 8 ≤ s.wbits.toNat ∧ s.wbits.toNat ≤ 15 := by
    rcases current.config.window with range | ⟨zero, _⟩
    · exact range
    · exact absurd zero nonzero
  refine ⟨good, allocator, frame.tables codeViews current.tables, frame.pending current.pending,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [frame]
    exact current.lengths
  · rw [frame]
    exact current.headerLengths
  · rw [frame]
    exact current.held
  · rw [frame]
    exact ⟨current.config.wrap, current.config.reqwrap, Or.inl window, current.config.reqbits,
      current.config.header, current.config.raw, current.config.reqraw, current.config.pair⟩
  · rw [frame]
    exact current.modes
  · rw [frame]
    exact ⟨current.phase.started, current.phase.gzipFlags,
      current.phase.gzipModes, current.phase.gzipRead⟩
  · rw [frame]
    exact current.origin
  · change after.static = _
    rw [static]
    exact current.globals

/-- The final dictionary flag store keeps the invariant. -/
theorem InflateInv.set_havedict {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (current : InflateInv h r zs z s) :
    InflateInv (setI h zs { s with havedict := 1 }) r zs z { s with havedict := 1 } := by
  let state := { s with havedict := 1 }
  have good : Good (setI h zs state) r zs z state :=
    good_state current.good rfl current.good.live.mode
      (current.good.inv.of_fields rfl rfl rfl rfl rfl rfl rfl rfl rfl current.good.inv.bits rfl rfl rfl)
  have views : ∀ ref : CodeRef, (Space.get (setI h zs state) ref : Option (Array Code)) = Space.get h ref := by
    intro ref
    cases ref with
    | istate_codes i =>
      by_cases same : i = zs
      · subst i
        simp only [Space.get, setI_istates_same, current.good.live.hs, Option.map_some, state]
      · simp only [Space.get, setI_istates_ne h zs i state same]
    | st_lenfix | st_distfix => rfl
  have tables : DataTableInvariant (setI h zs state) state := by
    intro active
    have old := current.tables active
    constructor
    · obtain ⟨ref, offset, codes, pointer, get, safe⟩ := old.lengthTable
      exact ⟨ref, offset, codes, pointer, (views ref).trans get, safe⟩
    · obtain ⟨ref, offset, codes, pointer, get, safe⟩ := old.distanceTable
      exact ⟨ref, offset, codes, pointer, (views ref).trans get, safe⟩
  exact ⟨good, current.alloc, tables,
    ⟨current.pending.sane, current.pending.lenext, current.pending.dist,
      current.pending.distext, current.pending.matching⟩,
    current.lengths, current.headerLengths, current.held,
    ⟨current.config.wrap, current.config.reqwrap, current.config.window, current.config.reqbits,
      current.config.header, current.config.raw, current.config.reqraw, current.config.pair⟩, current.modes,
    ⟨current.phase.started, current.phase.gzipFlags,
      current.phase.gzipModes, current.phase.gzipRead⟩,
    current.origin, current.globals⟩

/-- A failed window allocation enters `MEM` with the invariant. -/
theorem InflateInv.mem_update {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s : InflateState} (current : InflateInv h r zs z s)
    (good : Good after r zs stream { s with mode := MEM })
    (static : after.static = h.static) (allocator : DefAlloc stream) (nonzero : s.wbits ≠ 0) :
    InflateInv after r zs stream { s with mode := MEM } := by
  have window : 8 ≤ s.wbits.toNat ∧ s.wbits.toNat ≤ 15 := by
    rcases current.config.window with range | ⟨zero, _⟩
    · exact range
    · exact absurd zero nonzero
  refine ⟨good, allocator, ?_, dataPendingInvariant_idle current.pending.sane ?_, ?_, ?_,
    current.held,
    ⟨current.config.wrap, current.config.reqwrap, Or.inl window, current.config.reqbits,
      current.config.header, current.config.raw, current.config.reqraw, current.config.pair⟩,
    good.live.mode,
    ⟨Or.inr (Or.inr (Or.inl rfl)), current.phase.gzipFlags,
      fun _ high => absurd high (by decide : ¬ MEM ≤ HCRC),
      fun _ high => absurd high (by decide : ¬ MEM ≤ HCRC)⟩,
    current.origin, ?_⟩
  · intro active
    exact False.elim ((by unfold DataTableMode; decide : ¬ DataTableMode MEM) active)
  · change MEM ≠ LENEXT ∧ MEM ≠ DIST ∧ MEM ≠ DISTEXT ∧ MEM ≠ MATCH
    decide
  · intro active
    change MEM = CODELENS at active
    contradiction
  · intro active
    change MEM = LENLENS at active
    contradiction
  · change after.static = _
    rw [static]
    exact current.globals

/-- Every actual dictionary request: refusals, checksum mismatch, success
and allocation failure. -/
theorem inflateSetDictionary_preserves (r : ZStreamRef) (source : BPtr) (len : UInt32) :
    InflatePreserves r (.inflateSetDictionary (some r) source len) := by
  intro h after zs z s result current _platform range actual
  have finish : ∀ {rc : Int32} {written : Heap} {state : InflateState},
      C.run (inflateSetDictionary (some r) source len) h = .ok (rc, written) →
      InflateInv written r zs z state → (HeldBits s → HeldBits state) →
      ∃ z' s', InflateInv after r zs z' s' ∧ (HeldBits s → HeldBits s') := by
    intro rc written state run next nextHeld
    have same := Except.ok.inj ((heapCall_of_actual_run run default).symm.trans actual)
    cases same
    exact ⟨z, state, next, nextHeld⟩
  by_cases refused : source = .null ∨ (s.wrap ≠ 0 ∧ s.mode ≠ DICT)
  · exact finish (inflateSetDictionary_refused_any current.good.live source len refused) current id
  have nonnull : source ≠ .null := fun null => refused (Or.inl null)
  have allowed : s.wrap = 0 ∨ s.mode = DICT := by
    by_cases raw : s.wrap = 0
    · exact Or.inl raw
    · right
      apply Classical.byContradiction
      intro wrong
      exact refused (Or.inr ⟨raw, wrong⟩)
  have nonzero : s.wbits ≠ 0 := by
    rcases allowed with raw | dict
    · exact current.config.raw raw
    · intro zero
      rcases current.config.window with ⟨low, _⟩ | ⟨_, _, early⟩
      · rw [zero] at low
        exact absurd low (by decide)
      · rw [dict] at early
        rcases early with e | e | e <;> exact absurd e (by decide)
  have readable : ∃ xs, Bytes h source len.toNat xs := by
    rcases range with null | ⟨readable, _⟩
    · exact False.elim (nonnull null)
    · exact readable
  obtain ⟨xs, null | ⟨ref, off, array, pointer, get, room, _values⟩⟩ := readable
  · exact False.elim (nonnull null.1)
  subst pointer
  by_cases mismatch : s.mode = DICT ∧
      (ZlibF.Spec.adler32 (Zlib.Adler32.Proofs.seg array off len.toNat)).toUInt64 ≠ s.check
  · exact finish (inflateSetDictionary_dataerr_any current.good.live get room mismatch.1 mismatch.2)
      current id
  have checked : s.mode = DICT →
      (ZlibF.Spec.adler32 (Zlib.Adler32.Proofs.seg array off len.toNat)).toUInt64 = s.check := by
    intro dict
    apply Classical.byContradiction
    intro wrong
    exact mismatch ⟨dict, wrong⟩
  have unowned := callerRange_private_window current.good range rfl
  have separate : Separate (.ref ref off) len.toNat s.window (2 ^ s.wbits.toNat) := by
    rcases current.good.inv.win.block with null | ⟨w, bytes, window, _⟩
    · simp [Separate, null]
    · simp [Separate, window, unowned w window]
  obtain ⟨wr, heap1, state1, windowRun, good1, windowFrame, _sourceView, codeViews, outcome⟩ :=
    updatewindow_decoder_boundary current.good current.alloc.1 get
      (by omega : len.toNat ≤ off + len.toNat) room unowned
  have static := updatewindow_static current.good current.alloc.1 get
    (by omega : len.toNat ≤ off + len.toNat) room
    (by simpa only [Nat.add_sub_cancel] using separate) windowRun
  have next := current.window_update good1 windowFrame codeViews static current.alloc nonzero
  have run := inflateSetDictionary_window_cut current.good.live get room allowed checked windowRun
    good1.live.hs
  rcases outcome with success | failure
  · subst wr
    exact finish (by simpa only [ite_true] using run) next.set_havedict (fun held => by rw [windowFrame]; exact held)
  · obtain ⟨code, _window, sameState, _heap⟩ := failure
    subst wr
    subst state1
    have good : Good (setI heap1 zs { s with mode := MEM }) r zs z { s with mode := MEM } :=
      good1.decode_update (by rfl) (by change HEAD ≤ MEM ∧ MEM ≤ SYNC; decide)
    have memory := next.mem_update good rfl current.alloc nonzero
    exact finish (by simpa only [show ¬ ((1 : Int32) = 0) from by decide, ite_false] using run) memory
      (fun _ _ notMem _ => absurd rfl notMem)

#print axioms inflateSetDictionary_preserves

end Zlib.Inflate.Proofs
