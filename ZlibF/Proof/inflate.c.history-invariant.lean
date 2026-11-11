import ZlibF.Proof.«inflate.c.invariant»
import ZlibF.Proof.«inflate.c.default-history-calls»

/-!
# inflate.c: caller edits and stream operations preserve the general invariant

Each lemma covers one actual return of a public operation from any state
with `InflateInv`, in every configuration.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- A caller rebuffer keeps the decoder state and its owned memory. -/
theorem rebuffer_invariant {h after : Heap} {r : ZStreamRef} {i : Nat} {z : ZStream}
    {s : InflateState} (current : InflateInv h r i z s) (edit : Rebuffer h after r) :
    ∃ z', InflateInv after r i z' s := by
  obtain ⟨stream, fields, good⟩ := rebuffer_inflate_good current.good edit
  have tables := (rebuffer_dataTableInvariant current.good edit current.tables).2
  refine ⟨stream, ⟨good, ?_, tables, current.pending, current.lengths, current.headerLengths,
    current.held, current.config, current.modes, current.phase, current.origin, edit.2.2.1⟩⟩
  rw [fields]
  exact current.alloc

/-- Preservation by one actual return of a stream operation. -/
def InflatePreserves (r : ZStreamRef) (call : Call) : Prop :=
  ∀ (h after : Heap) (i : Nat) (z : ZStream) (s : InflateState) (value : call.Result),
    InflateInv h r i z s → StreamArguments h r call →
    call.execute default h = .ok ((value, default), after) →
    ∃ z' s', InflateInv after r i z' s'

theorem inflateSyncPoint_preserves (r : ZStreamRef) :
    InflatePreserves r (.inflateSyncPoint (some r)) := by
  intro h after i z s value current _ actual
  have run := inflateSyncPoint_spec current.good.live
  have same := Except.ok.inj ((heapCall_of_actual_run run default).symm.trans actual)
  cases same
  exact ⟨z, s, current⟩

theorem inflateMark_preserves (r : ZStreamRef) : InflatePreserves r (.inflateMark (some r)) := by
  intro h after i z s value current _ actual
  obtain ⟨mark, run, _⟩ := inflateMark_spec current.good.live
  have same := Except.ok.inj ((heapCall_of_actual_run run default).symm.trans actual)
  cases same
  exact ⟨z, s, current⟩

theorem inflateCodesUsed_preserves (r : ZStreamRef) :
    InflatePreserves r (.inflateCodesUsed (some r)) := by
  intro h after i z s value current _ actual
  obtain ⟨offset, _, _, run⟩ := inflateCodesUsed_spec current.good
  have same := Except.ok.inj ((heapCall_of_actual_run run default).symm.trans actual)
  cases same
  exact ⟨z, s, current⟩

/-- The default build refuses undermining and keeps `sane = 1`. -/
theorem inflateUndermine_preserves (r : ZStreamRef) (subvert : Int32) :
    InflatePreserves r (.inflateUndermine (some r) subvert) := by
  intro h after i z s value current _ actual
  obtain ⟨written, run, heap, _⟩ := inflateUndermine_safe current.good subvert
  have state : { s with sane := 1 } = s := by rw [← current.pending.sane]
  have unchanged : written = h := by rw [heap, state, tcSetI_same current.good.live.hs]
  subst unchanged
  have same := Except.ok.inj ((heapCall_of_actual_run run default).symm.trans actual)
  cases same
  exact ⟨z, s, current⟩

#print axioms rebuffer_invariant
#print axioms inflateSyncPoint_preserves
#print axioms inflateMark_preserves
#print axioms inflateCodesUsed_preserves
#print axioms inflateUndermine_preserves

/-- Prime changes only the private bit buffer. A checked new held value
transports every other clause. -/
theorem InflateInv.prime_set_bits
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (current : InflateInv h r zs z s) (hold : UInt64) (bits : UInt32)
    (good : Good (setI h zs { s with hold, bits }) r zs z { s with hold, bits })
    (held : hold.toNat < 2 ^ bits.toNat) :
    InflateInv (setI h zs { s with hold, bits }) r zs z { s with hold, bits } := by
  obtain ⟨tables, lengths⟩ := table_clauses_set_bits current.good.live.hs
    hold bits current.tables current.lengths
  refine ⟨good, current.alloc, tables, ?_, lengths, ?_, held,
    ⟨current.config.wrap, current.config.reqwrap, current.config.window, current.config.reqbits,
      current.config.header, current.config.raw, current.config.reqraw, current.config.pair⟩, current.modes,
    ⟨current.phase.started, current.phase.flags, current.phase.gzipFlags⟩, current.origin, ?_⟩
  · refine ⟨current.pending.sane, ?_, ?_, ?_, ?_⟩
    · simpa [LengthExtraSafe, BackBound] using current.pending.lenext
    · simpa [DistanceSafe, PendingLengthSafe, BackBound] using current.pending.dist
    · simpa [DistanceExtraSafe, PendingLengthSafe, BackBound] using current.pending.distext
    · simpa [MatchSafe] using current.pending.matching
  · simpa [LengthHeaderInvariant] using current.headerLengths
  · simpa only [LibraryGlobals, setI] using current.globals

/-- Every signed prime request: refusals leave the heap unchanged, accepted
requests keep the checked bit-buffer bound. -/
theorem inflatePrime_preserves (r : ZStreamRef) (bits value : Int32) :
    InflatePreserves r (.inflatePrime (some r) bits value) := by
  intro h after i z s result current _ actual
  have finish : ∀ {rc : Int32} {written : Heap} {state : InflateState},
      C.run (inflatePrime (some r) bits value) h = .ok (rc, written) →
      InflateInv written r i z state → ∃ z' s', InflateInv after r i z' s' := by
    intro rc written state run next
    have same := Except.ok.inj ((heapCall_of_actual_run run default).symm.trans actual)
    cases same
    exact ⟨z, state, next⟩
  obtain ⟨zero, clear, reject, insert⟩ := inflatePrime_spec current.good bits value
  by_cases equal : bits = 0
  · exact finish (zero equal) current
  by_cases negative : bits < 0
  · obtain ⟨run, good⟩ := clear negative
    have held : (0 : UInt64).toNat < 2 ^ (0 : UInt32).toNat := by decide
    exact finish run (current.prime_set_bits 0 0 good held)
  have positive : 0 < bits := by
    rw [Int32.lt_iff_toInt_lt] at negative ⊢
    simp only [Int32.toInt_zero] at negative ⊢
    have notZero : bits.toInt ≠ 0 := by
      intro eq
      apply equal
      exact Int32.toInt_inj.mp eq
    omega
  by_cases wide : 16 < bits.toInt
  · exact finish (reject positive (Or.inl wide)) current
  by_cases full : 32 < s.bits.toNat + bits.toInt.toNat
  · exact finish (reject positive (Or.inr full)) current
  obtain ⟨run, good⟩ := insert positive (by omega) (by omega)
  have held := primeState_held s bits value current.held positive (by omega) (by omega)
  exact finish run (current.prime_set_bits _ _ good held)

/-- Toggling bit 2 keeps a reachable wrapper value. -/
theorem validateWrap_value {w check : Int32} (value : WrapValue w) :
    WrapValue (if check != 0 && w != 0 then w ||| 4 else w &&& ~~~4) := by
  unfold WrapValue at value ⊢
  rcases value with v | v | v | v | v | v | v <;> subst v <;> cases (check != 0) <;> decide

/-- Toggling bit 2 gives 0 only from 0. -/
theorem validateWrap_zero {w check : Int32} (value : WrapValue w)
    (zero : (if check != 0 && w != 0 then w ||| 4 else w &&& ~~~4) = 0) : w = 0 := by
  unfold WrapValue at value
  revert zero
  rcases value with v | v | v | v | v | v | v <;> subst v <;> cases (check != 0) <;> decide

/-- Toggling bit 2 keeps bit 1, in both directions. -/
theorem validateWrap_gzip_iff {w check : Int32} (value : WrapValue w) :
    GzipAllowed (if check != 0 && w != 0 then w ||| 4 else w &&& ~~~4) ↔ GzipAllowed w := by
  unfold WrapValue at value
  unfold GzipAllowed
  rcases value with v | v | v | v | v | v | v <;> subst v <;> cases (check != 0) <;> decide

/-- Toggling bit 2 keeps bit 1. -/
theorem validateWrap_gzip {w check : Int32} (gzip : GzipAllowed w) :
    GzipAllowed (if check != 0 && w != 0 then w ||| 4 else w &&& ~~~4) := by
  unfold GzipAllowed at gzip ⊢
  rcases gzip with v | v | v | v <;> subst v <;> cases (check != 0) <;> decide

theorem inflateValidate_preserves (r : ZStreamRef) (check : Int32) :
    InflatePreserves r (.inflateValidate (some r) check) := by
  intro h after i z s result current _ actual
  obtain ⟨written, run, heap, good, _⟩ := inflateValidate_safe current.good check
  subst written
  have same := Except.ok.inj ((heapCall_of_actual_run run default).symm.trans actual)
  cases same
  let state := validateState check s
  have tables : DataTableInvariant (setI h i state) state := by
    intro active
    have original := current.tables active
    constructor
    · obtain ⟨ref, off, array, ptr, get, safe⟩ := original.lengthTable
      exact ⟨ref, off, array, ptr, by rw [validate_code_views current.good.live.hs]; exact get, safe⟩
    · obtain ⟨ref, off, array, ptr, get, safe⟩ := original.distanceTable
      exact ⟨ref, off, array, ptr, by rw [validate_code_views current.good.live.hs]; exact get, safe⟩
  refine ⟨z, state, ⟨good, current.alloc, tables,
    ⟨current.pending.sane, current.pending.lenext, current.pending.dist,
      current.pending.distext, current.pending.matching⟩,
    current.lengths, current.headerLengths, current.held, ?_, current.modes, ?_,
    current.origin, current.globals⟩⟩
  · refine ⟨validateWrap_value current.config.wrap, validateWrap_value current.config.reqwrap,
      current.config.window, current.config.reqbits,
      fun attached => validateWrap_gzip (current.config.header attached),
      fun zero => current.config.raw (validateWrap_zero current.config.wrap zero),
      fun zero => current.config.reqraw (validateWrap_zero current.config.reqwrap zero), ?_⟩
    rcases current.config.pair with zero | same
    · exact Or.inl (validateState_raw_wrap zero check)
    · exact Or.inr ((validateWrap_gzip_iff current.config.wrap).trans
        (same.trans (validateWrap_gzip_iff current.config.reqwrap).symm))
  · refine ⟨?_, current.phase.flags,
      fun unread zero => validateWrap_gzip (current.phase.gzipFlags unread zero)⟩
    rcases current.phase.started with head | bad | mem | sync | raw | started
    · exact Or.inl head
    · exact Or.inr (Or.inl bad)
    · exact Or.inr (Or.inr (Or.inl mem))
    · exact Or.inr (Or.inr (Or.inr (Or.inl sync)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (validateState_raw_wrap raw check)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr started))))

#print axioms inflatePrime_preserves
#print axioms inflateValidate_preserves

/-- A write to a caller byte object outside the window keeps the invariant. -/
theorem InflateInv.byte_view_put {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (current : InflateInv h r zs z s)
    {dest : BRef} {old : Array UInt8} (get : Space.get h dest = some old)
    (write : Space.ro h dest = false)
    (separate : ∀ w, s.window = .ref (.blk w) 0 → dest ≠ .blk w)
    (array : Array UInt8) :
    InflateInv (Space.put h dest array) r zs z s := by
  have good := current.good.byte_view_put get write separate array
  have tables : DataTableInvariant (Space.put h dest array) s := by
    intro active
    exact (current.tables active).byte_view_put dest array
  have globals : LibraryGlobals (Space.put h dest array) := by
    change (Space.put h dest array).static = _
    rw [byte_view_put_static]
    exact current.globals
  exact ⟨good, current.alloc, tables, current.pending, current.lengths, current.headerLengths,
    current.held, current.config, current.modes, current.phase, current.origin, globals⟩

/-- `inflateGetDictionary` copies the window into a caller range. -/
theorem inflateGetDictionary_preserves (r : ZStreamRef) (dest : BPtr) (dl : Option UInt32) :
    InflatePreserves r (.inflateGetDictionary (some r) dest dl) := by
  intro h after zs z s result current arguments actual
  obtain ⟨stream, index, state, streamGet, pointer, stateGet, range⟩ := arguments
  have sameStream : stream = z := Option.some.inj (streamGet.symm.trans current.good.live.hz)
  subst stream
  have sameIndex : index = zs := by
    rw [current.good.live.zst] at pointer
    cases pointer
    rfl
  subst index
  have sameState : state = s := Option.some.inj (stateGet.symm.trans current.good.live.hs)
  subst state
  have good := current.good
  have finish : ∀ {written : Heap} {value},
      C.run (inflateGetDictionary (some r) dest dl) h = .ok (value, written) →
      InflateInv written r zs z s → ∃ z' s', InflateInv after r zs z' s' := by
    intro written value run next
    have same := Except.ok.inj ((heapCall_of_actual_run run default).symm.trans actual)
    cases same
    exact ⟨z, s, next⟩
  by_cases empty : dest = .null ∨ s.whave = 0
  · refine finish (written := h) (value := (Z_OK, dl.map (fun _ => s.whave))) ?_ current
    unfold C.run inflateGetDictionary
    rcases empty with null | zero
    · cases dl <;> simp [stateCheck_live good.live, ldZ_eq, ldI_eq,
        good.live.hz, good.live.zst, castI, good.live.hs, null]
    · cases dl <;> simp [stateCheck_live good.live, ldZ_eq, ldI_eq,
        good.live.hz, good.live.zst, castI, good.live.hs, zero]
  have nonnull : dest ≠ .null := fun null => empty (Or.inl null)
  have positive : s.whave ≠ 0 := fun zero => empty (Or.inr zero)
  have positiveNat : 0 < s.whave.toNat := by
    have : s.whave.toNat ≠ 0 := fun zero => positive (UInt32.toNat_inj.mp (by simpa using zero))
    omega
  obtain ⟨w, a, window, bytes, _write, size⟩ :
      ∃ w a, s.window = .ref (.blk w) 0 ∧ h.bytes w = some a ∧
        h.ro w = false ∧ a.size = 2 ^ s.wbits.toNat := by
    rcases good.inv.win.block with null | block
    · have := good.inv.win.nullws null
      have := good.inv.win.hv
      simp_all
    · exact block
  have windowSize : s.wsize.toNat = a.size := by
    rcases good.inv.win.ws with zero | full
    · have := good.inv.win.hv
      omega
    · omega
  have bounded : s.whave.toNat ≤ a.size := by
    have := good.inv.win.hv
    omega
  have chronological : s.wnext.toNat ≤ s.whave.toNat := by
    rcases Nat.lt_or_ge s.whave.toNat s.wsize.toNat with growing | full
    · have := good.inv.win.eq growing
      omega
    · have := good.inv.win.wn
      have := good.inv.win.hv
      omega
  have writable : Writable h dest s.whave.toNat := by
    rcases range with null | ⟨_read, write⟩
    · exact False.elim (nonnull null)
    · exact write.1 rfl
  rcases writable with ⟨null, _⟩ | ⟨ref, off, old, pointer, get, write, room⟩
  · exact False.elim (nonnull null)
  have separate := callerRange_private_window good range pointer
  have run := inflateGetDictionary_copy_general (dl := dl) good.live window bytes get write
    (separate w window) positive chronological bounded room
  exact finish (by simpa only [C.run, pointer] using run)
    (current.byte_view_put get write separate _)

/-- `inflateResetKeep` returns to `HEAD` and keeps the configuration. -/
theorem inflateResetKeep_preserves (r : ZStreamRef) :
    InflatePreserves r (.inflateResetKeep (some r)) := by
  intro h after zs z s result current _ actual
  obtain ⟨written, run, exactHeap, good, _⟩ := inflateResetKeep_safe current.good
  subst written
  have same := Except.ok.inj ((heapCall_of_actual_run run default).symm.trans actual)
  cases same
  let state := resetKeepState zs s
  have stateMode : state.mode = HEAD := rfl
  have pending : DataPendingInvariant state := dataPendingInvariant_head (by rfl) stateMode
  have table : DataTableInvariant (setI (r.put h (resetKeepStream z s)) zs state) state :=
    dataTableInvariant_inactive (by rw [stateMode]; unfold DataTableMode; decide)
  refine ⟨resetKeepStream z s, state, ⟨good, current.alloc, table, pending, ?_, ?_, ?_, ?_,
    good.live.mode, ?_, Or.inl rfl, ?_⟩⟩
  · intro active
    rw [stateMode] at active
    contradiction
  · intro active
    rw [stateMode] at active
    contradiction
  · change (0 : UInt64).toNat < 2 ^ (0 : UInt32).toNat
    decide
  · refine ⟨current.config.wrap, current.config.reqwrap, ?_, current.config.reqbits, ?_,
      current.config.raw, current.config.reqraw, current.config.pair⟩
    · rcases current.config.window with fixed | ⟨zero, null, _⟩
      · exact Or.inl fixed
      · exact Or.inr ⟨zero, null, Or.inl stateMode⟩
    · intro attached
      exact absurd rfl attached
  · exact ⟨Or.inl stateMode, Or.inl rfl, fun unread => absurd rfl unread⟩
  · simpa only [LibraryGlobals, setI, ZStreamRef.put_static] using current.globals

#print axioms InflateInv.byte_view_put
#print axioms inflateGetDictionary_preserves
#print axioms inflateResetKeep_preserves

/-- Attaching a header record changes no code array. -/
theorem getHeader_code_views {h : Heap} {zs : Nat} {s : InflateState}
    (get : h.istates zs = some s) (g : GzHeaderRef) (gh : GzHeader) (ref : CodeRef) :
    (Space.get (g.put (setI h zs (getHeaderState (some g) s)) gh) ref : Option (Array Code)) =
      Space.get h ref := by
  cases g with
  | tab b =>
    simp only [GzHeaderRef.put, setI]
    cases ref with
    | istate_codes i =>
      by_cases same : i = zs
      · subst i
        split <;> simp [Space.get, upd_same, get, getHeaderState]
      · split <;> simp [Space.get, upd_ne _ _ _ _ same]
    | st_lenfix => split <;> rfl
    | st_distfix => split <;> rfl

/-- On a reachable wrapper value, bit 1 is exactly `GzipAllowed`. -/
theorem gzipAllowed_of_bit {w : Int32} (value : WrapValue w) (bit : ¬ w &&& 2 = 0) :
    GzipAllowed w := by
  unfold WrapValue at value
  unfold GzipAllowed
  rcases value with v | v | v | v | v | v | v <;> subst v <;> revert bit <;> decide

/-- `inflateGetHeader` refuses without gzip and otherwise attaches a live
caller record. -/
theorem inflateGetHeader_preserves (r : ZStreamRef) (head : GzHeaderPtr) :
    InflatePreserves r (.inflateGetHeader (some r) head) := by
  intro h after zs z s result current arguments actual
  obtain ⟨memory, present⟩ := arguments
  by_cases nogzip : s.wrap &&& 2 = 0
  · have run := inflateGetHeader_nogzip current.good.live head nogzip
    have same := Except.ok.inj ((heapCall_of_actual_run run default).symm.trans actual)
    cases same
    exact ⟨z, s, current⟩
  rcases memory with none | ⟨b, gh, pointer, get, _⟩
  · exact absurd none present
  subst pointer
  obtain ⟨written, run, heap, good, _, _⟩ :=
    inflateGetHeader_ok current.good (g := .tab b) get nogzip
  subst written
  have same := Except.ok.inj ((heapCall_of_actual_run run default).symm.trans actual)
  cases same
  have gzip := gzipAllowed_of_bit current.config.wrap nogzip
  let state := getHeaderState (some (.tab b)) s
  have tables : DataTableInvariant
      ((GzHeaderRef.tab b).put (setI h zs state) { gh with done := 0 }) state := by
    intro active
    have original := current.tables active
    constructor
    · obtain ⟨ref, off, array, ptr, get, safe⟩ := original.lengthTable
      exact ⟨ref, off, array, ptr,
        by rw [getHeader_code_views current.good.live.hs]; exact get, safe⟩
    · obtain ⟨ref, off, array, ptr, get, safe⟩ := original.distanceTable
      exact ⟨ref, off, array, ptr,
        by rw [getHeader_code_views current.good.live.hs]; exact get, safe⟩
  refine ⟨z, state, ⟨good, current.alloc, tables,
    ⟨current.pending.sane, current.pending.lenext, current.pending.dist,
      current.pending.distext, current.pending.matching⟩,
    current.lengths, current.headerLengths, current.held,
    ⟨current.config.wrap, current.config.reqwrap, current.config.window, current.config.reqbits,
      fun _ => gzip, current.config.raw, current.config.reqraw, current.config.pair⟩, current.modes,
    ⟨current.phase.started, current.phase.flags, current.phase.gzipFlags⟩,
    current.origin, ?_⟩⟩
  change (GzHeaderRef.put (setI h zs state) (.tab b) { gh with done := 0 }).static = _
  simp only [GzHeaderRef.put, setI]
  split <;> exact current.globals

#print axioms inflateGetHeader_preserves

theorem resetHeap_static (h : Heap) (s : InflateState) :
    (resetHeap h s).static = h.static := by
  unfold resetHeap freeWin
  split
  · split <;> rfl
  · rfl

/-- `inflateReset` restores the requested width and wrapper. A window of
another width is freed; a requested width of 0 leaves no window. -/
theorem inflateReset_preserves (r : ZStreamRef) : InflatePreserves r (.inflateReset (some r)) := by
  intro h after zs z s result current _ actual
  obtain ⟨written, run, exactHeap, good, _⟩ := inflateReset_safe current.good current.alloc.2
  subst written
  have same := Except.ok.inj ((heapCall_of_actual_run run default).symm.trans actual)
  cases same
  let H := resetHeap h s
  let stream := resetKeepStream z (resetPre s)
  let state := resetKeepState zs (resetPre s)
  have stateMode : state.mode = HEAD := rfl
  have pending : DataPendingInvariant state := dataPendingInvariant_head (by rfl) stateMode
  have table : DataTableInvariant (setI (r.put H stream) zs state) state :=
    dataTableInvariant_inactive (by rw [stateMode]; unfold DataTableMode; decide)
  have stateBits : state.wbits = s.reqbits := by
    simp only [state, resetKeepState, resetPre]
    split <;> simp_all
  have stateReq : state.reqbits = s.reqbits := by
    simp only [state, resetKeepState, resetPre]
    try ((try split) <;> rfl)
  have stateWrap : state.wrap = s.reqwrap := by
    simp only [state, resetKeepState, resetPre]
    try ((try split) <;> rfl)
  have stateReqWrap : state.reqwrap = s.reqwrap := by
    simp only [state, resetKeepState, resetPre]
    try ((try split) <;> rfl)
  have window : (8 ≤ state.wbits.toNat ∧ state.wbits.toNat ≤ 15) ∨
      (state.wbits = 0 ∧ state.window = .null ∧
        (state.mode = HEAD ∨ state.mode = BAD ∨ state.mode = SYNC)) := by
    by_cases equal : s.wbits = s.reqbits
    · have keep : state.window = s.window := by
        simp only [state, resetKeepState, resetPre, equal, bne_self_eq_false, Bool.false_eq_true,
          ↓reduceIte]
      rw [stateBits, ← equal, keep]
      rcases current.config.window with range | ⟨zero, null, _⟩
      · exact Or.inl range
      · exact Or.inr ⟨zero, null, Or.inl stateMode⟩
    · rcases current.config.reqbits with requested | ⟨zero, _⟩
      · exact False.elim (equal requested.symm)
      · have cleared : state.window = .null := by
          have differ : (s.wbits != s.reqbits) = true := by simpa using equal
          simp only [state, resetKeepState, resetPre, differ, ↓reduceIte]
        exact Or.inr ⟨stateBits.trans zero, cleared, Or.inl stateMode⟩
  refine ⟨stream, state, ⟨good, current.alloc, table, pending, ?_, ?_, ?_,
    ⟨by rw [stateWrap]; exact current.config.reqwrap,
      by rw [stateReqWrap]; exact current.config.reqwrap, window,
      Or.inl (stateReq.trans stateBits.symm), fun attached => absurd rfl attached,
      fun zero => by rw [stateBits]; exact current.config.reqraw (stateWrap ▸ zero),
      fun zero => by rw [stateReq]; exact current.config.reqraw (stateReqWrap ▸ zero),
      Or.inr (by rw [stateWrap, stateReqWrap])⟩,
    good.live.mode, ⟨Or.inl stateMode, Or.inl rfl, fun unread => absurd rfl unread⟩,
    Or.inl rfl, ?_⟩⟩
  · intro active
    rw [stateMode] at active
    contradiction
  · intro active
    rw [stateMode] at active
    contradiction
  · change (0 : UInt64).toNat < 2 ^ (0 : UInt32).toNat
    decide
  · change (setI (r.put H stream) zs state).static = _
    simp only [setI, ZStreamRef.put_static]
    rw [resetHeap_static]
    exact current.globals

/-- `inflateReset2` for every argument: a refusal changes nothing; an
accepted argument selects any wrapper and a width of 0 or 8 to 15. -/
theorem inflateReset2_preserves (r : ZStreamRef) (wb : Int32) :
    InflatePreserves r (.inflateReset2 (some r) wb) := by
  intro h after zs z s result current _ actual
  obtain ⟨rc, written, run, outcome⟩ := inflateReset2_safe current.good current.alloc.2 wb
  have same := Except.ok.inj ((heapCall_of_actual_run run default).symm.trans actual)
  cases same
  cases params : reset2Params wb with
  | none =>
    rw [params] at outcome
    obtain ⟨_, unchanged⟩ := outcome
    subst unchanged
    exact ⟨z, s, current⟩
  | some selected =>
    obtain ⟨code, width⟩ := selected
    rw [params] at outcome
    obtain ⟨_, exactHeap, good, _⟩ := outcome
    subst exactHeap
    have mapped := ZlibF.Spec.Public.Proofs.InflateInit.params_equiv wb
    rw [params] at mapped
    cases chosen : ZlibF.Spec.Api.inflWbits wb.toInt with
    | none =>
      rw [chosen] at mapped
      cases mapped
    | some picked =>
      obtain ⟨wrap, bits⟩ := picked
      rw [chosen] at mapped
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at mapped
      obtain ⟨codeEq, widthEq⟩ := mapped
      have range := inflWbits_bits chosen
      have small : bits < 16 := by omega
      have widthNat : (i2u width).toNat = bits := by
        rw [widthEq]
        have key : ∀ k : Nat, k < 16 → (i2u (Int32.ofInt (k : Int))).toNat = k := by decide
        exact key bits small
      have codeValue : WrapValue code := by
        unfold WrapValue
        rw [codeEq]
        cases wrap <;> decide
      have rawWidth : code = 0 → i2u width ≠ 0 := by
        intro zero widthZero
        have bitsZero : bits = 0 := by rw [← widthNat, widthZero]; rfl
        cases wrap with
        | raw =>
          have := inflWbits_raw chosen
          omega
        | zlib => rw [codeEq] at zero; exact absurd zero (by decide)
        | gzip => rw [codeEq] at zero; exact absurd zero (by decide)
        | auto => rw [codeEq] at zero; exact absurd zero (by decide)
      let H := reset2Heap h width s
      let stream := resetKeepStream z (resetPre (reset2Pre code width s))
      let state := resetKeepState zs (resetPre (reset2Pre code width s))
      have stateMode : state.mode = HEAD := rfl
      have pending : DataPendingInvariant state := dataPendingInvariant_head (by rfl) stateMode
      have table : DataTableInvariant (setI (r.put H stream) zs state) state :=
        dataTableInvariant_inactive (by rw [stateMode]; unfold DataTableMode; decide)
      have stateBits : state.wbits = i2u width := by
        simp [state, resetKeepState, resetPre, reset2Pre]
      have stateReq : state.reqbits = i2u width := by
        simp [state, resetKeepState, resetPre, reset2Pre]
      have stateWrap : state.wrap = code := by
        simp [state, resetKeepState, resetPre, reset2Pre]
      have stateReqWrap : state.reqwrap = code := by
        simp [state, resetKeepState, resetPre, reset2Pre]
      have window : (8 ≤ state.wbits.toNat ∧ state.wbits.toNat ≤ 15) ∨
          (state.wbits = 0 ∧ state.window = .null ∧
            (state.mode = HEAD ∨ state.mode = BAD ∨ state.mode = SYNC)) := by
        rcases range with zero | ⟨low, high⟩
        · have widthZero : i2u width = 0 := UInt32.toNat_inj.mp (by rw [widthNat, zero]; rfl)
          have cleared : state.window = .null := by
            by_cases equal : s.wbits = i2u width
            · have keep : state.window = s.window := by
                simp [state, resetKeepState, resetPre, reset2Pre, equal]
              rw [keep]
              rcases current.config.window with ⟨low, _⟩ | ⟨_, null, _⟩
              · rw [equal, widthZero] at low
                exact absurd low (by decide)
              · exact null
            · have differ : (s.wbits != i2u width) = true := by simpa using equal
              simp [state, resetKeepState, resetPre, reset2Pre, differ]
          exact Or.inr ⟨stateBits.trans widthZero, cleared, Or.inl stateMode⟩
        · exact Or.inl ⟨by rw [stateBits, widthNat]; exact low,
            by rw [stateBits, widthNat]; exact high⟩
      refine ⟨stream, state, ⟨good, current.alloc, table, pending, ?_, ?_, ?_,
        ⟨by rw [stateWrap]; exact codeValue, by rw [stateReqWrap]; exact codeValue, window,
          Or.inl (stateReq.trans stateBits.symm), fun attached => absurd rfl attached,
          fun zero => by rw [stateBits]; exact rawWidth (stateWrap ▸ zero),
          fun zero => by rw [stateReq]; exact rawWidth (stateReqWrap ▸ zero),
          Or.inr (by rw [stateWrap, stateReqWrap])⟩,
        good.live.mode, ⟨Or.inl stateMode, Or.inl rfl, fun unread => absurd rfl unread⟩,
        Or.inl rfl, ?_⟩⟩
      · intro active
        rw [stateMode] at active
        contradiction
      · intro active
        rw [stateMode] at active
        contradiction
      · change (0 : UInt64).toNat < 2 ^ (0 : UInt32).toNat
        decide
      · change (setI (r.put H stream) zs state).static = _
        simp only [setI, ZStreamRef.put_static]
        rw [reset2Heap_static]
        exact current.globals

#print axioms inflateReset_preserves
#print axioms inflateReset2_preserves

end Zlib.Inflate.Proofs
