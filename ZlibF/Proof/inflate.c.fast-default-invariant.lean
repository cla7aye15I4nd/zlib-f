import ZlibF.Proof.«inflate.c.data-invariant»
import ZlibF.Proof.«inflate.c.fast-entry»
import ZlibF.Proof.«inflate.c.dispatch-rank»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual fast LEN call and LOAD retain J for distinct raw caller
blocks. The remaining public byte-view cases are a separate obligation. -/
theorem inflate_LEN_fast_raw_default_J_configuration {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8} {ib io ob oo : Nat}
    (E : Env c h r zs z s) (invariant : DefaultDecodeJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = LEN)
    (input : l.next = .ref (.blk ib) io) (output : l.put = .ref (.blk ob) oo)
    (different : ib ≠ ob) (fast : (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    ∃ outcome regs after stream state,
      runX (inflate_LEN c) l h = .ok ((outcome, regs), after) ∧
      DefaultDecodeJ after r zs stream state ∧ DataExitMode state.mode ∧ DefaultConfigFrame s state := by
  let good := invariant.good
  let fit := invariant.platform
  let tables := invariant.tables (by rw [mode]; unfold DataTableMode; decide)
  let pending := invariant.pending
  obtain ⟨entry, heap1, cut, post, platform, strmEq, refEq, idEq, stateEq, streamEq, heapEq, outputEq⟩ :=
    inflate_LEN_fast_raw_cut E good fit tables buffers pending input output different fast
  have count : l.bits.toNat < 8 := by
    have margins : (6 ≤ l.have_ ∧ 258 ≤ l.left) ∧ l.bits < 8 := by
      simpa only [Bool.and_eq_true, decide_eq_true_eq] using fast
    simpa [UInt32.lt_iff_toNat_lt] using margins.2
  obtain ⟨good0, pending0, _, _⟩ := leave_restore_invariant E good pending buffers.bits (by omega)
  have entryGood : Good entry.toEnv.h0 entry.toEnv.r entry.toEnv.stid entry.toEnv.sm0 entry.toEnv.s0 := by
    change Good entry.h0 entry.r entry.stid entry.sm0 entry.s0
    rw [heapEq, refEq, idEq, streamEq, stateEq]
    exact good0
  have entryPending : DataPendingInvariant entry.toEnv.s0 := by change DataPendingInvariant entry.s0; rw [stateEq]; exact pending0
  have privateWindow := callerRange_private_window good buffers.output.range output
  have window : ∀ w, entry.toEnv.s0.window = .ref (.blk w) 0 → entry.toEnv.ob ≠ w := by
    change ∀ w, entry.s0.window = .ref (.blk w) 0 → entry.ob ≠ w
    rw [stateEq, outputEq]
    intro w win equal
    exact privateWindow w win (by rw [equal])
  obtain ⟨stream1, state1, good1, tables1, pending1, held1, bits1, _⟩ :=
    fastPost_retained entry.toEnv entryGood entryPending window post
  have good1' : Good heap1 r zs stream1 state1 := by change Good heap1 entry.r entry.stid stream1 state1 at good1; simpa only [refEq, idEq] using good1
  obtain ⟨_, _, _, _, _, nextMode, normalizedBits, normalizedHold, _, _, _, _, _, _,
    exactHeap, _, classification, _⟩ := post
  have exactState : state1 = { entry.s0 with mode := nextMode, bits := normalizedBits, hold := normalizedHold } := by
    apply Option.some.inj
    have get := good1'.live.hs
    rw [exactHeap] at get
    have entryId : entry.toEnv.stid = zs := idEq
    simp only [ZStreamRef.put_istates, entryId, upd_same] at get
    exact get.symm
  have selected : DataExitMode state1.mode := by
    rw [exactState]
    change DataExitMode nextMode
    rcases classification with same | type | bad
    · rw [same.1]
      change DataExitMode entry.s0.mode
      rw [stateEq]
      change DataExitMode s.mode
      rw [mode]
      exact Or.inl (by unfold DataTableMode; decide)
    · exact Or.inr (Or.inl type.1)
    · exact Or.inr (Or.inr bad)
  have static : heap1.static = h.static := by
    rw [exactHeap, ZStreamRef.put_static]
    change entry.h0.static = h.static
    rw [heapEq]
    simp only [setI, ZStreamRef.put_static]
  have current := invariant.data_writeback good1' tables1 pending1 selected held1
    (by rw [exactState, stateEq]; rfl) (by rw [exactState, stateEq]; rfl)
    (by rw [exactState, stateEq]; rfl) static platform
  have config : DefaultConfigFrame s state1 := by
    rw [exactState, stateEq]
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  have env1 : Env c heap1 r zs stream1 state1 := ⟨E.strm, E.st, good1'.live.hz, good1'.live.hs⟩
  let regs := { l with put := stream1.next_out, left := stream1.avail_out, next := stream1.next_in, have_ := stream1.avail_in, hold := state1.hold, bits := state1.bits }
  by_cases type : state1.mode = TYPE
  · let state2 := { state1 with back := -1 }
    have good2 := good1'.decode_update (after := state2) (by rfl) (by exact good1'.live.mode)
    have pending2 : DataPendingInvariant state2 := by
      apply dataPendingInvariant_idle (s := state2) pending1.sane
      change state1.mode ≠ LENEXT ∧ state1.mode ≠ DIST ∧ state1.mode ≠ DISTEXT ∧ state1.mode ≠ MATCH
      rw [type]; decide
    have tables2 : DataTableInvariant (setI heap1 zs state2) state2 := by
      intro active
      change DataTableMode state1.mode at active
      rw [type] at active
      exact False.elim ((by unfold DataTableMode; decide : ¬ DataTableMode TYPE) active)
    have selected2 : DataExitMode state2.mode := selected
    have final := current.decode_update good2 tables2 pending2 (by rfl) selected2
      (byte_view_sizes_setI heap1 zs state2) rfl
    refine ⟨.ok (), regs, setI heap1 zs state2, stream1, state2, ?_, final, selected2, config⟩
    rw [cut, inflateAfterFast_run env1]
    simp only [state2, type, ↓reduceIte, regs]
  · refine ⟨.ok (), regs, heap1, stream1, state1, ?_, current, selected, config⟩
    rw [cut, inflateAfterFast_run env1]
    simp only [type, ↓reduceIte, regs]

/-- The actual fast call retains the common default decoder relation. -/
theorem inflate_LEN_fast_raw_default_J {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8} {ib io ob oo : Nat}
    (E : Env c h r zs z s) (invariant : DefaultDecodeJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = LEN)
    (input : l.next = .ref (.blk ib) io) (output : l.put = .ref (.blk ob) oo)
    (different : ib ≠ ob) (fast : (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    ∃ outcome regs after stream state,
      runX (inflate_LEN c) l h = .ok ((outcome, regs), after) ∧
      DefaultDecodeJ after r zs stream state ∧ DataExitMode state.mode := by
  obtain ⟨outcome, regs, after, stream, state, run, final, modes, _⟩ :=
    inflate_LEN_fast_raw_default_J_configuration E invariant buffers mode input output different fast
  exact ⟨outcome, regs, after, stream, state, run, final, modes⟩

/-- The actual LEN_ mode write establishes J for its full fast continuation. -/
theorem inflate_LEN_start_fast_raw_default_J_configuration {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8} {ib io ob oo : Nat}
    (E : Env c h r zs z s) (invariant : DefaultDecodeJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = LEN_)
    (input : l.next = .ref (.blk ib) io) (output : l.put = .ref (.blk ob) oo)
    (different : ib ≠ ob) (fast : (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    ∃ outcome regs after stream state,
      runX (inflate_LEN_ c) l h = .ok ((outcome, regs), after) ∧
      DefaultDecodeJ after r zs stream state ∧ DataExitMode state.mode ∧ DefaultConfigFrame s state := by
  let good := invariant.good
  let tables := invariant.tables (by rw [mode]; unfold DataTableMode; decide)
  let pending := invariant.pending
  let current := { s with mode := LEN }
  let heap := setI h zs current
  have frame : DecodeStateFrame s current := by rfl
  have currentGood := good.decode_update frame (by change HEAD ≤ LEN ∧ LEN ≤ SYNC; decide)
  have currentTables := tables.decode_update good.live.hs frame
  have currentPending : DataPendingInvariant current := by
    apply dataPendingInvariant_idle (s := current) (by exact pending.sane)
    change LEN ≠ LENEXT ∧ LEN ≠ DIST ∧ LEN ≠ DISTEXT ∧ LEN ≠ MATCH
    decide
  have currentBuffers : DispatchBuffers heap r l bs := by
    have inv := buffers.bits.decode_update zs current
    apply buffers.consume good currentGood (by rw [frame]) _ _ (by rfl)
      (used := 0) (inputAdvance_zero l.next).symm (by omega) (by simpa using inv)
    · intro ref
      exact byte_view_get_setI h zs current ref
    · intro ref
      exact byte_view_ro_setI h zs current ref
  have currentEnv : Env c heap r zs z current := ⟨E.strm, E.st, currentGood.live.hz, currentGood.live.hs⟩
  have currentJ := invariant.decode_update currentGood (fun _ => currentTables) currentPending
    frame (by change DataExitMode LEN; exact Or.inl (by unfold DataTableMode; decide))
    (byte_view_sizes_setI h zs current) rfl
  obtain ⟨outcome, regs, after, stream, state, run, final, finalMode, config⟩ :=
    inflate_LEN_fast_raw_default_J_configuration currentEnv currentJ currentBuffers rfl input output different fast
  have source : runX (inflate_LEN_ c) l h = runX (inflate_LEN c) l heap := by
    unfold inflate_LEN_
    rw [runX_bind, runX_setMode E]
  exact ⟨outcome, regs, after, stream, state, source.trans run, final, finalMode, config⟩


/-- Actual LEN_ normalization retains the common default decoder relation. -/
theorem inflate_LEN_start_fast_raw_default_J {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8} {ib io ob oo : Nat}
    (E : Env c h r zs z s) (invariant : DefaultDecodeJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = LEN_)
    (input : l.next = .ref (.blk ib) io) (output : l.put = .ref (.blk ob) oo)
    (different : ib ≠ ob) (fast : (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    ∃ outcome regs after stream state,
      runX (inflate_LEN_ c) l h = .ok ((outcome, regs), after) ∧
      DefaultDecodeJ after r zs stream state ∧ DataExitMode state.mode := by
  obtain ⟨outcome, regs, after, stream, state, run, final, modes, _⟩ :=
    inflate_LEN_start_fast_raw_default_J_configuration E invariant buffers mode input output different fast
  exact ⟨outcome, regs, after, stream, state, run, final, modes⟩

/-- Actual data dispatch preserves J through slow decoding and the proved
raw fast interface. This internal premise does not restrict a public goal. -/
theorem inflate_dispatch_data_J {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultDecodeJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : DataTableMode s.mode)
    (raw : (s.mode = LEN_ ∨ s.mode = LEN) ∧ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true → RawFastIO l) :
    ∃ outcome regs after stream state,
      runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) ∧
      DefaultDecodeJ after r zs stream state ∧ DataExitMode state.mode := by
  by_cases activeFast : (s.mode = LEN_ ∨ s.mode = LEN) ∧ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true
  · obtain ⟨ib, io, ob, oo, input, output, different⟩ := raw activeFast
    rcases activeFast.1 with start | lengthMode
    · obtain ⟨outcome, regs, after, stream, state, run, final, finalMode⟩ :=
        inflate_LEN_start_fast_raw_default_J E invariant buffers start input output different activeFast.2
      exact ⟨outcome, regs, after, stream, state,
        (inflate_dispatch_LEN_start E l start).trans run, final, finalMode⟩
    · obtain ⟨outcome, regs, after, stream, state, run, final, finalMode⟩ :=
        inflate_LEN_fast_raw_default_J E invariant buffers lengthMode input output different activeFast.2
      exact ⟨outcome, regs, after, stream, state,
        (inflate_dispatch_LEN E l lengthMode).trans run, final, finalMode⟩
  · exact inflate_dispatch_data_slow_J E invariant buffers mode (fun selected fast => activeFast ⟨selected, fast⟩)

/-- The actual data switch simultaneously retains the strong default
relation, exact public buffer accounting and the bounded strict rank.
The distinct-raw fast-entry obligation remains explicit. -/
theorem inflate_dispatch_data_J_rank {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultDecodeJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : DataTableMode s.mode)
    (raw : (s.mode = LEN_ ∨ s.mode = LEN) ∧ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true → RawFastIO l) :
    ∃ outcome regs after stream state used made,
      used ≤ bs.length ∧ runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) ∧
      DefaultDecodeJ after r zs stream state ∧ DataExitMode state.mode ∧
      DispatchBuffers after r regs (bs.drop used) ∧ ByteViewSizes h after ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = inputAdvance l.put made ∧ regs.left.toNat + made = l.left.toNat ∧
      regs.bits.toNat ≤ max l.bits.toNat 22 ∧
      (outcome = .error Ex.leave ∨ (outcome = .ok () ∧ dispatchRank regs state.mode < dispatchRank l s.mode)) := by
  obtain ⟨outcome, regs, after, stream, state, run, current, modes⟩ :=
    inflate_dispatch_data_J E invariant buffers mode raw
  obtain ⟨otherOutcome, otherRegs, otherHeap, otherStream, otherState, used, made,
    usedBound, otherRun, good, _, _, packet, sizes, next, haveCount, put, left, bits, progress⟩ :=
    inflate_dispatch_data_rank E invariant.good invariant.platform invariant.tables buffers invariant.pending mode raw
  rw [run] at otherRun
  cases otherRun
  have streamEq : otherStream = stream := Option.some.inj (good.live.hz.symm.trans current.good.live.hz)
  have stateEq : otherState = state := Option.some.inj (good.live.hs.symm.trans current.good.live.hs)
  subst otherStream otherState
  exact ⟨outcome, regs, after, stream, state, used, made, usedBound, run,
    current, modes, packet, sizes, next, haveCount, put, left, bits, progress⟩

/-- Actual data execution retains the requested reset configuration and
header classification. Slow decoding uses its checked state frame; fast
decoding uses the exact translated callee's writeback. -/
theorem inflate_dispatch_data_configuration {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultDecodeJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : DataTableMode s.mode)
    (raw : (s.mode = LEN_ ∨ s.mode = LEN) ∧ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true → RawFastIO l) :
    ∃ outcome regs after stream state,
      runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) ∧
      Good after r zs stream state ∧ DefaultConfigFrame s state := by
  by_cases activeFast : (s.mode = LEN_ ∨ s.mode = LEN) ∧ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true
  · obtain ⟨ib, io, ob, oo, input, output, different⟩ := raw activeFast
    rcases activeFast.1 with start | lengthMode
    · obtain ⟨outcome, regs, after, stream, state, run, final, _, config⟩ :=
        inflate_LEN_start_fast_raw_default_J_configuration E invariant buffers start input output different activeFast.2
      exact ⟨outcome, regs, after, stream, state,
        (inflate_dispatch_LEN_start E l start).trans run, final.good, config⟩
    · obtain ⟨outcome, regs, after, stream, state, run, final, _, config⟩ :=
        inflate_LEN_fast_raw_default_J_configuration E invariant buffers lengthMode input output different activeFast.2
      exact ⟨outcome, regs, after, stream, state,
        (inflate_dispatch_LEN E l lengthMode).trans run, final.good, config⟩
  · obtain ⟨outcome, regs, after, stream, state, _, _, _, _, _, run,
      good, _, _, _, _, frame, _⟩ :=
      inflate_dispatch_pending E invariant.good invariant.tables buffers invariant.pending mode
        (fun selected fast => activeFast ⟨selected, fast⟩)
    exact ⟨outcome, regs, after, stream, state, run, good, frame.default_config⟩

end Zlib.Inflate.Proofs
