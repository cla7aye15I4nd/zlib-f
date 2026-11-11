import ZlibF.Proof.«inflate.c.head-default-state»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Stored-block execution only resumes its header, its copy or a block/error boundary. -/
def StoredExitMode (mode : UInt32) : Prop :=
  mode = STORED ∨ mode = COPY_ ∨ mode = COPY ∨ mode = TYPE ∨ mode = BAD

/-- The active stored-block mode excludes initial and terminal history alternatives. -/
theorem DefaultStateJ.stored_format {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (invariant : DefaultStateJ h r zs z s)
    (mode : s.mode = STORED ∨ s.mode = COPY_ ∨ s.mode = COPY) : s.wrap = 0 ∨ s.flags = 0 := by
  rcases invariant.phase with head | bad | mem | sync | format
  · rcases mode with selected | selected | selected <;> rw [selected] at head <;> contradiction
  · rcases mode with selected | selected | selected <;> rw [selected] at bad <;> contradiction
  · rcases mode with selected | selected | selected <;> rw [selected] at mem <;> contradiction
  · rcases mode with selected | selected | selected <;> rw [selected] at sync <;> contradiction
  · exact format

/-- The checked stored-block state frame retains reset fields, header
classification and every clause of the common default relation. -/
theorem DefaultStateJ.stored_update {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState} (invariant : DefaultStateJ h r zs z s)
    (beforeMode : s.mode = STORED ∨ s.mode = COPY_ ∨ s.mode = COPY)
    (current : Good after r zs stream state) (tables : DataTableInvariant after state)
    (pending : DataPendingInvariant state) (frame : DecodeStateFrame s state)
    (modes : StoredExitMode state.mode) (sizes : ByteViewSizes h after) (static : after.static = h.static) :
    DefaultStateJ after r zs stream state := by
  have guards : state.mode ≠ CODELENS ∧ state.mode ≠ LENLENS ∧ state.mode ≠ CHECK ∧ state.mode ≠ LENGTH ∧
      DICTID ≤ state.mode ∧ state.mode ≤ SYNC := by
    rcases modes with selected | selected | selected | selected | selected <;> rw [selected] <;> decide
  have base : DefaultDecodeJ after r zs stream state := by
    refine ⟨current, tables, pending, ?_, ?_, ?_, ?_, ?_, ?_, Or.inr guards.2.2.2.2, ?_, ?_, sizes.platform invariant.platform⟩
    · intro active
      exact False.elim (guards.1 active)
    · intro active
      exact False.elim (guards.2.1 active)
    · rw [frame]
      exact invariant.held
    · rw [frame]
      exact invariant.window
    · rw [frame]
      exact invariant.wrapper
    · exact HeaderMemory.step invariant.header invariant.good current (by rw [frame]) (by rw [frame]) sizes
    · rintro (active | active)
      · exact False.elim (guards.2.2.1 active)
      · exact False.elim (guards.2.2.2.1 active)
    · change after.static = _
      rw [static]
      exact invariant.globals
  have format : state.wrap = 0 ∨ state.flags = 0 := by rw [frame]; exact invariant.stored_format beforeMode
  exact ⟨base, by rw [frame]; exact invariant.requestedBits,
    by rw [frame]; exact invariant.requestedWrap, Or.inr (Or.inr (Or.inr (Or.inr format)))⟩

/-- Actual stored copying preserves the full relation for every admitted
caller byte view, including separated slices of one allocation. -/
theorem inflate_COPY_default_state {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = COPY) :
    ∃ outcome regs after state,
      runX (inflate_COPY c) l h = .ok ((outcome, regs), after) ∧
      DefaultStateJ after r zs z state ∧ StoredExitMode state.mode := by
  obtain ⟨outcome, regs, after, state, _, _, run, current, tables, pending,
    _, sizes, frame, _, _, _, _, _, _, kinds, static, _⟩ :=
    inflate_COPY_boundary_frame E invariant.good invariant.pending buffers mode
  have modes : StoredExitMode state.mode := by
    rcases kinds with ⟨_, _, stateEq⟩ | ⟨_, _, type⟩ | ⟨_, _, copy, _⟩
    · rw [stateEq]; exact Or.inr (Or.inr (Or.inl mode))
    · exact Or.inr (Or.inr (Or.inr (Or.inl type)))
    · exact Or.inr (Or.inr (Or.inl copy))
  exact ⟨outcome, regs, after, state, run,
    invariant.stored_update (Or.inr (Or.inr mode)) current tables pending frame modes sizes static, modes⟩

/-- Actual COPY_ normalization includes its real copying continuation. -/
theorem inflate_COPY_start_default_state {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = COPY_) :
    ∃ outcome regs after state,
      runX (inflate_COPY_ c) l h = .ok ((outcome, regs), after) ∧
      DefaultStateJ after r zs z state ∧ StoredExitMode state.mode := by
  obtain ⟨outcome, regs, after, state, _, _, run, current, tables, pending,
    _, sizes, frame, _, _, _, _, _, _, kinds, static, _⟩ :=
    inflate_COPY_start_boundary_frame E invariant.good invariant.pending buffers mode
  have modes : StoredExitMode state.mode := by
    rcases kinds with ⟨_, _, stateEq⟩ | ⟨_, _, type⟩ | ⟨_, _, copy, _⟩
    · rw [stateEq]; exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl type)))
    · exact Or.inr (Or.inr (Or.inl copy))
  exact ⟨outcome, regs, after, state, run,
    invariant.stored_update (Or.inr (Or.inl mode)) current tables pending frame modes sizes static, modes⟩

/-- The entire actual stored-header branch includes complement checking,
Z_TREES and the actual COPY_ call. Input exhaustion retains the old state. -/
theorem inflate_STORED_default_state {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = STORED) :
    ∃ outcome regs after stream state,
      runX (inflate_STORED c) l h = .ok ((outcome, regs), after) ∧
      DefaultStateJ after r zs stream state ∧ StoredExitMode state.mode := by
  obtain ⟨aligned, _, _⟩ := BYTEBITS_inv buffers.bits
  obtain ⟨outcome, current, used, pull, bound, bitInv, _, _, shape, _, _, _, _, kinds, cursor⟩ :=
    NEEDBITS_run_cursor aligned 32 (by decide)
  have symbolShape : SymbolRegShape l current := by rw [shape]; rfl
  have packet := buffers.consume invariant.good invariant.good rfl (fun _ => rfl) (fun _ => rfl)
    symbolShape cursor bound bitInv
  rcases kinds with normal | wait
  · rw [normal] at pull
    by_cases bad : ((current.hold &&& (0xffff : UInt64)) != ((current.hold >>> 16) ^^^ (0xffff : UInt64))) = true
    · obtain ⟨i, _, run⟩ := inflate_STORED_bad E l current pull bad
      obtain ⟨good, tables, pending, _, sizes, static⟩ :=
        head_bad_packet invariant.good invariant.pending packet bitInv (by rfl) i
      have modes : StoredExitMode ({ s with mode := BAD } : InflateState).mode :=
        Or.inr (Or.inr (Or.inr (Or.inr rfl)))
      exact ⟨.ok (), current, _, _, _, run,
        invariant.stored_update (Or.inl mode) good tables pending (by rfl) modes sizes static, modes⟩
    · let ready := { s with length := current.hold.toUInt32 &&& 0xffff, mode := COPY_ }
      let heap0 := setI h zs ready
      let first := { current with hold := 0, bits := 0 }
      have frame : DecodeStateFrame s ready := by rfl
      have good0 : Good heap0 r zs z ready := invariant.good.decode_update frame
        (by change HEAD ≤ COPY_ ∧ COPY_ ≤ SYNC; decide)
      have pending0 : DataPendingInvariant ready := by
        apply dataPendingInvariant_idle (s := ready) invariant.pending.sane
        change COPY_ ≠ LENEXT ∧ COPY_ ≠ DIST ∧ COPY_ ≠ DISTEXT ∧ COPY_ ≠ MATCH
        decide
      have tables0 : DataTableInvariant heap0 ready :=
        dataTableInvariant_inactive (by change ¬ DataTableMode COPY_; unfold DataTableMode; decide)
      have modes : StoredExitMode ready.mode := Or.inr (Or.inl rfl)
      have state0 := invariant.stored_update (Or.inl mode) good0 tables0 pending0 frame modes
        (byte_view_sizes_setI h zs ready) rfl
      have E0 : Env c heap0 r zs z ready := ⟨E.strm, E.st, good0.live.hz, good0.live.hs⟩
      have inv0 : BitInv heap0 first (bs.drop used) := (INITBITS_inv bitInv).1.decode_update zs ready
      have packet0 : DispatchBuffers heap0 r first (bs.drop used) :=
        buffers.consume invariant.good good0 rfl (fun ref => byte_view_get_setI h zs ready ref)
          (fun ref => byte_view_ro_setI h zs ready ref) (by dsimp only [first]; rw [shape]; rfl) cursor bound inv0
      have sourceCut := inflate_STORED_ok E l current pull bad
      by_cases trees : c.flush = Z_TREES
      · have run : runX (inflate_STORED c) l h = .ok ((.error Ex.leave, first), heap0) := by
          rw [sourceCut]
          simp only [trees, beq_self_eq_true, ↓reduceIte]
          rfl
        exact ⟨.error Ex.leave, first, heap0, z, ready, run, state0, modes⟩
      · have sourceRun : runX (inflate_STORED c) l h = runX (inflate_COPY_ c) first heap0 := by
          rw [sourceCut]
          simp only [beq_iff_eq, trees, ↓reduceIte]
          rfl
        obtain ⟨outcome, regs, after, state, run, final, finalMode⟩ :=
          inflate_COPY_start_default_state E0 state0 packet0 rfl
        exact ⟨outcome, regs, after, z, state, sourceRun.trans run, final, finalMode⟩
  · have run := inflate_STORED_wait (c := c) l current h Ex.leave (by rwa [wait] at pull)
    exact ⟨.error Ex.leave, current, h, z, s, run, invariant, Or.inl mode⟩

/-- All three actual stored-block switch cases retain the full default relation. -/
theorem inflate_dispatch_stored_state {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = STORED ∨ s.mode = COPY_ ∨ s.mode = COPY) :
    ∃ outcome regs after stream state,
      runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) ∧
      DefaultStateJ after r zs stream state ∧ StoredExitMode state.mode := by
  rcases mode with stored | start | copy
  · rw [inflate_dispatch_STORED E l stored]
    exact inflate_STORED_default_state E invariant buffers stored
  · obtain ⟨outcome, regs, after, state, run, final, modes⟩ := inflate_COPY_start_default_state E invariant buffers start
    exact ⟨outcome, regs, after, z, state, (inflate_dispatch_COPY_start E l start).trans run, final, modes⟩
  · obtain ⟨outcome, regs, after, state, run, final, modes⟩ := inflate_COPY_default_state E invariant buffers copy
    exact ⟨outcome, regs, after, z, state, (inflate_dispatch_COPY E l copy).trans run, final, modes⟩

/-- Actual stored-block dispatch preserves the complete default relation,
all public buffer views, exact source/output counts and the strict common
rank. It does not require the fast decoder's raw-block interface. -/
theorem inflate_dispatch_stored_state_rank {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = STORED ∨ s.mode = COPY_ ∨ s.mode = COPY)
    (incoming : l.bits.toNat ≤ 39) :
    ∃ outcome regs after stream state used made, used ≤ bs.length ∧
      runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) ∧
      DefaultStateJ after r zs stream state ∧ StoredExitMode state.mode ∧
      DispatchBuffers after r regs (bs.drop used) ∧ ByteViewSizes h after ∧ DecodeStateFrame s state ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = inputAdvance l.put made ∧ regs.left.toNat + made = l.left.toNat ∧ regs.bits.toNat ≤ 39 ∧
      (outcome = .error Ex.leave ∨ (outcome = .ok () ∧ dispatchRank regs state.mode < dispatchRank l s.mode)) ∧
      after.static = h.static ∧ Shape h after := by
  obtain ⟨outcome, regs, after, stream, state, run, current, modes⟩ :=
    inflate_dispatch_stored_state E invariant buffers mode
  obtain ⟨otherOutcome, otherRegs, otherHeap, otherStream, otherState, used, made, bound, otherRun,
    good, _, _, packet, sizes, frame, next, count, put, left, bits, progress, static, shape⟩ :=
    inflate_dispatch_stored_rank E invariant.good invariant.pending buffers mode incoming
  rw [run] at otherRun
  cases otherRun
  have streamEq : otherStream = stream := Option.some.inj (good.live.hz.symm.trans current.good.live.hz)
  have stateEq : otherState = state := Option.some.inj (good.live.hs.symm.trans current.good.live.hs)
  subst otherStream otherState
  exact ⟨outcome, regs, after, stream, state, used, made, bound, run, current, modes,
    packet, sizes, frame, next, count, put, left, bits, progress, static, shape⟩

end Zlib.Inflate.Proofs
