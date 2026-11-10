import ZlibF.Proof.«inflate.c.default-invariant»
import ZlibF.Proof.«inflate.c.no-return»
import ZlibF.Proof.«inflate.c.pending-dispatch»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Configuration and header classification retained during data decoding. -/
def DefaultConfigFrame (before after : InflateState) : Prop :=
  after.reqbits = before.reqbits ∧ after.reqwrap = before.reqwrap ∧
  after.wrap = before.wrap ∧ after.flags = before.flags ∧ after.wbits = before.wbits

theorem DecodeStateFrame.default_config {s state : InflateState} (frame : DecodeStateFrame s state) :
    DefaultConfigFrame s state := by
  rw [frame]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Modes reached while decoding data or reporting its block/error boundary. -/
def DataExitMode (mode : UInt32) : Prop := DataTableMode mode ∨ mode = TYPE ∨ mode = BAD

theorem dataExitMode_bounds {mode : UInt32} (selected : DataExitMode mode) :
    mode ≠ CODELENS ∧ mode ≠ LENLENS ∧ mode ≠ CHECK ∧ mode ≠ LENGTH ∧ DICTID ≤ mode ∧ mode ≤ SYNC := by
  rcases selected with (selected | selected | selected | selected | selected | selected | selected) | selected | selected <;>
    rw [selected] <;> decide

/-- A checked scalar data update preserves all construction, wrapper,
held-bit and platform clauses of the common default invariant. -/
theorem DefaultDecodeJ.decode_update {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState} (invariant : DefaultDecodeJ h r zs z s)
    (current : Good after r zs stream state) (tables : DataTableInvariant after state)
    (pending : DataPendingInvariant state) (frame : DecodeStateFrame s state)
    (modes : DataExitMode state.mode) (sizes : ByteViewSizes h after) (static : after.static = h.static) :
    DefaultDecodeJ after r zs stream state := by
  obtain ⟨notCodes, notLengths, notCheck, notLength, lower, upper⟩ := dataExitMode_bounds modes
  refine ⟨current, tables, pending, ?_, ?_, ?_, ?_, ?_, ?_, Or.inr ⟨lower, upper⟩, ?_, ?_,
    sizes.platform invariant.platform⟩
  · intro active
    exact False.elim (notCodes active)
  · intro active
    exact False.elim (notLengths active)
  · rw [frame]
    exact invariant.held
  · rw [frame]
    exact invariant.window
  · rw [frame]
    exact invariant.wrapper
  · rw [frame]
    exact invariant.header
  · rintro (active | active)
    · exact False.elim (notCheck active)
    · exact False.elim (notLength active)
  · change after.static = _
    rw [static]
    exact invariant.globals

/-- Data-mode writeback may normalize held bits while retaining the
wrapper configuration. Construction and trailer clauses are inactive. -/
theorem DefaultDecodeJ.data_writeback {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState} (invariant : DefaultDecodeJ h r zs z s)
    (current : Good after r zs stream state) (tables : DataTableInvariant after state)
    (pending : DataPendingInvariant state) (modes : DataExitMode state.mode)
    (held : state.hold.toNat < 2 ^ state.bits.toNat)
    (window : state.wbits = s.wbits) (wrapper : state.wrap = s.wrap) (header : state.head = s.head)
    (static : after.static = h.static) (platform : ZlibF.PlatformMemory.ByteObjectsFit after) :
    DefaultDecodeJ after r zs stream state := by
  obtain ⟨notCodes, notLengths, notCheck, notLength, lower, upper⟩ := dataExitMode_bounds modes
  refine ⟨current, tables, pending, ?_, ?_, held, (by rw [window]; exact invariant.window), ?_,
    header.trans invariant.header, Or.inr ⟨lower, upper⟩, ?_, ?_, platform⟩
  · intro active
    exact False.elim (notCodes active)
  · intro active
    exact False.elim (notLengths active)
  · rw [wrapper]
    exact invariant.wrapper
  · rintro (active | active)
    · exact False.elim (notCheck active)
    · exact False.elim (notLength active)
  · change after.static = _
    rw [static]
    exact invariant.globals

/-- The complete actual literal mode preserves J on both output exhaustion
and its one-byte store, for every supported writable caller byte view. -/
theorem inflate_LIT_default_J {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultDecodeJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = LIT) :
    ∃ outcome regs after stream state,
      runX (inflate_LIT c) l h = .ok ((outcome, regs), after) ∧
      DefaultDecodeJ after r zs stream state ∧ DataExitMode state.mode := by
  have beforeMode : DataTableMode s.mode := by rw [mode]; unfold DataTableMode; decide
  obtain ⟨outcome, regs, after, state, run, current, tables, _, _, _, sizes, frame, _, _, kinds⟩ :=
    inflate_LIT_step E invariant.good (invariant.tables beforeMode) buffers.bits buffers.output buffers.separate
  rcases kinds with ⟨_, _, heapEq, stateEq⟩ | ⟨_, stateEq, _, _, dest, off, array, _, _, heapEq⟩
  · exact ⟨outcome, regs, after, z, state, run, by rw [heapEq, stateEq]; exact invariant,
      by rw [stateEq]; exact Or.inl beforeMode⟩
  · have modes : DataExitMode state.mode := by rw [stateEq]; exact Or.inl (by change DataTableMode LEN; unfold DataTableMode; decide)
    have pending : DataPendingInvariant state := by
      apply dataPendingInvariant_idle (by rw [frame]; exact invariant.pending.sane)
      rw [stateEq]
      change LEN ≠ LENEXT ∧ LEN ≠ DIST ∧ LEN ≠ DISTEXT ∧ LEN ≠ MATCH
      decide
    have static : after.static = h.static := by rw [heapEq]; simp only [setI, byte_view_put_static]
    exact ⟨outcome, regs, after, z, state, run,
      invariant.decode_update current (fun _ => tables) pending frame modes sizes static, modes⟩

/-- Actual MATCH execution preserves J on exhausted output, unavailable
history and overlapping output copies. The old execution theorem supplies
all copying and scalar bounds; its exact heap image retains statics. -/
theorem inflate_MATCH_default_J {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultDecodeJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = MATCH) :
    ∃ outcome regs after stream state,
      runX (inflate_MATCH c) l h = .ok ((outcome, regs), after) ∧
      DefaultDecodeJ after r zs stream state ∧ DataExitMode state.mode := by
  have beforeMode : DataTableMode s.mode := by rw [mode]; unfold DataTableMode; decide
  have facts := invariant.pending.matching mode
  have sane : s.sane ≠ 0 := by rw [invariant.pending.sane]; decide
  by_cases empty : l.left = 0
  · exact ⟨.error Ex.leave, l, h, z, s, inflate_MATCH_wait c h l empty, invariant, Or.inl beforeMode⟩
  · obtain ⟨dest, array, off, put, get, write, room, count, produced, privateWindow⟩ :=
      callerRange_slow_output invariant.good l buffers.output.range buffers.output.nonnull
        buffers.output.count buffers.output.produced
    obtain ⟨outcome, regs, after, stream, state, run, current, tables, _, frame, kinds⟩ :=
      inflate_MATCH_boundary_ranges E invariant.good (invariant.tables beforeMode) buffers.bits put get write
        mode facts.1 facts.2.2.2 sane room count produced privateWindow
        (buffers.bits.output_positions put empty buffers.separate)
    obtain ⟨otherOutcome, otherRegs, otherHeap, otherStream, otherState, _, otherRun, otherGood,
      _, _, pending, sizes, _, _, _, _, _, _⟩ :=
      inflate_MATCH_pending E invariant.good (invariant.tables beforeMode) buffers invariant.pending mode
    rw [run] at otherRun
    cases otherRun
    have sameStream : otherStream = stream := Option.some.inj (otherGood.live.hz.symm.trans current.live.hz)
    have sameState : otherState = state := Option.some.inj (otherGood.live.hs.symm.trans current.live.hs)
    subst otherStream otherState
    have modes : DataExitMode state.mode := by
      rcases kinds with ⟨_, _, _, stateEq⟩ | ⟨_, bad, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, _, _, selected, _⟩
      · rw [stateEq]
        exact Or.inl beforeMode
      · exact Or.inr (Or.inr bad)
      · rcases selected with lengthMode | matching
        · rw [lengthMode]
          exact Or.inl (by unfold DataTableMode; decide)
        · rw [matching]
          exact Or.inl (by unfold DataTableMode; decide)
    have static : after.static = h.static := by
      rcases kinds with ⟨_, _, heapEq, _⟩ | ⟨_, _, _, _, _, heapEq⟩ |
        ⟨_, _, _, _, _, _, _, _, _, heapEq, _⟩
      · rw [heapEq]
      · rw [heapEq]
        simp only [badHeap, setI, ZStreamRef.put_static]
      · rw [heapEq]
        simp only [setI, byte_view_put_static]
    exact ⟨outcome, regs, after, stream, state, run,
      invariant.decode_update current tables pending frame modes sizes static, modes⟩

/-- Actual distance-extra decoding includes the real match-copy continuation.
Both input exhaustion and every copying outcome retain the common invariant. -/
theorem inflate_DISTEXT_default_J {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultDecodeJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = DISTEXT) :
    ∃ outcome regs after stream state,
      runX (inflate_DISTEXT c) l h = .ok ((outcome, regs), after) ∧
      DefaultDecodeJ after r zs stream state ∧ DataExitMode state.mode := by
  have beforeMode : DataTableMode s.mode := by rw [mode]; unfold DataTableMode; decide
  rcases inflate_DISTEXT_pending_boundary E invariant.good (invariant.tables beforeMode)
      buffers invariant.pending mode with wait | continued
  · obtain ⟨regs, _, run, _⟩ := wait
    exact ⟨.error Ex.leave, regs, h, z, s, run, invariant, Or.inl beforeMode⟩
  · obtain ⟨regs, after, state, _, sourceRun, _, good, tables, packet, pending,
      nextMode, frame, sizes, _, _, _, heapEq, _⟩ := continued
    have modes : DataExitMode state.mode := by rw [nextMode]; exact Or.inl (by unfold DataTableMode; decide)
    have current := invariant.decode_update good (fun _ => tables) pending frame modes sizes
      (by rw [heapEq]; rfl)
    obtain ⟨outcome, finalRegs, finalHeap, stream, finalState, run, final, finalMode⟩ :=
      inflate_MATCH_default_J ⟨E.strm, E.st, good.live.hz, good.live.hs⟩ current packet nextMode
    exact ⟨outcome, finalRegs, finalHeap, stream, finalState, sourceRun.trans run, final, finalMode⟩

/-- Actual distance lookup and classification establish J before entering
its real extra-bit and match-copy continuation. -/
theorem inflate_DIST_default_J {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultDecodeJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = DIST) :
    ∃ outcome regs after stream state,
      runX (inflate_DIST c) l h = .ok ((outcome, regs), after) ∧
      DefaultDecodeJ after r zs stream state ∧ DataExitMode state.mode := by
  let good := invariant.good
  have beforeMode : DataTableMode s.mode := by rw [mode]; unfold DataTableMode; decide
  let tables := invariant.tables beforeMode
  let pending := invariant.pending
  obtain ⟨lengthFacts, before, backBound, back⟩ := pending.dist mode
  rcases inflate_DIST_lookup_boundary_bounded before E.st good tables buffers.bits back backBound with wait | continued
  · obtain ⟨regs, used, _, usedBound, run, inv, _, bits, shape, cursor, bitBound⟩ := wait
    exact ⟨.error Ex.leave, regs, h, z, s, run, invariant, Or.inl beforeMode⟩
  · obtain ⟨regs, rootHeap, rootState, used, dropped, _, usedBound, droppedBound,
      sourceRun, rootGood, rootTables, rootInv, leaf, enough, rootBack, rootBits, rootShape,
      _, _, rootHeapEq, rootStateEq, rootCursor, rootBitBound⟩ := continued
    obtain ⟨leafRegs, leafHeap, leafState, consumeRun, leafGood, leafTables, leafInv,
      _, leafShape, leafHeapEq, leafStateEq, leafBits, leafCount, _, leafCursor⟩ :=
      distFinish_consume_cursor before dropped E.st rootGood rootTables leaf rootBack backBound enough rootInv
    let codeBits := dropped + regs.here.bits.toNat
    have codeBound : codeBits ≤ 15 := by have := leaf.1; omega
    have parsed : Zlib.Inflate.Proofs.stream leafRegs (bs.drop used) =
        (Zlib.Inflate.Proofs.stream l bs).drop codeBits := by rw [leafBits, rootBits, List.drop_drop]
    have leafBitBound : leafRegs.bits.toNat ≤ max l.bits.toNat 22 := by rw [leafCount]; omega
    have leafHeapOriginal : leafHeap = setI h zs leafState := by rw [leafHeapEq, rootHeapEq, setI_setI]
    have leafFrame : DecodeStateFrame s leafState := by
      unfold DecodeStateFrame
      rw [leafStateEq, rootStateEq]
    have leafPacket : DispatchBuffers leafHeap r leafRegs (bs.drop used) := by
      apply buffers.consume good leafGood (by rw [leafFrame]) _ _ (rootShape.trans leafShape)
        (leafCursor.trans rootCursor) usedBound leafInv
      · intro ref
        rw [leafHeapOriginal, byte_view_get_setI]
      · intro ref
        rw [leafHeapOriginal, byte_view_ro_setI]
    have source : runX (inflate_DIST c) l h = runX (distLeafTail c regs.here) leafRegs leafHeap :=
      sourceRun.trans consumeRun
    rcases distLeafTail_boundary_frame E.strm E.st leafGood leafTables leafInv leaf with invalid | valid
    · obtain ⟨after, stream, state, run, finalGood, data, inv, bad, stateEq, heapEq⟩ := invalid
      have frame : DecodeStateFrame s state := by unfold DecodeStateFrame; rw [stateEq, leafStateEq, rootStateEq]
      have packet : DispatchBuffers after r leafRegs (bs.drop used) := by
        apply buffers.consume good finalGood (by rw [frame]) _ _ (rootShape.trans leafShape)
          (leafCursor.trans rootCursor) usedBound inv
        · intro ref
          rw [heapEq, byte_view_get_setI, byte_view_get_stream_put, leafHeapOriginal, byte_view_get_setI]
        · intro ref
          rw [heapEq, byte_view_ro_setI, byte_view_ro_stream_put, leafHeapOriginal, byte_view_ro_setI]
      have idle : DataPendingInvariant state := by
        apply dataPendingInvariant_idle (by rw [frame]; exact pending.sane)
        rw [bad]
        decide
      have sizes : ByteViewSizes h after := by
        rw [heapEq]
        have leafSizes : ByteViewSizes h leafHeap := by rw [leafHeapOriginal]; exact byte_view_sizes_setI h zs leafState
        exact leafSizes.trans
          ((byte_view_sizes_stream_put leafHeap r stream).trans (byte_view_sizes_setI _ zs state))
      have selected : DataExitMode state.mode := Or.inr (Or.inr bad)
      have static : after.static = h.static := by
        rw [heapEq, leafHeapOriginal]
        simp only [setI, ZStreamRef.put_static]
      exact ⟨.ok (), leafRegs, after, stream, state, source.trans run,
        invariant.decode_update finalGood data idle frame selected sizes static, selected⟩
    · obtain ⟨baseHeap, baseState, classifyRun, baseGood, baseTables, baseInv, nextMode,
        baseHeapEq, baseStateEq, extra, lower, budget⟩ := valid
      have baseFrame : DecodeStateFrame s baseState := by
        unfold DecodeStateFrame
        rw [baseStateEq, leafStateEq, rootStateEq]
      have baseHeapOriginal : baseHeap = setI h zs baseState := by rw [baseHeapEq, leafHeapOriginal, setI_setI]
      have baseLength : PendingLengthSafe baseState := by
        rw [baseStateEq, leafStateEq, rootStateEq]
        exact lengthFacts
      have baseBack : baseState.back = Int32.ofNat (before + codeBits) := by
        rw [baseStateEq, leafStateEq]
        simp only [codeBits, Nat.add_assoc]
      have basePending := dataPendingInvariant_distext (by rw [baseFrame]; exact pending.sane) nextMode
        ⟨baseLength, extra, lower, budget, before + codeBits, by omega, baseBack⟩
      have basePacket : DispatchBuffers baseHeap r leafRegs (bs.drop used) := by
        apply buffers.consume good baseGood (by rw [baseFrame]) _ _ (rootShape.trans leafShape)
          (leafCursor.trans rootCursor) usedBound baseInv
        · intro ref
          rw [baseHeapOriginal, byte_view_get_setI]
        · intro ref
          rw [baseHeapOriginal, byte_view_ro_setI]
      have baseEnv : Env c baseHeap r zs z baseState := ⟨E.strm, E.st, baseGood.live.hz, baseGood.live.hs⟩
      have selected : DataExitMode baseState.mode := by
        rw [nextMode]; exact Or.inl (by unfold DataTableMode; decide)
      have baseSizes : ByteViewSizes h baseHeap := by
        rw [baseHeapOriginal]; exact byte_view_sizes_setI h zs baseState
      have current := invariant.decode_update baseGood (fun _ => baseTables) basePending
        baseFrame selected baseSizes (by rw [baseHeapOriginal]; rfl)
      obtain ⟨outcome, finalRegs, after, stream, state, run, final, finalMode⟩ :=
        inflate_DISTEXT_default_J baseEnv current basePacket nextMode
      exact ⟨outcome, finalRegs, after, stream, state,
        source.trans (classifyRun.trans run), final, finalMode⟩

/-- Actual length-extra decoding includes the real distance and copy continuation.
Both input exhaustion and every copying outcome retain the common invariant. -/
theorem inflate_LENEXT_default_J {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultDecodeJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = LENEXT) :
    ∃ outcome regs after stream state,
      runX (inflate_LENEXT c) l h = .ok ((outcome, regs), after) ∧
      DefaultDecodeJ after r zs stream state ∧ DataExitMode state.mode := by
  have beforeMode : DataTableMode s.mode := by rw [mode]; unfold DataTableMode; decide
  rcases inflate_LENEXT_pending_boundary E invariant.good (invariant.tables beforeMode)
      buffers invariant.pending mode with wait | continued
  · obtain ⟨regs, _, run, _⟩ := wait
    exact ⟨.error Ex.leave, regs, h, z, s, run, invariant, Or.inl beforeMode⟩
  · obtain ⟨regs, after, state, _, sourceRun, _, good, tables, packet, pending,
      nextMode, frame, sizes, _, _, _, heapEq, _⟩ := continued
    have modes : DataExitMode state.mode := by rw [nextMode]; exact Or.inl (by unfold DataTableMode; decide)
    have current := invariant.decode_update good (fun _ => tables) pending frame modes sizes
      (by rw [heapEq]; rfl)
    obtain ⟨outcome, finalRegs, finalHeap, stream, finalState, run, final, finalMode⟩ :=
      inflate_DIST_default_J ⟨E.strm, E.st, good.live.hz, good.live.hs⟩ current packet nextMode
    exact ⟨outcome, finalRegs, finalHeap, stream, finalState, sourceRun.trans run, final, finalMode⟩


/-- Actual slow length decoding preserves J through literal, end-of-block,
invalid-symbol and the full length/distance/match continuation. -/
theorem inflate_LEN_slow_default_J {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultDecodeJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = LEN)
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    ∃ outcome regs after stream state,
      runX (inflate_LEN c) l h = .ok ((outcome, regs), after) ∧
      DefaultDecodeJ after r zs stream state ∧ DataExitMode state.mode := by
  let good := invariant.good
  have beforeMode : DataTableMode s.mode := by rw [mode]; unfold DataTableMode; decide
  let tables := invariant.tables beforeMode
  let pending := invariant.pending
  rcases inflate_LEN_slow_lookup_boundary_mode E.st good tables buffers.bits slow with wait | continued
  · obtain ⟨regs, after, state, used, _, usedBound, run, finalGood, finalTables,
      inv, _, bits, shape, frame, bitBound, cursor, heapEq, modeEq⟩ := wait
    have packet : DispatchBuffers after r regs (bs.drop used) := by
      apply buffers.consume good finalGood (by rw [frame]) _ _ shape cursor usedBound inv
      · intro ref
        rw [heapEq, byte_view_get_setI]
      · intro ref
        rw [heapEq, byte_view_ro_setI]
    have idle : DataPendingInvariant state := by
      apply dataPendingInvariant_idle (by rw [frame]; exact pending.sane)
      rw [modeEq, mode]
      decide
    have selected : DataExitMode state.mode := by rw [modeEq]; exact Or.inl beforeMode
    exact ⟨.error Ex.leave, regs, after, z, state, run,
      invariant.decode_update finalGood (fun _ => finalTables) idle frame selected
        (by rw [heapEq]; exact byte_view_sizes_setI h zs state) (by rw [heapEq]; rfl), selected⟩
  · obtain ⟨regs, rootHeap, rootState, used, dropped, _, usedBound, droppedBound, sourceRun,
      rootGood, rootTables, rootInv, leaf, enough, rootBack, rootBits, rootShape, rootFrame,
      _, rootBitBound, rootHeapEq, rootCursor⟩ := continued
    have backNat : rootState.back.toInt = dropped := by rw [rootBack]; exact back_ofNat_small dropped droppedBound
    obtain ⟨leafRegs, leafHeap, leafState, consumeRun, leafGood, leafTables, leafInv,
      leafFrame, leafShape, lengthEq, leafBack, leafBits, leafCount, _, leafHeapEq, leafCursor⟩ :=
      lenFinish_consume_cursor dropped E.st rootGood rootTables leaf backNat enough rootInv
    let codeBits := dropped + regs.here.bits.toNat
    have codeBound : codeBits ≤ 15 := by have := leaf.1; omega
    have parsed : Zlib.Inflate.Proofs.stream leafRegs (bs.drop used) =
        (Zlib.Inflate.Proofs.stream l bs).drop codeBits := by rw [leafBits, rootBits, List.drop_drop]
    have leafBitBound : leafRegs.bits.toNat ≤ max l.bits.toNat 22 := by rw [leafCount]; omega
    have leafHeapOriginal : leafHeap = setI h zs leafState := by rw [leafHeapEq, rootHeapEq, setI_setI]
    have source : runX (inflate_LEN c) l h = runX (lenLeafTail c regs.here) leafRegs leafHeap :=
      sourceRun.trans consumeRun
    rcases lenLeafTail_boundary_frame E.strm E.st leafGood leafTables leafInv leaf lengthEq with terminal | valid
    · obtain ⟨after, stream, state, run, finalGood, data, inv, modes, finalFrame, heapEq⟩ := terminal
      have frame := rootFrame.trans (leafFrame.trans finalFrame)
      have packet : DispatchBuffers after r leafRegs (bs.drop used) := by
        apply buffers.consume good finalGood (by rw [frame]) _ _ (rootShape.trans leafShape)
          (leafCursor.trans rootCursor) usedBound inv
        · intro ref
          rw [heapEq, byte_view_get_setI, byte_view_get_stream_put, leafHeapOriginal, byte_view_get_setI]
        · intro ref
          rw [heapEq, byte_view_ro_setI, byte_view_ro_stream_put, leafHeapOriginal, byte_view_ro_setI]
      have idle : DataPendingInvariant state := by
        apply dataPendingInvariant_idle (by rw [frame]; exact pending.sane)
        rcases modes with literalMode | typeMode | badMode
        · rw [literalMode]; decide
        · rw [typeMode]; decide
        · rw [badMode]; decide
      have sizes : ByteViewSizes h after := by
        rw [heapEq]
        have leafSizes : ByteViewSizes h leafHeap := by rw [leafHeapOriginal]; exact byte_view_sizes_setI h zs leafState
        exact leafSizes.trans ((byte_view_sizes_stream_put leafHeap r stream).trans (byte_view_sizes_setI _ zs state))
      have selected : DataExitMode state.mode := by
        rcases modes with literalMode | typeMode | badMode
        · rw [literalMode]; exact Or.inl (by unfold DataTableMode; decide)
        · exact Or.inr (Or.inl typeMode)
        · exact Or.inr (Or.inr badMode)
      have static : after.static = h.static := by
        rw [heapEq, leafHeapOriginal]
        simp only [setI, ZStreamRef.put_static]
      exact ⟨.ok (), leafRegs, after, stream, state, source.trans run,
        invariant.decode_update finalGood data idle frame selected sizes static, selected⟩
    · obtain ⟨baseHeap, baseState, classifyRun, baseGood, baseTables, baseInv, nextMode,
        baseFrame, extra, lower, budget, retainedBack, baseHeapEq⟩ := valid
      have prefixFrame := rootFrame.trans (leafFrame.trans baseFrame)
      have baseHeapOriginal : baseHeap = setI h zs baseState := by rw [baseHeapEq, leafHeapOriginal, setI_setI]
      have basePending := dataPendingInvariant_lenext (by rw [prefixFrame]; exact pending.sane) nextMode
        ⟨extra, lower, budget, codeBits, codeBound, retainedBack.trans leafBack⟩
      have basePacket : DispatchBuffers baseHeap r leafRegs (bs.drop used) := by
        apply buffers.consume good baseGood (by rw [prefixFrame]) _ _ (rootShape.trans leafShape)
          (leafCursor.trans rootCursor) usedBound baseInv
        · intro ref
          rw [baseHeapOriginal, byte_view_get_setI]
        · intro ref
          rw [baseHeapOriginal, byte_view_ro_setI]
      have baseEnv : Env c baseHeap r zs z baseState := ⟨E.strm, E.st, baseGood.live.hz, baseGood.live.hs⟩
      have selected : DataExitMode baseState.mode := by
        rw [nextMode]; exact Or.inl (by unfold DataTableMode; decide)
      have baseSizes : ByteViewSizes h baseHeap := by
        rw [baseHeapOriginal]; exact byte_view_sizes_setI h zs baseState
      have current := invariant.decode_update baseGood (fun _ => baseTables) basePending
        prefixFrame selected baseSizes (by rw [baseHeapOriginal]; rfl)
      obtain ⟨outcome, finalRegs, after, stream, state, run, final, finalMode⟩ :=
        inflate_LENEXT_default_J baseEnv current basePacket nextMode
      exact ⟨outcome, finalRegs, after, stream, state,
        source.trans (classifyRun.trans run), final, finalMode⟩

/-- The actual LEN_ mode write establishes J for its full slow continuation. -/
theorem inflate_LEN_start_slow_default_J {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultDecodeJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = LEN_)
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    ∃ outcome regs after stream state,
      runX (inflate_LEN_ c) l h = .ok ((outcome, regs), after) ∧
      DefaultDecodeJ after r zs stream state ∧ DataExitMode state.mode := by
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
  obtain ⟨outcome, regs, after, stream, state, run, final, finalMode⟩ :=
    inflate_LEN_slow_default_J currentEnv currentJ currentBuffers rfl slow
  have source : runX (inflate_LEN_ c) l h = runX (inflate_LEN c) l heap := by
    unfold inflate_LEN_
    rw [runX_bind, runX_setMode E]
  exact ⟨outcome, regs, after, stream, state, source.trans run, final, finalMode⟩

/-- The actual seven-way data switch retains J through every slow path.
The fast guard is an explicit internal branch premise. -/
theorem inflate_dispatch_data_slow_J {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultDecodeJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : DataTableMode s.mode)
    (slow : s.mode = LEN_ ∨ s.mode = LEN → ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    ∃ outcome regs after stream state,
      runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) ∧
      DefaultDecodeJ after r zs stream state ∧ DataExitMode state.mode := by
  rcases mode with start | lengthMode | lengthExtra | distanceMode | distanceExtra | matchMode | literalMode
  · obtain ⟨outcome, regs, after, stream, state, run, final, finalMode⟩ :=
      inflate_LEN_start_slow_default_J E invariant buffers start (slow (Or.inl start))
    exact ⟨outcome, regs, after, stream, state,
      (inflate_dispatch_LEN_start E l start).trans run, final, finalMode⟩
  · obtain ⟨outcome, regs, after, stream, state, run, final, finalMode⟩ :=
      inflate_LEN_slow_default_J E invariant buffers lengthMode (slow (Or.inr lengthMode))
    exact ⟨outcome, regs, after, stream, state,
      (inflate_dispatch_LEN E l lengthMode).trans run, final, finalMode⟩
  · obtain ⟨outcome, regs, after, stream, state, run, final, finalMode⟩ :=
      inflate_LENEXT_default_J E invariant buffers lengthExtra
    exact ⟨outcome, regs, after, stream, state,
      (inflate_dispatch_LENEXT E l lengthExtra).trans run, final, finalMode⟩
  · obtain ⟨outcome, regs, after, stream, state, run, final, finalMode⟩ :=
      inflate_DIST_default_J E invariant buffers distanceMode
    exact ⟨outcome, regs, after, stream, state,
      (inflate_dispatch_DIST E l distanceMode).trans run, final, finalMode⟩
  · obtain ⟨outcome, regs, after, stream, state, run, final, finalMode⟩ :=
      inflate_DISTEXT_default_J E invariant buffers distanceExtra
    exact ⟨outcome, regs, after, stream, state,
      (inflate_dispatch_DISTEXT E l distanceExtra).trans run, final, finalMode⟩
  · obtain ⟨outcome, regs, after, stream, state, run, final, finalMode⟩ :=
      inflate_MATCH_default_J E invariant buffers matchMode
    exact ⟨outcome, regs, after, stream, state,
      (inflate_dispatch_MATCH E l matchMode).trans run, final, finalMode⟩
  · obtain ⟨outcome, regs, after, stream, state, run, final, finalMode⟩ :=
      inflate_LIT_default_J E invariant buffers literalMode
    exact ⟨outcome, regs, after, stream, state,
      (inflate_dispatch_LIT E l literalMode).trans run, final, finalMode⟩

end Zlib.Inflate.Proofs
