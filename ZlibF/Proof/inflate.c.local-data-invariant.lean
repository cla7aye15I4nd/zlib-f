import ZlibF.Proof.«inflate.c.local-match-pending»
import ZlibF.Proof.«inflate.c.local-default-state»
import ZlibF.Proof.«inflate.c.data-invariant»

/-! Actual decoder execution with local allocation uniqueness. -/
namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inffast.Spec ZlibF.Spec.Public
set_option autoImplicit false
set_option maxRecDepth 8192

theorem inflate_LENEXT_pending_boundary {c : Ctx} {l : IL} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8}
    (E : Env c h r zs z s) (good : LocalGood h cutoff r zs z s) (tables : DataTablesSafe h s)
    (buffers : DispatchBuffers h r l bs) (pending : DataPendingInvariant s) (mode : s.mode = LENEXT) :
    (∃ regs used,
      runX (inflate_LENEXT c) l h = .ok ((.error Ex.leave, regs), h) ∧ used ≤ bs.length ∧
      DispatchBuffers h r regs (bs.drop used) ∧
      stream regs (bs.drop used) = stream l bs ∧ SymbolRegShape l regs ∧ regs.next = inputAdvance l.next used ∧ regs.bits.toNat ≤ max l.bits.toNat 22) ∨
    (∃ regs after state used,
      runX (inflate_LENEXT c) l h = runX (inflate_DIST c) regs after ∧ used ≤ bs.length ∧
      LocalGood after cutoff r zs z state ∧ DataTablesSafe after state ∧
      DispatchBuffers after r regs (bs.drop used) ∧ DataPendingInvariant state ∧
      state.mode = DIST ∧ DecodeStateFrame s state ∧ ByteViewSizes h after ∧
      stream regs (bs.drop used) = (stream l bs).drop s.extra.toNat ∧ SymbolRegShape l regs ∧
      regs.next = inputAdvance l.next used ∧ after = setI h zs state ∧ regs.bits.toNat ≤ max l.bits.toNat 22) := by
  obtain ⟨extra, lower, budget, before, backBound, back⟩ := pending.lenext mode
  rcases inflate_LENEXT_boundary_bounded before E.strm E.st good tables buffers.bits
      extra lower budget back backBound with wait | continued
  · obtain ⟨regs, used, run, usedBound, inv, _, bits, shape, cursor, bitBound⟩ := wait
    have packet := dispatch_consume_local buffers good good rfl (fun _ => rfl) (fun _ => rfl) shape cursor usedBound inv
    exact Or.inl ⟨regs, used, run, usedBound, packet, bits, shape, cursor, by omega⟩
  · obtain ⟨regs, after, state, used, run, usedBound, finalGood, finalTables, inv,
      nextMode, frame, shape, bits, was, finalLower, finalUpper, finalBack, heapEq, cursor, bitBound⟩ := continued
    have packet : DispatchBuffers after r regs (bs.drop used) := by
      apply dispatch_consume_local buffers good finalGood (by rw [frame]) _ _ shape cursor usedBound inv
      · intro ref
        rw [heapEq, byte_view_get_setI]
      · intro ref
        rw [heapEq, byte_view_ro_setI]
    have invariant := dataPendingInvariant_dist (by rw [frame]; exact pending.sane) nextMode
      ⟨⟨finalLower, finalUpper, was⟩, before + s.extra.toNat, by omega, finalBack⟩
    exact Or.inr ⟨regs, after, state, used, run, usedBound, finalGood, finalTables, packet,
      invariant, nextMode, frame, by rw [heapEq]; exact byte_view_sizes_setI h zs state, bits, shape, cursor, heapEq, by omega⟩

theorem inflate_DISTEXT_pending_boundary {c : Ctx} {l : IL} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8}
    (E : Env c h r zs z s) (good : LocalGood h cutoff r zs z s) (tables : DataTablesSafe h s)
    (buffers : DispatchBuffers h r l bs) (pending : DataPendingInvariant s) (mode : s.mode = DISTEXT) :
    (∃ regs used,
      runX (inflate_DISTEXT c) l h = .ok ((.error Ex.leave, regs), h) ∧ used ≤ bs.length ∧
      DispatchBuffers h r regs (bs.drop used) ∧
      stream regs (bs.drop used) = stream l bs ∧ SymbolRegShape l regs ∧ regs.next = inputAdvance l.next used ∧ regs.bits.toNat ≤ max l.bits.toNat 22) ∨
    (∃ regs after state used,
      runX (inflate_DISTEXT c) l h = runX (inflate_MATCH c) regs after ∧ used ≤ bs.length ∧
      LocalGood after cutoff r zs z state ∧ DataTablesSafe after state ∧
      DispatchBuffers after r regs (bs.drop used) ∧ DataPendingInvariant state ∧
      state.mode = MATCH ∧ DecodeStateFrame s state ∧ ByteViewSizes h after ∧
      stream regs (bs.drop used) = (stream l bs).drop s.extra.toNat ∧ SymbolRegShape l regs ∧
      regs.next = inputAdvance l.next used ∧ after = setI h zs state ∧ regs.bits.toNat ≤ max l.bits.toNat 22) := by
  obtain ⟨lengthFacts, extra, lower, budget, before, backBound, back⟩ := pending.distext mode
  rcases inflate_DISTEXT_boundary_bounded before E.strm E.st good tables buffers.bits
      extra lower budget back backBound with wait | continued
  · obtain ⟨regs, used, run, usedBound, inv, _, bits, shape, cursor, bitBound⟩ := wait
    have packet := dispatch_consume_local buffers good good rfl (fun _ => rfl) (fun _ => rfl) shape cursor usedBound inv
    exact Or.inl ⟨regs, used, run, usedBound, packet, bits, shape, cursor, by omega⟩
  · obtain ⟨regs, after, state, used, run, usedBound, finalGood, finalTables, inv,
      nextMode, frame, shape, bits, heapEq, stateEq, finalLower, _, _, cursor, bitBound⟩ := continued
    have packet : DispatchBuffers after r regs (bs.drop used) := by
      apply dispatch_consume_local buffers good finalGood (by rw [frame]) _ _ shape cursor usedBound inv
      · intro ref
        rw [heapEq, byte_view_get_setI]
      · intro ref
        rw [heapEq, byte_view_ro_setI]
    have facts : MatchSafe state := by
      rw [stateEq]
      change 0 < s.length.toNat ∧ s.length.toNat ≤ s.was.toNat ∧ s.was.toNat ≤ 258 ∧ 0 < state.offset.toNat
      obtain ⟨lengthLower, lengthUpper, was⟩ := lengthFacts
      rw [was]
      exact ⟨by omega, Nat.le_refl _, lengthUpper, by omega⟩
    have invariant := dataPendingInvariant_match (by rw [frame]; exact pending.sane) nextMode facts
    exact Or.inr ⟨regs, after, state, used, run, usedBound, finalGood, finalTables, packet,
      invariant, nextMode, frame, by rw [heapEq]; exact byte_view_sizes_setI h zs state, bits, shape, cursor, heapEq, by omega⟩

theorem LocalDecodeJ.decode_update {h after : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState} (invariant : LocalDecodeJ h cutoff r zs z s)
    (current : LocalGood after cutoff r zs stream state) (tables : DataTableInvariant after state)
    (pending : DataPendingInvariant state) (frame : DecodeStateFrame s state)
    (modes : DataExitMode state.mode) (sizes : ByteViewSizes h after) (static : after.static = h.static) :
    LocalDecodeJ after cutoff r zs stream state := by
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

theorem LocalDecodeJ.data_writeback {h after : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState} (invariant : LocalDecodeJ h cutoff r zs z s)
    (current : LocalGood after cutoff r zs stream state) (tables : DataTableInvariant after state)
    (pending : DataPendingInvariant state) (modes : DataExitMode state.mode)
    (held : state.hold.toNat < 2 ^ state.bits.toNat)
    (window : state.wbits = s.wbits) (wrapper : state.wrap = s.wrap) (header : state.head = s.head)
    (static : after.static = h.static) (platform : ZlibF.PlatformMemory.ByteObjectsFit after) :
    LocalDecodeJ after cutoff r zs stream state := by
  obtain ⟨notCodes, notLengths, notCheck, notLength, lower, upper⟩ := dataExitMode_bounds modes
  refine ⟨current, tables, pending, ?_, ?_, held, window.trans invariant.window, ?_,
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

theorem inflate_LIT_default_J {c : Ctx} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : LocalDecodeJ h cutoff r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = LIT) :
    ∃ outcome regs after stream state,
      runX (inflate_LIT c) l h = .ok ((outcome, regs), after) ∧
      LocalDecodeJ after cutoff r zs stream state ∧ DataExitMode state.mode := by
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

theorem inflate_MATCH_default_J {c : Ctx} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : LocalDecodeJ h cutoff r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = MATCH) :
    ∃ outcome regs after stream state,
      runX (inflate_MATCH c) l h = .ok ((outcome, regs), after) ∧
      LocalDecodeJ after cutoff r zs stream state ∧ DataExitMode state.mode := by
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

theorem inflate_DISTEXT_default_J {c : Ctx} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : LocalDecodeJ h cutoff r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = DISTEXT) :
    ∃ outcome regs after stream state,
      runX (inflate_DISTEXT c) l h = .ok ((outcome, regs), after) ∧
      LocalDecodeJ after cutoff r zs stream state ∧ DataExitMode state.mode := by
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

theorem inflate_DIST_default_J {c : Ctx} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : LocalDecodeJ h cutoff r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = DIST) :
    ∃ outcome regs after stream state,
      runX (inflate_DIST c) l h = .ok ((outcome, regs), after) ∧
      LocalDecodeJ after cutoff r zs stream state ∧ DataExitMode state.mode := by
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
      apply dispatch_consume_local buffers good leafGood (by rw [leafFrame]) _ _ (rootShape.trans leafShape)
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
        apply dispatch_consume_local buffers good finalGood (by rw [frame]) _ _ (rootShape.trans leafShape)
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
        apply dispatch_consume_local buffers good baseGood (by rw [baseFrame]) _ _ (rootShape.trans leafShape)
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

theorem inflate_LENEXT_default_J {c : Ctx} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : LocalDecodeJ h cutoff r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = LENEXT) :
    ∃ outcome regs after stream state,
      runX (inflate_LENEXT c) l h = .ok ((outcome, regs), after) ∧
      LocalDecodeJ after cutoff r zs stream state ∧ DataExitMode state.mode := by
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

theorem inflate_LEN_slow_default_J {c : Ctx} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : LocalDecodeJ h cutoff r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = LEN)
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    ∃ outcome regs after stream state,
      runX (inflate_LEN c) l h = .ok ((outcome, regs), after) ∧
      LocalDecodeJ after cutoff r zs stream state ∧ DataExitMode state.mode := by
  let good := invariant.good
  have beforeMode : DataTableMode s.mode := by rw [mode]; unfold DataTableMode; decide
  let tables := invariant.tables beforeMode
  let pending := invariant.pending
  rcases inflate_LEN_slow_lookup_boundary_mode E.st good tables buffers.bits slow with wait | continued
  · obtain ⟨regs, after, state, used, _, usedBound, run, finalGood, finalTables,
      inv, _, bits, shape, frame, bitBound, cursor, heapEq, modeEq⟩ := wait
    have packet : DispatchBuffers after r regs (bs.drop used) := by
      apply dispatch_consume_local buffers good finalGood (by rw [frame]) _ _ shape cursor usedBound inv
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
        apply dispatch_consume_local buffers good finalGood (by rw [frame]) _ _ (rootShape.trans leafShape)
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
        apply dispatch_consume_local buffers good baseGood (by rw [prefixFrame]) _ _ (rootShape.trans leafShape)
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

theorem inflate_LEN_start_slow_default_J {c : Ctx} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : LocalDecodeJ h cutoff r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = LEN_)
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    ∃ outcome regs after stream state,
      runX (inflate_LEN_ c) l h = .ok ((outcome, regs), after) ∧
      LocalDecodeJ after cutoff r zs stream state ∧ DataExitMode state.mode := by
  let good := invariant.good
  let tables := invariant.tables (by rw [mode]; unfold DataTableMode; decide)
  let pending := invariant.pending
  let current := { s with mode := LEN }
  let heap := setI h zs current
  have frame : DecodeStateFrame s current := by rfl
  have currentGood := good.decode_after frame (by change HEAD ≤ LEN ∧ LEN ≤ SYNC; decide)
  have currentTables := tables.decode_update good.live.hs frame
  have currentPending : DataPendingInvariant current := by
    apply dataPendingInvariant_idle (s := current) (by exact pending.sane)
    change LEN ≠ LENEXT ∧ LEN ≠ DIST ∧ LEN ≠ DISTEXT ∧ LEN ≠ MATCH
    decide
  have currentBuffers : DispatchBuffers heap r l bs := by
    have inv := buffers.bits.decode_update zs current
    apply dispatch_consume_local buffers good currentGood (by rw [frame]) _ _ (by rfl)
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

theorem inflate_dispatch_data_slow_J {c : Ctx} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : LocalDecodeJ h cutoff r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : DataTableMode s.mode)
    (slow : s.mode = LEN_ ∨ s.mode = LEN → ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    ∃ outcome regs after stream state,
      runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) ∧
      LocalDecodeJ after cutoff r zs stream state ∧ DataExitMode state.mode := by
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

#print axioms inflate_LENEXT_pending_boundary
#print axioms inflate_DISTEXT_pending_boundary
#print axioms LocalDecodeJ.decode_update
#print axioms LocalDecodeJ.data_writeback
#print axioms inflate_LIT_default_J
#print axioms inflate_MATCH_default_J
#print axioms inflate_DISTEXT_default_J
#print axioms inflate_DIST_default_J
#print axioms inflate_LENEXT_default_J
#print axioms inflate_LEN_slow_default_J
#print axioms inflate_LEN_start_slow_default_J
#print axioms inflate_dispatch_data_slow_J
end Zlib.Inflate.Local
